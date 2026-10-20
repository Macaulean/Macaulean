import Macaulean.Interpreter.Parser
import Macaulean.Interpreter.Runtime
import Macaulean.Interpreter.Semantics
import Macaulean.Interpreter.SourceFile

/-!
# Euclid: actual interpreter components and the missing while seam

This is a worked example, NOT a new production interpreter. `Plan` adds only
structured composition/while around existing `Term`s; `CodePlan` does the same
around existing `Lexical.Code`. Remove these adapters when GCD-01 adds while to
the production pipeline. All leaf compilation and execution use the real
`Lexical.resolve` and `Runtime.eval`.

The literal source file is not parsed successfully by the baseline: while/do
are missing. `lowerPlan bodyPlan` is consequently NOT yet a translation of the
whole source file. GCD-01/GCD-03/GCD-09 record the missing source/DSL connections.
No claim in this module uses the native D interpreter as its specification.
-/
namespace Macaulean.M2.Verification.Examples.GcdTranslation

open Lexical

/-- Kept verbatim as an input artifact, including the actual while loop. -/
def sourceText : String := m2_source% "../../../../Examples/GcdTranslation/gcd.m2"

/-- The helper is written in the existing source language, not an external CAS. -/
def absBody : Term :=
  .ifElse (.binop .lt (.var "n") (.int 0)) (.unop .neg (.var "n")) (.var "n")
def absDefinition : Term := .assign "abs" (.lambda (.fixed ["n"]) absBody)

def initializeTerm : Term :=
  .seq (.assign "a" (.apply (.var "abs") (.var "a")))
       (.assign "b" (.apply (.var "abs") (.var "b")))
def conditionTerm : Term := .binop .ne (.var "b") (.int 0)
def iterationTerm : Term :=
  .seq (.localAssign "r" (.binop .rem (.var "a") (.var "b")))
    (.seq (.assign "a" (.var "b")) (.assign "b" (.var "r")))
def resultTerm : Term := .var "a"

/-- Only the missing control seam; do not duplicate arithmetic/function syntax. -/
inductive Plan where
  | leaf (term : Term)
  | seq (first second : Plan)
  | whileDo (condition : Term) (body : Plan)
  deriving Repr

inductive CodePlan where
  | leaf (code : Code)
  | seq (first second : CodePlan)
  | whileDo (condition : Code) (body : CodePlan)
  deriving Repr

/-- Same sequence/control structure as the source function body. -/
def bodyPlan : Plan :=
  .seq (.leaf initializeTerm)
    (.seq (.whileDo conditionTerm (.leaf iterationTerm)) (.leaf resultTerm))

/-- Source-ordered resolution, using the existing resolver for every Term.
While does not create a scope. Its body's declarations are resolved once, not
once per dynamic iteration. This adapter is provisional until GCD-01. -/
def lowerPlan : Plan → Resolver → CodePlan × Resolver
  | .leaf t, r =>
    let (c, r) := Lexical.resolve t r
    (.leaf c, r)
  | .seq a b, r =>
    let (a, r) := lowerPlan a r
    let (b, r) := lowerPlan b r
    (.seq a b, r)
  | .whileDo test body, r =>
    let (test, r) := Lexical.resolve test r
    let (body, r) := lowerPlan body r
    (.whileDo test body, r)

def parameters : Parameters := .fixed ["a", "b"]
def parameterResolver : Resolver := (Resolver.declareMany parameters.names {}).2
def lowered : CodePlan × Resolver := lowerPlan bodyPlan parameterResolver

def aRef : Ref := .slot 0 0
def bRef : Ref := .slot 0 1
def rRef : Ref := .slot 0 2

def expectedInitialize : Code :=
  .seq (.set aRef (.apply (.read (.global "abs")) (.read aRef)))
       (.set bRef (.apply (.read (.global "abs")) (.read bRef)))
def expectedCondition : Code := .binop .ne (.read bRef) (.int 0)
def expectedIteration : Code :=
  .seq (.set rRef (.binop .rem (.read aRef) (.read bRef)))
    (.seq (.set aRef (.read bRef)) (.set bRef (.read rRef)))
def expectedResult : Code := .read aRef

def expectedPlan : CodePlan :=
  .seq (.leaf expectedInitialize)
    (.seq (.whileDo expectedCondition (.leaf expectedIteration)) (.leaf expectedResult))

/-- A finite, concrete lowering check, distinct from general preservation. -/
def LoweringShape : Prop :=
  lowered.1 = expectedPlan ∧ lowered.2.current.count = 3 ∧
  lowered.2.lookup "a" = aRef ∧ lowered.2.lookup "b" = bRef ∧
  lowered.2.lookup "r" = rRef

/-- A test driver around real leaf execution, not a claimed production while.
Both bounds are DEPTH bounds. They are not a count of total executed steps.
Exhaustion remains the baseline `.fuelExhausted` error. A future resumable budget
interface is a separate design choice, not silently imposed on this baseline. -/
def executePlan : Nat → Nat → CodePlan → Runtime.Frames → Runtime.State → Runtime.Result Value
  | 0, _, _, _, _ => .error (.error .fuelExhausted)
  | fuel + 1, depth, .leaf code, frames, state =>
    Runtime.eval depth code frames state
  | fuel + 1, depth, .seq first second, frames, state => do
    let (_, state) ← executePlan fuel depth first frames state
    executePlan fuel depth second frames state
  | fuel + 1, depth, .whileDo test body, frames, state => do
    let (value, state) ← Runtime.eval depth test frames state
    match value with
    | .bool false => return (.null, state)
    | .bool true =>
      let (_, state) ← executePlan fuel depth body frames state
      executePlan fuel depth (.whileDo test body) frames state
    | _ => .error (.error (.conditionNotBoolean value.className))

/-- Install the explicit abs helper and allocate the function's THREE slots once.
This sets up a body test; it does not claim to run the source's outer declaration
or `Runtime.call` on a production while-containing closure. See GCD-08. -/
def setup (depth : Nat) (a b : Int) : Runtime.Result Runtime.Frames := do
  let (_, state) ← Runtime.eval depth (Lexical.prepare absDefinition).1 [] {}
  let (cells, state) := state.allocate [.zz a, .zz b, .null]
  return ([cells], state)

def runBody (controlDepth runtimeDepth : Nat) (a b : Int) : Runtime.Result Value := do
  let (frames, state) ← setup runtimeDepth a b
  executePlan controlDepth runtimeDepth lowered.1 frames state

/-- A named bounded computation is already usable in Lean propositions. It is
not a total Int → Int function and does not assert any preservation theorem. -/
def result (controlDepth runtimeDepth : Nat) (a b : Int) : Except Error Value :=
  (Runtime.finish (runBody controlDepth runtimeDepth a b)).map Prod.fst

/-- Inspect one actual iteration in an isolated frame. Useful for detecting
assignment-order and slot-aliasing mistakes without relying on a gcd oracle. -/
def iterationResult (depth : Nat) (a b : Int) : Except Error (List Value) := do
  let (cells, state) := ({} : Runtime.State).allocate [.zz a, .zz b, .null]
  let (_, state) ← Runtime.finish (Runtime.eval depth expectedIteration [cells] state)
  return [← Runtime.readRef aRef [cells] state,
          ← Runtime.readRef bRef [cells] state,
          ← Runtime.readRef rRef [cells] state]

/-- Existing arithmetic theorem reused verbatim: no new modulo axiom. -/
theorem remainder_leaf (a b : Int) :
    evalBinOp .rem (.zz a) (.zz b) = .ok (.zz (a % b)) := rfl

/-- Existing semantics already supplies the Euclidean remainder facts; these
are needed for termination later, not for source/slot simulation itself. -/
example (a b : Int) (hb : b ≠ 0) :
    ∃ q r, evalBinOp .quot (.zz a) (.zz b) = .ok (.zz q) ∧
      evalBinOp .rem (.zz a) (.zz b) = .ok (.zz r) ∧
      a = b * q + r ∧ 0 ≤ r ∧ r < b.natAbs :=
  quot_rem_spec a b hb

end Macaulean.M2.Verification.Examples.GcdTranslation
