import Macaulean.Verification.Examples.GcdTranslation.Program

/-!
# Euclid: independent source meaning and explicit proof TODOs

This module states the missing theorems as `def ... : Prop`, following the
repository's `Verification.Contracts` convention. It does not install axioms,
admitted proofs, approvals, or a proof of mathematical gcd correctness.

`Source.Eval` is deliberately independent of `Runtime.eval` and `lowerPlan`.
It specifies only the successful exact-integer fragment used in this example.
It is NOT a semantics for arbitrary Term values, dynamic global calls,
redeclaration/shadowing, nontermination, or error traces. The source store uses
names only because the example has three distinct fixed binding sites; a general
binder theorem must use declaration/activation identities (GCD-04).
-/
namespace Macaulean.M2.Verification.Examples.GcdTranslation

namespace Source

abbrev Store := String → Value

def locals : List String := ["a", "b", "r"]
def initial (a b : Int) : Store := fun name =>
  if name = "a" then .zz a else if name = "b" then .zz b else .null

def update (store : Store) (name : String) (value : Value) : Store :=
  fun other => if other = name then value else store other

def absInt (n : Int) : Int := if n < 0 then -n else n

@[simp] theorem update_same (s : Store) (x : String) (v : Value) :
    update s x v x = v := by simp [update]
@[simp] theorem update_other (s : Store) (x y : String) (v : Value) (h : y ≠ x) :
    update s x v y = s y := by simp [update, h]

/-- Exact rules for the leaf fragment, not evaluation through the target.
The `abs` rule is a contract for the explicit helper in gcd.m2. AbsBridge below
requires its actual Runtime closure to implement this rule; it is not assumed
true by the definition of the relation. -/
inductive Eval : Term → Store → Store → Value → Prop where
  | int (s : Store) (n : Int) : Eval (.int n) s s (.zz n)
  | read (s : Store) (x : String) (hx : x ∈ locals) :
      Eval (.var x) s s (s x)
  | neg {t : Term} {s s' : Store} {n : Int} :
      Eval t s s' (.zz n) → Eval (.unop .neg t) s s' (.zz (-n))
  | rem {a b : Term} {s s1 s2 : Store} {m n : Int} :
      Eval a s s1 (.zz m) → Eval b s1 s2 (.zz n) →
      Eval (.binop .rem a b) s s2 (.zz (m % n))
  | ne {a b : Term} {s s1 s2 : Store} {m n : Int} :
      Eval a s s1 (.zz m) → Eval b s1 s2 (.zz n) →
      Eval (.binop .ne a b) s s2 (.bool (decide (m ≠ n)))
  | lt {a b : Term} {s s1 s2 : Store} {m n : Int} :
      Eval a s s1 (.zz m) → Eval b s1 s2 (.zz n) →
      Eval (.binop .lt a b) s s2 (.bool (decide (m < n)))
  | abs {t : Term} {s s' : Store} {n : Int} :
      Eval t s s' (.zz n) →
      Eval (.apply (.var "abs") t) s s' (.zz (absInt n))
  | set {t : Term} {s s' : Store} {v : Value} (x : String) :
      x ∈ locals → Eval t s s' v →
      Eval (.assign x t) s (update s' x v) v
  | temporary {t : Term} {s s' : Store} {v : Value} :
      Eval t s s' v →
      Eval (.localAssign "r" t) s (update s' "r" v) v
  | seq {a b : Term} {s s1 s2 : Store} {v w : Value} :
      Eval a s s1 v → Eval b s1 s2 w → Eval (.seq a b) s s2 w

/-- Finite successful executions. The recursive while premise is a smaller
DERIVATION, even though it contains the same program syntax. -/
inductive Exec : Plan → Store → Store → Value → Prop where
  | leaf {t : Term} {s s' : Store} {v : Value} :
      Eval t s s' v → Exec (.leaf t) s s' v
  | seq {a b : Plan} {s s1 s2 : Store} {v w : Value} :
      Exec a s s1 v → Exec b s1 s2 w → Exec (.seq a b) s s2 w
  | whileFalse {test : Term} {body : Plan} {s s1 : Store} :
      Eval test s s1 (.bool false) →
      Exec (.whileDo test body) s s1 .null
  | whileTrue {test : Term} {body : Plan} {s s1 s2 s3 : Store} {v : Value} :
      Eval test s s1 (.bool true) →
      Exec body s1 s2 v → Exec (.whileDo test body) s2 s3 .null →
      Exec (.whileDo test body) s s3 .null

/-- The graph of the SOURCE computation. No occurrence of Runtime.eval,
executePlan, lowerPlan, or mathematical gcd defines this graph. -/
def Graph (a b z : Int) : Prop :=
  ∃ final, Exec bodyPlan (initial a b) final (.zz z)

end Source

/-- The helper's exact code, already expressible in production Lexical.Code. -/
def absCode : Lexical.Code :=
  .ifElse (.binop .lt (.read (.slot 0 0)) (.int 0))
    (.unop .neg (.read (.slot 0 0))) (.read (.slot 0 0))

/-- An actual installed closure, not an arbitrary binding named abs. -/
def AbsInstalled (state : Runtime.State) : Prop :=
  ∃ id, state.env.lookup "abs" = some (.closure id) ∧
    state.heap.functions[id]? =
      some (.closure (.fixed ["n"]) 1 absCode [])

def slotFor (name : String) : Nat :=
  if name = "a" then 0 else if name = "b" then 1 else 2

/-- A real three-cell runtime frame. Distinctness prevents writing a from
silently changing b. Existing cells may be at any offset in a larger heap. -/
def FrameValid (frames : Runtime.Frames) (state : Runtime.State) : Prop :=
  ∃ cells outer, frames = cells :: outer ∧ cells.length = 3 ∧
    cells.Pairwise (fun i j => i ≠ j) ∧
    ∀ i ∈ cells, i < state.heap.cells.length

/-- Actual readRef operations, not an unrelated Nat → Int toy memory. -/
def Related (source : Source.Store) (frames : Runtime.Frames)
    (state : Runtime.State) : Prop :=
  FrameValid frames state ∧
    ∀ name ∈ Source.locals,
      Runtime.readRef (.slot 0 (slotFor name)) frames state = .ok (source name)

/-- Auxiliaries allocated by abs may extend the heap. Existing non-local cells,
global bindings, function definitions and algebraic ring identities must stay
unchanged. This is an explicit closed-call observation, NOT contextual equivalence
under arbitrary reflection of heap allocation. -/
def OutsideUnchanged (frames : Runtime.Frames)
    (before after : Runtime.State) : Prop :=
  after.env = before.env ∧
  after.heap.functions = before.heap.functions ∧
  after.heap.nextRing = before.heap.nextRing ∧
  ∀ i v, before.heap.cells[i]? = some v → i ∉ frames.headD [] →
    after.heap.cells[i]? = some v

namespace TODO

/-- GCD-02. Close the helper contract against the actual Runtime.call.
Prove from absCode's comparison/negation branches and fixed-argument allocation.
The statement deliberately quantifies over arbitrary integers and installed
states, not only the example (1071,462). -/
def AbsBridge : Prop :=
  ∀ before n, AbsInstalled before →
    ∃ minimumDepth, ∀ depth, minimumDepth ≤ depth →
      ∃ fn after, before.env.lookup "abs" = some fn ∧
        Runtime.call depth fn (.zz n) before = .ok (.zz (Source.absInt n), after) ∧
        AbsInstalled after ∧ OutsideUnchanged [] before after

/-- GCD-03. Concrete resolution and parsing of SUPPORTED leaf source.
Full while-source parsing has no existing Term constructor: it is GCD-01,
not an axiom or a theorem placeholder asserting something currently false. -/
def LeafSyntax : Prop :=
  parse "a = abs a; b = abs b" = .ok initializeTerm ∧
  parse "b != 0" = .ok conditionTerm ∧
  parse "r := a % b; a = b; b = r" = .ok iterationTerm ∧
  parse "a" = .ok resultTerm ∧ LoweringShape

/-- GCD-04. The reusable local-store update lemma for this frame relation.
No gcd, arithmetic, function call or loop hypothesis occurs here. -/
def WritePreserves : Prop :=
  ∀ source frames before name value,
    Related source frames before → name ∈ Source.locals →
    ∃ after,
      Runtime.writeRef (.slot 0 (slotFor name)) value frames before = .ok after ∧
      Related (Source.update source name value) frames after ∧
      OutsideUnchanged frames before after

/-- GCD-05. Leaf compilation preserves independently specified successful
execution. This is a family of propositions, not a blanket theorem for arbitrary
Terms/Resolvers. Apply it to the four closed, resolved leaves below. -/
def LeafPreserves (term : Term) (code : Lexical.Code) : Prop :=
  ∀ source source' value frames before,
    Related source frames before → AbsInstalled before →
    Source.Eval term source source' value →
    ∃ minimumDepth, ∀ depth, minimumDepth ≤ depth →
      ∃ after, Runtime.eval depth code frames before = .ok (value, after) ∧
        Related source' frames after ∧ AbsInstalled after ∧
        OutsideUnchanged frames before after

/-- Establish agreement of integer ne/lt through the existing rational fallback,
in addition to remainder_leaf. Do not assume Value.toRat? casts preserve ordering
without discharging the elementary cast lemmas. -/
def ScalarOperations : Prop :=
  ∀ a b : Int,
    evalBinOp .ne (.zz a) (.zz b) = .ok (.bool (decide (a ≠ b))) ∧
    evalBinOp .lt (.zz a) (.zz b) = .ok (.bool (decide (a < b)))

/-- GCD-06a. Generic loop/sequence lifting for any related plan pair.
A future proof uses induction on Source.Exec, with the recursive while execution
as its own smaller derivation, and increasing bounds for the target driver. -/
def PlanPreserves (plan : Plan) (code : CodePlan) : Prop :=
  ∀ source source' value frames before,
    Related source frames before → AbsInstalled before →
    Source.Exec plan source source' value →
    ∃ minimumControl minimumDepth,
      ∀ controlDepth runtimeDepth,
        minimumControl ≤ controlDepth → minimumDepth ≤ runtimeDepth →
        ∃ after,
          executePlan controlDepth runtimeDepth code frames before = .ok (value, after) ∧
          Related source' frames after ∧ AbsInstalled after ∧
          OutsideUnchanged frames before after

/-- GCD-06b. Successful machine runs must have a source derivation as well.
This is stronger than testing one run and separate from existence of enough fuel. -/
def PlanReflects (plan : Plan) (code : CodePlan) : Prop :=
  ∀ source frames before controlDepth runtimeDepth value after,
    Related source frames before → AbsInstalled before →
    executePlan controlDepth runtimeDepth code frames before = .ok (value, after) →
    ∃ source', Source.Exec plan source source' value ∧
      Related source' frames after ∧ OutsideUnchanged frames before after

/-- GCD-07. Total existence for this integer program. This prevents a
successful-return-only contract from being satisfied by an always-failing runner.
Use abs nonnegativity and strict decrease of b on an iteration; no gcd identity. -/
def SourceTerminates : Prop := ∀ a b : Int, ∃ z, Source.Graph a b z

/-- GCD-08. The body harness initializes the real frame and helper correctly.
Full production closure application/return is a further integration TODO. -/
def SetupCorrect : Prop :=
  ∀ a b : Int, ∃ minimumDepth, ∀ depth, minimumDepth ≤ depth →
    ∃ frames state, setup depth a b = .ok (frames, state) ∧
      Related (Source.initial a b) frames state ∧ AbsInstalled state

/-- A useful end-to-end BODY target: finite source meaning iff some sufficiently
resourced harness run returns z. This does not claim that the whole source string
has passed through the production while parser or DSL. -/
def BodyTranslation : Prop :=
  ∀ a b z : Int,
    Source.Graph a b z ↔
      ∃ controlDepth runtimeDepth after,
        runBody controlDepth runtimeDepth a b = .ok (.zz z, after)

/-- A reviewable list of proof obligations. No value of this structure is
constructed by this PR. Approval or a concrete #guard cannot populate it. -/
structure Proofs : Prop where
  leafSyntax : LeafSyntax
  writePreserves : WritePreserves
  absBridge : AbsBridge
  scalarOperations : ScalarOperations
  initialize : LeafPreserves initializeTerm expectedInitialize
  condition : LeafPreserves conditionTerm expectedCondition
  iteration : LeafPreserves iterationTerm expectedIteration
  result : LeafPreserves resultTerm expectedResult
  forward : PlanPreserves bodyPlan lowered.1
  backward : PlanReflects bodyPlan lowered.1
  setup : SetupCorrect
  termination : SourceTerminates
  translation : BodyTranslation

end TODO
end Macaulean.M2.Verification.Examples.GcdTranslation
