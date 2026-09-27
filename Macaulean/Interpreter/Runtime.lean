import Macaulean.Interpreter.Eval
import Macaulean.Interpreter.Lexical

/-!
# Pure lexical runtime

Captured cells, closures, and fresh ring identities live in immutable session data.
Evaluation is depth-bounded. Polynomial operations invoke pure Lean functions,
never a foreign engine. Global publication of ring variables deliberately leaves
lexically shadowing cells untouched, matching native M2.
-/
namespace Macaulean.M2.Runtime
open Lexical
abbrev Frames := List (List Nat)
inductive Function where
  | closure (params : Parameters) (slots : Nat) (body : Code) (captured : Frames)
  | composition (outer inner : Value)
  | predicate (op : LogicOp) (left right : Value)
  | negated (fn : Value)
  deriving Repr, Inhabited
structure Heap where
  cells : List Value := []
  functions : List Function := []
  nextRing : Nat := 0
  deriving Repr, Inhabited
structure State where
  env : Env := prelude
  heap : Heap := {}
  deriving Repr, Inhabited

def State.allocate (s : State) (values : List Value) : List Nat × State :=
  let base := s.heap.cells.length
  ((List.range values.length).map (base + ·),
    { s with heap := { s.heap with cells := s.heap.cells ++ values } })
def State.function (s : State) (f : Function) : Value × State :=
  (.closure s.heap.functions.length,
    { s with heap := { s.heap with functions := s.heap.functions ++ [f] } })
def cellAt (frames : Frames) (depth index : Nat) : Option Nat := do
  let frame ← frames[depth]?
  frame[index]?
def readRef (ref : Ref) (frames : Frames) (s : State) : Except Error Value :=
  match ref with
  | .global name => match s.env.lookup name with
    | some value => .ok value
    | none => .error (.unboundVar name)
  | .slot d i => do
    let some cell := cellAt frames d i | .error .invalidReference
    let some value := s.heap.cells[cell]? | .error .invalidReference
    return value

def checkWritable : Ref → Except Error Unit
  | .global name => if name ∈ protectedNames then .error (.protectedSymbol name) else .ok ()
  | .slot .. => .ok ()
def writeRef (ref : Ref) (value : Value) (frames : Frames) (s : State) : Except Error State := do
  checkWritable ref
  match ref with
  | .global name => return { s with env := (name, value) :: s.env }
  | .slot d i =>
    let some cell := cellAt frames d i | .error .invalidReference
    if cell < s.heap.cells.length then
      return { s with heap := { s.heap with cells := s.heap.cells.set cell value } }
    else .error .invalidReference
def writeMany : List Ref → List Value → Frames → State → Except Error State
  | [], [], _, s => .ok s
  | r :: rs, v :: vs, frames, s => do
    writeMany rs vs frames (← writeRef r v frames s)
  | rs, vs, _, _ => .error (.assignmentArity rs.length vs.length)

/-- Validate all names before publishing anything or advancing ring identity. -/
def State.polynomialRing (s : State) (base : Value) (names : List String) : Except Error (Value × State) := do
  unless base = .algebra .rationals do
    .error (.algebra "only polynomial rings over QQ are supported")
  if names.eraseDups.length != names.length then
    .error (.algebra "duplicate polynomial names require the indexed-variable extension")
  else
    names.forM fun x => checkWritable (.global x)
    let r : Polynomials.RingInfo := ⟨s.heap.nextRing, names⟩
    let vars := (names.zip (List.range names.length)).map fun (x,i) =>
      (x, Value.algebra (.poly r (Polynomials.generator names.length i)))
    let env := vars.foldl (fun env (x,v) => (x,v) :: env) s.env
    let heap := { s.heap with nextRing := s.heap.nextRing + 1 }
    let next : State := { env := env, heap := heap }
    return (.algebra (.ring r), next)

def arguments (params : Parameters) (arg : Value) : Except Error (List Value) :=
  match params with
  | .variadic _ => .ok [arg]
  | .fixed names =>
    let values := match arg with | .sequence xs => xs | _ => [arg]
    if names.length = values.length then .ok values
    else .error (.arity names.length values.length)
inductive Signal where
  | error (error : Error)
  | returned (value : Value) (state : State)
  deriving Repr
abbrev Result (α : Type) := Except Signal (α × State)
def liftResult (r : Except Error α) : Except Signal α := r.mapError Signal.error
def finish (r : Result Value) : Except Error (Value × State) :=
  match r with
  | .ok result => .ok result
  | .error (.returned value state) => .ok (value, state)
  | .error (.error error) => .error error
def catchReturn (r : Result Value) : Result Value :=
  match r with
  | .error (.returned v s) => .ok (v, s)
  | other => other

def callable : Value → Bool
  | .closure _ | .algebra (.builtin _) => true | _ => false

mutual
def eval : Nat → Code → Frames → State → Except Signal (Value × State)
  | 0, _, _, _ => .error (.error .fuelExhausted)
  | fuel + 1, code, frames, s => do
    match code with
    | .int n => return (.zz n, s)
    | .empty => return (.null, s)
    | .read ref => return (← liftResult (readRef ref frames s), s)
    | .unop op a =>
      let (v, s) ← eval fuel a frames s
      match op, v with
      | .notOp, .closure _ | .notOp, .algebra (.builtin _) => return s.function (.negated v)
      | _, _ => return (← liftResult (evalUnOp op v), s)
    | .binop op a b =>
      let (va, s) ← eval fuel a frames s
      let (vb, s) ← eval fuel b frames s
      match op, va, vb with
      | .compose, .closure _, .closure _ => return s.function (.composition va vb)
      | .compose, .algebra (.builtin _), _ =>
        if callable vb then return s.function (.composition va vb)
        else return (← liftResult (evalBinOp op va vb), s)
      | .compose, .closure _, .algebra (.builtin _) => return s.function (.composition va vb)
      | _, _, _ => return (← liftResult (evalBinOp op va vb), s)
    | .logic op a b =>
      let (va, s) ← eval fuel a frames s
      if va = .bool op.shortCircuit then return (va, s)
      let (vb, s) ← eval fuel b frames s
      if callable va && callable vb then return s.function (.predicate op va vb)
      else return (← liftResult (evalLogicOp op va vb), s)
    | .ifThen c yes =>
      let (v, s) ← eval fuel c frames s
      match v with
      | .bool true => eval fuel yes frames s
      | .bool false => return (.null, s)
      | _ => .error (.error (.conditionNotBoolean v.className))
    | .ifElse c yes no =>
      let (v, s) ← eval fuel c frames s
      match v with
      | .bool true => eval fuel yes frames s
      | .bool false => eval fuel no frames s
      | _ => .error (.error (.conditionNotBoolean v.className))
    | .set ref rhs =>
      liftResult (checkWritable ref)
      let (value, s) ← eval fuel rhs frames s
      return (value, ← liftResult (writeRef ref value frames s))
    | .setMany refs rhs =>
      let (value, s) ← eval fuel rhs frames s
      let values := value.elements?.getD [value]
      if refs.length != values.length then
        .error (.error (.assignmentArity refs.length values.length))
      else return (value, ← liftResult (writeMany refs values frames s))
    | .indexAssign a i v =>
      let (a, s) ← eval fuel a frames s
      let (i, s) ← eval fuel i frames s
      let (v, _) ← eval fuel v frames s
      match a with
      | .list _ | .sequence _ => .error (.error (.immutableCollection a.className))
      | _ => .error (.error (.noMethod "#=" [a.className, i.className, v.className]))
    | .seq a b =>
      let (_, s) ← eval fuel a frames s
      eval fuel b frames s
    | .listLit xs =>
      let (xs, s) ← evalMany fuel xs frames s
      return (.list xs, s)
    | .sequence xs =>
      let (xs, s) ← evalMany fuel xs frames s
      return (.sequence xs, s)
    | .lambda params slots body => return s.function (.closure params slots body frames)
    | .apply f a =>
      let (f, s) ← eval fuel f frames s
      let (a, s) ← eval fuel a frames s
      call fuel f a s
    | .symbol name ref =>
      match ref with
      | .slot d i =>
        let some cell := cellAt frames d i | .error (.error .invalidReference)
        return (.symbol name cell, s)
      | _ => .error (.error .invalidReference)
    | .returnTerm a =>
      let (v, s) ← eval fuel a frames s
      .error (.returned v s)
    | .polyRing base names =>
      let (base, s) ← eval fuel base frames s
      liftResult (s.polynomialRing base names)

def evalMany : Nat → List Code → Frames → State → Except Signal (List Value × State)
  | 0, _, _, _ => .error (.error .fuelExhausted)
  | _ + 1, [], _, s => .ok ([], s)
  | fuel + 1, x :: xs, frames, s => do
    let (v, s) ← eval fuel x frames s
    let (vs, s) ← evalMany fuel xs frames s
    return (v :: vs, s)

def call : Nat → Value → Value → State → Except Signal (Value × State)
  | 0, _, _, _ => .error (.error .fuelExhausted)
  | fuel + 1, fn, arg, s => do
    if let .algebra (.builtin p) := fn then
      return (← liftResult (Polynomials.callPrimitive p arg), s)
    let .closure id := fn
      | .error (.error (.noMethod "SPACE" [fn.className, arg.className]))
    let some entry := s.heap.functions[id]? | .error (.error .invalidReference)
    match entry with
    | .closure params slots body captured =>
      let values ← liftResult (arguments params arg)
      let (frame, s) := s.allocate (values ++ List.replicate (slots - values.length) .null)
      catchReturn (eval fuel body (frame :: captured) s)
    | .composition f g =>
      let (v, s) ← call fuel g arg s
      call fuel f v s
    | .predicate op f g =>
      let (v, s) ← call fuel f arg s
      if v = .bool op.shortCircuit then return (v, s)
      let (w, s) ← call fuel g arg s
      return (← liftResult (evalLogicOp op v w), s)
    | .negated f =>
      let (v, s) ← call fuel f arg s
      return (← liftResult (evalUnOp .notOp v), s)
end

def defaultFuel : Nat := 4096
structure InputResult where
  value : Value
  state : State
  scope : Scope
  fileFrame : List Nat
  warnings : List String
  deriving Repr

def evaluate (t : Term) (s : State := {}) (scope : Scope := {})
    (fileFrame : List Nat := []) (fuel : Nat := defaultFuel) : Except Error InputResult := do
  let (code, scope, warnings) := Lexical.prepare t scope
  let (fresh, s) := s.allocate (List.replicate (scope.count - fileFrame.length) .null)
  let frame := fileFrame ++ fresh
  let (value, s) ← finish (eval fuel code [frame] s)
  return ⟨value, s, scope, frame, warnings⟩
end Macaulean.M2.Runtime
