import Macaulean.Language.Design.Binding

/-! Executable design IR with direct locations, captured activations, first-class
symbol reification and real while nodes. Lists are a reference/prototype layout;
indexed persistent stores are a separately stated optimization TODO.
-/
namespace Macaulean.Language.Design.Machine

structure Frame where
  scope : ScopeId
  layout : List SymbolId
  values : List Value
  parent : Option ActivationId
  deriving Repr, Inhabited
structure Closure where
  scope : ScopeId
  parameters : List SymbolId
  layout : List SymbolId
  body : Code
  captured : Option ActivationId
  deriving Repr, Inhabited
structure State where
  catalog : Catalog
  globals : List Value
  frames : List Frame
  closures : List Closure := []
  actors : Actors
  deriving Repr, Inhabited

def initial (c : Catalog) : State :=
  { catalog := c, globals := c.globalSeeds.map Prod.snd, actors := c.bootstrapActors
    frames := [⟨⟨0⟩, (c.scopes[0]?.getD {}).layout,
      List.replicate (c.scopes[0]?.getD {}).layout.length .null, none⟩] }

def frameAt : Nat → Option ActivationId → State → Except String ActivationId
  | _, none, _ => .error "no active frame"
  | 0, some id, s =>
    if id.index < s.frames.length then .ok id else .error "invalid activation"
  | n + 1, some id, s => do
    let some frame := s.frames[id.index]? | .error "invalid activation"
    frameAt n frame.parent s

def read (r : Ref) (active : Option ActivationId) (s : State) : Except String Value := do
  match r.location with
  | .global slot =>
    let some v := s.globals[slot]? | .error "invalid global slot"
    return v
  | .lexical depth slot =>
    let id ← frameAt depth active s
    let some f := s.frames[id.index]? | .error "invalid activation"
    let some v := f.values[slot]? | .error "invalid local slot"
    return v

def reify (r : Ref) (active : Option ActivationId) (s : State) : Except String Value := do
  match r.location with
  | .global _ => return .symbol r.symbol none
  | .lexical depth _ => return .symbol r.symbol (some (← frameAt depth active s))

def write (r : Ref) (v : Value) (active : Option ActivationId) (s : State) : Except String State := do
  let some info := s.catalog.symbols[r.symbol.index]? | .error "invalid declaration"
  if info.isProtected then .error "protected binding" else
    match r.location with
    | .global slot =>
      if slot < s.globals.length then return { s with globals := s.globals.set slot v }
      else .error "invalid global slot"
    | .lexical depth slot =>
      let id ← frameAt depth active s
      let some f := s.frames[id.index]? | .error "invalid activation"
      if slot < f.values.length then
        return { s with frames := s.frames.set id.index { f with values := f.values.set slot v } }
      else .error "invalid local slot"

def lift (r : Except String α) (s : State) : Result State α :=
  match r with | .ok v => .done v s | .error e => .error e s

def allocateClosure (sc : ScopeId) (ps layout : List SymbolId) (body : Code)
    (active : Option ActivationId) (s : State) : Value × State :=
  (.closure s.closures.length,
    { s with closures := s.closures ++ [⟨sc, ps, layout, body, active⟩] })

def enter (f : Closure) (args : List Value) (s : State) : Except String (ActivationId × State) :=
  if args.length != f.parameters.length then .error "arity mismatch"
  else if f.parameters != f.layout.take f.parameters.length then .error "invalid parameter layout"
  else
    let frame : Frame := ⟨f.scope, f.layout,
      args ++ List.replicate (f.layout.length - args.length) .null, f.captured⟩
    .ok (⟨s.frames.length⟩, { s with frames := s.frames ++ [frame] })

mutual
/-- Depth bounds are implementation resources, not a semantic step count.
Errors and exhaustion retain reached state; no D-specific error quirk is imported. -/
def eval : Nat → Code → Option ActivationId → State → Result State Value
  | 0, _, _, s => .exhausted s
  | fuel + 1, code, active, s =>
    match code with
    | .int n => .done (.int n) s
    | .read r => lift (read r active s) s
    | .quote r => lift (reify r active s) s
    | .unary op a => (eval fuel a active s).bind fun v s' => lift (dispatch s'.actors op [v]) s'
    | .binary op a b => (eval fuel a active s).bind fun va s1 =>
      (eval fuel b active s1).bind fun vb s2 => lift (dispatch s2.actors op [va, vb]) s2
    | .set r rhs => (eval fuel rhs active s).bind fun v s' =>
      match write r v active s' with
      | .ok after => .done v after
      | .error e => .error e s'
    | .seq a b => (eval fuel a active s).bind fun _ s' => eval fuel b active s'
    | .ifElse p yes no => (eval fuel p active s).bind fun v s' =>
      match v with
      | .bool true => eval fuel yes active s'
      | .bool false => eval fuel no active s'
      | _ => .error "condition must be Boolean" s'
    | .whileDo test body => (eval fuel test active s).bind fun v s' =>
      match v with
      | .bool false => .done .null s'
      | .bool true => (eval fuel body active s').bind fun _ s'' =>
        eval fuel (.whileDo test body) active s''
      | _ => .error "condition must be Boolean" s'
    | .lambda sc ps layout body =>
      let (v, s') := allocateClosure sc ps layout body active s
      .done v s'
    | .call f args => (eval fuel f active s).bind fun fn s1 =>
      (evalMany fuel args active s1).bind fun vs s2 => call fuel fn vs s2

def evalMany : Nat → List Code → Option ActivationId → State → Result State (List Value)
  | 0, _, _, s => .exhausted s
  | _ + 1, [], _, s => .done [] s
  | fuel + 1, a :: rest, active, s => (eval fuel a active s).bind fun v s1 =>
    (evalMany fuel rest active s1).bind fun vs s2 => .done (v :: vs) s2

def call : Nat → Value → List Value → State → Result State Value
  | 0, _, _, s => .exhausted s
  | fuel + 1, .closure id, args, s =>
    match s.closures[id]? with
    | none => .error "invalid closure" s
    | some f => match enter f args s with
      | .error e => .error e s
      | .ok (activation, s') => eval fuel f.body (some activation) s'
  | _ + 1, _, _, s => .error "value is not callable" s
end

end Macaulean.Language.Design.Machine
