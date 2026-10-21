import Macaulean.Language.Design.Machine

/-! Independent relational meaning for the chosen language fragment.
The source uses SymbolId-keyed bindings, not machine depth/slot accesses. It
never invokes Machine.eval, Binding.lower, or a gcd implementation. Both sides
share primitiveValue as the deliberately chosen arithmetic contract.
Only finite normal executions are specified here. Error/divergence/host-event
relations are explicit TODOs, not claimed consequences of this normal relation.
-/
namespace Macaulean.Language.Design.Meaning

structure Frame where
  scope : ScopeId
  bindings : List (SymbolId × Value)
  parent : Option ActivationId
  deriving Repr, Inhabited
structure Closure where
  scope : ScopeId
  parameters : List SymbolId
  layout : List SymbolId
  body : Bound
  captured : Option ActivationId
  deriving Repr, Inhabited
structure State where
  catalog : Catalog
  globals : List (SymbolId × Value)
  frames : List Frame
  closures : List Closure := []
  actors : Actors
  deriving Repr, Inhabited

def initial (c : Catalog) : State :=
  { catalog := c, globals := c.globalSeeds, actors := c.bootstrapActors
    frames := [⟨⟨0⟩, (c.scopes[0]?.getD {}).layout.map (fun id => (id, .null)), none⟩] }

/-- Search by declaration identity, not a compiler-provided depth or slot. -/
def findLocal : Nat → SymbolId → Option ActivationId → State → Except String ActivationId
  | 0, _, _, _ => .error "invalid lexical chain"
  | _ + 1, _, none, _ => .error "no binding activation"
  | fuel + 1, sym, some id, s => do
    let some f := s.frames[id.index]? | .error "invalid activation"
    if (f.bindings.lookup sym).isSome then return id
    else findLocal fuel sym f.parent s

def reify (sym : SymbolId) (active : Option ActivationId) (s : State) : Except String Value := do
  let some info := s.catalog.symbols[sym.index]? | .error "unknown declaration"
  match info.home with
  | .global .. => return .symbol sym none
  | .lexical .. => return .symbol sym (some (← findLocal (s.frames.length + 1) sym active s))

def read (sym : SymbolId) (active : Option ActivationId) (s : State) : Except String Value := do
  let ref ← reify sym active s
  match ref with
  | .symbol _ none =>
    let some v := s.globals.lookup sym | .error "uninitialized global binding"
    return v
  | .symbol _ (some id) =>
    let some f := s.frames[id.index]? | .error "invalid activation"
    let some v := f.bindings.lookup sym | .error "missing local binding"
    return v
  | _ => .error "invalid symbol reification"

def write (sym : SymbolId) (v : Value) (active : Option ActivationId) (s : State) : Except String State := do
  let some info := s.catalog.symbols[sym.index]? | .error "unknown declaration"
  if info.isProtected then .error "protected binding" else do
    let ref ← reify sym active s
    match ref with
    | .symbol _ none => return { s with globals := (sym, v) :: s.globals }
    | .symbol _ (some id) =>
      let some f := s.frames[id.index]? | .error "invalid activation"
      return { s with frames := s.frames.set id.index { f with bindings := (sym, v) :: f.bindings } }
    | _ => .error "invalid symbol reification"

def allocateClosure (sc : ScopeId) (ps layout : List SymbolId) (body : Bound)
    (active : Option ActivationId) (s : State) : Value × State :=
  (.closure s.closures.length,
    { s with closures := s.closures ++ [⟨sc, ps, layout, body, active⟩] })

/-- Parameters are matched by SymbolId. The target instead fills a slot prefix:
proving those representations agree is a real frame-layout obligation. -/
def enter (f : Closure) (args : List Value) (s : State) : Except String (ActivationId × State) :=
  if args.length != f.parameters.length then .error "arity mismatch"
  else
    let arguments := f.parameters.zip args
    let frame : Frame := ⟨f.scope,
      f.layout.map (fun sym => (sym, (arguments.lookup sym).getD .null)), f.captured⟩
    .ok (⟨s.frames.length⟩, { s with frames := s.frames ++ [frame] })

mutual
inductive Eval : Bound → Option ActivationId → State → State → Value → Prop where
  | int (a : Option ActivationId) (s : State) (n : Int) : Eval (.int n) a s s (.int n)
  | read {id : SymbolId} {a : Option ActivationId} {s : State} {v : Value} :
      Meaning.read id a s = .ok v → Eval (.read id) a s s v
  | quote {id : SymbolId} {a : Option ActivationId} {s : State} {v : Value} :
      reify id a s = .ok v → Eval (.quote id) a s s v
  | unary {op : OperatorRef} {e : Bound} {a : Option ActivationId}
      {s s1 : State} {v w : Value} : Eval e a s s1 v → dispatch s1.actors op [v] = .ok w →
      Eval (.unary op e) a s s1 w
  | binary {op : OperatorRef} {l r : Bound} {a : Option ActivationId}
      {s s1 s2 : State} {v w z : Value} :
      Eval l a s s1 v → Eval r a s1 s2 w → dispatch s2.actors op [v, w] = .ok z →
      Eval (.binary op l r) a s s2 z
  | set {id : SymbolId} {rhs : Bound} {a : Option ActivationId}
      {s s1 s2 : State} {v : Value} :
      Eval rhs a s s1 v → Meaning.write id v a s1 = .ok s2 → Eval (.set id rhs) a s s2 v
  | seq {l r : Bound} {a : Option ActivationId} {s s1 s2 : State} {v w : Value} :
      Eval l a s s1 v → Eval r a s1 s2 w → Eval (.seq l r) a s s2 w
  | ifTrue {p y n : Bound} {a : Option ActivationId} {s s1 s2 : State} {v : Value} :
      Eval p a s s1 (.bool true) → Eval y a s1 s2 v → Eval (.ifElse p y n) a s s2 v
  | ifFalse {p y n : Bound} {a : Option ActivationId} {s s1 s2 : State} {v : Value} :
      Eval p a s s1 (.bool false) → Eval n a s1 s2 v → Eval (.ifElse p y n) a s s2 v
  | whileFalse {p b : Bound} {a : Option ActivationId} {s s1 : State} :
      Eval p a s s1 (.bool false) → Eval (.whileDo p b) a s s1 .null
  | whileTrue {p b : Bound} {a : Option ActivationId} {s s1 s2 s3 : State} {v : Value} :
      Eval p a s s1 (.bool true) → Eval b a s1 s2 v →
      Eval (.whileDo p b) a s2 s3 .null → Eval (.whileDo p b) a s s3 .null
  | lambda {sc : ScopeId} {ps layout : List SymbolId} {body : Bound}
      {a : Option ActivationId} {s s1 : State} {v : Value} :
      allocateClosure sc ps layout body a s = (v, s1) →
      Eval (.lambda sc ps layout body) a s s1 v
  | call {f : Bound} {args : List Bound} {a : Option ActivationId}
      {s s1 s2 s3 : State} {fn v : Value} {vs : List Value} :
      Eval f a s s1 fn → EvalMany args a s1 s2 vs → Call fn vs s2 s3 v →
      Eval (.call f args) a s s3 v
inductive EvalMany : List Bound → Option ActivationId → State → State → List Value → Prop where
  | nil (a : Option ActivationId) (s : State) : EvalMany [] a s s []
  | cons {e : Bound} {es : List Bound} {a : Option ActivationId}
      {s s1 s2 : State} {v : Value} {vs : List Value} :
      Eval e a s s1 v → EvalMany es a s1 s2 vs → EvalMany (e :: es) a s s2 (v :: vs)
inductive Call : Value → List Value → State → State → Value → Prop where
  | closure {id : Nat} {args : List Value} {s s1 s2 : State} {f : Closure}
      {active : ActivationId} {v : Value} : s.closures[id]? = some f →
      enter f args s = .ok (active, s1) → Eval f.body (some active) s1 s2 v →
      Call (.closure id) args s s2 v
end

/-- Captured lexical path, used by the representation relation, not by Eval. -/
def scopePathAux : Nat → Option ActivationId → State → List ScopeId
  | 0, _, _ => []
  | _ + 1, none, _ => []
  | fuel + 1, some id, s => match s.frames[id.index]? with
    | none => [] | some f => f.scope :: scopePathAux fuel f.parent s

def scopePath (active : Option ActivationId) (s : State) : List ScopeId :=
  scopePathAux (s.frames.length + 1) active s

/-- Concrete layout invariant, not an opaque assumption named 'valid state'. -/
def WellFormed (s : State) : Prop :=
  (∀ i f, s.frames[i]? = some f →
    (∀ parent, f.parent = some parent → parent.index < i) ∧
    ∃ sc, s.catalog.scopes[f.scope.index]? = some sc ∧
      (∀ sym, (f.bindings.lookup sym).isSome ↔ sym ∈ sc.layout)) ∧
  (∀ i f, s.closures[i]? = some f →
    f.parameters = f.layout.take f.parameters.length ∧
    f.parameters.eraseDups = f.parameters ∧
    ∃ sc, s.catalog.scopes[f.scope.index]? = some sc ∧ sc.layout = f.layout) ∧
  (∀ i info, s.catalog.symbols[i]? = some info →
    match info.home with
    | .global _ slot => ∃ v, s.catalog.globalSeeds[slot]? = some (⟨i⟩, v)
    | .lexical scope slot => ∃ sc, s.catalog.scopes[scope.index]? = some sc ∧
        sc.layout[slot]? = some ⟨i⟩) ∧
  (∀ scope sc slot sym, s.catalog.scopes[scope]? = some sc →
    sc.layout[slot]? = some sym →
    (s.catalog.symbols[sym.index]?).map SymbolInfo.home = some (.lexical ⟨scope⟩ slot))

end Macaulean.Language.Design.Meaning

namespace Macaulean.Language.Design

def FrameRel (c : Catalog) (s : Meaning.Frame) (m : Machine.Frame) : Prop :=
  s.scope = m.scope ∧ s.parent = m.parent ∧
  (∃ sc, c.scopes[s.scope.index]? = some sc ∧ m.layout = sc.layout) ∧
  m.layout.length = m.values.length ∧
  ∀ slot sym, m.layout[slot]? = some sym → s.bindings.lookup sym = m.values[slot]?

def ClosureRel (s : Meaning.State) (f : Meaning.Closure) (g : Machine.Closure) : Prop :=
  f.scope = g.scope ∧ f.parameters = g.parameters ∧ f.layout = g.layout ∧
  f.captured = g.captured ∧
  ∃ fuel, Binding.lower fuel s.catalog (f.scope :: Meaning.scopePath f.captured s) f.body = .ok g.body

/-- A concrete representation relation. IDs agree in this prototype; a compacting
machine may later replace equality by a renaming relation. Values are not proofs. -/
def Related (s : Meaning.State) (m : Machine.State) : Prop :=
  s.catalog = m.catalog ∧ s.actors = m.actors ∧
  (∀ (id : SymbolId) (ns : NamespaceId) (slot : Nat), (s.catalog.symbols[id.index]?).map SymbolInfo.home = some (.global ns slot) →
    s.globals.lookup id = m.globals[slot]?) ∧
  s.frames.length = m.frames.length ∧
  (∀ i f, s.frames[i]? = some f → ∃ g, m.frames[i]? = some g ∧ FrameRel s.catalog f g) ∧
  s.closures.length = m.closures.length ∧
  (∀ i f, s.closures[i]? = some f → ∃ g, m.closures[i]? = some g ∧ ClosureRel s f g)

namespace TODO
/-- Generic finite-success preservation for the designed IR, NOT legacy Runtime.
Fuel is a machine resource. The source relation has no fuel parameter. -/
def LowerForward : Prop :=
  ∀ (bound : Bound) (code : Code) (path : List ScopeId) (lowerFuel : Nat)
    (active : Option ActivationId) (s s' : Meaning.State) (m : Machine.State) (v : Value),
    Meaning.WellFormed s → Related s m → Meaning.scopePath active s = path →
    Binding.lower lowerFuel s.catalog path bound = .ok code →
    Meaning.Eval bound active s s' v →
    ∃ minimum, ∀ fuel, minimum ≤ fuel →
      ∃ m', Machine.eval fuel code active m = .done v m' ∧ Related s' m'

/-- Reverse finite-success correspondence, with no assumption that the compiled
code computes gcd. Errors/divergence require a separate, richer outcome relation. -/
def LowerBackward : Prop :=
  ∀ (bound : Bound) (code : Code) (path : List ScopeId) (lowerFuel fuel : Nat)
    (active : Option ActivationId) (s : Meaning.State) (m m' : Machine.State) (v : Value),
    Meaning.WellFormed s → Related s m → Meaning.scopePath active s = path →
    Binding.lower lowerFuel s.catalog path bound = .ok code →
    Machine.eval fuel code active m = .done v m' →
    ∃ s', Meaning.Eval bound active s s' v ∧ Related s' m'
end TODO
end Macaulean.Language.Design
