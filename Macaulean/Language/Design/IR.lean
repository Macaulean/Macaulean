import Macaulean.Language.Design.Words

/-! Syntax, declaration, activation and execution identity are different domains.
No dependency on legacy Interpreter.Term, BinOp, Lexical.Code or Runtime.
While is a real language node. This is a closed prototype, not all M2.
-/
namespace Macaulean.Language.Design

inductive Value where
  | int (n : Int)
  | bool (b : Bool)
  | null
  | symbol (declaration : SymbolId) (activation : Option ActivationId)
  | closure (id : Nat)
  deriving DecidableEq, BEq, Repr, Inhabited
inductive Home where
  | global (namespaceId : NamespaceId) (slot : Nat)
  | lexical (scope : ScopeId) (slot : Nat)
  deriving DecidableEq, BEq, Repr, Inhabited
structure SymbolInfo where
  canonicalWord : WordId
  home : Home
  isProtected : Bool := false
  deriving DecidableEq, BEq, Repr, Inhabited
structure Namespace where
  entries : List (WordId × SymbolId) := []
  writable : Bool := true
  deriving DecidableEq, BEq, Repr, Inhabited
structure Scope where
  entries : List (WordId × SymbolId) := []
  layout : List SymbolId := []
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Operators retain lexical identity; there is no Surface.add/rem/abs. -/
inductive Surface where
  | int (n : Int)
  | read (word : WordId)
  | quote (policy : QuotePolicy) (word : WordId)
  | unary (operator : WordId) (arg : Surface)
  | binary (operator : WordId) (left right : Surface)
  | set (declareLocal : Bool) (word : WordId) (rhs : Surface)
  | seq (first second : Surface)
  | ifElse (test yes no : Surface)
  | whileDo (test body : Surface)
  | lambda (parameters : List WordId) (body : Surface)
  | call (fn : Surface) (arguments : List Surface)
  deriving Repr, Inhabited
structure OperatorRef where
  sourceWord : WordId
  symbol : SymbolId
  deriving DecidableEq, BEq, Repr, Inhabited
inductive Location where
  | global (slot : Nat)
  | lexical (depth slot : Nat)
  deriving DecidableEq, BEq, Repr, Inhabited
structure Ref where
  symbol : SymbolId
  location : Location
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Shared grammar of control nodes, but DIFFERENT references and semantics:
Bound uses SymbolId association lookup; Code uses direct depth/slot addresses. -/
inductive Node (reference : Type) where
  | int (n : Int)
  | read (ref : reference)
  | quote (ref : reference)
  | unary (operator : OperatorRef) (arg : Node reference)
  | binary (operator : OperatorRef) (left right : Node reference)
  | set (ref : reference) (rhs : Node reference)
  | seq (first second : Node reference)
  | ifElse (test yes no : Node reference)
  | whileDo (test body : Node reference)
  | lambda (scope : ScopeId) (parameters layout : List SymbolId) (body : Node reference)
  | call (fn : Node reference) (arguments : List (Node reference))
  deriving Repr, Inhabited
abbrev Bound := Node SymbolId
abbrev Code := Node Ref

/-- An execution choice keyed by resolved Symbol, NOT a parsing category. -/
inductive Primitive where
  | neg | rem | ne | lt
  deriving DecidableEq, BEq, Repr, Inhabited
abbrev Actors := List ((SymbolId × Nat) × Primitive)
structure Catalog where
  words : WordRegistry := {}
  namespaces : List Namespace := [{writable := false}, {}]
  searchPath : List NamespaceId := [⟨1⟩, ⟨0⟩]
  symbols : List SymbolInfo := []
  scopes : List Scope := [{}]
  /-- Allocation seeds only; execution does not consult these as a second store. -/
  globalSeeds : List (SymbolId × Value) := []
  bootstrapActors : Actors := []
  deriving Repr, Inhabited

inductive Result (σ α : Type) where
  | done (value : α) (after : σ)
  | error (message : String) (after : σ)
  | exhausted (after : σ)
  deriving Repr

def Result.bind (r : Result σ α) (next : α → σ → Result σ β) : Result σ β :=
  match r with
  | .done v s => next v s
  | .error e s => .error e s
  | .exhausted s => .exhausted s

def primitiveValue (p : Primitive) (args : List Value) : Except String Value :=
  match p, args with
  | .neg, [.int a] => .ok (.int (-a))
  | .rem, [.int a, .int b] => .ok (.int (a % b))
  | .ne, [.int a, .int b] => .ok (.bool (decide (a ≠ b)))
  | .lt, [.int a, .int b] => .ok (.bool (decide (a < b)))
  | _, _ => .error "operator argument shape outside the integer fragment"
def dispatch (actors : Actors) (op : OperatorRef) (args : List Value) : Except String Value := do
  let some p := actors.lookup (op.symbol, args.length) | .error "no installed actor"
  primitiveValue p args

end Macaulean.Language.Design
