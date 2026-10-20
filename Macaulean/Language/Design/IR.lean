import Macaulean.Language.Design.Words

/-!
# Distinct syntax, binding, and storage identities

Unlike the superseded example, no Interpreter.Term/Code/Ref/Runtime is imported.
`whileDo` is a first-class node, not a Plan wrapper around the old interpreter.
The prototype covers the Euclidean source fragment, not all of M2 syntax.
-/
namespace Macaulean.Language.Design

/-- An actual symbol value denotes declaration plus activation. A local slot need
not be a separately allocated object. None denotes this session's global binding. -/
inductive Value where
  | int (n : Int)
  | bool (b : Bool)
  | null
  | symbol (declaration : SymbolId) (activation : Option ActivationId)
  | closure (id : Nat)
  deriving DecidableEq, BEq, Repr, Inhabited

inductive Home where
  | global (namespaceId : NamespaceId) (slot : Nat)
  | local (scope : ScopeId) (slot : Nat)
  deriving DecidableEq, BEq, Repr, Inhabited
structure SymbolInfo where
  canonicalWord : WordId
  home : Home
  protected : Bool := false
  deriving DecidableEq, BEq, Repr, Inhabited
structure Namespace where
  /-- Retained entries, newest first. Lookup and enumeration are different views. -/
  entries : List (WordId × SymbolId) := []
  writable : Bool := true
  deriving DecidableEq, BEq, Repr, Inhabited
structure Scope where
  entries : List (WordId × SymbolId) := []
  layout : List SymbolId := []
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Syntax does not know the integer meaning of %, !=, < or unary -. -/
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
  | local (depth slot : Nat)
  deriving DecidableEq, BEq, Repr, Inhabited
structure Ref where
  symbol : SymbolId
  location : Location
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Bound syntax is Node SymbolId; executable IR is Node Ref. Sharing the
control-node vocabulary does not define either evaluator in terms of the other.
Source reads use declaration lookup; machine reads use direct locations. -/
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

/-- Implementation of a resolved operator, never its lexical identity. The four
primitive cases are a chosen closed integer fragment, not a full method system. -/
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
  /-- Initial values for newly allocated globals, not a second runtime store. -/
  globalSeeds : List (SymbolId × Value) := []
  bootstrapActors : Actors := []
  deriving Repr, Inhabited

/-- Reached state survives errors; resource exhaustion is not a language error.
The prototype does not import native D's exceptional-control quirks. -/
inductive Result (state : Type) (value : Type) where
  | done (value : value) (after : state)
  | error (message : String) (after : state)
  | exhausted (after : state)
  deriving Repr

def Result.bind (r : Result s a) (next : a → s → Result s b) : Result s b :=
  match r with
  | .done v state => next v state
  | .error e state => .error e state
  | .exhausted state => .exhausted state

/-- These source operations are our explicit integer semantics. A future object
method table replaces/extends Actors under a separately stated dispatch contract. -/
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
