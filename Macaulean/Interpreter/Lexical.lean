import Macaulean.Interpreter.Syntax

/-!
# Static, source-ordered lexical resolution

:= creates a slot before resolving its initializer. `local` reuses current-scope
bindings. Only function bodies create scopes. Bracket identifiers are resolved to their current bindings. Ring construction
can publish global generators without treating those identifiers as assignments.
-/
namespace Macaulean.M2.Lexical
inductive Ref where
  | global (name : String)
  | slot (depth index : Nat)
  deriving Repr, DecidableEq, Inhabited
inductive Code where
  | int (n : Int)
  | read (ref : Ref)
  | unop (op : UnOp) (arg : Code)
  | binop (op : BinOp) (left right : Code)
  | logic (op : LogicOp) (left right : Code)
  | ifThen (condition yes : Code)
  | ifElse (condition yes no : Code)
  | set (ref : Ref) (rhs : Code)
  | setMany (refs : List Ref) (rhs : Code)
  | indexAssign (collection index value : Code)
  | seq (first second : Code)
  | empty
  | listLit (elements : List Code)
  | sequence (elements : List Code)
  | lambda (params : Parameters) (slots : Nat) (body : Code)
  | apply (fn arg : Code)
  | symbol (name : String) (ref : Ref)
  | returnTerm (arg : Code)
  | polyRing (base : Code) (names : List (String × Ref))
  deriving Repr, Inhabited
structure Scope where
  names : List (String × Nat) := []
  count : Nat := 0
  deriving Repr, DecidableEq, Inhabited
structure Resolver where
  current : Scope := {}
  outers : List Scope := []
  warnings : List String := []
  deriving Repr, Inhabited
def findOuter (name : String) : List Scope → Nat → Ref
  | [], _ => .global name
  | s :: ss, d => match s.names.lookup name with
    | some i => .slot d i | none => findOuter name ss (d + 1)
def Resolver.lookup (r : Resolver) (name : String) : Ref :=
  match r.current.names.lookup name with
  | some i => .slot 0 i | none => findOuter name r.outers 1
def Resolver.declare (r : Resolver) (name : String) : Ref × Resolver :=
  let i := r.current.count
  let warnings := if (r.current.names.lookup name).isSome then
      r.warnings ++ [s!"redeclaration of local variable '{name}'"] else r.warnings
  (.slot 0 i, { r with current := ⟨(name, i) :: r.current.names, i + 1⟩, warnings })
def Resolver.localRef (r : Resolver) (name : String) : Ref × Resolver :=
  match r.current.names.lookup name with
  | some i => (.slot 0 i, r)
  | none => r.declare name
def Resolver.declareMany : List String → Resolver → List Ref × Resolver
  | [], r => ([], r)
  | x :: xs, r =>
    let (v, r) := r.declare x
    let (vs, r) := r.declareMany xs
    (v :: vs, r)
mutual
def resolve : Term → Resolver → Code × Resolver
  | .int n, r => (.int n, r)
  | .var x, r => (.read (r.lookup x), r)
  | .empty, r => (.empty, r)
  | .unop op a, r =>
    let (a, r) := resolve a r
    (.unop op a, r)
  | .binop op a b, r =>
    let (a, r) := resolve a r
    let (b, r) := resolve b r
    (.binop op a b, r)
  | .logic op a b, r =>
    let (a, r) := resolve a r
    let (b, r) := resolve b r
    (.logic op a b, r)
  | .ifThen c y, r =>
    let (c, r) := resolve c r
    let (y, r) := resolve y r
    (.ifThen c y, r)
  | .ifElse c y n, r =>
    let (c, r) := resolve c r
    let (y, r) := resolve y r
    let (n, r) := resolve n r
    (.ifElse c y n, r)
  | .assign x a, r =>
    let ref := r.lookup x
    let (a, r) := resolve a r
    (.set ref a, r)
  | .localAssign x a, r =>
    let (ref, r) := r.declare x
    let (a, r) := resolve a r
    (.set ref a, r)
  | .assignMany isLocal xs a, r =>
    let (refs, r) := if isLocal then r.declareMany xs else (xs.map r.lookup, r)
    let (a, r) := resolve a r
    (.setMany refs a, r)
  | .localSymbol name, r =>
    let (ref, r) := r.localRef name
    (.symbol name ref, r)
  | .indexAssign a i v, r =>
    let (a, r) := resolve a r
    let (i, r) := resolve i r
    let (v, r) := resolve v r
    (.indexAssign a i v, r)
  | .seq a b, r =>
    let (a, r) := resolve a r
    let (b, r) := resolve b r
    (.seq a b, r)
  | .listLit xs, r =>
    let (xs, r) := resolveMany xs r
    (.listLit xs, r)
  | .sequence xs, r =>
    let (xs, r) := resolveMany xs r
    (.sequence xs, r)
  | .lambda params body, r =>
    let inner : Resolver := { outers := r.current :: r.outers }
    let (_, inner) := inner.declareMany params.names
    let (body, inner) := resolve body inner
    (.lambda params inner.current.count body, { r with warnings := r.warnings ++ inner.warnings })
  | .apply f a, r =>
    let (f, r) := resolve f r
    let (a, r) := resolve a r
    (.apply f a, r)
  | .returnTerm a, r =>
    let (a, r) := resolve a r
    (.returnTerm a, r)
  | .polyRing a names, r =>
    let (a, r) := resolve a r
    (.polyRing a (names.map fun x => (x,r.lookup x)), r)
def resolveMany : List Term → Resolver → List Code × Resolver
  | [], r => ([], r)
  | a :: xs, r =>
    let (a, r) := resolve a r
    let (xs, r) := resolveMany xs r
    (a :: xs, r)
end
def prepare (t : Term) (scope : Scope := {}) : Code × Scope × List String :=
  let (code, r) := resolve t { current := scope }
  (code, r.current, r.warnings)
end Macaulean.M2.Lexical
