import Lean
import Macaulean.Interpreter.Parser
import Macaulean.Interpreter.Lexical

/-! Compile the checked-in M2 library to literal lexical code, once at elaboration.
No evaluation of that code is performed by this elaborator. A separate kernel
identity checks that the generated literal equals the pure compilation result. -/
namespace Macaulean.M2.LibraryCompiler
open Lean Elab Term Meta Lexical

deriving instance ToExpr for BinOp, UnOp, LogicOp, Parameters, Ref

mutual
def codeExpr : Code → Expr
  | .int n => mkApp (mkConst ``Code.int) (toExpr n)
  | .read r => mkApp (mkConst ``Code.read) (toExpr r)
  | .unop op a => mkApp2 (mkConst ``Code.unop) (toExpr op) (codeExpr a)
  | .binop op a b => mkApp3 (mkConst ``Code.binop) (toExpr op) (codeExpr a) (codeExpr b)
  | .logic op a b => mkApp3 (mkConst ``Code.logic) (toExpr op) (codeExpr a) (codeExpr b)
  | .ifThen a b => mkApp2 (mkConst ``Code.ifThen) (codeExpr a) (codeExpr b)
  | .ifElse a b c => mkApp3 (mkConst ``Code.ifElse) (codeExpr a) (codeExpr b) (codeExpr c)
  | .set r a => mkApp2 (mkConst ``Code.set) (toExpr r) (codeExpr a)
  | .setMany rs a => mkApp2 (mkConst ``Code.setMany) (toExpr rs) (codeExpr a)
  | .indexAssign a b c => mkApp3 (mkConst ``Code.indexAssign) (codeExpr a) (codeExpr b) (codeExpr c)
  | .seq a b => mkApp2 (mkConst ``Code.seq) (codeExpr a) (codeExpr b)
  | .empty => mkConst ``Code.empty
  | .listLit xs => mkApp (mkConst ``Code.listLit) (codesExpr xs)
  | .sequence xs => mkApp (mkConst ``Code.sequence) (codesExpr xs)
  | .lambda ps slots body => mkApp3 (mkConst ``Code.lambda) (toExpr ps) (toExpr slots) (codeExpr body)
  | .apply a b => mkApp2 (mkConst ``Code.apply) (codeExpr a) (codeExpr b)
  | .symbol x r => mkApp2 (mkConst ``Code.symbol) (toExpr x) (toExpr r)
  | .returnTerm a => mkApp (mkConst ``Code.returnTerm) (codeExpr a)
  | .ringNew a b => mkApp2 (mkConst ``Code.ringNew) (codeExpr a) (codeExpr b)
  | .ringName x => mkApp (mkConst ``Code.ringName) (toExpr x)
def codesExpr : List Code → Expr
  | [] => mkApp (mkConst ``List.nil [0]) (mkConst ``Code)
  | x :: xs => mkApp3 (mkConst ``List.cons [0]) (mkConst ``Code) (codeExpr x) (codesExpr xs)
end
instance : ToExpr Code where
  toTypeExpr := mkConst ``Code
  toExpr := codeExpr

def collect : Macaulean.M2.Term → Except String (List (String × Code))
  | .empty => .ok []
  | .seq a b => do return (← collect a) ++ (← collect b)
  | .assign name (.lambda ps body) =>
    .ok [(name, (Lexical.resolve (.lambda ps body) {}).1)]
  | _ => .error "library source must consist of named function definitions"

def compile (source : String) : Except String (List (String × Code)) := do
  let terms ← Macaulean.M2.parse source
  let definitions ← collect terms
  let names := definitions.map Prod.fst
  if names.eraseDups.length != names.length then .error "duplicate library definition"
  else return definitions

syntax (name := literalLibrary) "m2_library% " term:max : term
@[term_elab literalLibrary]
def elabLiteralLibrary : TermElab := fun stx _ => do
  let source ← elabTerm stx[1] (some (mkConst ``String))
  let source ← withTransparency .all (whnf source)
  let .lit (.strVal text) := source | throwErrorAt stx "expected a reducible source string"
  match compile text with
  | .error error => throwErrorAt stx "M2 library compilation failed: {error}"
  | .ok definitions => return toExpr definitions
end Macaulean.M2.LibraryCompiler
