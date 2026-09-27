import Macaulean.Interpreter.LibraryCompiler
import Macaulean.Interpreter.SourceFile

/-! # M2 algorithms supplied as source, not engine primitives

Lake tracks Buchberger.m2 as an input dependency. Its lexical code is compiled
once into literal Lean data; recursive calls neither reparse source nor install
fresh helper closures. This has the same parser/elaborator boundary as the bare
DSL. Compilation fidelity is checked at elaboration, not asserted as an axiom
or advertised as a proved parser-correctness theorem.
-/
namespace Macaulean.M2.Library
open Lexical LibraryCompiler
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def source : String := m2_source% "Buchberger.m2"
def definitions : List (String × Code) := m2_library% source

open Lean Elab Command in
run_cmd do
  let expected ← match LibraryCompiler.compile source with
    | .ok ds => pure ds
    | .error error => throwError "M2 library no longer parses/compiles: {error}"
  let quoteEntry : String × Code → String × Lean.Expr :=
    fun (name,code) => (name,LibraryCompiler.codeExpr code)
  unless expected.map quoteEntry == definitions.map quoteEntry do
    throwError "compiled M2 library differs from its checked-in source"

def aliases : List (String × String) := [
  ("gb", "m2gbMain"), ("normalForm", "m2gbNormalForm"), ("sPolynomial", "m2gbSPolynomial")
]
def names : List String := definitions.map Prod.fst ++ aliases.map Prod.fst

def lookup (name : String) : Option Code :=
  definitions.lookup ((aliases.lookup name).getD name)
end Macaulean.M2.Library
