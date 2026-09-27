import Macaulean.Interpreter.LibraryCompiler
import Macaulean.Interpreter.SourceFile

/-! # M2 algorithms supplied as source, not engine primitives
The source is a tracked Lake input. Compilation is an elaboration boundary,
not an axiom or a claimed parser-correctness theorem. -/
namespace Macaulean.M2.Library
open Lexical LibraryCompiler Lean Elab Command
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def source : String := m2_source% "Buchberger.m2"

-- Report the failing definition rather than a context-free token error.
run_cmd do
  logInfo m!"LIBRARY_READER_CONTROL: {repr (Macaulean.M2.parse "f=x->\n x+1;")}"
  logInfo m!"LIBRARY_NEWLINE_CONTROL: {repr (Macaulean.M2.Parser.skipNewlines [.newline,.newline,.num 7])}"
  for block in source.splitOn "\n\n" do
    match Macaulean.M2.parse block with
    | .ok _ => pure ()
    | .error error => logError m!"LIBRARY_FRAGMENT {repr block}: {error}"

def definitions : List (String × Code) := m2_library% source

run_cmd do
  let expected ← match LibraryCompiler.compile source with
    | .ok ds => pure ds
    | .error error => throwError "M2 library no longer parses/compiles: {error}"
  let quoteEntry : String × Code → String × Lean.Expr :=
    fun (name,code) => (name,LibraryCompiler.codeExpr code)
  let actualEntries := definitions.map quoteEntry
  let expectedEntries := expected.map quoteEntry
  if actualEntries != expectedEntries then
    throwError "compiled M2 library differs from its checked-in source"

def aliases : List (String × String) := [
  ("gb", "m2gbMain"), ("normalForm", "m2gbNormalForm"), ("sPolynomial", "m2gbSPolynomial")
]
def names : List String := definitions.map Prod.fst ++ aliases.map Prod.fst

def lookup (name : String) : Option Code :=
  definitions.lookup ((aliases.lookup name).getD name)
end Macaulean.M2.Library
