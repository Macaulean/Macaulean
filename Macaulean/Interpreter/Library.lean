import Macaulean.Interpreter.LibraryCompiler
import Macaulean.Interpreter.SourceFile

/-! The tracked M2 file is the single source of the algorithm. The generated code
is literal data, so kernel evaluation does not repeatedly parse the library.
The elaboration check below is a compilation check, not a parser-correctness axiom. -/
namespace Macaulean.M2.Library
open Lexical LibraryCompiler Lean Elab Command
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000

def source : String := m2_source% "Buchberger.m2"
def gcdSource : String := m2_source% "GCD.m2"
def buchbergerDefinitions : List (String × Code) := m2_library% source
def gcdDefinitions : List (String × Code) := m2_library% gcdSource
def definitions : List (String × Code) := buchbergerDefinitions ++ gcdDefinitions

run_cmd do
  let expected ← match LibraryCompiler.compile (source ++ "\n" ++ gcdSource) with
    | .ok ds => pure ds
    | .error error => throwError "M2 library no longer parses/compiles: {error}"
  let quoteEntry : String × Code → String × Lean.Expr :=
    fun (name,code) => (name,LibraryCompiler.codeExpr code)
  unless definitions.map quoteEntry == expected.map quoteEntry do
    throwError "compiled M2 library differs from its tracked source"

def aliases : List (String × String) := [
  ("gb", "m2gbMain"), ("normalForm", "m2gbNormalForm"), ("sPolynomial", "m2gbSPolynomial")
]
def names : List String := definitions.map Prod.fst ++ aliases.map Prod.fst

def lookup (name : String) : Option Code :=
  definitions.lookup ((aliases.lookup name).getD name)

/-- Source attribution follows the owning library, including public aliases. -/
def sourceFor (name : String) : Option (String × String) :=
  let target := (aliases.lookup name).getD name
  if (gcdDefinitions.lookup target).isSome then
    some ("Macaulean/Interpreter/GCD.m2", gcdSource)
  else if (buchbergerDefinitions.lookup target).isSome then
    some ("Macaulean/Interpreter/Buchberger.m2", source)
  else none
end Macaulean.M2.Library
