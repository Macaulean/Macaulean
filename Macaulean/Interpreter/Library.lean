import Macaulean.Interpreter.LibraryCompiler

/-! # M2 algorithms supplied as source, not engine primitives

Lake tracks Buchberger.m2 as an input dependency. The literal lexical code is
compiled once; recursive calls do not reparse source or install fresh helper
closures. The following rfl theorem kernel-checks the compiler's complete output.
-/
namespace Macaulean.M2.Library
open Lexical LibraryCompiler
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def source : String := include_str "Buchberger.m2"
def definitions : List (String × Code) := m2_library% source

theorem compiled_exact : LibraryCompiler.compile source = .ok definitions := by rfl

def aliases : List (String × String) := [
  ("gb", "m2gbMain"), ("normalForm", "m2gbNormalForm"), ("sPolynomial", "m2gbSPolynomial")
]
def names : List String := definitions.map Prod.fst ++ aliases.map Prod.fst

def lookup (name : String) : Option Code :=
  definitions.lookup ((aliases.lookup name).getD name)
end Macaulean.M2.Library
