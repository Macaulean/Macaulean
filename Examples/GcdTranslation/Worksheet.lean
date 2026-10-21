import Macaulean.Verification.Examples.GcdTranslation.Semantics

/-! Design-first worksheet. These are honest Lean definitions of the new model's
artifacts and computations. The legacy `open M2` parser is intentionally not used.
It still erases operator identity to BinOp and does not implement the proposed
Word/namespace pipeline. DESIGN-DSL will connect the fork's editor/review adapter
to the new frontend; DESIGN-PARSE is required first.
-/
namespace GcdDesignWorksheet
open Macaulean.Language.Design

/-- Immutable source, not a mutable interpreter binding. -/
def source : String := Gcd.sourceText
/-- Contains byte-word registry, Symbols, bound syntax and resolved Code. -/
def artifact := Gcd.build
/-- A resource-bounded computation on actual designed closures and while nodes. -/
def run := Gcd.run
/-- A proposition waiting for a proof, not an automatically admitted theorem. -/
def translationStatement : Prop := Gcd.TODO.Translation

def terminationStatement : Prop := Gcd.TODO.Terminates

#eval Gcd.answer 256 1071 462
#eval Gcd.answer 256 (-1071) 462
#check translationStatement
#check terminationStatement

-- TODO(DESIGN-EXPORT): after source-link and runtime preservation are proved,
-- generate these versioned definitions from the new frontend's accepted syntax.
-- Export source/registry/dependencies together; never import raw session IDs as
-- live symbols in an unrelated session. Do not emit a theorem before its proof.
end GcdDesignWorksheet
