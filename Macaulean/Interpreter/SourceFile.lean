import Lean

/-! Literal file inclusion for the checked-in M2 library. This elaborator performs
file I/O only while building the Lean module; the runtime sees a literal String.
Unlike include_str, it does not compile/evaluate an arbitrary FilePath term. -/
namespace Macaulean.M2
open Lean Elab Term
syntax (name := sourceFile) "m2_source% " str : term
@[term_elab sourceFile]
def elabSourceFile : TermElab := fun stx _ => do
  let ctx ← readThe Lean.Core.Context
  let some directory := (System.FilePath.mk ctx.fileName).parent
    | throwErrorAt stx "cannot locate the source module"
  let file : TSyntax `str := ⟨stx[1]⟩
  let contents ← IO.FS.readFile (directory / file.getString)
  return mkStrLit contents
end Macaulean.M2
