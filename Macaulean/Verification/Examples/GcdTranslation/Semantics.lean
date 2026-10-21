import Macaulean.Language.Design.Meaning
import Macaulean.Verification.Examples.GcdTranslation.Program

/-! Precise open proof targets. Definitions of Prop are not theorem admissions.
There is deliberately no inhabitant of Obligations, no sorry and no axiom.
The source semantics handles closures and while itself, not a special gcd rule.
-/
namespace Macaulean.Language.Design.Gcd

/-- Meaning of the compiled fixture before location lowering. No Machine.eval,
Int.gcd, Nat.gcd, or algorithm-specific arithmetic shortcut appears in this graph. -/
def Graph (artifact : Artifact) (a b z : Int) : Prop :=
  ∃ final, Meaning.Eval (boundInvocation artifact a b) (some ⟨0⟩)
    (Meaning.initial artifact.catalog) final (.int z)

/-- DESIGN-PARSE: a pipeline boundary, not an installed implementation.
A parser must retain reached word history, byte spans and newline policy. An
implementation which just returns the fixture does not satisfy parser correctness. -/
structure Frontend where
  parseUnit : Nat → Bytes → WordRegistry → Result WordRegistry Surface

namespace TODO
/-- The fixed source fixture must actually compile; conditional contracts alone
could otherwise be vacuous if build always failed. -/
def Builds : Prop := ∃ artifact final, build = .done artifact final

/-- Exact source/fixture agreement, separate from generic parser correctness.
Only the registered grammar seed is supplied: ordinary names must be discovered
from source, not pre-installed by registerNames as a shortcut. -/
def SourceLink (frontend : Frontend) : Prop :=
  ∀ vocabulary seed artifact final,
    bootstrap ({} : Catalog) = .done vocabulary seed →
    build = .done artifact final →
    ∃ fuel, frontend.parseUnit fuel sourceBytes seed.words =
      .done artifact.surface artifact.catalog.words

/-- Binding/layout evidence for this fixture. Bound reads retain declaration
identity. Only the subsequent lowering computes runtime depth/slot addresses. -/
def Layout : Prop := ∀ artifact final, build = .done artifact final →
  artifact.layout.length = 3 ∧ artifact.parameters = artifact.layout.take 2 ∧
  ∃ sc, artifact.catalog.scopes[artifact.scope.index]? = some sc ∧
    sc.layout = artifact.layout ∧
    (∀ slot name, [(0, artifact.names.a), (1, artifact.names.b), (2, artifact.names.r)].lookup slot = some name →
      ∃ sym, sc.entries.lookup name = some sym ∧
        Binding.address artifact.catalog [artifact.scope, ⟨0⟩] sym = .ok ⟨sym, .lexical 0 slot⟩)

/-- The full initialization relation, not just equality of one answer. -/
def InitialRelated : Prop := ∀ artifact final, build = .done artifact final →
  Meaning.WellFormed (Meaning.initial artifact.catalog) ∧
  Related (Meaning.initial artifact.catalog) (Machine.initial artifact.catalog)

/-- The fixed lowered function and the invocation assembly really correspond. -/
def InvocationLowering : Prop := ∀ artifact final, build = .done artifact final →
  ∀ a b, ∃ fuel, Binding.lower fuel artifact.catalog [⟨0⟩]
    (boundInvocation artifact a b) = .ok (codeInvocation artifact a b)

/-- Generic lowering preservation instantiates here. This is NOT a property of
only input (1071,462), and it does not assert mathematical gcd correctness. -/
def Translation : Prop := ∀ artifact final, build = .done artifact final →
  ∀ a b z : Int, Graph artifact a b z ↔
    ∃ fuel after, Machine.eval fuel (codeInvocation artifact a b)
      (some ⟨0⟩) (Machine.initial artifact.catalog) = .done (.int z) after

/-- Non-vacuity / termination for the source program. Prove by abs nonnegativity
and strictly decreasing positive b. Do not use a gcd oracle to define the answer. -/
def Terminates : Prop := ∀ artifact final, build = .done artifact final →
  ∀ a b : Int, ∃ z, Graph artifact a b z

/-- Resource adequacy is not 'one fuel value happened to work'. -/
def Adequate : Prop := ∀ artifact final, build = .done artifact final →
  ∀ a b : Int, ∃ z minimum, ∀ fuel, minimum ≤ fuel →
    ∃ after, Machine.eval fuel (codeInvocation artifact a b)
      (some ⟨0⟩) (Machine.initial artifact.catalog) = .done (.int z) after

/-- No implementation is accepted as a translator just because it emits a typed
Code term. The source link, lowering theorem and resource adequacy are separate. -/
structure Obligations (frontend : Frontend) : Prop where
  builds : Builds
  wordHistory : Macaulean.Language.Design.TODO.FirstWins
  sourceLink : SourceLink frontend
  layout : Layout
  initial : InitialRelated
  invocation : InvocationLowering
  forward : Macaulean.Language.Design.TODO.LowerForward
  backward : Macaulean.Language.Design.TODO.LowerBackward
  translation : Translation
  termination : Terminates
  adequate : Adequate
end TODO
end Macaulean.Language.Design.Gcd
