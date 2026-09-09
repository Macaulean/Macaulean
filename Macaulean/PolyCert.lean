/-
Copyright (c) 2026 Macaulean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Macaulean.Grind.AlgPoly.Tactic
import Macaulean.PolyDef

/-!
# `poly_cert`: close a membership or divisibility goal from committed cofactors

A computer algebra system finds the cofactors `qᵢ` of

```
p - r = q₁ * g₁ + ⋯ + q_k * g_k        (ideal membership)
f     = g * q                          (divisibility)
```

but nothing about *checking* such a certificate needs the computer algebra
system: the identity is a polynomial identity, and `algebra_norm_reflect`
proves those in the kernel.  `poly_cert` is that checking half on its own.  It
imports neither `Macaulean.Macaulay2` nor `Macaulean.IdealMembership`, so a
file whose certificates are committed as data does not start an M2 process,
does not depend on M2 being installed, and builds the same on every machine.

`m2cert?` (`Macaulean/M2Cert.lean`) prints exactly this tactic, with the
cofactors it just obtained from Macaulay2, as a paste-able replacement for
itself.

## Syntax

```
poly_cert [q]                                  -- goal `g ∣ f`
poly_cert [q₁, …, q_k] using [h₁, …, h_k]      -- goal `p = r`, `hᵢ : gᵢ = 0`
poly_cert ["1.1.0.1 0.0.1.-3"] in [x, y, z]    -- cofactors as monomial strings
poly_cert +native […] …                        -- see below
```

A cofactor is either an ordinary term of the ambient ring (a `poly_def`
constant, say) or a **monomial string** in `poly_def`'s `e₁.….eₙ.k` format, in
which case the variables it is written in must be listed after `in`.  The two
forms produce the same term: the string goes through the same `PolyBuilder`
that `poly_def` uses.

`+native` closes the reflective certificate with `decide +native` rather than
`decide +kernel`.  It is never the default and always warns; see
`Macaulean/Grind/AlgPoly/Tactic.lean`.
-/

open Lean Meta Elab Tactic

namespace Macaulean.PolyCert

/--
`a = d` and `g = 0` give `a + c * g = d`: one generator peeled off the
right-hand side of a membership certificate.  Folding this over the
generators turns the reflective identity `p = r + Σ qᵢ gᵢ` into `p = r`.
-/
theorem gen_step {R : Type u} [Lean.Grind.CommRing R] {a c g d : R}
    (h : a = d) (hg : g = 0) : a + c * g = d := by
  rw [hg, Lean.Grind.Semiring.mul_zero, Lean.Grind.Semiring.add_zero]
  exact h

/-- The numeral `(n : A)`, in the shape `poly_def` produces. -/
def ringNumeral (A : Expr) (n : Nat) : TermElabM Expr :=
  mkAppOptM ``OfNat.ofNat #[A, mkRawNatLit n, none]

/-- A `PolyBuilder` over the ambient ring `A` and the given variable terms. -/
def mkBuilder (A : Expr) (vars : Array Expr) : TermElabM PolyBuilder :=
  PolyBuilder.ofType A vars (ringNumeral A)

/--
Elaborate the cofactor list: a string literal is a monomial spec over `vars?`
(which must then be present), anything else is a term of `A`.
-/
def elabCofactors (A : Expr) (vars? : Option (Array Expr)) (stxs : Array Term) :
    TermElabM (Array Expr) := do
  let b? ← vars?.mapM (mkBuilder A)
  stxs.mapM fun stx => do
    match stx.raw.isStrLit? with
    | some spec =>
      let some b := b?
        | throwErrorAt stx "poly_cert: a monomial-string cofactor has to say which \
            variables it is written in; add `in [x, y, …]`"
      match ← b.build? "poly_cert" spec with
      | some e => pure e
      | none => b.mkNum 0
    | none =>
      let e ← Term.elabTerm stx (some A)
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e

/--
Close a goal `g ∣ f` with the cofactor `q`: the divisibility unfolds to
`∃ c, f = g * c`, and `f = g * q` is a polynomial identity.
-/
def closeDvd (native : Bool) (goal : MVarId) (q : Expr) : TacticM Unit := do
  let target ← instantiateMVars (← goal.getType)
  let existsTy ← whnf target
  let some (α, p) := (match_expr existsTy with
      | Exists α p => some (α, p)
      | _ => none)
    | throwError m!"poly_cert: expected a divisibility goal `g ∣ f`, got{indentExpr target}"
  let eqTy ← instantiateMVars (p.beta #[q])
  let some (_, lhs, rhs) := eqTy.eq?
    | throwError m!"poly_cert: `{target}` does not unfold to an equation in the cofactor"
  let hEq ← AlgPoly.Tactic.proveEq lhs rhs native
  let u ← getLevel α
  let proof := mkApp4 (mkConst ``Exists.intro [u]) α p q hEq
  unless ← goal.checkedAssign proof do
    throwError m!"poly_cert: the divisibility witness did not typecheck against{indentExpr target}"

/--
Close a goal `p = r` given `hᵢ : gᵢ = 0` and cofactors `qᵢ` with
`p - r = Σ qᵢ gᵢ`: prove `p = r + Σ qᵢ gᵢ` reflectively, then peel the
generators off with `gen_step`.
-/
def closeEq (native : Bool) (goal : MVarId) (hyps cofactors : Array Expr) : TacticM Unit := do
  let target ← instantiateMVars (← goal.getType)
  let some (_, p, r) := target.eq?
    | throwError m!"poly_cert: expected an equality goal, got{indentExpr target}"
  unless hyps.size == cofactors.size do
    throwError "poly_cert: {cofactors.size} cofactors for {hyps.size} generators"
  let mut acc ← mkEqRefl r
  for h : i in [0 : hyps.size] do
    acc ← mkAppOptM ``gen_step
      #[none, none, none, some cofactors[i]!, none, none, some acc, some hyps[i]]
  let some (_, big, _) := (← instantiateMVars (← inferType acc)).eq?
    | throwError "poly_cert: assembling the certificate did not produce an equation"
  let hRefl ← AlgPoly.Tactic.proveEq p big native
  let proof ← instantiateMVars (← mkEqTrans hRefl acc)
  unless ← goal.checkedAssign proof do
    throwError m!"poly_cert: the certificate did not typecheck against{indentExpr target}"

/-- The ambient ring of the goal: the type of either side of an equation, or
the type the divisibility is stated in. -/
def goalRing (target : Expr) : MetaM Expr := do
  if let some (A, _, _) := target.eq? then return A
  match_expr target with
  | Dvd.dvd A _ _ _ => return A
  | _ => throwError m!"poly_cert: expected `p = r` or `g ∣ f`, got{indentExpr target}"

/-- A bracketed, comma-separated list of terms. -/
syntax certList := " [" term,* "]"
/-- The variables a monomial-string cofactor is written in. -/
syntax certVars := " in" certList
/-- The generator hypotheses `hᵢ : gᵢ = 0` the cofactors go with. -/
syntax certHyps := " using" certList

/-- The terms of a `certList`. -/
def listTerms (stx : TSyntax ``certList) : Array Term :=
  stx.raw[1].getSepArgs.map (⟨·⟩)

/--
`poly_cert [q₁, …, q_k] using [h₁, …, h_k]` closes a goal `p = r` from
hypotheses `hᵢ : gᵢ = 0` and cofactors witnessing `p - r = Σ qᵢ gᵢ`;
`poly_cert [q]` closes a goal `g ∣ f` from a cofactor witnessing `f = g * q`.
The identity itself is proved by `algebra_norm_reflect`'s kernel certificate.

Each cofactor is a term of the ambient ring, or a `poly_def`-style monomial
string `"e₁.….eₙ.k …"` — in which case the variables have to be listed after
`in`.  `+native` swaps the kernel check for `decide +native`, and warns.

This tactic never invokes a computer algebra system; `m2cert?` prints the
invocation to write here.
-/
elab "poly_cert" native:(Macaulean.AlgPoly.Tactic.nativeFlag)? cofs:certList
    vars:(certVars)? hyps:(certHyps)? : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let A ← goalRing target
  let varEs ← vars.mapM fun v => do
    (listTerms ⟨v.raw[1]⟩).mapM fun t => do
      let e ← Term.elabTerm t (some A)
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
  let cofactors ← elabCofactors A varEs (listTerms cofs)
  match hyps with
  | none =>
    unless cofactors.size == 1 do
      throwError "poly_cert: a divisibility goal takes exactly one cofactor, got {cofactors.size}"
    closeDvd native.isSome goal cofactors[0]!
  | some h =>
    let hypEs ← (listTerms ⟨h.raw[1]⟩).mapM (elabTerm · none)
    closeEq native.isSome goal hypEs cofactors
  replaceMainGoal []

end Macaulean.PolyCert
