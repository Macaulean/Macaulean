/-
Copyright (c) 2026 Macaulean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Lean
public meta import Lean

@[expose] public section

/-!
# `poly_def`: computer-algebra polynomial data as Lean definitions

Certificates emitted by a computer algebra system (quotients and remainders of
a division, syzygies, …) routinely have hundreds or thousands of monomials.
Writing such a polynomial as source syntax is prohibitively slow to elaborate
— roughly a second per monomial at certificate sizes, superlinear in practice
— so this module provides a command that builds the definition body directly
as an `Expr` from a compact positional encoding:

```
poly_def name : MvPolynomial (Fin 3) ℚ in [X 0, X 1, X 2] :=
  "16.2.15.-885735 16.2.14.10749105 …"
```

Each space-separated token is `e₁.e₂.….eₙ.k`: the exponents of the `n` listed
variable terms followed by an integer coefficient.  The number of exponent
fields must match the number of variables; the variables are arbitrary terms
of the ascribed type, so this works for any type carrying the required
`+ - * ^ Neg OfNat` instances, not just `MvPolynomial`.

The term produced is exactly what the corresponding source syntax would
elaborate to (a left-fold of `*` over `[coeff, v₁^e₁, …]` with `^` omitted at
exponent `1` and the factor omitted at exponent `0`, the monomials combined
by a left-nested chain of `+`/`-`), so downstream proofs cannot tell the
difference — they just do not pay for the elaboration.

`PolyBuilder` exposes the same monomial-string parser to other elaborators
(see `MacauleanTest/AlgebraNormPerf.lean`).
-/

set_option autoImplicit false

namespace Macaulean

meta section

open Lean Meta Elab

/--
The pieces needed to turn a monomial string into an `Expr`: the variable
terms, the arithmetic operations of the ambient type, and a numeral builder.
Build one with `PolyBuilder.ofType`, or by hand when the caller wants to
control the exact shape of the numerals.
-/
structure PolyBuilder where
  /-- The variable terms; one exponent field per entry, in this order. -/
  vars : Array Expr
  /-- `a * b`. -/
  mkMul : Expr → Expr → Expr
  /-- `a + b`. -/
  mkAdd : Expr → Expr → Expr
  /-- `a - b`. -/
  mkSub : Expr → Expr → Expr
  /-- `a ^ (k : Nat)`. -/
  mkPow : Expr → Nat → Expr
  /-- `-a`. -/
  mkNeg : Expr → Expr
  /-- The numeral `(n : α)`, cached by `ofType`. -/
  mkNum : Nat → TermElabM Expr

/--
A `PolyBuilder` for the type `ty`, whose `+ - * ^ Neg` come from instance
synthesis and whose numerals come from `mkNum` (memoized).
-/
def PolyBuilder.ofType (ty : Expr) (vars : Array Expr)
    (mkNum : Nat → TermElabM Expr) : TermElabM PolyBuilder := do
  let natTy := mkConst ``Nat
  let hMulInst ← synthInstance (mkApp3 (mkConst ``HMul [0, 0, 0]) ty ty ty)
  let hAddInst ← synthInstance (mkApp3 (mkConst ``HAdd [0, 0, 0]) ty ty ty)
  let hSubInst ← synthInstance (mkApp3 (mkConst ``HSub [0, 0, 0]) ty ty ty)
  let hPowInst ← synthInstance (mkApp3 (mkConst ``HPow [0, 0, 0]) ty natTy ty)
  let negInst ← synthInstance (mkApp (mkConst ``Neg [0]) ty)
  let cache ← IO.mkRef (∅ : Std.HashMap Nat Expr)
  return {
    vars := vars
    mkMul := fun a b => mkApp6 (mkConst ``HMul.hMul [0, 0, 0]) ty ty ty hMulInst a b
    mkAdd := fun a b => mkApp6 (mkConst ``HAdd.hAdd [0, 0, 0]) ty ty ty hAddInst a b
    mkSub := fun a b => mkApp6 (mkConst ``HSub.hSub [0, 0, 0]) ty ty ty hSubInst a b
    mkPow := fun a k => mkApp6 (mkConst ``HPow.hPow [0, 0, 0]) ty natTy ty hPowInst a
      (mkNatLit k)
    mkNeg := fun a => mkApp3 (mkConst ``Neg.neg [0]) ty negInst a
    mkNum := fun n => do
      if let some e := (← cache.get)[n]? then return e
      let e ← mkNum n
      cache.modify (·.insert n e)
      return e }

/--
Parse one space-separated monomial string `"e₁.….eₙ.k …"` and build the
corresponding sum, or `none` if the string contains no monomials.  `ctx` only
labels error messages.
-/
def PolyBuilder.build? (b : PolyBuilder) (ctx : String) (s : String) :
    TermElabM (Option Expr) := do
  let n := b.vars.size
  let mut acc : Option Expr := none
  for tok in s.splitOn " " do
    let tok := tok.trimAscii.toString
    if tok.isEmpty then continue
    let fields := (tok.splitOn ".").map (·.trimAscii.toString)
    unless fields.length == n + 1 do
      throwError "{ctx}: monomial {tok} has {fields.length} fields, expected \
        {n + 1} ({n} exponents and a coefficient)"
    let some k := fields[n]!.toInt? |
      throwError "{ctx}: bad coefficient in monomial {tok}"
    let kAbs := k.natAbs
    let mut factors : Array Expr := #[]
    if kAbs != 1 then
      factors := factors.push (← b.mkNum kAbs)
    for i in [0:n] do
      let some e := fields[i]!.toNat? |
        throwError "{ctx}: bad exponent in monomial {tok}"
      if e == 1 then factors := factors.push b.vars[i]!
      else if e > 1 then factors := factors.push (b.mkPow b.vars[i]! e)
    let term ←
      if factors.isEmpty then b.mkNum kAbs
      else pure (factors[1:].foldl b.mkMul factors[0]!)
    acc := some <| match acc with
      | none => if k < 0 then b.mkNeg term else term
      | some e => if k < 0 then b.mkSub e term else b.mkAdd e term
  return acc

/--
`poly_def name : α in [v₁, …, vₙ] := "e₁.….eₙ.k …"` defines `name : α` as the
monomial sum `Σ k · v₁^e₁ ⋯ vₙ^eₙ`, the monomials separated by spaces and
negative coefficients allowed, building the body directly as an `Expr`.  The
variable terms `vᵢ` are elaborated with expected type `α`, and the number of
exponent fields in each monomial must be the number of variables listed.

The resulting definition is term-for-term what writing the sum as source
syntax produces — but elaborating such sums costs roughly a second per
monomial at certificate sizes (superlinear in practice; a ~660-monomial
definition set measures ≈ 10 min), while this command is essentially instant.
Intended for large computer-algebra-generated certificate polynomials.

An optional doc comment in front of the command becomes the doc string of the
generated definition.
-/
elab doc:(Lean.Parser.Command.docComment)? "poly_def " name:ident " : " ty:term
    " in " "[" vars:term,* "]" " := " spec:str : command => do
  Command.liftTermElabM do
    let elab1 (stx : Term) (expected : Option Expr) : TermElabM Expr := do
      let e ← Term.elabTerm stx expected
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    let ty ← elab1 ty none
    let mut varEs : Array Expr := #[]
    for v in vars.getElems do
      varEs := varEs.push (← elab1 v (some ty))
    if varEs.isEmpty then
      throwError "poly_def: at least one variable term is required"
    let b ← PolyBuilder.ofType ty varEs fun n => do
      elab1 ⟨Syntax.mkNumLit (toString n)⟩ (some ty)
    let some body ← b.build? "poly_def" spec.getString |
      throwError "poly_def: empty polynomial"
    let body ← instantiateMVars body
    let declName := (← getCurrNamespace) ++ name.getId
    addDecl <| .defnDecl {
      name := declName, levelParams := [], type := ty, value := body,
      hints := .abbrev, safety := .safe }
    Term.addTermInfo' name (mkConst declName) (isBinder := true)
    if let some doc := doc then
      addDocStringCore declName doc.getDocString

end

end Macaulean
