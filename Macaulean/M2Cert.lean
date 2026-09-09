/-
Copyright (c) 2026 Macaulean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Macaulean.IdealMembership
import Macaulean.PolyCert

/-!
# `m2cert` / `m2cert?`: a Macaulay2 certificate, checked by the Lean kernel

`m2idealmem` and `m2remainder` get their cofactors from Macaulay2 and then
close the resulting polynomial identity with `simp` on `Macaulean.Polynomial`'s
denotation.  That step is superlinear and does not finish at certificate scale.
`m2cert` keeps the Macaulay2 round trip and replaces the closing step: the
cofactors are rebuilt as terms of the *ambient* ring (through the same
`PolyBuilder` that `poly_def` uses) and the identity goes to
`algebra_norm_reflect`'s kernel certificate.

Two goal shapes:

* `g ∣ f` — one generator.  Macaulay2 divides `f` by `g`; if the remainder is
  zero the quotient `q` is the witness, `f = g * q` is proved reflectively and
  `Exists.intro` finishes.
* `p = r` with `hᵢ : gᵢ = 0` given as arguments.  Macaulay2 divides `p - r` by
  the `gᵢ`; if the remainder is zero the cofactors satisfy
  `p - r = Σ qᵢ gᵢ`, `p = r + Σ qᵢ gᵢ` is proved reflectively, and the
  generators are peeled off with the hypotheses.

```
m2cert                       -- goal `g ∣ f`
m2cert [h₁, …, h_k]          -- goal `p = r`
m2cert? …                    -- the same, and print a Macaulay2-free replacement
m2cert +native …             -- check the certificate natively instead (warns)
```

`m2cert?` also prints, as a "Try this:" suggestion, the `poly_cert` invocation
carrying the cofactors it just obtained, in `poly_def`'s `e₁.….eₙ.k` monomial
format and in Macaulay2's emission order.  Pasting it over the `m2cert?` closes
the same goal with the same proof term and no Macaulay2 in the loop, which is
the recommended way to keep a computer algebra system out of a build.

## Which base ring, and what happens to denominators

The ambient ring's `Macaulean.CASRing` instance says whether its coefficients
are serialised over `ZZ` or over `QQ`; that is the only thing choosing the
Macaulay2 base ring, and `Int` and `Rat` ship with instances saying `ZZ` and
`QQ`.

Over `QQ` the cofactors are routinely *not* integral, and the reflective check
has nowhere to put a denominator -- it normalises over
`Macaulean.Polynomial Int nv`, and `Rat` coefficients would drag `Nat.gcd`, an
out-of-line GMP call, into the kernel.  So `m2cert` clears them: it takes the
least common denominator `d` of all the cofactors at once, hands
`poly_cert … / d` the integral cofactors `d * qᵢ`, and lets it check the
integer identity and cancel `d` through the ring's `Macaulean.CASRingRat`
instance.  The printed suggestion carries the `/ d`, so a paste proves the same
thing the same way.  A ring with no `CASRingRat` instance gets a message
naming the class.

A `poly_def` *declaration* cannot hold such a cofactor: its body is a closed
term, and the ring variables here are the goal's own bound variables.  When the
variables are constants of a concrete polynomial ring, the same monomial
strings go into `poly_def` directly and the resulting constants into
`poly_cert [name, …]`.
-/

open Lean Grind Elab Parser Tactic Meta

namespace Macaulean.M2Cert

/-- One certificate polynomial as Macaulay2 sent it: exponent vectors over the
goal's variables (in the request's index order) with rational coefficients, in
Macaulay2's emission order.  Over `ZZ` every coefficient is an integer; over
`QQ` they need not be, and `certify` scales them (see `CertPoly.denominator`).
-/
abbrev CertPoly := Array (Array Nat × Rat)

/-- Read a coefficient: `"3"` (an `Int`) or `["3", "4"]` (a `Rat`). -/
def parseCoeff (j : Json) : Except String Rat :=
  match j with
  | .str s => (s.toInt?).elim (.error s!"not an integer: {s}") (fun k => .ok (Rat.ofInt k))
  | .arr #[n, d] => do
    let nS ← n.getStr?
    let dS ← d.getStr?
    let some num := nS.toInt? | .error s!"not an integer numerator: {nS}"
    let some den := dS.toNat? | .error s!"not a natural denominator: {dS}"
    if den == 0 then .error "a coefficient with denominator 0"
    else .ok (mkRat num den)
  | j => do
    let k : Int ← Lean.fromJson? j
    pure (Rat.ofInt k)

/-- Read one exponent vector; it has one entry per variable of the request. -/
def parseMon (nv : Nat) (j : Json) : Except String (Array Nat) := do
  let .arr entries := j | .error "expected an array of exponents"
  let powers ← entries.mapM fun e => do
    let s ← e.getStr?
    let some k := s.toNat? | .error s!"not an exponent: {s}"
    pure k
  if powers.size == nv then .ok powers
  else .error s!"expected {nv} exponents, got {powers.size}"

/-- Read a polynomial out of a `Polynomial` MRDI reply.  An empty `data` array
is the zero polynomial (Macaulay2 sends `listForm 0` as `{}`). -/
def parseCertPoly (nv : Nat) (m : Mrdi) : Except String CertPoly := do
  let .arr terms := m.data | .error "expected an array of terms"
  terms.mapM fun t => do
    let .arr #[c, mon] := t | .error "expected a coefficient/monomial pair"
    pure (← parseMon nv mon, ← parseCoeff c)

/-- The least common denominator of a certificate polynomial's coefficients:
the smallest `d` for which `d * p` has integer coefficients. -/
def CertPoly.denominator (p : CertPoly) : Nat :=
  p.foldl (fun acc (_, k) => Nat.lcm acc k.den) 1

/-- Render `scale * p` in `poly_def`'s monomial format: space-separated
`e₁.….eₙ.k` tokens, in the order they arrived.  `scale` is a common
denominator of the *whole* certificate, so every `scale * k` is an integer;
`certify` checks that rather than trusting it. -/
def CertPoly.toSpec (p : CertPoly) (nv : Nat) (scale : Nat := 1) : String :=
  if p.isEmpty then
    -- the zero polynomial still has to name `nv` exponents
    String.intercalate "." (List.replicate nv "0") ++ ".0"
  else
    " ".intercalate (p.toList.map fun (powers, k) =>
      String.intercalate "."
        ((powers.toList.map toString) ++ [toString (k * (scale : Int)).num]))

/-- Is this the zero polynomial? -/
def CertPoly.isZero (p : CertPoly) : Bool := p.all fun (_, k) => k == 0

/-- Are all coefficients of `scale * p` integers? -/
def CertPoly.scalesToInt (p : CertPoly) (scale : Nat) : Bool :=
  p.all fun (_, k) => (k * (scale : Int)).den == 1

/-- The user-facing name of a goal variable, for the `in [x, y, z]` clause of
the printed suggestion. -/
def varName (fv : FVarId) : MetaM String := do
  pure (toString (← fv.getUserName).eraseMacroScopes)

/--
The Macaulay2 half: divide `polyExpr` by `gens`, insist that the remainder
vanishes, and hand back the cofactors as monomial specs together with the
variables they are written in.
-/
unsafe def certify (tacName : Name) (goal : MVarId) (A : Expr) (gens : Array Expr)
    (polyExpr : Expr) : MetaM (Array FVarId × Array String × Nat) := do
  let fail {α} (e : String) : MetaM α := throwTacticEx tacName goal e
  -- Which base ring the coefficients travel in is the ambient ring's own
  -- decision, taken through its `Macaulean.CASRing` instance.
  let crd ← AlgPoly.Tactic.casRingData A
  let base ← crd.m2BaseRing
  let coeffRing := match base with
    | .ZZ => mkConst ``Int
    | .QQ => mkConst ``Rat
  let (fvars, reply) ← m2QuotientRemainderRaw goal A gens polyExpr (sortVars := true)
    (coeffRing := some coeffRing)
  let nv := fvars.size
  let .ok remainder := parseCertPoly nv reply.remainder
    | fail "could not read Macaulay2's remainder"
  unless remainder.isZero do
    throwTacticEx tacName goal
      "the remainder modulo the given generators is not zero, so the goal does \
        not follow from them"
  let quotients : Array CertPoly ← reply.quotient.toArray.mapM fun q =>
    match parseCertPoly nv q with
    | .ok p => pure p
    | .error e => fail s!"could not read a Macaulay2 quotient: {e}"
  unless quotients.size == gens.size do
    fail s!"Macaulay2 returned {quotients.size} cofactors for {gens.size} generators"
  -- One denominator for the whole certificate: the kernel checks
  -- `d * (p - r) = Σ (d * qᵢ) gᵢ` over the integers, and `d` is cancelled
  -- afterwards.
  let denom := quotients.foldl (fun acc q => Nat.lcm acc q.denominator) 1
  if denom != 1 && base matches .ZZ then
    fail s!"Macaulay2 returned a cofactor with denominator {denom} over ZZ, \
      which should not happen"
  unless quotients.all (·.scalesToInt denom) do
    fail s!"scaling the cofactors by {denom} did not clear their denominators"
  pure (fvars, quotients.map (·.toSpec nv denom), denom)

/-- Build the cofactor terms from their monomial specs, over the goal's own
variables.  This goes through `poly_cert`'s builder, so the term proved here is
the term the printed suggestion proves. -/
def buildCofactors (A : Expr) (fvars : Array FVarId) (specs : Array String) :
    TermElabM (Array Expr) := do
  let b ← PolyCert.mkBuilder A (fvars.map mkFVar)
  specs.mapM fun s => do
    match ← b.build? "m2cert" s with
    | some e => pure e
    | none => b.mkNum 0

/-- The `poly_cert …` line that replaces this `m2cert?`. -/
def suggestionText (specs : Array String) (vars : Array String)
    (native : Bool) (hypNames : Array String) (denom : Nat := 1) : String :=
  let quoted := ", ".intercalate (specs.toList.map fun s => "\"" ++ s ++ "\"")
  let flag := if native then " +native" else ""
  let scale := if denom == 1 then "" else " / " ++ toString denom
  let using_ :=
    if hypNames.isEmpty then ""
    else " using [" ++ ", ".intercalate hypNames.toList ++ "]"
  "poly_cert" ++ flag ++ " [" ++ quoted ++ "]" ++ scale ++ " in ["
    ++ ", ".intercalate vars.toList ++ "]" ++ using_

/--
The whole tactic.  `hypStxs` is `none` for the divisibility shape and the
generator hypotheses for the membership shape; `suggest` turns on the "Try
this:" replacement.
-/
unsafe def run (ref : Syntax) (tacName : Name) (native suggest : Bool)
    (hypStxs : Option (Array Term)) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let fail {α} (e : MessageData) : TacticM α := throwTacticEx tacName goal e
  -- The two shapes differ only in what gets divided by what.
  let (A, gens, dividend, hyps) ←
    match hypStxs with
    | none =>
      match_expr target with
      | Dvd.dvd A _ g f => pure (A, #[g], f, (#[] : Array Expr))
      | _ => fail m!"expected a divisibility goal `g ∣ f`, got{indentExpr target}"
    | some stxs =>
      let some (A, p, r) := target.eq?
        | fail m!"expected an equality goal `p = r`, got{indentExpr target}"
      let hyps ← stxs.mapM (elabTerm · none)
      let zeroExpr ← natAsRingElem A 0
      let gens ← hyps.mapM fun h => do
        let some (ring, lhs, rhs) := (← inferType h).eq?
          | fail m!"expected each argument to prove `g = 0`, got{indentExpr (← inferType h)}"
        unless (← isDefEq A ring) && (← isDefEq rhs zeroExpr) do
          fail m!"expected each argument to prove `g = 0` over{indentExpr A}"
        pure lhs
      pure (A, gens, ← mkSub p r, hyps)
  let (fvars, specs, denom) ← certify tacName goal A gens dividend
  let cofactors ← buildCofactors A fvars specs
  if hypStxs.isNone then
    PolyCert.closeDvd native goal cofactors[0]! denom
  else
    PolyCert.closeEq native goal hyps cofactors denom
  replaceMainGoal []
  if suggest then
    let vars ← fvars.mapM fun fv => (varName fv : MetaM String)
    let hypNames := (hypStxs.getD #[]).map fun t => (Syntax.prettyPrint t.raw).pretty
    let text := suggestionText specs vars native hypNames denom
    Lean.Meta.Tactic.TryThis.addSuggestion ref
      { suggestion := .string text
        postInfo? := some "\n(the cofactors are Macaulay2's, in its emission order; \
          pasting this keeps Macaulay2 out of the build)" }

/--
`m2cert` closes `g ∣ f`, and `m2cert [h₁, …, h_k]` — with `hᵢ : gᵢ = 0` —
closes `p = r`, by asking Macaulay2 for the cofactors and checking the
resulting polynomial identity with `algebra_norm_reflect`'s kernel certificate.
Macaulay2 has to find remainder zero; otherwise the goal does not follow and
the tactic says so.

`m2cert +native` checks the identity with `decide +native` instead, and warns.
`m2cert?` additionally prints the Macaulay2-free `poly_cert` line to write in
its place.
-/
syntax (name := m2cert) "m2cert" (Macaulean.AlgPoly.Tactic.nativeFlag)?
  (Macaulean.PolyCert.certList)? : tactic

/-- `m2cert?` is `m2cert` plus a "Try this:" suggestion: the `poly_cert`
invocation carrying the cofactors Macaulay2 just produced, which closes the
same goal with the same proof and no Macaulay2. -/
syntax (name := m2certSuggest) "m2cert?" (Macaulean.AlgPoly.Tactic.nativeFlag)?
  (Macaulean.PolyCert.certList)? : tactic

@[tactic m2cert]
unsafe def m2CertTactic : Tactic := fun stx => do
  let native := !stx[1].isNone
  let hyps := if stx[2].isNone then none else some (PolyCert.listTerms ⟨stx[2][0]⟩)
  run stx `m2cert native (suggest := false) hyps

@[tactic m2certSuggest]
unsafe def m2CertSuggestTactic : Tactic := fun stx => do
  let native := !stx[1].isNone
  let hyps := if stx[2].isNone then none else some (PolyCert.listTerms ⟨stx[2][0]⟩)
  run stx `m2cert? native (suggest := true) hyps

end Macaulean.M2Cert
