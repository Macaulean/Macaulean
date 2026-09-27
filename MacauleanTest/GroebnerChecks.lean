import Macaulean.Interpreter.Algebra

/-!
# Independent test-side verification

This reducer is not part of the production interpreter or its `gb` operation.
It checks source-language results by a separately written finite reduction
routine. Native M2 supplies a second, external oracle.
-/
namespace Macaulean.M2.GroebnerChecks
open Algebra

private def exact (x : Option α) : Except String α :=
  match x with | some a => .ok a | none => .error "invalid polynomial operation in checker"

private def reduction (h : Poly) : List Poly → Option Poly
  | [] => none
  | g :: gs =>
    match Poly.monomialQuotient h.leadingTerm g.leadingTerm with
    | some factor => do
      let product ← factor.mul g
      h.sub product
    | none => reduction h gs

/-- Move irreducible leading terms into the remainder; never fabricate success on exhaustion. -/
def normalForm : Nat → Poly → List Poly → Except String Poly
  | 0, _, _ => .error "test-side polynomial reduction exhausted"
  | fuel + 1, p, gs => do
    if p.isZero then return p
    match reduction p gs with
    | some smaller => normalForm fuel smaller gs
    | none =>
      let lt := p.leadingTerm
      let tail ← exact (p.sub lt)
      let remainder ← normalForm fuel tail gs
      exact (lt.add remainder)

private def sPolynomial (p q : Poly) : Except String Poly := do
  let m ← exact (Poly.monomialLCM p.leadingMonomial q.leadingMonomial)
  let a ← exact (Poly.monomialQuotient m p.leadingTerm)
  let b ← exact (Poly.monomialQuotient m q.leadingTerm)
  let a ← exact (a.mul p)
  let b ← exact (b.mul q)
  exact (a.sub b)

private def irreducibleTails (p : Poly) (gs : List Poly) : Bool :=
  p.data.terms.tail.all fun term =>
    let monomial := Poly.ofData p.ring ⟨[term]⟩
    gs.all fun g => Poly.monomialDivides g.leadingMonomial monomial == some false

/-- Check both ideal containments, Buchberger pairs, normalized monicity, and
reduced tails. Certificate identities are checked separately from m2MakeBasis. -/
def check (g : Basis) : Except String Unit := do
  let r := g.input.ring
  if g.generators.length != g.representations.length then
    throw "basis/change-matrix row count mismatch"
  for p in g.generators do
    unless p.ring == r && !p.isZero && p.leadingCoefficient == 1 do
      throw "basis contains a zero, nonmonic, or foreign-ring element"
    unless p == Poly.ofData p.ring p.data do throw "basis contains unnormalized data"
    unless irreducibleTails p g.generators do throw "basis tail is reducible"
  for (p,row) in g.generators.zip g.representations do
    let image ← (linearCombination r row g.input.generators).mapError Error.toM2String
    unless image == p do throw "invalid basis provenance"
  for p in g.input.generators do
    let remainder ← normalForm 10000 p g.generators
    unless remainder.isZero do throw "input generator is not in the computed ideal"
  for i in List.range g.generators.length do
    for j in List.range i do
      let p := g.generators[i]!
      let q := g.generators[j]!
      unless Poly.monomialDivides p.leadingMonomial q.leadingMonomial == some false &&
          Poly.monomialDivides q.leadingMonomial p.leadingMonomial == some false do
        throw "basis has redundant leading monomials"
      let s ← sPolynomial p q
      let remainder ← normalForm 10000 s g.generators
      unless remainder.isZero do throw "a final S-polynomial has nonzero normal form"

private def eraseOne (x : Value) : List Value → Option (List Value)
  | [] => none
  | y :: ys => if x == y then some ys else (y :: ·) <$> eraseOne x ys

def sameMultiset : List Value → List Value → Bool
  | [], ys => ys.isEmpty
  | x :: xs, ys => match eraseOne x ys with
    | none => false | some ys => sameMultiset xs ys

def observed (g : Basis) : Value := .list (g.generators.map listFormValue)
end Macaulean.M2.GroebnerChecks
