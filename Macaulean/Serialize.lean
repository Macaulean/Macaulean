import MRDI.Poly

open MRDI

namespace Lean.Grind.CommRing

def Mon.serialize : Mon → Monomial
  | .unit => #[]
  | .mult p m => (#[p] : Array Power).append m.serialize

def Poly.serialize : Poly → PolynomialData
  | .num k => #[⟨k, #[]⟩]
  | .add k m p => p.serialize.push ⟨k, m.serialize⟩

def Monomial.deserialize : Monomial → Mon
  | #[] => .unit
  | powers =>
      let powers := powers.qsort fun a b => a.x < b.x
      powers.foldr (fun power acc => .mult power acc) .unit

def PolynomialData.deserialize : PolynomialData → Poly :=
  fun terms => terms.foldl (init := .num 0) fun acc term =>
    acc.insert term.coeff (Monomial.deserialize term.mon)

end Lean.Grind.CommRing
