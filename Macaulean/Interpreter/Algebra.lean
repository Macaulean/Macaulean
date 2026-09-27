import Macaulean.Interpreter.Syntax
import Macaulean.Interpreter.Value

/-!
# Checked scalar algebra and small polynomial interfaces

These are first-order operations. Polynomial division, S-polynomials,
Buchberger's pair loop, and interreduction are intentionally absent: they live
in `Buchberger.m2` and execute through the same lexical runtime as user code.
-/
namespace Macaulean.M2.Algebra

def rational? : Value → Option Rat
  | .zz n => some n | .qq q => some q | _ => none

def promotePolynomial (r : Ring) : Value → Except Error Poly
  | .polynomial p => if p.ring = r then .ok p else .error .differentRings
  | .zz n => .ok (Poly.constant r n)
  | .qq q => .ok (Poly.constant r q)
  | v => .error (.algebra s!"expected a polynomial over {r.toM2String}, got {v.className}")

def polynomialPair (a b : Value) : Except Error (Poly × Poly) := do
  match a, b with
  | .polynomial p, b => return (p, ← promotePolynomial p.ring b)
  | a, .polynomial q => return (← promotePolynomial q.ring a, q)
  | _, _ => .error (.algebra "expected at least one polynomial operand")

def polynomialEqual (a b : Value) : Except Error Bool := do
  let (a,b) ← polynomialPair a b
  return decide (a = b)

def checked (message : String) : Option α → Except Error α
  | some a => .ok a | none => .error (.algebra message)

def matrixValid (m : Matrix) : Bool :=
  m.rows.all fun row => row.length == m.columns && row.all (fun p => p.ring == m.ring)

def matrixMultiply (a b : Matrix) : Except Error Matrix := do
  if a.ring != b.ring then .error .differentRings else do
    if !matrixValid a || !matrixValid b || a.columns != b.rows.length then
      .error (.algebra "incompatible matrix dimensions")
    else do
      let rows ← a.rows.mapM fun row => (List.range b.columns).mapM fun j => do
        let q ← (row.zip b.rows).mapM fun (p, other) => do
          let q ← checked "invalid matrix entry" other[j]?
          checked "incompatible matrix rings" (p.mul q)
        q.foldlM (fun sum p => checked "incompatible matrix rings" (sum.add p))
          (Poly.constant a.ring 0)
      return ⟨a.ring, b.columns, rows⟩

def matrixSub (a b : Matrix) : Except Error Matrix := do
  if a.ring != b.ring then .error .differentRings else do
    if !matrixValid a || !matrixValid b || a.columns != b.columns || a.rows.length != b.rows.length then
      .error (.algebra "incompatible matrix dimensions")
    else do
      let rows ← (a.rows.zip b.rows).mapM fun (xs,ys) =>
        (xs.zip ys).mapM fun (p,q) => checked "incompatible matrix rings" (p.sub q)
      return ⟨a.ring, a.columns, rows⟩

def subscript (a b : Value) : Except Error Value := do
  match a, b with
  | a, .ring r => return .polynomial (← promotePolynomial r a)
  | .ring r, .zz i =>
    if i < 0 || r.names.length ≤ i.toNat then
      .error (.indexOutOfBounds i r.names.length)
    else return .polynomial (Poly.indeterminate r i.toNat)
  | .matrix m, .sequence [.zz i, .zz j] =>
    if i < 0 || j < 0 then .error (.algebra "matrix indices must be nonnegative") else do
      let row ← checked "matrix row index out of bounds" m.rows[i.toNat]?
      let p ← checked "matrix column index out of bounds" row[j.toNat]?
      return .polynomial p
  | _, _ => .error (.noMethod "_" [a.className, b.className])

/-- Called only after the shared scalar/collection dispatcher has no method. -/
def binary (op : BinOp) (a b : Value) : Except Error Value := do
  match op, a, b with
  | .subscript, _, _ => subscript a b
  | .eq, .ring r, .ring s => return .bool (r == s)
  | .ne, .ring r, .ring s => return .bool (r != s)
  | .eq, .coefficientRing r, .coefficientRing s => return .bool (r == s)
  | .ne, .coefficientRing r, .coefficientRing s => return .bool (r != s)
  | .eq, .globalSymbol x, .globalSymbol y => return .bool (x == y)
  | .ne, .globalSymbol x, .globalSymbol y => return .bool (x != y)
  | .mul, .matrix x, .matrix y => return .matrix (← matrixMultiply x y)
  | .sub, .matrix x, .matrix y => return .matrix (← matrixSub x y)
  | .eq, .matrix x, .matrix y => return .bool (x == y)
  | .ne, .matrix x, .matrix y => return .bool (x != y)
  | .eq, .matrix x, .zz 0 | .eq, .zz 0, .matrix x =>
    return .bool (x.rows.all fun row => row.all Poly.isZero)
  | .pow, .polynomial p, .zz n =>
    if 0 ≤ n then return .polynomial (p.pow n.toNat)
    else do
      let c ← checked "negative powers require a constant polynomial" p.constant?
      -- Native polynomial inversion uses zero for the zero polynomial. This
      -- is deliberately different from scalar QQ division by zero.
      return .polynomial (Poly.constant p.ring (c ^ n))
  | _, _, _ =>
    let isPolynomial := match a,b with | .polynomial _,_ | _,.polynomial _ => true | _,_ => false
    if !isPolynomial then .error (.noMethod op.symbol [a.className,b.className]) else do
      let (p,q) ← polynomialPair a b
      match op with
      | .add => return .polynomial (← checked "incompatible polynomial rings" (p.add q))
      | .sub => return .polynomial (← checked "incompatible polynomial rings" (p.sub q))
      | .mul => return .polynomial (← checked "incompatible polynomial rings" (p.mul q))
      | .div =>
        let c ← checked "division by a nonconstant polynomial requires a fraction field" q.constant?
        if c = 0 then .error .divByZero else return .polynomial (p.smul (1/c))
      | .eq => return .bool (p == q)
      | .ne => return .bool (p != q)
      | _ => .error (.noMethod op.symbol [a.className,b.className])

def unary (op : UnOp) (v : Value) : Except Error Value :=
  match op,v with
  | .neg,.polynomial p => .ok (.polynomial p.neg)
  | .pos,.polynomial p => .ok (.polynomial p)
  | _,_ => .error (.noMethod op.symbol [v.className])

def polynomialRing? : Value → Option Ring
  | .polynomial p => some p.ring | .ring r => some r
  | .ideal i => some i.ring | .basis b => some b.input.ring | .matrix m => some m.ring
  | _ => none

def polynomialValues (ps : List Poly) : Value := .list (ps.map Value.polynomial)

def listFormValue (p : Poly) : Value := .list (p.data.terms.map fun t =>
  .sequence [.list (t.monomial.powers.map fun (n : Nat) => .zz (Int.ofNat n)), .qq t.coefficient])

def asIdeal (arg : Value) : Except Error Ideal := do
  match arg with
  | .ideal i => return i
  | .basis g => return g.input
  | .matrix m =>
    if !matrixValid m || m.rows.length != 1 then
      .error (.algebra "only ideals (one-row polynomial matrices) are supported")
    else return ⟨m.ring, m.rows.flatten⟩
  | _ =>
    let xs := arg.elements?.getD [arg]
    let some r := xs.findSome? polynomialRing?
      | .error (.algebra "expected a polynomial-typed generator; use ideal(0_R) for the zero ideal")
    let ps ← xs.mapM (promotePolynomial r)
    return ⟨r,ps⟩

def generatorList (arg : Value) : Except Error (List Poly) := do
  match arg with
  | .basis g => return g.generators
  | .list [] | .sequence [] => return []
  | _ => return (← asIdeal arg).generators

def linearCombination (r : Ring) : List Poly → List Poly → Except Error Poly
  | [], [] => .ok (Poly.constant r 0)
  | a :: restA, b :: restB => do
    let p ← checked "incompatible representation rings" (a.mul b)
    let tail ← linearCombination r restA restB
    checked "incompatible representation rings" (p.add tail)
  | _,_ => .error (.algebra "invalid representation length")

/-- Check change-of-basis identities before publishing a result object.
This checks provenance only, not Buchberger's criterion. -/
def makeBasis (input : Ideal) (pairs : List Value) : Except Error Basis := do
  let pairs ← pairs.mapM fun pair => do
    let some [.polynomial p, .list row] := pair.elements?
      | .error (.algebra "expected {polynomial, representation} in basis result")
    let p ← promotePolynomial input.ring (.polynomial p)
    let row ← row.mapM (promotePolynomial input.ring)
    let represented ← linearCombination input.ring row input.generators
    if represented != p then .error (.algebra "invalid change-of-basis identity")
    else return (p,row)
  return ⟨input, pairs.map Prod.fst, pairs.map Prod.snd⟩

def primitive (op : Primitive) (arg : Value) : Except Error Value := do
  match op,arg with
  | .ideal,_ | .asIdeal,_ => return .ideal (← asIdeal arg)
  | .generatorList,_ => return polynomialValues (← generatorList arg)
  | .gens,.ring r => return polynomialValues ((List.range r.names.length).map (Poly.indeterminate r))
  | .gens,.ideal i => return .matrix ⟨i.ring,i.generators.length,[i.generators]⟩
  | .gens,.basis g => return .matrix ⟨g.input.ring,g.generators.length,[g.generators]⟩
  | .entries,.matrix m => return .list (m.rows.map polynomialValues)
  | .flatten,.list xs => return .list (xs.flatMap fun v => v.elements?.getD [v])
  | .flatten,.sequence xs => return .sequence (xs.flatMap fun v => v.elements?.getD [v])
  | .ringOf,.zz _ => return .coefficientRing .integers
  | .ringOf,.qq _ => return .coefficientRing .rationals
  | .ringOf,_ =>
    let r ← checked "expected a polynomial, ideal, matrix, or basis" (polynomialRing? arg)
    return .ring r
  | .numgens,.ring r => return .zz r.names.length
  | .numgens,.ideal i => return .zz i.generators.length
  | .numgens,.basis b => return .zz b.generators.length
  | .leadCoefficient,.polynomial p => return .qq p.leadingCoefficient
  | .leadMonomial,.polynomial p =>
    if p.isZero then .error (.algebra "zero polynomial has no leading monomial")
    else return .polynomial p.leadingMonomial
  | .leadTerm,.polynomial p => return .polynomial p.leadingTerm
  | .exponents,.polynomial p =>
    return .list (p.data.terms.map fun t => .list (t.monomial.powers.map fun (n : Nat) => .zz (Int.ofNat n)))
  | .listForm,.polynomial p => return listFormValue p
  | .terms,.polynomial p =>
    return polynomialValues (p.data.terms.map fun t => Poly.ofData p.ring ⟨[t]⟩)
  | .promote,.sequence [v,.ring r] => return .polynomial (← promotePolynomial r v)
  | .promote,.sequence [v,.coefficientRing .rationals] =>
    return .qq (← checked "expected a rational number" (rational? v))
  | .numerator,.qq q => return .zz q.num
  | .denominator,.qq q => return .zz q.den
  | .numerator,.zz n => return .zz n
  | .denominator,.zz _ => return .zz 1
  | .size,.polynomial p => return .zz p.data.terms.length
  | .size,.list xs | .size,.sequence xs => return .zz xs.length
  | .monomialDivides,.sequence [.polynomial a,.polynomial b] =>
    if a.ring != b.ring then .error .differentRings else
      return .bool (← checked "expected nonzero monomials" (Poly.monomialDivides a b))
  | .monomialQuotient,.sequence [.polynomial a,.polynomial b] =>
    if a.ring != b.ring then .error .differentRings else
      return .polynomial (← checked "monomial quotient is not exact" (Poly.monomialQuotient a b))
  | .monomialLCM,.sequence [.polynomial a,.polynomial b] =>
    if a.ring != b.ring then .error .differentRings else
      return .polynomial (← checked "expected nonzero monomials" (Poly.monomialLCM a b))
  | .monomialCompare,.sequence [.polynomial a,.polynomial b] =>
    if a.ring != b.ring then .error .differentRings else do
      let o ← checked "incompatible monomial rings" (Poly.leadingCompare a b)
      return .zz (match o with | .lt => -1 | .eq => 0 | .gt => 1)
  | .makeBasis,.sequence [.ideal input,.list pairs] => return .basis (← makeBasis input pairs)
  | .basisInput,.basis g => return .ideal g.input
  | .changeMatrix,.basis g =>
    let rows ← (List.range g.input.generators.length).mapM fun i =>
      g.representations.mapM fun row => checked "invalid change-of-basis dimensions" row[i]?
    return .matrix ⟨g.input.ring,g.generators.length,rows⟩
  | _,_ => .error (.algebra s!"unsupported argument for {repr op}: {arg.className}")

mutual
/-- Ring specs are values. Existing indeterminates carry the underlying symbol,
not the alias spelling used by the caller. -/
def variableSpecifications : Value → Except Error (List (String × Option Nat))
  | .null => .ok []
  | .globalSymbol name => .ok [(name,none)]
  | .symbol name cell => .ok [(name,some cell)]
  | .polynomial p => do
    let spec ← checked "expected an indeterminate in ring specification" p.indeterminate?
    return [spec]
  | .list xs | .sequence xs => variableSpecificationsMany xs
  | _ => .error (.algebra "unsupported ring-variable specification; expected symbols or indeterminates")
def variableSpecificationsMany : List Value → Except Error (List (String × Option Nat))
  | [] => .ok []
  | x :: xs => do return (← variableSpecifications x) ++ (← variableSpecificationsMany xs)
end
end Macaulean.M2.Algebra
