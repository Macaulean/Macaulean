import Macaulean.Interpreter.Syntax
import Macaulean.Interpreter.Value

/-! # Pure polynomial operations

General reduction and Buchberger are M2 library code, not primitives here.
This module provides coefficient arithmetic, narrow monomial operations, and
checked first-order basis/matrix containers. It makes no Groebner-basis theorem
from the mere construction of a result object.
-/
namespace Macaulean.M2.Polynomials
def liftError (r : Except String α) : Except Error α := r.mapError Error.algebra
def scalar? : Value → Option Rat
  | .zz n => some n | .qq q => some q | _ => none
def ringOf? : Value → Option RingInfo
  | .algebra a => a.ring? | _ => none
def polyRing? : Value → Option RingInfo
  | .algebra (.poly r _) => some r | _ => none
def asPolynomial (v : Value) : Except Error (RingInfo × Raw) :=
  match v with
  | .algebra (.poly r p) => do return (r, ← liftError (normalized r.names.length p))
  | _ => .error (.algebra s!"expected a polynomial, got {v.className}")
def cast (r : RingInfo) (v : Value) : Except Error Raw :=
  match v with
  | .algebra (.poly s p) =>
    if r = s then liftError (normalized r.names.length p)
    else .error (.algebra "polynomials belong to different rings")
  | _ => match scalar? v with
    | some c => .ok (constant r.names.length c)
    | none => .error (.algebra s!"cannot promote {v.className} to {r.display}")
def common (a b : Value) : Except Error (RingInfo × Raw × Raw) := do
  let some r := (polyRing? a).or (polyRing? b)
    | .error (.algebra "expected a polynomial operand")
  return (r, ← cast r a, ← cast r b)

/-- Dimensions are retained even for zero-column and zero-row matrices. -/
def matrixView? : Value → Option (RingInfo × Nat × List (List Raw))
  | .algebra (.row r ps) => some (r, ps.length, [ps])
  | .algebra (.matrix r cols rows) => some (r, cols, rows)
  | _ => none
def asMatrix (v : Value) : Except Error (RingInfo × Nat × List (List Raw)) := do
  let some (r,cols,rows) := matrixView? v | .error (.algebra "expected a matrix")
  let rows ← rows.mapM fun row => do
    if row.length != cols then .error (.algebra "invalid matrix dimensions")
    else row.mapM fun p => liftError (normalized r.names.length p)
  return (r,cols,rows)
def matrixValue (r : RingInfo) (cols : Nat) (rows : List (List Raw)) : Value :=
  match rows with
  | [row] => .algebra (.row r row)
  | _ => .algebra (.matrix r cols rows)

/-- An exact linear combination, with explicit dimension checks before zipping. -/
def linearCombination (n : Nat) (coefficients generators : List Raw) : Except Error Raw := do
  if coefficients.length != generators.length then
    .error (.algebra "coefficient row has the wrong dimension")
  else
    let products ← (coefficients.zip generators).mapM fun (a,b) => liftError (mul n a b)
    products.foldlM (fun sum p => liftError (add n sum p)) []

def multiplyMatrices (a b : Value) : Except Error Value := do
  let (r,cols,left) ← asMatrix a
  let (s,resultCols,right) ← asMatrix b
  if r != s then .error (.algebra "matrices belong to different rings")
  else if cols != right.length then .error (.algebra "matrix multiplication dimension mismatch")
  else
    let result ← left.mapM fun row =>
      (List.range resultCols).mapM fun j => do
        let column ← right.mapM fun entries =>
          match entries[j]? with
          | some p => .ok p
          | none => .error (.algebra "invalid matrix dimensions")
        linearCombination r.names.length row column
    return matrixValue r resultCols result

def equal (a b : Value) : Except Error Bool := do
  match matrixView? a, matrixView? b with
  | some _, some _ =>
    let (r,c,p) ← asMatrix a
    let (s,d,q) ← asMatrix b
    return r == s && c == d && p == q
  | some _, none | none, some _ => .error (.noMethod "==" [a.className,b.className])
  | none, none =>
    match a, b with
    | .algebra .rationals, _ | _, .algebra .rationals
    | .algebra (.ring _), _ | _, .algebra (.ring _) =>
      .error (.noMethod "==" [a.className,b.className])
    | _, _ =>
      let (_, p, q) ← common a b
      return p = q

def constantValue? (p : Raw) : Option Rat :=
  match p with
  | [] => some 0
  | [(c, exps)] => if exps.all (· == 0) then some c else none
  | _ => none

def arithmetic (op : BinOp) (n : Nat) (p q : Raw) : Except Error Raw :=
  match op with
  | .add => liftError (add n p q)
  | .sub => liftError (sub n p q)
  | .mul => liftError (mul n p q)
  | .quot | .rem => do
    if q.isEmpty then .error .divByZero
    else
      let result ← liftError (divideByTerm n p q)
      pure (if op = .quot then result.1 else result.2)
  | _ => .error (.algebra "unsupported polynomial operator")

def evalBinary (op : BinOp) (a b : Value) : Except Error Value := do
  match op with
  | .eq => return .bool (← equal a b)
  | .ne => return .bool (!(← equal a b))
  | .pow =>
    let (r, p) ← asPolynomial a
    let .zz k := b | .error (.algebra "polynomial exponent must be an integer")
    if k ≥ 0 then return .algebra (.poly r (← liftError (pow r.names.length p k.toNat)))
    -- Native M2 totalizes negative powers of the zero polynomial to zero.
    -- This is a polynomial compatibility convention, not field inversion.
    if p.isEmpty then return .algebra (.poly r [])
    let some c := constantValue? p
      | .error (.algebra "negative polynomial powers require a nonzero constant")
    if c = 0 then .error .divByZero
    else return .algebra (.poly r (constant r.names.length (c ^ k)))
  | .div =>
    let (r, p) ← asPolynomial a
    let some c := scalar? b
      | .error (.algebra "polynomial division by a polynomial requires the fraction-field extension")
    if c = 0 then .error .divByZero
    else return .algebra (.poly r (← liftError (smul r.names.length (1/c) p)))
  | .mul =>
    if (matrixView? a).isSome || (matrixView? b).isSome then multiplyMatrices a b
    else
      let (r,p,q) ← common a b
      return .algebra (.poly r (← arithmetic op r.names.length p q))
  | .add | .sub | .quot | .rem =>
    let (r, p, q) ← common a b
    let result ← arithmetic op r.names.length p q
    return .algebra (.poly r result)
  | _ => .error (.noMethod op.symbol [a.className,b.className])

def evalUnary (op : UnOp) (a : Value) : Except Error Value := do
  let (r, p) ← asPolynomial a
  match op with
  | .neg => return .algebra (.poly r (← liftError (neg r.names.length p)))
  | .pos => return .algebra (.poly r p)
  | _ => .error (.noMethod op.symbol [a.className])
def builtinEnv : List (String × Value) :=
  ("QQ", .algebra .rationals) :: ("gens", .algebra (.builtin .generators)) ::
    primitives.map (fun p => (p.name, .algebra (.builtin p)))
def natList (ns : List Nat) : Value := .list (ns.map fun n => .zz (Int.ofNat n))
def unpack (arg : Value) : List Value :=
  match arg with | .sequence xs => xs | _ => [arg]
def unaryArg (arg : Value) : Except Error Value :=
  match unpack arg with
  | [a] => .ok a | xs => .error (.arity 1 xs.length)
def binaryArgs (arg : Value) : Except Error (Value × Value) :=
  match unpack arg with
  | [a,b] => .ok (a,b) | xs => .error (.arity 2 xs.length)
def makeIdeal (arg : Value) : Except Error Value := do
  if let .algebra (.ideal r ps) := arg then return .algebra (.ideal r ps)
  if let .algebra (.row r ps) := arg then return .algebra (.ideal r ps)
  if let .algebra (.basis r _ ps _) := arg then return .algebra (.ideal r ps)
  let args := arg.elements?.getD [arg]
  let some r := args.findSome? polyRing?
    | .error (.algebra "ideal construction requires a polynomial to determine the ring")
  let ps ← args.mapM (cast r)
  return .algebra (.ideal r ps)
def exponentsArg (arg : Value) : Except Error (List Nat) := do
  let .list values := arg | .error (.algebra "expected a list of nonnegative exponents")
  values.mapM fun v => match v with
    | .zz n => if n ≥ 0 then .ok n.toNat else .error (.algebra "negative monomial exponent")
    | _ => .error (.algebra "expected integer monomial exponents")

/-- Extract ordered generators, not a computed basis. -/
def generatorValues (arg : Value) : Except Error (List Value) := do
  match arg with
  | .algebra (.ideal r ps) | .algebra (.row r ps) | .algebra (.basis r _ ps _) =>
    return ps.map fun p => .algebra (.poly r p)
  | .algebra (.poly ..) => return [arg]
  | .list xs | .sequence xs => return xs
  | _ => .error (.algebra "expected a polynomial, generator list, ideal, or Groebner basis")

/-- Validate the ring even if the divisor list is empty or contains only zeros. -/
def normalFormData (f g : Value) : Except Error Value := do
  let some r := (polyRing? f).or (ringOf? g)
    | .error (.algebra "normal form requires a polynomial ring")
  if let some s := ringOf? g then
    if r != s then .error (.algebra "polynomials belong to different rings")
  let p ← cast r f
  let values ← generatorValues g
  let ps ← values.mapM (cast r)
  return .list [.algebra (.poly r p), .list (ps.map fun q => .algebra (.poly r q))]

/-- Validate dimensions, rings, normalization, monicity and exact provenance.
This checks basis-to-input containment only: Buchberger's criterion and the
other ideal containment are checked independently in tests, not assumed here. -/
def makeBasis (input pairs : Value) : Except Error Value := do
  let .algebra (.ideal r original) ← makeIdeal input
    | .error (.algebra "expected an ideal")
  let original ← original.mapM fun p => liftError (normalized r.names.length p)
  let .list pairs := pairs | .error (.algebra "expected a list of represented polynomials")
  let represented ← pairs.mapM fun pair => do
    let .list [p,.list row] := pair
      | .error (.algebra "expected a polynomial and its coefficient row")
    let p ← cast r p
    let some (c,_) := p.head? | .error (.algebra "basis contains a zero polynomial")
    if c != 1 then .error (.algebra "basis must be monic")
    let row ← row.mapM (cast r)
    let image ← linearCombination r.names.length row original
    if image != p then .error (.algebra "invalid basis provenance")
    else return (p,row)
  return .algebra (.basis r original (represented.map Prod.fst) (represented.map Prod.snd))

/-- The coefficient rows are stored per basis element; the displayed change
matrix has one row per original input and one column per basis element. -/
def changeMatrix (arg : Value) : Except Error Value := do
  let .algebra (.basis r input gs rows) := arg
    | .error (.algebra "expected a Groebner basis")
  if rows.length != gs.length || rows.any (fun row => row.length != input.length) then
    .error (.algebra "invalid basis representation dimensions")
  else
    let data ← (List.range input.length).mapM fun i =>
      rows.mapM fun row => match row[i]? with
        | some p => liftError (normalized r.names.length p)
        | none => .error (.algebra "invalid basis representation dimensions")
    return matrixValue r gs.length data

def callPrimitive (primitive : Primitive) (arg : Value) : Except Error Value := do
  match primitive with
  | .ideal | .asIdeal => makeIdeal arg
  | .generatorList => return .list (← generatorValues (← unaryArg arg))
  | .makeBasis =>
    let (a,b) ← binaryArgs arg
    makeBasis a b
  | .normalFormData =>
    let (a,b) ← binaryArgs arg
    normalFormData a b
  | .changeMatrix => changeMatrix (← unaryArg arg)
  | .numRows | .numColumns =>
    let (_,cols,rows) ← asMatrix (← unaryArg arg)
    return .zz (if primitive = .numRows then rows.length else cols)
  | .promote =>
    let (a, b) ← binaryArgs arg
    let .algebra (.ring r) := b | .error (.algebra "expected a polynomial ring")
    return .algebra (.poly r (← cast r a))
  | .fromExponents =>
    let (a, b) ← binaryArgs arg
    let .algebra (.ring r) := a | .error (.algebra "expected a polynomial ring")
    let ns ← exponentsArg b
    if ns.length != r.names.length then .error (.algebra "monomial exponent vector has the wrong dimension")
    else return .algebra (.poly r [(1,ns)])
  | .coefficient | .monomialDivides | .monomialQuotient | .monomialLCM | .monomialCompare =>
    let (a, b) ← binaryArgs arg
    let (r, p, q) ← common a b
    let n := r.names.length
    match primitive with
    | .coefficient =>
      let (c, powers) ← liftError (monomial n p)
      if c != 1 then .error (.algebra "coefficient expects a monic monomial")
      else return .qq ((q.find? fun t => t.2 == powers).map (·.1) |>.getD 0)
    | .monomialDivides =>
      let (_, x) ← liftError (monomial n p)
      let (_, y) ← liftError (monomial n q)
      return .bool (divides x y)
    | .monomialQuotient => return .algebra (.poly r (← liftError (monomialQuotient n p q)))
    | .monomialLCM => return .algebra (.poly r (← liftError (monomialLCM n p q)))
    | .monomialCompare => return .zz (← liftError (monomialCompare n p q))
    | _ => .error (.algebra "invalid polynomial primitive")
  | .ring | .coefficientRing | .generators | .entries | .numgens =>
    let a ← unaryArg arg
    match primitive, a with
    | .ring, .algebra object =>
      let some r := object.ring? | .error (.algebra "expected a polynomial, ideal, or matrix")
      return .algebra (.ring r)
    | .coefficientRing, .algebra (.ring _) => return .algebra .rationals
    | .generators, .algebra (.ring r) =>
      return .list ((List.range r.names.length).map fun i => .algebra (.poly r (generator r.names.length i)))
    | .generators, .algebra (.ideal r ps) | .generators, .algebra (.basis r _ ps _) =>
      return .algebra (.row r ps)
    | .entries, .algebra (.row r ps) => return .list [.list (ps.map fun p => .algebra (.poly r p))]
    | .entries, .algebra (.matrix ..) =>
      let (r,_,rows) ← asMatrix a
      return .list (rows.map fun ps => .list (ps.map fun p => .algebra (.poly r p)))
    | .numgens, .algebra (.ring r) => return .zz r.names.length
    | .numgens, .algebra (.ideal _ ps) | .numgens, .algebra (.basis _ _ ps _) => return .zz ps.length
    | _, _ => .error (.noMethod primitive.name [a.className])
  | _ =>
    let a ← unaryArg arg
    let (r, ps) ← asPolynomial a
    match primitive with
    | .leadCoefficient => return .qq (ps.head?.map (·.1) |>.getD 0)
    | .leadTerm => return .algebra (.poly r (ps.take 1))
    | .leadMonomial =>
      let some (_, ns) := ps.head? | .error (.algebra "zero polynomial has no leading monomial")
      return .algebra (.poly r [(1, ns)])
    | .exponents => return .list (ps.map fun t => natList t.2)
    | .terms => return .list (ps.map fun t => .algebra (.poly r [t]))
    | .listForm => return .list (ps.map fun (c,ns) => .sequence [natList ns, .qq c])
    | .size => return .zz ps.length
    | _ => .error (.noMethod primitive.name [a.className])
end Macaulean.M2.Polynomials
