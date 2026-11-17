import Macaulean.Interpreter.Syntax
import Macaulean.Interpreter.Value

/-! Finite-field primitive dispatch. General reduction and Buchberger remain
M2 library programs. All polynomial arithmetic uses the field-generic kernel
operations; canonical residues and dimensions are checked on input. -/
namespace Macaulean.M2.Finite
open Algebra
attribute [local instance] Lean.Grind.Ring.intCast Lean.Grind.Semiring.natCast
abbrev Data := Algebra.FinitePolynomialData.Raw

def wrap (a : Object) : Value := .algebra (.finite a)
def liftError (x : Except String α) : Except Error α := x.mapError Error.algebra

mutual
@[simp] def contains : Value → Bool
  | .algebra (.finite _) => true
  | .list xs | .sequence xs => containsList xs
  | _ => false
@[simp] def containsList : List Value → Bool
  | [] => false
  | x::xs => contains x || containsList xs
end

def ringOf? : Value → Option RingInfo
  | .algebra (.finite a) => a.ring? | _ => none

def polyRing? : Value → Option RingInfo
  | .algebra (.finite (.poly r _)) => some r | _ => none

def scalarOffset? : Value → Option Nat
  | .algebra (.finite (.scalar p _)) => some p | _ => none

def scalar (offset : Nat) (v : Value) : Except Error (PrimeField.Element offset) :=
  match v with
  | .zz n => .ok (Int.cast n : PrimeField.Element offset)
  | .qq q =>
    let numerator : PrimeField.Element offset := Int.cast q.num
    let denominator : PrimeField.Element offset := Nat.cast q.den
    if denominator = 0 then .error .divByZero
    else .ok (numerator * PrimeField.inverse denominator)
  | .algebra (.finite (.scalar p c)) =>
    if p != offset then .error (.algebra "coefficients belong to different fields")
    else if hc : c < offset+2 then .ok ⟨c,hc⟩
    else .error (.algebra "finite-field coefficient is not a canonical residue")
  | _ => .error (.algebra "expected a rational number or a coefficient in the same finite field")

def scalarValue (c : PrimeField.Element offset) : Value := wrap (.scalar offset c.val)

def constant (r : RingInfo) (c : PrimeField.Element r.offset) : Raw :=
  if c = 0 then [] else [(c.val,List.replicate r.names.length 0)]

def generator (r : RingInfo) (i : Nat) : Raw :=
  [(1,(List.range r.names.length).map fun j => if i = j then 1 else 0)]

def normalized (r : RingInfo) (p : Raw) : Except Error Raw :=
  liftError (FinitePolynomialData.normalized r.offset r.names.length p)

def cast (r : RingInfo) : Value → Except Error Raw
  | .algebra (.finite (.poly s p)) =>
    if r = s then normalized r p else .error (.algebra "polynomials belong to different rings")
  | v => do return constant r (← scalar r.offset v)

def asPolynomial : Value → Except Error (RingInfo × Raw)
  | .algebra (.finite (.poly r p)) => do return (r, ← normalized r p)
  | _ => .error (.algebra "expected a finite-field polynomial")

def common (a b : Value) : Except Error (RingInfo × Raw × Raw) := do
  let some r := (polyRing? a).or (polyRing? b) | .error (.algebra "expected a polynomial operand")
  return (r, ← cast r a, ← cast r b)

def unary (r : RingInfo)
    (op : FinitePolynomialData.Poly r.offset r.names.length → FinitePolynomialData.Poly r.offset r.names.length)
    (p : Raw) : Except Error Raw := do
  return FinitePolynomialData.encode (KernelPolynomial.normalize (op (← liftError (FinitePolynomialData.decode r.offset r.names.length p))))

def binary (r : RingInfo) (op : BinOp) (p q : Raw) : Except Error Raw :=
  match op with
  | .add => liftError (FinitePolynomialData.add r.offset r.names.length p q)
  | .sub => liftError (FinitePolynomialData.sub r.offset r.names.length p q)
  | .mul => liftError (FinitePolynomialData.mul r.offset r.names.length p q)
  | _ => .error (.algebra "unsupported finite polynomial operator")

def monomial (r : RingInfo) (p : Raw) : Except Error (PrimeField.Element r.offset × List Nat) := do
  let ps ← normalized r p
  match ps with
  | [(c,ns)] => return (← scalar r.offset (wrap (.scalar r.offset c)),ns)
  | _ => .error (.algebra "expected a nonzero single-term polynomial")

def divideByTerm (r : RingInfo) (p q : Raw) : Except Error (Raw × Raw) := do
  let (c,ns) ← monomial r q
  let p ← normalized r p
  let quot ← p.filterMapM fun (d,ds) => do
    if Polynomials.divides ns ds then
      let a ← scalar r.offset (wrap (.scalar r.offset d))
      return some ((a * PrimeField.inverse c).val,(ds.zip ns).map fun (i,j) => i-j)
    else return none
  return (quot,p.filter fun (_,ds) => !Polynomials.divides ns ds)

def unpack (v : Value) : List Value := match v with | .sequence xs => xs | _ => [v]
def unaryArg (v : Value) : Except Error Value :=
  match unpack v with | [a] => .ok a | xs => .error (.arity 1 xs.length)
def binaryArgs (v : Value) : Except Error (Value × Value) :=
  match unpack v with | [a,b] => .ok (a,b) | xs => .error (.arity 2 xs.length)
def natList (ns : List Nat) : Value := .list (ns.map fun n => .zz (Int.ofNat n))
def exponents (v : Value) : Except Error (List Nat) := do
  let .list xs := v | .error (.algebra "expected a list of nonnegative exponents")
  xs.mapM fun v => match v with
    | .zz n => if n ≥ 0 then .ok n.toNat else .error (.algebra "negative monomial exponent")
    | _ => .error (.algebra "expected integer monomial exponents")

def matrixView? : Value → Option (RingInfo × Nat × List (List Raw))
  | .algebra (.finite (.row r ps)) => some (r,ps.length,[ps])
  | .algebra (.finite (.matrix r cols rows)) => some (r,cols,rows)
  | _ => none

def asMatrix (v : Value) : Except Error (RingInfo × Nat × List (List Raw)) := do
  let some (r,cols,rows) := matrixView? v | .error (.algebra "expected a matrix")
  let rows ← rows.mapM fun row => do
    if row.length != cols then .error (.algebra "invalid matrix dimensions")
    else row.mapM (normalized r)
  return (r,cols,rows)

def matrixValue (r : RingInfo) (cols : Nat) (rows : List (List Raw)) : Value :=
  match rows with | [row] => wrap (.row r row) | _ => wrap (.matrix r cols rows)

def linearCombination (r : RingInfo) (row gs : List Raw) : Except Error Raw := do
  if row.length != gs.length then .error (.algebra "coefficient row has the wrong dimension")
  else
    let products ← (row.zip gs).mapM fun (a,b) => binary r .mul a b
    products.foldlM (binary r .add) []

def multiplyMatrices (a b : Value) : Except Error Value := do
  let (r,cols,left) ← asMatrix a
  let (s,resultCols,right) ← asMatrix b
  if r != s then .error (.algebra "matrices belong to different rings")
  else if cols != right.length then .error (.algebra "matrix multiplication dimension mismatch")
  else
    let result ← left.mapM fun row => (List.range resultCols).mapM fun j => do
      let column ← right.mapM fun entries => match entries[j]? with
        | some p => .ok p | none => .error (.algebra "invalid matrix dimensions")
      linearCombination r row column
    return matrixValue r resultCols result

def equal (a b : Value) : Except Error Bool := do
  if (matrixView? a).isSome || (matrixView? b).isSome then
    let (r,c,p) ← asMatrix a
    let (s,d,q) ← asMatrix b
    return r == s && c == d && p == q
  if (polyRing? a).isSome || (polyRing? b).isSome then
    let (r,p,q) ← common a b
    let _ := r
    return p == q
  if let some p := (scalarOffset? a).or (scalarOffset? b) then
    return (← scalar p a) == (← scalar p b)
  match a,b with
  | .algebra (.finite (.field _)), _ | _, .algebra (.finite (.field _))
  | .algebra (.finite (.ring _)), _ | _, .algebra (.finite (.ring _)) => return a == b
  | _,_ => .error (.noMethod "==" [a.className,b.className])

def evalBinary (op : BinOp) (a b : Value) : Except Error Value := do
  if op = .eq then return .bool (← equal a b)
  if op = .ne then return .bool (!(← equal a b))
  if op = .mul && ((matrixView? a).isSome || (matrixView? b).isSome) then
    return ← multiplyMatrices a b
  if let some r := (polyRing? a).or (polyRing? b) then
    if op = .pow then
      let p ← cast r a
      let .zz k := b | .error (.algebra "polynomial exponent must be an integer")
      if k ≥ 0 then return wrap (.poly r (← unary r (fun p => KernelPolynomial.pow p k.toNat) p))
      if p.isEmpty then return wrap (.poly r [])
      let [(c,ns)] := p | .error (.algebra "negative polynomial powers require a nonzero constant")
      unless ns.all (· == 0) do .error (.algebra "negative polynomial powers require a nonzero constant")
      let c ← scalar r.offset (wrap (.scalar r.offset c))
      return wrap (.poly r (constant r (PrimeField.inverse c ^ (-k).toNat)))
    if op = .div then
      let p ← cast r a
      let c ← scalar r.offset b
      if c = 0 then .error .divByZero
      else return wrap (.poly r (← unary r (Macaulean.Polynomial.smul (PrimeField.inverse c)) p))
    let p ← cast r a
    let q ← cast r b
    if op = .quot || op = .rem then
      if q.isEmpty then .error .divByZero
      else
        let (quot,rem) ← divideByTerm r p q
        return wrap (.poly r (if op = .quot then quot else rem))
    return wrap (.poly r (← binary r op p q))
  let some p := (scalarOffset? a).or (scalarOffset? b)
    | .error (.noMethod op.symbol [a.className,b.className])
  let x ← scalar p a
  if op = .pow then
    let .zz k := b | .error (.algebra "finite-field exponent must be an integer")
    if k ≥ 0 then return scalarValue (x ^ k.toNat)
    if x = 0 then .error .divByZero else return scalarValue (PrimeField.inverse x ^ (-k).toNat)
  let y ← scalar p b
  match op with
  | .add => return scalarValue (x+y)
  | .sub => return scalarValue (x-y)
  | .mul => return scalarValue (x*y)
  | .div => if y = 0 then .error .divByZero else return scalarValue (x * PrimeField.inverse y)
  | _ => .error (.noMethod op.symbol [a.className,b.className])

def evalUnary (op : UnOp) (a : Value) : Except Error Value := do
  if let some r := polyRing? a then
    let p ← cast r a
    match op with
    | .neg => return wrap (.poly r (← unary r Macaulean.Polynomial.neg p))
    | .pos => return wrap (.poly r p)
    | _ => .error (.noMethod op.symbol [a.className])
  let some p := scalarOffset? a | .error (.noMethod op.symbol [a.className])
  let c ← scalar p a
  match op with
  | .neg => return scalarValue (-c)
  | .pos => return scalarValue c
  | _ => .error (.noMethod op.symbol [a.className])

def makeIdeal (arg : Value) : Except Error Value := do
  match arg with
  | .algebra (.finite (.ideal r ps)) | .algebra (.finite (.row r ps))
  | .algebra (.finite (.basis r _ ps _)) => return wrap (.ideal r (← ps.mapM (normalized r)))
  | _ =>
    let args := arg.elements?.getD [arg]
    let some r := args.findSome? polyRing?
      | .error (.algebra "ideal construction requires a polynomial to determine the ring")
    return wrap (.ideal r (← args.mapM (cast r)))

def generatorValues (arg : Value) : Except Error (List Value) :=
  match arg with
  | .algebra (.finite (.ideal r ps)) | .algebra (.finite (.row r ps))
  | .algebra (.finite (.basis r _ ps _)) => .ok (ps.map fun p => wrap (.poly r p))
  | .algebra (.finite (.poly ..)) => .ok [arg]
  | .list xs | .sequence xs => .ok xs
  | _ => .error (.algebra "expected a polynomial, generator list, ideal, or Groebner basis")

def normalFormData (f g : Value) : Except Error Value := do
  let some r := (polyRing? f).or (ringOf? g) | .error (.algebra "normal form requires a polynomial ring")
  if let some s := ringOf? g then
    if r != s then .error (.algebra "polynomials belong to different rings")
  let p ← cast r f
  let gs ← generatorValues g
  let ps ← gs.mapM (cast r)
  return .list [wrap (.poly r p),.list (ps.map fun q => wrap (.poly r q))]

def makeBasis (input pairs : Value) : Except Error Value := do
  let .algebra (.finite (.ideal r original)) ← makeIdeal input | .error (.algebra "expected an ideal")
  let .list pairs := pairs | .error (.algebra "expected a list of represented polynomials")
  let represented ← pairs.mapM fun pair => do
    let .list [p,.list row] := pair | .error (.algebra "expected a polynomial and its coefficient row")
    let p ← cast r p
    let some (c,_) := p.head? | .error (.algebra "basis contains a zero polynomial")
    if c != 1 then .error (.algebra "basis must be monic")
    let row ← row.mapM (cast r)
    let image ← linearCombination r row original
    if image != p then .error (.algebra "invalid basis provenance") else return (p,row)
  return wrap (.basis r original (represented.map Prod.fst) (represented.map Prod.snd))

def changeMatrix (arg : Value) : Except Error Value := do
  let .algebra (.finite (.basis r input gs rows)) := arg | .error (.algebra "expected a Groebner basis")
  if rows.length != gs.length || rows.any (fun row => row.length != input.length) then
    .error (.algebra "invalid basis representation dimensions")
  else
    let data ← (List.range input.length).mapM fun i => rows.mapM fun row =>
      match row[i]? with | some p => normalized r p | none => .error (.algebra "invalid basis representation dimensions")
    return matrixValue r gs.length data

def callPrimitive (primitive : Polynomials.Primitive) (arg : Value) : Except Error Value := do
  match primitive with
  | .primeField =>
    let .zz p ← unaryArg arg | .error (.algebra "GF requires a prime integer characteristic")
    if p < 2 then .error (.algebra "a prime field characteristic must be at least two")
    else
      let field ← liftError (PrimeField.check p.toNat)
      return wrap (.field field.offset)
  | .ideal | .asIdeal => makeIdeal arg
  | .generatorList => return .list (← generatorValues (← unaryArg arg))
  | .makeBasis => let (a,b) ← binaryArgs arg; makeBasis a b
  | .normalFormData => let (a,b) ← binaryArgs arg; normalFormData a b
  | .changeMatrix => changeMatrix (← unaryArg arg)
  | .numRows | .numColumns =>
    let (_,cols,rows) ← asMatrix (← unaryArg arg)
    return .zz (if primitive = .numRows then rows.length else cols)
  | .promote =>
    let (a,b) ← binaryArgs arg
    match b with
    | .algebra (.finite (.ring r)) => return wrap (.poly r (← cast r a))
    | .algebra (.finite (.field p)) => return scalarValue (← scalar p a)
    | _ => .error (.algebra "expected a finite field or polynomial ring")
  | .fromExponents =>
    let (a,b) ← binaryArgs arg
    let .algebra (.finite (.ring r)) := a | .error (.algebra "expected a polynomial ring")
    let ns ← exponents b
    if ns.length != r.names.length then .error (.algebra "monomial exponent vector has the wrong dimension")
    else return wrap (.poly r [(1,ns)])
  | .coefficient | .monomialDivides | .monomialQuotient | .monomialLCM | .monomialCompare =>
    let (a,b) ← binaryArgs arg
    let (r,p,q) ← common a b
    let (c,x) ← monomial r p
    if primitive = .coefficient then
      if c != 1 then .error (.algebra "coefficient expects a monic monomial")
      else return wrap (.scalar r.offset ((q.find? fun t => t.2 == x).map (·.1) |>.getD 0))
    let (d,y) ← monomial r q
    match primitive with
    | .monomialDivides => return .bool (Polynomials.divides x y)
    | .monomialQuotient =>
      if Polynomials.divides y x then
        return wrap (.poly r [((c * PrimeField.inverse d).val,(x.zip y).map fun (i,j) => i-j)])
      else .error (.algebra "monomial does not divide the numerator")
    | .monomialLCM => return wrap (.poly r [(1,(x.zip y).map fun (i,j) => max i j)])
    | .monomialCompare =>
      if hx : x.length = r.names.length then
        if hy : y.length = r.names.length then
          return .zz (match Macaulean.Mon.grevlex ⟨x,hx⟩ ⟨y,hy⟩ with | .lt => -1 | .eq => 0 | .gt => 1)
        else .error (.algebra "invalid monomial dimension")
      else .error (.algebra "invalid monomial dimension")
    | _ => .error (.algebra "invalid polynomial primitive")
  | .ring | .coefficientRing | .generators | .entries | .numgens =>
    let a ← unaryArg arg
    match primitive,a with
    | .ring, .algebra (.finite object) =>
      match object with
      | .scalar p _ => return wrap (.field p)
      | _ =>
        let some r := object.ring? | .error (.algebra "expected a polynomial, ideal, or matrix")
        return wrap (.ring r)
    | .coefficientRing, .algebra (.finite (.ring r)) => return wrap (.field r.offset)
    | .generators, .algebra (.finite (.ring r)) =>
      return .list ((List.range r.names.length).map fun i => wrap (.poly r (generator r i)))
    | .generators, .algebra (.finite (.ideal r ps)) | .generators, .algebra (.finite (.basis r _ ps _)) =>
      return wrap (.row r ps)
    | .entries, .algebra (.finite (.row r ps)) => return .list [.list (ps.map fun p => wrap (.poly r p))]
    | .entries, .algebra (.finite (.matrix ..)) =>
      let (r,_,rows) ← asMatrix a
      return .list (rows.map fun ps => .list (ps.map fun p => wrap (.poly r p)))
    | .numgens, .algebra (.finite (.ring r)) => return .zz r.names.length
    | .numgens, .algebra (.finite (.ideal _ ps)) | .numgens, .algebra (.finite (.basis _ _ ps _)) => return .zz ps.length
    | _,_ => .error (.noMethod primitive.name [a.className])
  | _ =>
    let a ← unaryArg arg
    let (r,ps) ← asPolynomial a
    match primitive with
    | .leadCoefficient => return wrap (.scalar r.offset (ps.head?.map (·.1) |>.getD 0))
    | .leadTerm => return wrap (.poly r (ps.take 1))
    | .leadMonomial =>
      let some (_,ns) := ps.head? | .error (.algebra "zero polynomial has no leading monomial")
      return wrap (.poly r [(1,ns)])
    | .exponents => return .list (ps.map fun t => natList t.2)
    | .terms => return .list (ps.map fun t => wrap (.poly r [t]))
    | .listForm => return .list (ps.map fun (c,ns) => .sequence [natList ns,wrap (.scalar r.offset c)])
    | .size => return .zz ps.length
    | _ => .error (.noMethod primitive.name [a.className])
end Macaulean.M2.Finite
