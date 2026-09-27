import Macaulean.Interpreter.Syntax
import Macaulean.Interpreter.Value

/-!
# Polynomial value operations

These are pure operations on immutable data. General polynomial reduction,
Buchberger, fraction fields, ideal equality, and general matrices are not hidden
behind these primitives. The m2Monomial-prefixed helpers have deliberately narrow,
explicit contracts rather than impersonating all native M2 overloads.
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

def equal (a b : Value) : Except Error Bool := do
  match a, b with
  | .algebra (.rationals), .algebra (.rationals) => return true
  | .algebra (.ring r), .algebra (.ring s) => return r = s
  | .algebra (.row r p), .algebra (.row s q) =>
    if r != s then return false
    return p = q
  | _, _ =>
    let (_, p, q) ← common a b
    return p = q

def constantValue? (p : Raw) : Option Rat :=
  match p with
  | [] => some 0
  | [(c, exps)] => if exps.all (· == 0) then some c else none
  | _ => none

def evalBinary (op : BinOp) (a b : Value) : Except Error Value := do
  match op with
  | .eq => return .bool (← equal a b)
  | .ne => return .bool (!(← equal a b))
  | .pow =>
    let (r, p) ← asPolynomial a
    let .zz k := b | .error (.algebra "polynomial exponent must be an integer")
    if k ≥ 0 then return .algebra (.poly r (← liftError (pow r.names.length p k.toNat)))
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
  | .add | .sub | .mul | .quot | .rem =>
    let (r, p, q) ← common a b
    let n := r.names.length
    let result ← match op with
      | .add => liftError (add n p q)
      | .sub => liftError (sub n p q)
      | .mul => liftError (mul n p q)
      | .quot | .rem => do
        if q.isEmpty then .error .divByZero
        else
          let (quotient, remainder) ← liftError (divideByTerm n p q)
          return if op = .quot then quotient else remainder
      | _ => .error (.algebra "unsupported polynomial operator")
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

def natList (ns : List Nat) : Value := .list (ns.map fun n => .zz n)

def unpack (arg : Value) : List Value :=
  match arg with | .sequence xs => xs | _ => [arg]

def unaryArg (arg : Value) : Except Error Value :=
  match unpack arg with
  | [a] => .ok a | xs => .error (.arity 1 xs.length)

def binaryArgs (arg : Value) : Except Error (Value × Value) :=
  match unpack arg with
  | [a,b] => .ok (a,b) | xs => .error (.arity 2 xs.length)

/-- All columns, including duplicate and zero generators, are retained. -/
def makeIdeal (arg : Value) : Except Error Value := do
  if let .algebra (.ideal r ps) := arg then return .algebra (.ideal r ps)
  if let .algebra (.row r ps) := arg then return .algebra (.ideal r ps)
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

def callPrimitive (primitive : Primitive) (arg : Value) : Except Error Value := do
  match primitive with
  | .ideal => makeIdeal arg
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
      let some r := object.ring? | .error (.algebra "expected a polynomial, ideal, or generator matrix")
      return .algebra (.ring r)
    | .coefficientRing, .algebra (.ring _) => return .algebra .rationals
    | .generators, .algebra (.ring r) =>
      return .list ((List.range r.names.length).map fun i =>
        .algebra (.poly r (generator r.names.length i)))
    | .generators, .algebra (.ideal r ps) => return .algebra (.row r ps)
    | .entries, .algebra (.row r ps) => return .list [.list (ps.map fun p => .algebra (.poly r p))]
    | .numgens, .algebra (.ring r) => return .zz r.names.length
    | .numgens, .algebra (.ideal _ ps) => return .zz ps.length
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
