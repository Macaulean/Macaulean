import Macaulean.Interpreter.Value

/-!
# Independent test-side algebra

No production polynomial arithmetic, normalization, monomial order, division,
or provenance checker is called below. Raw coefficient/exponent lists are checked
with a separately written insertion normalizer and reduction implementation.
This is a test oracle, not a formal proof of Buchberger's criterion.
-/
namespace Macaulean.M2.GroebnerChecks
abbrev Poly := List (Rat × List Nat)

def reverseLex : List Nat → List Nat → Bool
  | [], [] => false
  | a :: as, b :: bs => if a == b then reverseLex as bs else a < b
  | _, _ => false

def before (a b : List Nat) : Bool :=
  if a.sum == b.sum then reverseLex a.reverse b.reverse else a.sum > b.sum

def insert (t : Rat × List Nat) : Poly → Poly
  | [] => if t.1 == 0 then [] else [t]
  | u :: us =>
    if t.1 == 0 then u :: us
    else if t.2 == u.2 then
      if t.1 + u.1 == 0 then us else (t.1 + u.1,t.2) :: us
    else if before t.2 u.2 then t :: u :: us
    else u :: insert t us

def normalize (p : Poly) : Poly := p.foldl (fun result t => insert t result) []
def add (p q : Poly) : Poly := q.foldl (fun result t => insert t result) (normalize p)
def neg (p : Poly) : Poly := p.map fun (c,e) => (-c,e)
def sub (p q : Poly) : Poly := add p (neg q)
def mulTerm (t : Rat × List Nat) (p : Poly) : Poly :=
  normalize (p.map fun (c,e) => (t.1*c,(t.2.zip e).map fun (a,b) => a+b))
def mul (p q : Poly) : Poly := p.foldl (fun result t => add result (mulTerm t q)) []

def divides : List Nat → List Nat → Bool
  | [], [] => true
  | a :: as, b :: bs => a ≤ b && divides as bs
  | _, _ => false

def reduction (p : Poly) : List Poly → Option Poly
  | [] => none
  | g :: gs =>
    match p.head?, g.head? with
    | some (a,x), some (b,y) =>
      if b != 0 && divides y x then
        some (sub p (mulTerm (a/b,(x.zip y).map fun (i,j) => i-j) g))
      else reduction p gs
    | _, _ => reduction p gs

/-- Exhaustion is failure, even in the test oracle. A decreasing leading
monomial is checked at every cancellation, independently of the DSL loop. -/
def normalForm : Nat → Poly → List Poly → Except String Poly
  | 0, _, _ => .error "independent reducer exhausted"
  | fuel + 1, p, gs => do
    let p := normalize p
    match p with
    | [] => return []
    | t :: ts =>
      match reduction p gs with
      | some q =>
        if let some u := q.head? then
          unless before t.2 u.2 do throw "independent reduction did not lower the leading monomial"
        normalForm fuel q gs
      | none => return insert t (← normalForm fuel ts gs)

def sPolynomial (p q : Poly) : Except String Poly := do
  let some (a,x) := p.head? | .error "zero S-polynomial operand"
  let some (b,y) := q.head? | .error "zero S-polynomial operand"
  if a == 0 || b == 0 || x.length != y.length then .error "invalid S-polynomial operand"
  else
    let lcm := (x.zip y).map fun (i,j) => max i j
    let u := (lcm.zip x).map fun (i,j) => i-j
    let v := (lcm.zip y).map fun (i,j) => i-j
    return sub (mulTerm (1/a,u) p) (mulTerm (1/b,v) q)

def combine : List Poly → List Poly → Except String Poly
  | [], [] => .ok []
  | a :: as, b :: bs => do return add (mul a b) (← combine as bs)
  | _, _ => .error "independent provenance dimension mismatch"

def validate (n : Nat) (p : Poly) : Except String Unit := do
  unless p.all (fun t => t.2.length == n) do throw "invalid exponent dimension"
  unless normalize p == p do throw "noncanonical polynomial data"

/-- Both ideal containments, every final S-pair, monicity, and reducedness. -/
def check (object : Polynomials.Object) : Except String Unit := do
  let .basis r input gs rows := object | .error "expected a basis object"
  if rows.length != gs.length then throw "basis/provenance row count mismatch"
  for p in input ++ gs ++ rows.flatten do validate r.names.length p
  for (p,row) in gs.zip rows do
    let some (c,_) := p.head? | .error "basis contains zero"
    unless c == 1 do throw "basis is not monic"
    let image ← combine row input
    unless image == p do throw "invalid independent basis provenance"
    for (_,exps) in p.tail do
      for g in gs do
        let some (_,lead) := g.head? | .error "basis contains zero"
        if divides lead exps then throw "basis has a reducible tail"
  for p in input do
    unless (← normalForm 10000 p gs).isEmpty do throw "input is not in the output ideal"
  for i in List.range gs.length do
    for j in List.range i do
      let p := gs[i]!
      let q := gs[j]!
      let some (_,a) := p.head? | .error "basis contains zero"
      let some (_,b) := q.head? | .error "basis contains zero"
      if divides a b || divides b a then throw "basis has redundant leading monomials"
      unless (← normalForm 10000 (← sPolynomial p q) gs).isEmpty do
        throw "a final S-pair does not reduce to zero"

def form (p : Poly) : Value :=
  .list (p.map fun (c,e) => .sequence [.list (e.map fun n => .zz (Int.ofNat n)), .qq c])
def observed (object : Polynomials.Object) : Except String (List Value) :=
  match object with
  | .basis _ _ gs _ => .ok (gs.map form)
  | _ => .error "expected a basis object"
private def eraseOne (x : Value) : List Value → Option (List Value)
  | [] => none
  | y :: ys => if x == y then some ys else (y :: ·) <$> eraseOne x ys

def sameMultiset : List Value → List Value → Bool
  | [], ys => ys.isEmpty
  | x :: xs, ys => match eraseOne x ys with
    | none => false | some ys => sameMultiset xs ys
end Macaulean.M2.GroebnerChecks
