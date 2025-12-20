import Macaulean
import MRDI.Basic
import MRDI.Poly

import Lean

open Lean Elab Tactic

def productOfFactors (factors : List (Nat × Nat)) : Nat :=
  factors.foldl (fun c ((a,b) : Nat × Nat) => c*a^b) 1

structure ProvenFactorization (n : Nat) where
  factors : List (Nat × Nat)
  proof : n = productOfFactors factors

def tryProveFactorization (n: Nat) (factors : List (Nat × Nat)) : Option (ProvenFactorization n) :=
  let p := productOfFactors factors
  let proof : Decidable (n = p) := inferInstance
  match proof with
    | .isTrue proof' => .some ⟨ factors, proof' ⟩
    | .isFalse _ => .none

def runJSONRPCTest := do
  let (m2Process,m2Server) <- startM2Server
  let result1 <- m2Server.eval "1+1"
  IO.println s!"Macaulay2 Output: {result1}"
  let result2 <- m2Server.eval "factor 20"
  IO.println s!"Macaulay2 Output: {result2}"
  let n := 7000
  let result3 <- m2Server.factorNat n
  IO.println s!"Macaualy2 Output: {result3}"
  match tryProveFactorization n result3 with
    | .some _ => IO.println s!"Proof Successful!"
    | .none => IO.println s!"Incorrect Factorization!"
  let poly : Grind.CommRing.Poly := .add 3 (.mult ⟨2, 2⟩ <| .unit) <| .add 5 (.mult ⟨2, 3⟩ <| .unit) <| .num 0
  let mrdiData := toMrdi poly
  --The toString is to deal with the fact that loadMRDI in MRDI.m2 only takes strings
  let result5 : List String <- m2Server.sendRequest "mrdiFactor" [toString <| toJson mrdiData]
  result5.forM <| fun x =>
    match Json.parse x >>= fromJson? with
      | .ok mrdiData => IO.println <| repr <| fromMrdi? (α := Grind.CommRing.Poly) mrdiData
      | .error str => IO.println ("Invalid reply from mrdiEcho: " ++ str)
  pure m2Process

elab "macaulay" : tactic => do
  IO.println "TEST"
  let goal ← getMainGoal
  let target ← getMainTarget
  let pf := Expr.const `True.intro []
  let s ← get
  try
    closeMainGoal `macaulay pf
  catch e =>
    set s
    throwError "macaulay can only prove True"
  return

example : True := by macaulay

def main : IO Unit :=
  do let m2Process <- runJSONRPCTest
     let returnCode <- m2Process.wait
     IO.println s!"Macaulay2 Return Code: {returnCode}"

-- #eval main
