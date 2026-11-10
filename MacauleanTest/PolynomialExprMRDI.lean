import Macaulean.IdealMembership

open Lean Macaulean
namespace Macaulean.Polynomial.Expr.MRDITests

deriving instance BEq for Polynomial.Expr

private def term (c : Int) (x y : Nat) : Polynomial.Expr Int 2 :=
  .term ⟨c,⟨[x,y],rfl⟩⟩
private def samples : List (Polynomial.Expr Int 2) := [
  term 3 2 1, .sum [], .product [], .pow (term (-2) 1 0) 0,
  .pow (term 1 0 1) 12345678901234567890,
  .sum [term 1 1 0, .product [term 2 0 1, .pow (.sum [term 3 0 0,term (-1) 1 1]) 4]],
  .product [.sum [],.product [],term 0 0 0]]

private def document [MrdiType α] (x : α) : Mrdi :=
  runMrdiWithSeed (m := Id) 0 (toMrdi x)
private def decodeDocument [MrdiType α] (doc : Mrdi) : Except String α :=
  runMrdiWithSeed (m := Id) 0 (fromMrdi? doc)
private def decodeData (data : Json) : Except String (Polynomial.Expr Int 2) :=
  decodeDocument { document (term 1 0 0) with data := data }

open Elab Command in
run_cmd do
  for expr in samples do
    -- Exercise the complete JSON document parser, not just the data decoder.
    let serialized := (toJson (document expr)).compress
    let json ← ofExcept (Json.parse serialized)
    let doc : Mrdi ← ofExcept (fromJson? json)
    let actual : Polynomial.Expr Int 2 ← ofExcept (decodeDocument doc)
    unless actual == expr do throwError "expression tree changed during MRDI round trip"
  let empty : Polynomial.Expr Rat 0 := .term ⟨mkRat (-5) 7,⟨[],rfl⟩⟩
  let actual : Polynomial.Expr Rat 0 ← ofExcept (decodeDocument (document empty))
  unless actual == empty do throwError "rational zero-variable round trip failed"
  let deep := (List.range 200).foldl (fun e _ => Polynomial.Expr.pow e 2) (term 1 1 0)
  let actual : Polynomial.Expr Int 2 ← ofExcept (decodeDocument (document deep))
  unless actual == deep do throwError "nested expression round trip failed"
  let mismatchDimension : Except String (Polynomial.Expr Int 3) := decodeDocument (document (.sum [] : Polynomial.Expr Int 2))
  unless mismatchDimension.toOption.isNone do throwError "accepted wrong variable count on empty expression"
  let mismatchCoefficient : Except String (Polynomial.Expr Rat 2) := decodeDocument (document (.sum [] : Polynomial.Expr Int 2))
  unless mismatchCoefficient.toOption.isNone do throwError "accepted wrong coefficient type on empty expression"
  let expected := Json.arr #[.str "pow",
    .arr #[.str "term", .arr #[toJson (3 : Int),.arr #[.str "2",.str "1"]]],.str "4"]
  unless (document (Polynomial.Expr.pow (term 3 2 1) 4)).data == expected do
    throwError "expression wire format changed"
  let goodTerm := (document (term 1 1 0)).data
  let malformed : List Json := [
    .null, .arr #[], .arr #[.str "unknown"], .arr #[.str "sum"],
    .arr #[.str "sum",.str "not an array"], .arr #[.str "product",.arr #[],.null],
    .arr #[.str "pow",goodTerm,.str "-1"], .arr #[.str "pow",goodTerm,toJson (2 : Nat)],
    .arr #[.str "pow",goodTerm,.str "1.5"], .arr #[.str "pow",goodTerm,.str ""],
    .arr #[.str "term",.arr #[]],
    .arr #[.str "term",.arr #[.str "bad coefficient",.arr #[.str "0",.str "0"]]],
    .arr #[.str "term",.arr #[toJson (1 : Int),.arr #[.str "0"]]],
    .arr #[.str "term",.arr #[toJson (1 : Int),.arr #[.str "-1",.str "0"]]],
    .arr #[.str "sum",.arr #[goodTerm,.arr #[.str "unknown"]]]]
  for bad in malformed do
    unless (decodeData bad).toOption.isNone do throwError "accepted malformed expression: {bad}"
  logInfo m!"POLYNOMIAL_EXPR_MRDI_COMPLETE: {samples.length + 2} round trips, metadata mismatches, {malformed.length} malformed inputs"

open Elab Command in
run_cmd do
  for name in [``Polynomial.Expr.encode, ``Polynomial.Expr.encodeList,
      ``Polynomial.Expr.decodeWithFuel?, ``Polynomial.Expr.decode?] do
    let axioms ← Lean.collectAxioms name
    for dependency in axioms do
      unless dependency ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "{name} depends on unapproved axiom {dependency}"

end Macaulean.Polynomial.Expr.MRDITests
