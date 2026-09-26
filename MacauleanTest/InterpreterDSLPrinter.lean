import Macaulean.Interpreter.DSL

/-!
Regression tests for the native Lean reader/formatter interface. These exercise
both registered printer hooks rather than merely checking that the parser builds.
-/

open Lean Elab Command

run_cmd do
  for source in #[
    "0", "x = 3;", "- -3", "+ +3", "2 * -7 // 2", "2^-2^2",
    "(1\n+2)", "1 +\n2", "(1 + -- λ, 中文\n 2) * 3", "value$2 = 0x1F"
  ] do
    let stx ← match Parser.runParserCategory (← getEnv) `m2 source with
      | .ok stx => pure stx
      | .error error => throwError "M2 parser failed on {repr source}: {error}"
    let printed ← liftCoreM <| PrettyPrinter.ppCategory `m2 stx
    let rendered := printed.pretty
    unless rendered == source do
      throwError "M2 formatter changed significant source: {repr source} -> {repr rendered}"
    let reparsed ← match Parser.runParserCategory (← getEnv) `m2 rendered with
      | .ok stx => pure stx
      | .error error => throwError "formatted M2 failed to parse: {error}"
    unless Macaulean.M2.DSL.lowerInput ⟨stx⟩ == Macaulean.M2.DSL.lowerInput ⟨reparsed⟩ do
      throwError "formatting changed the M2 AST or semicolon suppression"

-- A source-less synthetic node must not silently get a made-up fuel budget.
run_cmd do
  let body := Syntax.node .none `Macaulean.M2.DSL.num #[mkNumLit "3"]
  let input := Syntax.node .none `Macaulean.M2.DSL.input #[body, mkNullNode #[]]
  let stx := Syntax.node .none `Macaulean.M2.DSL.inputSyntax #[input]
  match Macaulean.M2.DSL.lowerInput ⟨stx⟩ with
  | .error "M2 syntax has no original source range" => pure ()
  | _ => throwError "accepted a source-less synthetic M2 input"
