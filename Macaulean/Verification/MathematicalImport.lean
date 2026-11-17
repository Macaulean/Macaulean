import Macaulean.Verification.MathematicalExport

/-!
# Explicit Lean-to-worksheet imports

Evaluation proposes a finite runtime value; the kernel checks that it equals the
encoding of the supplied Lean term before any binding is published. Ring identities
are reserved, and reuse of an existing identity requires a matching runtime ring.
-/
namespace Macaulean.M2.Verification.MathematicalImport
open Lean Elab Command Meta
open Macaulean.Algebra MathematicalViews

private def checked (result : Except String α) : CommandElabM α :=
  match result with | .ok a => pure a | .error e => throwError e

private partial def hasRing (ring : Value) : Value → Bool
  | .list vs | .sequence vs => vs.any (hasRing ring)
  | value => match Polynomials.callPrimitive .ring value with
    | .ok r => r == ring
    | .error _ => false

private def reserveRing (session : Session) (ring : Value) : CommandElabM Runtime.Heap := do
  let r ← checked (readRing ring)
  unless r.names.eraseDups.length == r.names.length do
    throwError "imported ring has duplicate variable names"
  if r.id < session.heap.nextRing then
    unless (session.env.map Prod.snd ++ session.heap.cells ++ session.outputs.map (·.value)).any (hasRing ring) do
      throwError "imported ring identity conflicts with the worksheet; use a fresh identity or an exported ring"
  return { session.heap with nextRing := max session.heap.nextRing (r.id + 1) }

private def publishRingVariables (ring : Value) (state : Runtime.State) : CommandElabM Runtime.State := do
  let r ← checked (readRing ring)
  let mut result := state
  for (name,i) in r.names.zip (List.range r.names.length) do
    let value := match ring with
      | .algebra (.ring s) => Value.algebra (.poly s (Polynomials.generator s.names.length i))
      | .algebra (.finite (.ring s)) => Finite.wrap (.poly s (Finite.generator s i))
      | _ => .null
    result ← checked ((Runtime.writeRef (.global name) value [] result).mapError toString)
  return result

syntax (name := importCommand) "#m2_import " term " as " str : command

@[command_elab importCommand]
unsafe def elabImport : CommandElab := fun stx => do
  let original ← getEnv
  try
    let binding := (⟨stx[3]⟩ : TSyntax `str).getString
    let validName := match binding.toList, Lexer.identifierToken binding with
      | c :: cs, .ident _ => Lexer.isIdentStart c && cs.all Lexer.isIdentChar
      | _, _ => false
    unless validName do throwError "import binding must be an M2 identifier"
    let (inputExpr,encoded,value,isRing) ← liftTermElabM do
      let input ← Term.elabTerm stx[1] none
      Term.synthesizeSyntheticMVarsNoPostponing
      let input ← instantiateMVars input
      if input.hasFVar || input.hasMVar then throwError "import requires a closed Lean value"
      let type ← whnf (← inferType input)
      let encoder ← match type.getAppFn.constName? with
        | some ``CoefficientField => pure ``fieldValue
        | some ``PolynomialRing => pure ``ringValue
        | some ``RingPolynomial => pure ``polynomialValue
        | some ``IdealPresentation => pure ``idealValue
        | _ => throwError "import expects a coefficient field, polynomial ring, polynomial, or finite ideal presentation"
      let encoded ← mkAppM encoder #[input]
      let value ← evalExpr Value (mkConst ``Value) encoded
      return (input,encoded,value,encoder == ``ringValue)
    let session ← DSL.getSession
    let mut state : Runtime.State := ⟨session.env,session.heap⟩
    match value with
    | .algebra .rationals | .algebra (.finite (.field _)) =>
      let _ ← checked (readField value)
    | _ =>
      let ring ← checked ((Polynomials.callPrimitive .ring value).mapError toString)
      state := { state with heap := ← reserveRing session ring }
      if isRing then state ← publishRingVariables ring state
    let ref := (Lexical.Resolver.mk session.scope [] []).lookup binding
    state ← checked ((Runtime.writeRef ref value [session.fileFrame] state).mapError toString)
    -- The evaluated value is only a candidate. Publish a kernel-checked encoding
    -- equality before committing it to the session or its immutable exports.
    let root := (← getEnv).mainModule ++ `M2Imports ++ Name.mkSimple s!"i{session.nextInput}"
    liftTermElabM do
      let type ← inferType inputExpr
      addAndCompile (.defnDecl {
        name := root ++ `source, levelParams := [], type, value := inputExpr,
        hints := .regular 0, safety := .safe })
      let rhs := valueExpr value
      let eqType ← mkEq encoded rhs
      let proof ← Term.elabTerm (← `(by decide +kernel)) (some eqType)
      Term.synthesizeSyntheticMVarsNoPostponing
      addDecl (.thmDecl {
        name := root ++ `encoding_eq, levelParams := [], type := eqType,
        value := ← instantiateMVars proof })
    let after : Session := { session with
      env := state.env, heap := state.heap,
      nextInput := session.nextInput + 1 }
    DefinitionExposure.record .empty session after
    modifyEnv fun env => DSL.sessionExt.setState env after
    for hook in ← DSL.inputHooks.get do hook session after
  catch error =>
    setEnv original
    throw error

end Macaulean.M2.Verification.MathematicalImport
