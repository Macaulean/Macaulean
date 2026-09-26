import Macaulean.Interpreter.Check
import Macaulean.Interpreter.Input
import Macaulean.Interpreter.DSL
import MacauleanTest.FunctionCases

/-!
# Lexical bindings versus keyword quotations

`local x` is supported lexical binding. Native `local +`, `local;`, and even
`local` followed by EOF are Keyword quotations, not declarations with an omitted
name. Keywords and their quotation are outside this fragment. Assert the native
behavior and the explicit frontend boundary separately; neither serialize an
opaque value and mistake its rejection for a parser failure, nor call a valid
native quote malformed.
-/
namespace Macaulean.M2.FunctionLocalReference
open Lean Elab Command

-- Preserve every earlier frontend rejection check, including the two cases
-- reclassified after native observations, and add four more keyword quotations.
example : (FunctionCases.unsupportedKeywordQuotes.all fun src => !(parse src).isOk) = true := by
  decide +kernel

run_cmd do
  for src in FunctionCases.unsupportedKeywordQuotes do
    if (Input.parse src).isOk then throwError "reader unexpectedly accepted unsupported quote {repr src}"
    if (Lean.Parser.runParserCategory (← getEnv) `m2 src).isOk then
      throwError "DSL unexpectedly accepted unsupported quote {repr src}"

-- Observe class and exact printable keyword spelling BEFORE crossing the wire.
-- The oracle receives only Boolean, never an unsupported Keyword/closure handle.
run_cmd do
  let cases := #[
    ("local", "symbol -*end of file*-"),
    ("local;", "symbol ;"),
    ("(local;)", "symbol ;"),
    ("local if", "symbol if"),
    ("local +", "symbol +")
  ]
  for (src, expected) in cases do
    let quoted := (Json.str src).compress
    let text := (Json.str expected).compress
    let probe := s!"(v := value {quoted}; toString class v == \"Keyword\" and toExternalString v == {text})"
    match ← queryM2 probe with
    | .ok (.ok (.bool true)) => pure ()
    | .ok reply => throwError "native keyword observation changed for {repr src}: {reply.toM2String}"
    | .error message => throwError "native keyword query failed: {message}"
  let src := (Json.str "f = (x,y) -> (local; x)").compress
  let probe := s!"(t := (parse {src})#0; v := value {src}; toString class v == \"FunctionClosure\" and toString(t#3#2#2#1#0) == \"LocalQuote\")"
  match ← queryM2 probe with
  | .ok (.ok (.bool true)) => pure ()
  | .ok reply => throwError "native closure containing keyword quote changed: {reply.toM2String}"
  | .error message => throwError "native keyword closure query failed: {message}"
  logInfo "FUNCTION_KEYWORD_BOUNDARIES_COMPLETE: 6 native-valid quotations explicitly outside lexical bindings"

-- An actual local binding returns a Symbol, and its cell starts at null.
-- A value's class is not inferred from a failed external-string conversion.
run_cmd do
  let probe := "(f=()->(local lexicalReferenceName); toString class f() == \"Symbol\")"
  match ← queryM2 probe with
  | .ok (.ok (.bool true)) => pure ()
  | .ok reply => throwError "native local binding did not yield a Symbol: {reply.toM2String}"
  | .error message => throwError "native local-binding query failed: {message}"

end Macaulean.M2.FunctionLocalReference
