import Lean

/-!
# M2 numeric lookahead at the language boundary

Lean's Pratt dispatcher lexes a leading token before trying even unindexed
custom parsers. Its numeral lexer rejects `0_R` (an M2 promotion) as a malformed
Lean numeral. The M2 reader itself accepts this input correctly.

This pure dispatcher adapter retries the category's existing unindexed parsers
only for a failed numeric lookahead. It is active for the `m2` category, and for
`command` only while the scoped M2 command parser is installed. It leaves Lean
terms, tactics, and commands outside that scope unchanged. The same registered
M2 reader still builds the syntax: there is no second grammar or string rewrite.

The initializer registers a parser adapter in Lean's existing parser registry;
it does not allocate or store an M2 session, heap, or mutable interpreter state.
-/
namespace Macaulean.M2.ParserPrelude
open Lean Lean.Parser

private def commandActive (env : Environment) : Bool :=
  (getParserCategory? env `command).any fun cat => cat.kinds.contains `M2.inputCommand

def numericFallback (previous : CategoryParserFn) : CategoryParserFn := fun name ctx state =>
  let result := previous name ctx state
  if state.hasError || !result.hasError || !(ctx.get state.pos).isDigit then result
  else if name != `m2 && !(name == `command && commandActive ctx.env) then result
  else
    match getParserCategory? ctx.env name with
    | none => result
    | some cat =>
      if cat.tables.leadingParsers.isEmpty then result
      else
        let retry := longestMatchFn none cat.tables.leadingParsers ctx state
        if retry.hasError then result else retry

initialize
  let previous ← Lean.Parser.categoryParserFnRef.get
  Lean.Parser.categoryParserFnRef.set (numericFallback previous)

end Macaulean.M2.ParserPrelude
