import Lean
import Macaulean.Interpreter.Input
import Macaulean.Interpreter.Session

/-! # Bare, scoped M2 commands with structured syntax and pure lexical sessions -/
declare_syntax_cat m2
register_option m2.maxDepth : Nat := {
  defValue := 4096
  descr := "Maximum M2 evaluation depth; exhaustion is an error and rolls back the input." }

namespace Macaulean.M2.DSL
open Lean
private def sourceInfo (c : Lean.Parser.InputContext) (start stop : String.Pos.Raw) : SourceInfo :=
  .original (c.substring start start) start (c.substring stop stop) stop
private def tokenSyntax (c : Lean.Parser.InputContext) (base : Nat)
    (tokens : Array Input.LocatedToken) (index : Nat) : Syntax :=
  let span := (tokens[index]!).span
  let start : String.Pos.Raw := ⟨base + span.start⟩
  let stop : String.Pos.Raw := ⟨base + span.stop⟩
  .atom (sourceInfo c start stop) (c.extract start stop)

def treeSyntax (c : Lean.Parser.InputContext) (base : Nat)
    (tokens : Array Input.LocatedToken) : Parser.Tree → Syntax
  | .num i _ => .node .none `Macaulean.M2.DSL.num
      #[.node .none numLitKind #[tokenSyntax c base tokens i]]
  | .var i x =>
    let span := (tokens[i]!).span
    let start : String.Pos.Raw := ⟨base + span.start⟩
    let stop : String.Pos.Raw := ⟨base + span.stop⟩
    .node .none `Macaulean.M2.DSL.var
      #[.ident (sourceInfo c start stop) (c.substring start stop) (Name.mkSimple x) []]
  | .paren i j a => .node .none `Macaulean.M2.DSL.paren
      #[tokenSyntax c base tokens i, treeSyntax c base tokens a, tokenSyntax c base tokens j]
  | .listBody i j a => .node .none `Macaulean.M2.DSL.listBody
      #[tokenSyntax c base tokens i, treeSyntax c base tokens a, tokenSyntax c base tokens j]
  | .emptyList i j => .node .none `Macaulean.M2.DSL.emptyList
      #[tokenSyntax c base tokens i, tokenSyntax c base tokens j]
  | .emptySequence i j => .node .none `Macaulean.M2.DSL.emptySequence
      #[tokenSyntax c base tokens i, tokenSyntax c base tokens j]
  | .missing i =>
    let pos : String.Pos.Raw := ⟨base + (tokens[i]!).span.start⟩
    .node (sourceInfo c pos pos) `Macaulean.M2.DSL.missing #[]
  | .comma i a b => .node .none `Macaulean.M2.DSL.comma
      #[treeSyntax c base tokens a, tokenSyntax c base tokens i, treeSyntax c base tokens b]
  | .unop i _ a => .node .none `Macaulean.M2.DSL.unop
      #[tokenSyntax c base tokens i, treeSyntax c base tokens a]
  | .binop i _ a b => .node .none `Macaulean.M2.DSL.binop
      #[treeSyntax c base tokens a, tokenSyntax c base tokens i, treeSyntax c base tokens b]
  | .logic i _ a b => .node .none `Macaulean.M2.DSL.logic
      #[treeSyntax c base tokens a, tokenSyntax c base tokens i, treeSyntax c base tokens b]
  | .assign i _ a b => .node .none `Macaulean.M2.DSL.assign
      #[treeSyntax c base tokens a, tokenSyntax c base tokens i, treeSyntax c base tokens b]
  | .indexAssign i a b => .node .none `Macaulean.M2.DSL.indexAssign
      #[treeSyntax c base tokens a, tokenSyntax c base tokens i, treeSyntax c base tokens b]
  | .ifThen i j condition yes => .node .none `Macaulean.M2.DSL.ifThen
      #[tokenSyntax c base tokens i, treeSyntax c base tokens condition,
        tokenSyntax c base tokens j, treeSyntax c base tokens yes]
  | .ifElse i j k condition yes no => .node .none `Macaulean.M2.DSL.ifElse
      #[tokenSyntax c base tokens i, treeSyntax c base tokens condition,
        tokenSyntax c base tokens j, treeSyntax c base tokens yes,
        tokenSyntax c base tokens k, treeSyntax c base tokens no]
  | .seq i a b => .node .none `Macaulean.M2.DSL.seq
      #[treeSyntax c base tokens a, tokenSyntax c base tokens i, treeSyntax c base tokens b]
  | .discard i a => .node .none `Macaulean.M2.DSL.discard
      #[treeSyntax c base tokens a, tokenSyntax c base tokens i]
  | .lambda i _ a b => .node .none `Macaulean.M2.DSL.lambda
      #[treeSyntax c base tokens a, tokenSyntax c base tokens i, treeSyntax c base tokens b]
  | .apply f a => .node .none `Macaulean.M2.DSL.apply
      #[treeSyntax c base tokens f, treeSyntax c base tokens a]
  | .localAssign i _ a b => .node .none `Macaulean.M2.DSL.localAssign
      #[treeSyntax c base tokens a, tokenSyntax c base tokens i, treeSyntax c base tokens b]
  | .assignMany i _ _ a b => .node .none `Macaulean.M2.DSL.assignMany
      #[treeSyntax c base tokens a, tokenSyntax c base tokens i, treeSyntax c base tokens b]
  | .localSymbol i _ a => .node .none `Macaulean.M2.DSL.localSymbol
      #[tokenSyntax c base tokens i, treeSyntax c base tokens a]
  | .returnTerm i a => .node .none `Macaulean.M2.DSL.returnTerm
      #[tokenSyntax c base tokens i, treeSyntax c base tokens a]

/-- Grammar decisions belong to the shared Pratt parser, not this editor adapter. -/
def reader : Lean.Parser.Parser where
  info := { firstTokens := .unknown }
  fn := fun c s =>
    let base := s.pos.byteIdx
    match Input.scan (c.extract s.pos c.endPos) with
    | .error error => s.mkError error
    | .ok tokens => match Parser.parseInputTree (tokens.located.toList.map (·.token)) with
      | .error error => (s.setPos ⟨base + tokens.stop⟩).mkError error
      | .ok tree =>
        let body := treeSyntax c.toInputContext base tokens.located tree
        let silent := if tokens.silent then
            let start : String.Pos.Raw := ⟨base + tokens.stop - 1⟩
            let stop : String.Pos.Raw := ⟨base + tokens.stop⟩
            Syntax.atom (sourceInfo c.toInputContext start stop) ";"
          else Syntax.node .none nullKind #[]
        let inputStop := if tokens.silent then tokens.stop else (tokens.located[tree.bounds.2]!).span.stop
        let info := sourceInfo c.toInputContext ⟨base⟩ ⟨base + inputStop⟩
        let input := Syntax.node info `Macaulean.M2.DSL.input #[body, silent]
        Lean.Parser.whitespace c ((s.setPos ⟨base + tokens.stop⟩).pushSyntax input)
@[combinator_parenthesizer reader]
def readerParenthesizer : Lean.PrettyPrinter.Parenthesizer := Lean.Syntax.MonadTraverser.goLeft
@[combinator_formatter reader]
def readerFormatter : Lean.PrettyPrinter.Formatter := do
  let stx ← Lean.Syntax.MonadTraverser.getCur
  let some source := stx.getSubstring? (withLeading := false) (withTrailing := false)
    | throwError "M2 syntax has no original source range"
  Lean.PrettyPrinter.Formatter.push (.text source.toString)
  Lean.PrettyPrinter.Formatter.resetLeadWord
  Lean.Syntax.MonadTraverser.goLeft
syntax (name := inputSyntax) reader : m2

private def binOp? : String → Option BinOp
  | "+" => some .add | "-" => some .sub | "*" => some .mul | "/" => some .div
  | "//" => some .quot | "%" => some .rem | "^" => some .pow
  | "==" => some .eq | "!=" => some .ne | "<" => some .lt | "<=" => some .le
  | ">" => some .gt | ">=" => some .ge | ".." => some .range | "..<" => some .rangeExclusive
  | "#" => some .index | "#?" => some .hasIndex | "|" => some .concat
  | ":" => some .repeat | "@@" => some .compose | _ => none

private def identifier? (stx : Syntax) : Option String :=
  if stx.getKind == `Macaulean.M2.DSL.var then
    match stx[0] with | .ident _ raw _ _ => some raw.toString | _ => none
  else none
private def parameterNames : Nat → Syntax → Option (List String)
  | 0, _ => none
  | n + 1, stx =>
    if stx.getKind == `Macaulean.M2.DSL.comma then do
      let xs ← parameterNames n stx[0]
      let x ← identifier? stx[2]
      return xs ++ [x]
    else (fun x => [x]) <$> identifier? stx
private def parameters (fuel : Nat) (stx : Syntax) : Except String Parameters := do
  let p ← if let some x := identifier? stx then .ok (.variadic x)
    else if stx.getKind == `Macaulean.M2.DSL.emptySequence ||
        stx.getKind == `Macaulean.M2.DSL.emptyList then .ok (.fixed [])
    else if stx.getKind == `Macaulean.M2.DSL.paren ||
        stx.getKind == `Macaulean.M2.DSL.listBody then
      match parameterNames fuel stx[1] with
      | some xs => .ok (.fixed xs) | none => .error "invalid fixed parameters"
    else .error "invalid function parameters"
  if p.names.eraseDups.length != p.names.length then .error "duplicate function parameter"
  else return p

/-- Lower structured syntax directly, including source-significant parameter delimiters. -/
def lowerTree : Nat → Syntax → Except String Term
  | 0, _ => .error "M2 syntax lowering ran out of fuel"
  | fuel + 1, stx => do
    match stx.getKind with
    | `Macaulean.M2.DSL.num =>
      let raw := stx[0][0].getAtomVal.toList
      let (n, rest) := Lexer.number raw
      if raw.head?.any Char.isDigit && rest.isEmpty then return .int n
      else .error "invalid M2 integer literal"
    | `Macaulean.M2.DSL.var =>
      let some x := identifier? stx | .error "invalid M2 identifier"
      return .var x
    | `Macaulean.M2.DSL.paren => lowerTree fuel stx[1]
    | `Macaulean.M2.DSL.emptyList => return .listLit []
    | `Macaulean.M2.DSL.emptySequence => return .sequence []
    | `Macaulean.M2.DSL.missing => return .empty
    | `Macaulean.M2.DSL.listBody =>
      return Term.inBraces (stx[1].getKind == `Macaulean.M2.DSL.comma) (← lowerTree fuel stx[1])
    | `Macaulean.M2.DSL.comma =>
      return Term.comma (stx[0].getKind == `Macaulean.M2.DSL.comma)
        (← lowerTree fuel stx[0]) (← lowerTree fuel stx[2])
    | `Macaulean.M2.DSL.unop =>
      let op ← match stx[0].getAtomVal with
        | "-" => .ok UnOp.neg | "+" => .ok UnOp.pos | "not" => .ok UnOp.notOp
        | "#" => .ok UnOp.length | _ => .error "invalid M2 prefix operator"
      return .unop op (← lowerTree fuel stx[1])
    | `Macaulean.M2.DSL.binop =>
      let some op := binOp? stx[1].getAtomVal | .error "invalid M2 binary operator"
      return .binop op (← lowerTree fuel stx[0]) (← lowerTree fuel stx[2])
    | `Macaulean.M2.DSL.logic =>
      let op ← match stx[1].getAtomVal with
        | "and" => .ok LogicOp.andOp | "or" => .ok LogicOp.orOp | _ => .error "invalid M2 Boolean operator"
      return .logic op (← lowerTree fuel stx[0]) (← lowerTree fuel stx[2])
    | `Macaulean.M2.DSL.ifThen => return .ifThen (← lowerTree fuel stx[1]) (← lowerTree fuel stx[3])
    | `Macaulean.M2.DSL.ifElse =>
      return .ifElse (← lowerTree fuel stx[1]) (← lowerTree fuel stx[3]) (← lowerTree fuel stx[5])
    | `Macaulean.M2.DSL.seq => return .seq (← lowerTree fuel stx[0]) (← lowerTree fuel stx[2])
    | `Macaulean.M2.DSL.discard => return .seq (← lowerTree fuel stx[0]) .empty
    | `Macaulean.M2.DSL.assign =>
      let .var name ← lowerTree fuel stx[0] | .error "left side of '=' must be a variable"
      return .assign name (← lowerTree fuel stx[2])
    | `Macaulean.M2.DSL.indexAssign =>
      let .binop .index a i ← lowerTree fuel stx[0] | .error "expected an indexed collection"
      return .indexAssign a i (← lowerTree fuel stx[2])
    | `Macaulean.M2.DSL.lambda =>
      return .lambda (← parameters fuel stx[0]) (← lowerTree fuel stx[2])
    | `Macaulean.M2.DSL.apply => return .apply (← lowerTree fuel stx[0]) (← lowerTree fuel stx[1])
    | `Macaulean.M2.DSL.localAssign =>
      let .var name ← lowerTree fuel stx[0] | .error "expected a local variable"
      return .localAssign name (← lowerTree fuel stx[2])
    | `Macaulean.M2.DSL.assignMany =>
      let .sequence xs ← lowerTree fuel stx[0] | .error "expected multiple assignment names"
      let some names := Term.variableNames xs | .error "invalid multiple assignment names"
      return .assignMany (stx[1].getAtomVal == ":=") names (← lowerTree fuel stx[2])
    | `Macaulean.M2.DSL.localSymbol =>
      let some x := identifier? stx[1] | .error "expected a local symbol name"
      return .localSymbol x
    | `Macaulean.M2.DSL.returnTerm => return .returnTerm (← lowerTree fuel stx[1])
    | _ => .error s!"unsupported M2 syntax node {stx.getKind}"

def lowerInput (stx : TSyntax `m2) : Except String (Term × Bool) := do
  let input := stx.raw[0]
  if input.getKind != `Macaulean.M2.DSL.input then .error "expected an M2 input"
  else
    let some source := input.getSubstring? (withLeading := false) (withTrailing := false)
      | .error "M2 syntax has no original source range"
    let term ← lowerTree (source.toString.utf8ByteSize + 1) input[0]
    return (term, input[1].getAtomVal == ";")

initialize sessionExt : EnvExtension Session ← registerEnvExtension (pure ({} : Session))
open Lean.Elab.Command

def getSession : CommandElabM Session := return sessionExt.getState (← getEnv)
def resetSession : CommandElabM Unit := modifyEnv fun env => sessionExt.setState env ({} : Session)
end Macaulean.M2.DSL
namespace M2
scoped syntax (name := inputCommand) (priority := low) m2 : command
end M2
namespace Macaulean.M2.DSL
open Lean Lean.Elab.Command
@[command_elab M2.inputCommand]
def elabInput : CommandElab := fun stx => do
  let parsed : TSyntax `m2 := ⟨stx[0]⟩
  let (term, silent) ← match lowerInput parsed with
    | .ok value => pure value | .error error => throwErrorAt stx error
  let state ← getSession
  let result := state.step term silent (m2.maxDepth.get (← getOptions))
  modifyEnv fun env => sessionExt.setState env result.session
  let body := parsed.raw[0][0]
  for warning in result.warnings do logWarningAt body warning
  match result.outcome with
  | .error error => logErrorAt body error.toM2String
  | .ok _ => if let some output := result.output then
      logInfoAt body m!"o{output.input} = {output.value.toM2String} : {output.value.className}"
end Macaulean.M2.DSL
