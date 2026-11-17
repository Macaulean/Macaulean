import Std

/-! Byte spellings and immutable parse profiles, independent of symbols and actors.
This is a design-first prototype for our language, not native-D conformance.
The byte lexer/Pratt parser and located source-link proof remain DESIGN-PARSE.
-/
namespace Macaulean.Language.Design

inductive IdKind where
  | word | profile | symbol | namespaceId | scope | activation
  deriving DecidableEq, Repr
structure Id (kind : IdKind) where
  index : Nat
  deriving DecidableEq, BEq, Repr, Inhabited
abbrev WordId := Id .word
abbrev ProfileId := Id .profile
abbrev SymbolId := Id .symbol
abbrev NamespaceId := Id .namespaceId
abbrev ScopeId := Id .scope
abbrev ActivationId := Id .activation
abbrev Bytes := List UInt8
abbrev WordKey := Bytes
def wordKey (s : String) : WordKey := s.toUTF8.data.toList

inductive QuotePolicy where
  | ordinary | currentLocal | global | threadGlobal
  deriving DecidableEq, BEq, Repr, Inhabited
inductive LeadingAction where
  | atom | reject | prefix | optionalPrefix | delimiter | ifForm | whileForm
  | forForm | tryForm | catchForm | newForm | quote (policy : QuotePolicy)
  deriving DecidableEq, BEq, Repr, Inhabited
inductive TrailingAction where
  | adjacent | reject | binary | optionalBinary | postfix | arrow
  deriving DecidableEq, BEq, Repr, Inhabited
structure ParseProfile where
  leftBP : Int
  rightBP : Int
  prefixBP : Int
  leading : LeadingAction
  trailing : TrailingAction
  deriving DecidableEq, BEq, Repr, Inhabited

def genericProfile : ParseProfile := ⟨65, 0, 0, .atom, .adjacent⟩
structure WordInfo where
  spelling : WordKey
  profile : ProfileId
  deriving DecidableEq, BEq, Repr, Inhabited
structure WordRegistry where
  profiles : List ParseProfile := [genericProfile]
  words : List WordInfo := []
  deriving DecidableEq, BEq, Repr, Inhabited

def WordRegistry.find (w : WordRegistry) (key : WordKey) : Option WordId :=
  (w.words.findIdx? (fun info => info.spelling == key)).map (fun i => ⟨i⟩)
def WordRegistry.addProfile (w : WordRegistry) (p : ParseProfile) : ProfileId × WordRegistry :=
  (⟨w.profiles.length⟩, { w with profiles := w.profiles ++ [p] })
/-- First registration wins, including ordinary identifiers. No Symbol allocation. -/
def WordRegistry.intern (w : WordRegistry) (key : WordKey) (requested : ProfileId) :
    Except String (WordId × WordRegistry) :=
  match w.find key with
  | some id => .ok (id, w)
  | none =>
    if requested.index < w.profiles.length then
      .ok (⟨w.words.length⟩, { w with words := w.words ++ [⟨key, requested⟩] })
    else .error "unregistered parse profile"
def WordRegistry.internIdentifier (w : WordRegistry) (key : WordKey) :
    Except String (WordId × WordRegistry) := w.intern key ⟨0⟩
def WordRegistry.alias (w : WordRegistry) (key : WordKey) (original : WordId) :
    Except String (WordId × WordRegistry) := do
  let some info := w.words[original.index]? | .error "unknown source word"
  w.intern key info.profile

structure WordToken where
  word : WordId
  profile : ProfileId
  startByte : Nat
  stopByte : Nat
  followsNewline : Bool
  deriving DecidableEq, BEq, Repr, Inhabited
structure Cursor where
  source : Bytes
  offset : Nat := 0
  buffered : Option WordToken := none
  deriving Repr, Inhabited

namespace TODO
/-- Target, not an asserted theorem. -/
def FirstWins : Prop := ∀ (w : WordRegistry) (key : WordKey)
    (requested : ProfileId) (id : WordId),
  w.find key = some id → w.intern key requested = .ok (id, w)
end TODO
end Macaulean.Language.Design
