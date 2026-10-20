import Std

/-!
# Design-first lexical identities

This is the architecture developed in the design discussion, NOT an adapter to
Interpreter.Sym. It is an executable data-model prototype, not the full parser.
Our language semantics are the authority; D is design evidence, not a normative
implementation to reproduce. TODO(DESIGN-PARSE): implement the byte cursor and
Pratt actions and prove their source link. Profiles below are data, not actors.
-/
namespace Macaulean.Language.Design

inductive IdKind where
  | word | profile | symbol | namespaceId | scope | activation
  deriving DecidableEq, Repr

/-- Distinct identifier domains; equal indices in different domains are not interchangeable. -/
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

/-- The distinguished generic profile is an identity, not a structural-equality test. -/
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

/-- First registration wins, including ordinary names encountered earlier.
No namespace or Symbol is created here. No punctuation-trie extension is implied. -/
def WordRegistry.intern (w : WordRegistry) (key : WordKey) (requested : ProfileId) :
    Except String (WordId × WordRegistry) :=
  match w.find key with
  | some id => .ok (id, w)
  | none =>
    if requested.index < w.profiles.length then
      .ok (⟨w.words.length⟩, { w with words := w.words ++ [⟨key, requested⟩] })
    else .error "unregistered parse profile"

def WordRegistry.internIdentifier (w : WordRegistry) (key : WordKey) :=
  w.intern key ⟨0⟩

/-- An immutable occurrence. Binding has not happened yet. Buffered occurrences
keep their WordId/profile and byte span; namespaces are a later phase. -/
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

/-- A source-word alias requests an existing profile. Previously seen names keep
whatever profile was registered first. Binding an alias is a separate operation. -/
def WordRegistry.alias (w : WordRegistry) (key : WordKey) (original : WordId) :
    Except String (WordId × WordRegistry) := do
  let some info := w.words[original.index]? | .error "unknown source word"
  w.intern key info.profile

namespace TODO
/-- A real theorem target, not an assumed law. -/
def FirstWins : Prop := ∀ w key requested id,
  w.find key = some id → w.intern key requested = .ok (id, w)
end TODO
end Macaulean.Language.Design
