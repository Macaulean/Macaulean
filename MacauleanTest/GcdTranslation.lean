import Macaulean.Verification.Examples.GcdTranslation.Semantics

/-! Concrete design-prototype checks, not universal proofs. No native M2 oracle.
No legacy Interpreter.Term, BinOp, Lexical.Code, Runtime or Plan adapter is used.
All checks below are supplied for Lean execution; consult VALIDATION.md for status.
-/
namespace Macaulean.Language.Design.Gcd.Tests
open Binding
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def frameLayout : Bool := match build with
  | .done a _ =>
    a.layout.length == 3 && a.parameters == a.layout.take 2 &&
    match a.catalog.scopes[a.scope.index]? with
    | none => false
    | some sc =>
      [(a.names.a, 0), (a.names.b, 1), (a.names.r, 2)].all fun (word, slot) =>
        match sc.entries.lookup word with
        | none => false
        | some sym => address a.catalog [a.scope, ⟨0⟩] sym == .ok ⟨sym, .lexical 0 slot⟩
  | _ => false

#guard frameLayout
#guard answer 256 1071 462 = .ok 21
#guard answer 256 (-1071) 462 = .ok 21
#guard answer 256 1071 (-462) = .ok 21
#guard answer 256 (-1071) (-462) = .ok 21
#guard answer 256 0 0 = .ok 0
#guard answer 256 0 37 = .ok 37
#guard answer 256 37 0 = .ok 37
#guard answer 256 55 34 = .ok 1
#guard answer 0 1071 462 = .error "resource exhausted"

/-- Root + gcd call + two abs calls. Loop iterations do not allocate r again. -/
def noPerIterationAllocation : Bool := match run 256 1071 462 with
  | .ok (.done (.int 21) state) =>
    state.frames.length == 4 &&
    (state.frames[1]?).map Machine.Frame.values == some [.int 21, .int 0, .int 0]
  | _ => false
#guard noPerIterationAllocation

def firstWins : Bool :=
  let registry : WordRegistry := {}
  match registry.internIdentifier (wordKey "seen") with
  | .error _ => false
  | .ok (id, r) =>
    let (profile, r) := r.addProfile ⟨60, 60, 0, .reject, .binary⟩
    match r.intern (wordKey "seen") profile with
    | .ok (id', r') => id == id' && (r'.words[id.index]?).map WordInfo.profile == some ⟨0⟩
    | _ => false
#guard firstWins

def unknownAndReified : Bool :=
  match (do
    let w ← intern (wordKey "x")
    let sym ← ordinary [⟨0⟩] w
    let c ← get
    let ref ← lift (address c [⟨0⟩] sym)
    return (sym, ref)) ({} : Catalog) with
  | .done (sym, ref) c =>
    let s := Machine.initial c
    Machine.read ref (some ⟨0⟩) s == .ok (.symbol sym none) &&
    match Machine.write ref (.int 7) (some ⟨0⟩) s with
    | .error _ => false
    | .ok s' => Machine.read ref (some ⟨0⟩) s' == .ok (.int 7) &&
        Machine.reify ref (some ⟨0⟩) s' == .ok (.symbol sym none)
  | _ => false
#guard unknownAndReified

/-- Merely interning an occurrence must not allocate a variable binding. -/
def wordsAreNotSymbols : Bool :=
  match intern (wordKey "onlyLexed") ({} : Catalog) with
  | .done _ c => c.words.words.length == 1 && c.symbols.isEmpty && c.globalSeeds.isEmpty
  | _ => false
#guard wordsAreNotSymbols

/-- Binding an uncalled lambda still creates its unknown global. -/
def bindUncalled : Bool :=
  match (do
    let w ← intern (wordKey "latent")
    let _ ← resolve 32 [⟨0⟩] (.lambda [] (.read w))
    let c ← get
    return (globalLookup c w c.searchPath).isSome) ({} : Catalog) with
  | .done b _ => b | _ => false
#guard bindUncalled

/-- A copied profile is not a bound operator. An actual namespace alias preserves
operator SymbolId even though source WordId changes. -/
def operatorAlias : Bool :=
  match (do
    let v ← bootstrap
    let sym ← global v.remainder false
    let aliasWord ← alias ⟨1⟩ (wordKey "remainderAlias") sym
    let (b, k) ← compile 64 [⟨0⟩] (.binary aliasWord (.int 11) (.int 4))
    return (v.remainder, aliasWord, sym, b, k)) ({} : Catalog) with
  | .done (original, aliasWord, sym, .binary op _ _, code) c =>
    original != aliasWord && op.sourceWord == aliasWord && op.symbol == sym &&
    match Machine.eval 32 code (some ⟨0⟩) (Machine.initial c) with
    | .done (.int 3) _ => true | _ => false
  | _ => false
#guard operatorAlias

def profileOnlyDoesNotBind : Bool :=
  match (do
    let v ← bootstrap
    let c ← get
    let (word, words) ← lift (c.words.alias (wordKey "profileOnly") v.remainder)
    put { c with words }
    resolve 32 [⟨0⟩] (.binary word (.int 11) (.int 4))) ({} : Catalog) with
  | .error "unbound operator" _ => true | _ => false
#guard profileOnlyDoesNotBind

def namespaceShadow : Bool :=
  match (do
    let word ← intern (wordKey "x")
    let first ← freshGlobal ⟨1⟩ word
    let c ← get
    put { c with namespaces := c.namespaces ++ [{}], searchPath := [⟨2⟩, ⟨1⟩, ⟨0⟩] }
    let second ← freshGlobal ⟨2⟩ word
    let selected ← ordinary [⟨0⟩] word
    return first != second && selected == second) ({} : Catalog) with
  | .done b _ => b | _ => false
#guard namespaceShadow

def declarationHistory : Bool :=
  match (do
    let word ← intern (wordKey "x")
    let first ← declare ⟨0⟩ word
    let second ← declare ⟨0⟩ word
    let selected ← ordinary [⟨0⟩] word
    let c ← get
    let a ← lift (address c [⟨0⟩] first)
    let b ← lift (address c [⟨0⟩] second)
    return first != second && selected == second &&
      a.location == .lexical 0 0 && b.location == .lexical 0 1 &&
      (c.scopes[0]?.getD {}).entries.length == 2) ({} : Catalog) with
  | .done b _ => b | _ => false
#guard declarationHistory

/-- Same lexical declaration, two live activations: first-class Symbols differ. -/
def activationIdentity : Bool :=
  match (do
    let x ← intern (wordKey "x")
    compile 64 [⟨0⟩] (.lambda [x] (.quote .ordinary x))) ({} : Catalog) with
  | .done (_, code) c =>
    match Machine.eval 32 code (some ⟨0⟩) (Machine.initial c) with
    | .done fn s => match Machine.call 32 fn [.int 1] s with
      | .done (.symbol d1 a1) s1 => match Machine.call 32 fn [.int 2] s1 with
        | .done (.symbol d2 a2) _ => d1 == d2 && a1 != a2
        | _ => false
      | _ => false
    | _ => false
  | _ => false
#guard activationIdentity

def errorKeepsWrites : Bool :=
  match (do
    let x ← intern (wordKey "x")
    let id ← declare ⟨0⟩ x
    let c ← get
    let ref ← lift (address c [⟨0⟩] id)
    return ref) ({} : Catalog) with
  | .done ref c =>
    let code : Code := .seq (.set ref (.int 7)) (.call (.int 0) [])
    match Machine.eval 32 code (some ⟨0⟩) (Machine.initial c) with
    | .error "value is not callable" after => Machine.read ref (some ⟨0⟩) after == .ok (.int 7)
    | _ => false
  | _ => false
#guard errorKeepsWrites

-- Declarations of obligations, not assertions that these types are inhabited.
#check Macaulean.Language.Design.TODO.FirstWins
#check Macaulean.Language.Design.TODO.LowerForward
#check Macaulean.Language.Design.TODO.LowerBackward
#check Gcd.TODO.Translation
#check Gcd.TODO.Terminates
#check Gcd.TODO.Obligations

end Macaulean.Language.Design.Gcd.Tests
