import Macaulean.Language.Design.IR

/-! Design-first binding. Words do not allocate Symbols. Namespaces and lexical
scopes select declarations; lowering subsequently computes direct locations.
Failures retain reached catalog state. This is our subset's policy, not D emulation.
-/
namespace Macaulean.Language.Design
namespace Binding

abbrev Build (α : Type) := Catalog → Result Catalog α
instance : Monad Build where
  pure a := fun s => .done a s
  bind m f := fun s => (m s).bind (fun a s' => f a s')
def get : Build Catalog := fun s => .done s s
def put (s : Catalog) : Build Unit := fun _ => .done () s
def fail (message : String) : Build α := fun s => .error message s
def lift (r : Except String α) : Build α := fun s =>
  match r with | .ok a => .done a s | .error e => .error e s

def intern (key : WordKey) (profile : ProfileId := ⟨0⟩) : Build WordId := do
  let c ← get
  let (id, words) ← lift (c.words.intern key profile)
  put { c with words }
  return id

def validWord (word : WordId) : Build Unit := do
  let c ← get
  if word.index < c.words.words.length then pure () else fail "invalid WordId"

def globalLookup (c : Catalog) (word : WordId) : List NamespaceId → Option SymbolId
  | [] => none
  | id :: ids =>
    match c.namespaces[id.index]? with
    | none => none
    | some ns => match ns.entries.lookup word with
      | some sym => some sym | none => globalLookup c word ids

def localLookup (c : Catalog) (word : WordId) : List ScopeId → Option SymbolId
  | [] => none
  | id :: ids =>
    match c.scopes[id.index]? with
    | none => none
    | some sc => match sc.entries.lookup word with
      | some sym => some sym | none => localLookup c word ids

def writableNamespace (c : Catalog) : List NamespaceId → Option NamespaceId
  | [] => none
  | id :: ids => match c.namespaces[id.index]? with
    | none => none
    | some ns => if ns.writable then some id else writableNamespace c ids

/-- Allocation in one explicitly selected dictionary, not interning by name globally. -/
def freshGlobal (namespaceId : NamespaceId) (word : WordId)
    (isProtected : Bool := false) : Build SymbolId := do
  validWord word
  let c ← get
  let some ns := c.namespaces[namespaceId.index]? | fail "invalid namespace"
  if !ns.writable then fail "namespace is protected" else do
    let id : SymbolId := ⟨c.symbols.length⟩
    let info : SymbolInfo := ⟨word, .global namespaceId c.globalSeeds.length, isProtected⟩
    put { c with
      namespaces := c.namespaces.set namespaceId.index
        { ns with entries := (word, id) :: ns.entries }
      symbols := c.symbols ++ [info]
      globalSeeds := c.globalSeeds ++ [(id, .symbol id none)] }
    return id

def global (word : WordId) (create : Bool) : Build SymbolId := do
  validWord word
  let c ← get
  match globalLookup c word c.searchPath with
  | some id => pure id
  | none =>
    if !create then fail "unbound operator" else do
      let some ns := writableNamespace c c.searchPath | fail "no creation namespace"
      freshGlobal ns word

def ordinary (path : List ScopeId) (word : WordId) (create : Bool := true) : Build SymbolId := do
  validWord word
  let c ← get
  match localLookup c word path with
  | some id => pure id
  | none => global word create

def freshScope : Build ScopeId := do
  let c ← get
  let id : ScopeId := ⟨c.scopes.length⟩
  put { c with scopes := c.scopes ++ [{}] }
  return id

def declare (scope : ScopeId) (word : WordId) : Build SymbolId := do
  validWord word
  let c ← get
  let some sc := c.scopes[scope.index]? | fail "invalid lexical scope"
  let id : SymbolId := ⟨c.symbols.length⟩
  let info : SymbolInfo := ⟨word, .lexical scope sc.layout.length, false⟩
  put { c with
    symbols := c.symbols ++ [info]
    scopes := c.scopes.set scope.index
      { entries := (word, id) :: sc.entries, layout := sc.layout ++ [id] } }
  return id

def current (path : List ScopeId) : Build ScopeId :=
  match path with | [] => fail "missing current scope" | id :: _ => pure id

def quoted (path : List ScopeId) (policy : QuotePolicy) (word : WordId) : Build SymbolId := do
  match policy with
  | .ordinary => ordinary path word
  | .global => global word true
  | .currentLocal =>
    let sc ← current path
    let c ← get
    match localLookup c word [sc] with
    | some id => pure id
    | none => declare sc word
  | .threadGlobal => fail "unsupported design capability: thread-global storage"

/-- Namespace aliasing and word-profile copying are distinct updates. This subset
accepts global aliases only. Earlier registration survives even a duplicate error. -/
def alias (nsId : NamespaceId) (key : WordKey) (symbol : SymbolId) : Build WordId := do
  let c ← get
  let some info := c.symbols[symbol.index]? | fail "unknown symbol"
  let .global _ _ := info.home | fail "local aliases require activation-qualified dictionaries"
  let some ns := c.namespaces[nsId.index]? | fail "unknown namespace"
  if !ns.writable then fail "namespace is protected" else do
    let (word, words) ← lift (c.words.alias key info.canonicalWord)
    put { c with words }
    if (ns.entries.lookup word).isSome then fail "duplicate namespace entry" else do
      put { c with words, namespaces := c.namespaces.set nsId.index
        { ns with entries := (word, symbol) :: ns.entries } }
      return word

/-- Resolution happens once, source-order, including unexecuted lambda bodies.
:= allocates before its RHS. A while body uses the same lexical scope. -/
def resolve : Nat → List ScopeId → Surface → Build Bound
  | 0, _, _ => fun c => .exhausted c
  | fuel + 1, path, tree => do
    match tree with
    | .int n => return .int n
    | .read w => return .read (← ordinary path w)
    | .quote p w => return .quote (← quoted path p w)
    | .unary w a =>
      let op ← ordinary path w false
      return .unary ⟨w, op⟩ (← resolve fuel path a)
    | .binary w a b =>
      let a ← resolve fuel path a
      let op ← ordinary path w false
      let b ← resolve fuel path b
      return .binary ⟨w, op⟩ a b
    | .set fresh w rhs =>
      let id ← if fresh then declare (← current path) w else ordinary path w
      return .set id (← resolve fuel path rhs)
    | .seq a b => return .seq (← resolve fuel path a) (← resolve fuel path b)
    | .ifElse a b d =>
      return .ifElse (← resolve fuel path a) (← resolve fuel path b) (← resolve fuel path d)
    | .whileDo test body =>
      return .whileDo (← resolve fuel path test) (← resolve fuel path body)
    | .lambda ps body =>
      if ps.eraseDups.length != ps.length then fail "duplicate parameters" else do
        let sc ← freshScope
        let parameters ← ps.mapM (declare sc)
        let body ← resolve fuel (sc :: path) body
        let c ← get
        let some layout := c.scopes[sc.index]? | fail "missing finalized layout"
        return .lambda sc parameters layout.layout body
    | .call f args =>
      let f ← resolve fuel path f
      let args ← args.mapM (resolve fuel path)
      return .call f args

def address (c : Catalog) (path : List ScopeId) (symbol : SymbolId) : Except String Ref := do
  let some info := c.symbols[symbol.index]? | .error "invalid SymbolId"
  match info.home with
  | .global _ slot => return ⟨symbol, .global slot⟩
  | .lexical scope slot =>
    let some depth := path.findIdx? (fun id => id == scope) | .error "symbol is outside lexical path"
    return ⟨symbol, .lexical depth slot⟩

/-- No arithmetic specialization: selected SymbolId and original WordId survive. -/
def lower : Nat → Catalog → List ScopeId → Bound → Except String Code
  | 0, _, _, _ => .error "lowering budget exhausted"
  | fuel + 1, c, path, tree => do
    match tree with
    | .int n => return .int n
    | .read s => return .read (← address c path s)
    | .quote s => return .quote (← address c path s)
    | .unary op a => return .unary op (← lower fuel c path a)
    | .binary op a b => return .binary op (← lower fuel c path a) (← lower fuel c path b)
    | .set s a => return .set (← address c path s) (← lower fuel c path a)
    | .seq a b => return .seq (← lower fuel c path a) (← lower fuel c path b)
    | .ifElse a b d => return .ifElse (← lower fuel c path a)
        (← lower fuel c path b) (← lower fuel c path d)
    | .whileDo a b => return .whileDo (← lower fuel c path a) (← lower fuel c path b)
    | .lambda sc ps slots body =>
      let some scope := c.scopes[sc.index]? | .error "unknown function scope"
      if slots != scope.layout || ps != slots.take ps.length || ps.eraseDups != ps then
        .error "invalid function layout"
      else return .lambda sc ps slots (← lower fuel c (sc :: path) body)
    | .call f args => return .call (← lower fuel c path f) (← args.mapM (lower fuel c path))

def compile (fuel : Nat) (path : List ScopeId) (tree : Surface) : Build (Bound × Code) := do
  let bound ← resolve fuel path tree
  let c ← get
  let code ← lift (lower fuel c path bound)
  return (bound, code)

end Binding
end Macaulean.Language.Design
