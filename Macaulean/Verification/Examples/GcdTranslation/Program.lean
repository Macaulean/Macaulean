import Macaulean.Language.Design.Machine
import Macaulean.Interpreter.SourceFile

/-! Design-first GCD case study. The only reused interpreter utility is literal
source-file inclusion. Neither the old parser nor Term/BinOp/Runtime determines
the new design. Surface below is an explicit fixture, NOT claimed parser output.
DESIGN-PARSE and DESIGN-DSL remain required before raw-source execution is claimed.
-/
namespace Macaulean.Language.Design.Gcd
open Binding

def sourceText : String := m2_source% "../../../../Examples/GcdTranslation/gcd.m2"
def sourceBytes : Bytes := wordKey sourceText

def registerProfile (key : String) (profile : ParseProfile) : Build WordId := do
  let c ← get
  let (id, words) := c.words.addProfile profile
  put { c with words }
  intern (wordKey key) id

def install (key : String) (profile : ParseProfile) (arity : Nat) (p : Primitive) : Build WordId := do
  let word ← registerProfile key profile
  let sym ← freshGlobal ⟨0⟩ word true
  let c ← get
  put { c with bootstrapActors := ((sym, arity), p) :: c.bootstrapActors }
  return word

structure Vocabulary where
  minus : WordId
  remainder : WordId
  notEqual : WordId
  less : WordId
  deriving Repr

/-- A deliberately enumerated GCD grammar seed, NOT the complete M2 table.
Profiles control syntax; Actors are installed separately under protected Symbols. -/
def bootstrap : Build Vocabulary := do
  let c ← get
  put { c with namespaces := [{}, {}] }
  let minus ← install "-" ⟨50, 50, 50, .prefix, .binary⟩ 1 .neg
  let remainder ← install "%" ⟨60, 60, 0, .reject, .binary⟩ 2 .rem
  let notEqual ← install "!=" ⟨30, 30, 0, .reject, .binary⟩ 2 .ne
  let less ← install "<" ⟨30, 30, 30, .prefix, .binary⟩ 2 .lt
  let _ ← registerProfile "=" ⟨10, 9, 0, .reject, .binary⟩
  let _ ← registerProfile ":=" ⟨10, 9, 0, .reject, .binary⟩
  let _ ← registerProfile "->" ⟨10, 9, 0, .reject, .arrow⟩
  let _ ← registerProfile "(" ⟨65, 6, 6, .delimiter, .adjacent⟩
  let _ ← registerProfile ")" ⟨6, 0, 0, .reject, .reject⟩
  let _ ← registerProfile "," ⟨9, 9, 0, .optionalPrefix, .optionalBinary⟩
  let _ ← registerProfile ";" ⟨8, 7, 0, .reject, .optionalBinary⟩
  let _ ← registerProfile "while" ⟨0, 0, 11, .whileForm, .reject⟩
  let _ ← registerProfile "do" ⟨0, 0, 0, .reject, .reject⟩
  let _ ← registerProfile "if" ⟨0, 0, 11, .ifForm, .reject⟩
  let _ ← registerProfile "then" ⟨0, 0, 0, .reject, .reject⟩
  let _ ← registerProfile "else" ⟨0, 0, 0, .reject, .reject⟩
  let _ ← registerProfile "symbol" ⟨0, 0, 0, .quote .ordinary, .reject⟩
  let c ← get
  let some core := c.namespaces[0]? | fail "missing bootstrap namespace"
  put { c with namespaces := c.namespaces.set 0 { core with writable := false } }
  return ⟨minus, remainder, notEqual, less⟩

structure Names where
  abs : WordId
  n : WordId
  gcd : WordId
  a : WordId
  b : WordId
  r : WordId
  deriving Repr

def registerNames : Build Names := do
  return ⟨← intern (wordKey "abs"), ← intern (wordKey "n"),
    ← intern (wordKey "gcdEuclid"), ← intern (wordKey "a"),
    ← intern (wordKey "b"), ← intern (wordKey "r")⟩

/-- Retains WordIds. `%` has not become a primitive instruction here. -/
def surfaceFixture (w : Vocabulary) (n : Names) : Surface :=
  .seq
    (.set false n.abs (.lambda [n.n]
      (.ifElse (.binary w.less (.read n.n) (.int 0))
        (.unary w.minus (.read n.n)) (.read n.n))))
    (.set false n.gcd (.lambda [n.a, n.b]
      (.seq (.set false n.a (.call (.read n.abs) [.read n.a]))
        (.seq (.set false n.b (.call (.read n.abs) [.read n.b]))
          (.seq
            (.whileDo (.binary w.notEqual (.read n.b) (.int 0))
              (.seq (.set true n.r (.binary w.remainder (.read n.a) (.read n.b)))
                (.seq (.set false n.a (.read n.b)) (.set false n.b (.read n.r)))))
            (.read n.a))))))

structure Artifact where
  catalog : Catalog
  vocabulary : Vocabulary
  names : Names
  surface : Surface
  bound : Bound
  code : Code
  functionRef : Ref
  scope : ScopeId
  parameters : List SymbolId
  layout : List SymbolId
  deriving Repr

def build : Result Catalog Artifact := (do
  let vocabulary ← bootstrap
  let names ← registerNames
  let surface := surfaceFixture vocabulary names
  let (bound, code) ← compile 256 [⟨0⟩] surface
  let c ← get
  let id ← global names.gcd false
  let ref ← lift (address c [⟨0⟩] id)
  let .seq _ (.set _ (.lambda scope ps layout _)) := bound
    | fail "GCD fixture did not bind to a function"
  return { catalog := c, vocabulary, names, surface, bound, code,
    functionRef := ref, scope, parameters := ps, layout }) {}

def boundInvocation (artifact : Artifact) (a b : Int) : Bound :=
  .seq artifact.bound (.call (.read artifact.functionRef.symbol) [.int a, .int b])
def codeInvocation (artifact : Artifact) (a b : Int) : Code :=
  .seq artifact.code (.call (.read artifact.functionRef) [.int a, .int b])

/-- Actual designed closure allocation and call, including actual while execution.
This accepts the structured fixture; it does not falsely claim to parse sourceText. -/
def run (fuel : Nat) (a b : Int) : Except String (Result Machine.State Value) :=
  match build with
  | .error e _ => .error e
  | .exhausted _ => .error "binding resource exhausted"
  | .done artifact _ => .ok (Machine.eval fuel (codeInvocation artifact a b)
      (some ⟨0⟩) (Machine.initial artifact.catalog))

/-- Observation for concrete tests only; keep the full Result in preservation claims. -/
def answer (fuel : Nat) (a b : Int) : Except String Int := do
  match ← run fuel a b with
  | .done (.int z) _ => return z
  | .done _ _ => .error "non-integer result"
  | .error e _ => .error e
  | .exhausted _ => .error "resource exhausted"

end Macaulean.Language.Design.Gcd
