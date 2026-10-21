#!/usr/bin/env python3
"""Limited source-structure checks. NOT a Lean compiler, evaluator, or proof checker."""
from pathlib import Path
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
DESIGN = ROOT / "Macaulean/Language/Design"
EXAMPLE = ROOT / "Macaulean/Verification/Examples/GcdTranslation"
paths = sorted(DESIGN.glob("*.lean")) + sorted(EXAMPLE.glob("*.lean"))
paths += [ROOT / "MacauleanTest/GcdTranslation.lean", ROOT / "Examples/GcdTranslation/Worksheet.lean"]
errors = []

def check(condition, message):
    if not condition:
        errors.append(message)

# Remove comments before looking for declarations/imports. Not a general Lean parser.
def uncomment(text):
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)

texts = {str(p.relative_to(ROOT)): p.read_text() for p in paths}
for name, text in texts.items():
    clean = uncomment(text)
    for module in re.findall(r"^import\s+(\S+)", clean, flags=re.M):
        if module.startswith("Macaulean.Interpreter"):
            check(module == "Macaulean.Interpreter.SourceFile", f"legacy semantic import: {name}: {module}")
        check(module != "Macaulean.Verification", f"legacy DSL import: {name}")
    check(not re.search(r"\b(sorry|admit|axiom|unsafe)\b", clean), f"untrusted/admitted code in {name}")
    check(not re.search(r"\b(?:inductive|def)\s+(?:Plan|CodePlan|executePlan)\b", clean), f"old adapter in {name}")

required = {
    "Words.lean": ["abbrev WordKey := Bytes", "def WordRegistry.intern", "def WordRegistry.alias", "structure ParseProfile"],
    "IR.lean": ["sourceWord : WordId", "symbol : SymbolId", "| whileDo", "abbrev Bound := Node SymbolId", "abbrev Code := Node Ref"],
    "Binding.lean": ["def ordinary", "def freshGlobal", "def declare", "def resolve", "def lower", "def alias"],
    "Machine.lean": ["def reify", "def write", "def enter", "def eval", "def call", ".whileDo test body"],
    "Meaning.lean": ["inductive Eval : Bound", "inductive EvalMany", "inductive Call", "def Related", "def LowerForward", "def LowerBackward"],
}
for filename, markers in required.items():
    text = (DESIGN / filename).read_text()
    for marker in markers:
        check(marker in text, f"missing design boundary: {filename}: {marker}")

meaning = (DESIGN / "Meaning.lean").read_text().split("end Macaulean.Language.Design.Meaning")[0]
meaning = uncomment(meaning)
check("Machine.eval" not in meaning and "Binding.lower" not in meaning, "source meaning delegates to target")
program = (EXAMPLE / "Program.lean").read_text()
check("surfaceFixture" in program and "NOT claimed parser output" in program, "unlabelled fixture/source boundary")
semantics = (EXAMPLE / "Semantics.lean").read_text()
for marker in ["def SourceLink", "def Translation", "def Terminates", "def Adequate", "structure Obligations"]:
    check(marker in semantics, f"missing open obligation: {marker}")
source = (ROOT / "Examples/GcdTranslation/gcd.m2").read_text()
check("while b != 0 do" in source, "source algorithm lost its while loop")
check("r := a % b" in source, "source algorithm lost remainder assignment")
for name, text in texts.items():
    check("Nat.gcd" not in uncomment(text) and "Int.gcd" not in uncomment(text), f"builtin gcd substitution: {name}")

report = {"status": "FAIL" if errors else "PASS_STRUCTURAL_ONLY",
          "files_checked": len(paths),
          "lean_guard_commands_supplied": sum(t.count("#guard ") for t in texts.values()),
          "lean_compiled": False, "lean_guards_executed": False,
          "universal_proofs_checked": False, "native_m2_executed": False,
          "limitations": "Text/import-boundary checks only; no typing, execution, semantic or proof validation.",
          "errors": errors}
print(json.dumps(report, indent=2))
sys.exit(1 if errors else 0)
