#!/usr/bin/env python3
"""Audit the compared API, source resolution, and actual theorem axioms.

Run after the complete build. This is an additional local/CI guard; the
separate Comparator and independent kernel replays remain the release gate.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def lean_code(source):
    """Remove nested Lean comments and strings before checking source tokens."""
    result, i, depth = [], 0, 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            result.append(" ")
            i += 2
        elif depth:
            i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        elif source[i] == '"':
            i += 1
            while i < len(source) and source[i] != '"':
                i += 2 if source[i] == "\\" else 1
            i += 1
            result.append(" ")
        else:
            result.append(source[i])
            i += 1
    require(depth == 0, "Unclosed Lean comment")
    return "".join(result)


def run(lake, *args):
    return subprocess.check_output([lake, *args], cwd=ROOT, text=True,
                                   stderr=subprocess.STDOUT)


def source_imports(code):
    lines = re.findall(r"^(?:public )?(?:meta )?import\s+([^\n]+)", code, re.M)
    return [module for line in lines for module in line.split()]


def audit(lake, structure_only=False):
    config = json.loads((ROOT / "comparator.json").read_text())
    require(set(config) <= {"challenge_module", "solution_module", "theorem_names",
                           "definition_names", "permitted_axioms", "enable_nanoda"},
            "Unrecognized Palomar comparator field")
    require(set(config["permitted_axioms"]) == ALLOWED, "Axiom allowlist changed")
    names = config["theorem_names"]
    require(names and len(names) == len(set(names)), "Missing or duplicate principal theorem")
    require(all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", n) for n in names),
            "Invalid theorem name")
    challenge = ROOT / (config["challenge_module"].replace(".", "/") + ".lean")
    solution = ROOT / (config["solution_module"].replace(".", "/") + ".lean")
    require(challenge != solution, "Challenge and solution must be separate modules")
    text = challenge.read_text()
    require(len(text.encode()) <= 100_000 and len(text.splitlines()) <= 1000,
            "Challenge exceeds the policy size ceiling")
    imports = source_imports(lean_code(text))
    require(imports and all(m == "Mathlib" or m.startswith("Mathlib.") for m in imports),
            "Challenge must import only Mathlib")
    sources = [*sorted(ROOT.glob("*.lean")), *sorted((ROOT / "FourRow").rglob("*.lean"))]
    for source in sources:
        code = lean_code(source.read_text())
        require(code.lstrip().startswith("module\n"),
                f"Missing module header in {source.relative_to(ROOT)}")
        require(len(source.read_text().splitlines()) <= 10_000,
                f"Lean source exceeds 10000 lines: {source.relative_to(ROOT)}")
        if source == challenge:
            continue
        banned = re.search(r"\b(sorry|admit|axiom|native_decide|ofReduceBool|unsafe)\b", code)
        require(banned is None, f"Forbidden proof token in {source.relative_to(ROOT)}: "
                f"{banned.group() if banned else ''}")
        require(config["challenge_module"] not in source_imports(code),
                "The solution must not import challenge holes")

    srcpath = run(lake, "env", "python3", "-c",
                  "import os; print(os.environ['LEAN_SRC_PATH'])").strip()
    roots = list(dict.fromkeys(Path(p).resolve() for p in srcpath.split(os.pathsep) if p))
    resolution = {}
    for module, expected in [(config["challenge_module"], challenge),
                             (config["solution_module"], solution)]:
        suffix = Path(*module.split(".")).with_suffix(".lean")
        matches = list(dict.fromkeys((base / suffix).resolve() for base in roots
                                     if (base / suffix).is_file()))
        require(matches == [expected.resolve()],
                f"Ambiguous or shadowed source module {module}: {matches}")
        resolution[module] = str(expected.relative_to(ROOT))
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    require(all(re.fullmatch(r"[0-9a-f]{40}", p["rev"])
                for p in manifest["packages"] if p["type"] == "git"),
            "Dependency revision is not an immutable commit")
    require((ROOT / "lean-toolchain").read_text().strip() ==
            (ROOT / ".lake/packages/mathlib/lean-toolchain").read_text().strip(),
            "Lean pin and Mathlib toolchain differ")
    if structure_only:
        print(json.dumps({"source_resolution": resolution, "theorems": len(names)}, indent=2))
        return

    with tempfile.TemporaryDirectory(prefix="four-row-audit-") as directory:
        check = Path(directory) / "Audit.lean"
        check.write_text("import " + config["solution_module"] + "\n" +
                         "\n".join("#print axioms " + n for n in names) + "\n")
        output = run(lake, "env", "lean", str(check))
    (ROOT / "axiom-audit.log").write_text(output)
    observed = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output):
        observed[name] = {a.strip() for a in axioms.split(",") if a.strip()}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        observed[name] = set()
    require(set(observed) == set(names), f"Axiom audit omitted declarations: {set(names)-set(observed)}")
    require(all(axioms <= ALLOWED for axioms in observed.values()),
            f"Disallowed theorem axioms: {observed}")
    print(output, end="")
    print(f"Release audit passed: {len(names)} principal theorems; unique local module "
          "resolution; only propext, Quot.sound and Classical.choice permitted.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default=os.environ.get("FOUR_ROW_LAKE", "lake"))
    parser.add_argument("--structure-only", action="store_true")
    arguments = parser.parse_args()
    audit(arguments.lake, arguments.structure_only)
