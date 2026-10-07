#!/usr/bin/env python3
"""Fetch canonical pinned Mathlib cache only for the actual imported closure."""
import os
from pathlib import Path
import subprocess

from audit_release import lean_code, source_imports

root = Path(__file__).resolve().parents[1]
sources = [*root.glob("*.lean"), *(root / "FourRow").rglob("*.lean")]
modules = sorted({name for path in sources for name in source_imports(lean_code(path.read_text()))
                  if name == "Mathlib" or name.startswith("Mathlib.")})
if not modules:
    raise SystemExit("No Mathlib import roots found")
print(f"Retrieving the pinned cache for {len(modules)} Mathlib import roots.", flush=True)
subprocess.run([os.environ.get("FOUR_ROW_LAKE", "lake"), "exe", "cache", "get", *modules],
               cwd=root, check=True)
