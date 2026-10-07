#!/usr/bin/env python3
"""Fail early if same-run certificate artifacts were extracted to the wrong path."""
from pathlib import Path

root = Path(__file__).resolve().parents[1] / ".lake/build/lib/lean/FourRow"
modules = [root / "Grams" / f"G{i:03}" for i in range(131)]
modules += [root / "CensusData" / f"Max{i:02}" for i in range(41)]
modules += [root / "CensusData" / f"Extension{i:02}" for i in range(40)]
modules += [root / "CensusTableChecks" / f"Action{i:02}" for i in range(24)]
modules += [root / "CensusTableChecks" / f"Primitive{i:02}" for i in range(10)]
modules += [root / name for name in ["CensusTableData", "CensusTables", "CensusIndependence"]]
missing = [str(p.with_suffix(suffix)) for p in modules for suffix in [".olean", ".olean.private", ".trace"]
           if not p.with_suffix(suffix).is_file()]
if missing:
    raise SystemExit("Missing restored certificate artifacts:\n" + "\n".join(missing))
print("Restored all 131 Gram, 81 census leaf, 34 table-check, and 3 census parent modules, including private proof artifacts and traces.")
