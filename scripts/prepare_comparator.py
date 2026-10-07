#!/usr/bin/env python3
"""Enable the two independent kernels required by the pinned Palomar policy.

The submission comparator.json remains within Palomar's accepted schema.
Only this temporary private-verification config adds external checker paths.
"""
import json
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
config = json.loads((root / 'comparator.json').read_text())
prefix = Path(subprocess.check_output(['lean', '--print-prefix'], text=True).strip())
config.pop('enable_nanoda', None)
config['external_kernels'] = {
    'nanoda': [str(prefix / 'bin/nanoda_bin')],
    'con-ron': [str(prefix / 'bin/con-ron'), '--jobs=2'],
}
for command in config['external_kernels'].values():
    if not Path(command[0]).is_file():
        raise SystemExit(f'Missing bundled checker: {command[0]}')
Path(sys.argv[1]).write_text(json.dumps(config, indent=2) + '\n')
