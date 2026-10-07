#!/usr/bin/env python3
"""Exercise the independent-kernel launcher inside Comparator's Linux sandbox.

The scratch theorem is an operational smoke check, not evidence for four-row.
"""
import json
from pathlib import Path
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parents[1]
with tempfile.TemporaryDirectory(prefix='four-row-kernel-smoke-') as directory:
    scratch = Path(directory)
    (scratch / 'lean-toolchain').write_text((root / 'lean-toolchain').read_text())
    (scratch / 'lakefile.toml').write_text('''name = "kernelSmoke"
version = "0.1.0"
[[lean_lib]]
name = "SmokeChallenge"
[[lean_lib]]
name = "SmokeSolution"
''')
    declaration = '''module
public import Init
@[expose] public section
namespace KernelSmoke
theorem checked : (17 : Nat) + 23 = 40 := PROOF
end KernelSmoke
'''
    (scratch / 'SmokeChallenge.lean').write_text(declaration.replace('PROOF', 'by sorry'))
    (scratch / 'SmokeSolution.lean').write_text(declaration.replace('PROOF', 'by decide +kernel'))
    config_path = scratch / 'comparator.json'
    subprocess.run([sys.executable, str(root / 'scripts/prepare_comparator.py'),
                    str(config_path)], check=True)
    config = json.loads(config_path.read_text())
    config['challenge_module'] = 'SmokeChallenge'
    config['solution_module'] = 'SmokeSolution'
    config['theorem_names'] = ['KernelSmoke.checked']
    config_path.write_text(json.dumps(config, indent=2) + '\n')
    subprocess.run(['lake', 'build', 'SmokeChallenge', 'SmokeSolution'],
                   cwd=scratch, check=True)
    subprocess.run(['lake', 'comparator', '--config', str(config_path)],
                   cwd=scratch, check=True)
