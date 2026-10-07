#!/usr/bin/env python3
"""Enable the two independent kernels required by the pinned Palomar policy.

The submission comparator.json remains within Palomar's accepted schema.
The temporary verification config adds external checker paths.
"""
import json
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
config = json.loads((root / 'comparator.json').read_text())
prefix = Path(subprocess.check_output(['lean', '--print-prefix'], text=True).strip())
destination = Path(sys.argv[1]).resolve()
nanoda = prefix / 'bin/nanoda_bin'
if not nanoda.is_file():
    raise SystemExit(f'Missing bundled checker: {nanoda}')
# Comparator defaults to four NanoDa workers. Keep the independent replay
# within a standard runner's memory budget without changing its input
# declarations or permitted axioms. A Linux anonymous file works inside the
# read-only bubblewrap sandbox and leaves no writable project dependency.
launcher = destination.with_name(destination.stem + '-nanoda.py')
launcher.write_text('''#!/usr/bin/python3
import json
import os
import sys

with open(sys.argv[1]) as source:
    config = json.load(source)
config['num_threads'] = 1
config['unpermitted_axiom_hard_error'] = True
fd = os.memfd_create('four-row-nanoda-config', flags=0)
with os.fdopen(os.dup(fd), 'w') as destination:
    json.dump(config, destination)
os.lseek(fd, 0, os.SEEK_SET)
os.set_inheritable(fd, True)
print('NanoDa: serial replay; unpermitted axioms are hard errors.', flush=True)
binary = ''' + repr(str(nanoda)) + '''
os.execv(binary, [binary, '/proc/self/fd/' + str(fd)])
''')
launcher.chmod(0o755)
config.pop('enable_nanoda', None)
config['external_kernels'] = {
    'nanoda': [str(launcher)],
    'con-ron': [str(prefix / 'bin/con-ron'), '--verified', '--jobs=1', '--progress=1000'],
}
for command in config['external_kernels'].values():
    if not Path(command[0]).is_file():
        raise SystemExit(f'Missing bundled checker: {command[0]}')
destination.write_text(json.dumps(config, indent=2) + '\n')
