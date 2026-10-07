#!/usr/bin/env python3
"""Build one deterministic shard of census leaves, with one compiler at a time.

The leaves contain kernel-checked integer inverse or support-extension
certificates. All shards must succeed at the same commit before the final
sequential package build and independent audits. This script never substitutes
an external computation for a Lean theorem.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--shard', type=int, required=True)
    parser.add_argument('--shards', type=int, default=1)
    parser.add_argument('--lake', default='lake')
    args = parser.parse_args()
    if args.shards <= 0 or not 0 <= args.shard < args.shards:
        parser.error('require --shards > 0 and 0 <= --shard < --shards')

    leaves = [f'FourRow.CensusData.Max{i:02}' for i in range(41)]
    leaves += [f'FourRow.CensusData.Extension{i:02}' for i in range(40)]
    selected = [name for index, name in enumerate(leaves)
                if index % args.shards == args.shard]
    logs = ROOT / 'build-logs' / 'census-shards' / f'{args.shard:02}'
    logs.mkdir(parents=True, exist_ok=True)
    commit_result = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=ROOT,
                                   text=True, capture_output=True, check=False)
    status_result = subprocess.run(['git', 'status', '--porcelain=v1', '--untracked-files=all'],
                                   cwd=ROOT, text=True, capture_output=True, check=False)
    initial_clean = status_result.returncode == 0 and not status_result.stdout.strip()
    report = {
        'shard': args.shard,
        'shards': args.shards,
        'commit': commit_result.stdout.strip() if commit_result.returncode == 0 else None,
        'worktree_clean_at_start': initial_clean,
        'selected_modules': selected,
        'results': [],
        'complete': False,
    }
    report_path = logs / 'results.json'

    def save() -> None:
        temporary = report_path.with_suffix('.json.tmp')
        temporary.write_text(json.dumps(report, indent=2) + '\n')
        temporary.replace(report_path)

    save()
    for number, name in enumerate(selected, 1):
        started = time.monotonic()
        log = logs / f'{name}.log'
        with log.open('w') as stream:
            process = subprocess.Popen([args.lake, 'build', name], cwd=ROOT,
                                       stdout=stream, stderr=subprocess.STDOUT)
            (logs / 'active-pid.txt').write_text(f'{process.pid}\n')
            result = process.wait()
        seconds = time.monotonic() - started
        report['results'].append({'module': name, 'exit_code': result,
                                  'seconds': round(seconds, 3),
                                  'log': str(log.relative_to(ROOT))})
        save()
        print(f'shard {args.shard + 1}/{args.shards}: {number}/{len(selected)} '
              f'{name}: exit={result} seconds={seconds:.1f}', flush=True)
        if result:
            print(log.read_text()[-6000:], flush=True)
            raise SystemExit(result)
    final_commit = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=ROOT,
                                  text=True, capture_output=True, check=False)
    final_status = subprocess.run(['git', 'status', '--porcelain=v1', '--untracked-files=all'],
                                  cwd=ROOT, text=True, capture_output=True, check=False)
    report['worktree_clean_at_end'] = final_status.returncode == 0 and not final_status.stdout.strip()
    report['exact_commit_check'] = bool(initial_clean and report['worktree_clean_at_end']
                                        and final_commit.returncode == 0
                                        and final_commit.stdout.strip() == report['commit'])
    report['complete'] = True
    save()
    print(f'Census shard {args.shard} completed; report: '
          f'{report_path.relative_to(ROOT)}', flush=True)


if __name__ == '__main__':
    main()
