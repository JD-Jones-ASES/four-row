# Four-row verification evidence

**Final exact-candidate Linux gate: PASSED.** Run 37572525271 completed successfully at clean source `c207efc787a7e1c88aae29dc92d4be5e10297bf2`. The original bundled Comparator, con-ron, NanoDa and Lean default kernel accepted; all 16 principal axiom audits and exact Python replays passed. Completed logs and an independent audit are preserved under `final-linux/`.

The candidate source is `c207efc787a7e1c88aae29dc92d4be5e10297bf2`. The repository is private; this bundle records no publication or Palomar submission.

## Evidence and scope

| Directory | Source / run | Recorded result |
| --- | --- | --- |
| `baseline-linux/` | `ff07f4f897d4c190227eeee3f8f752788487dd3b`, [run 37567252680](https://github.com/JD-Jones-ASES/four-row/actions/runs/37567252680) | Passed original bundled Comparator; con-ron, NanoDa and Lean default kernel accepted. All 16 principal axiom audits and exact Python replay passed. |
| `cold-build/` | `c207efc787a7e1c88aae29dc92d4be5e10297bf2`, [run 37572527284](https://github.com/JD-Jones-ASES/four-row/actions/runs/37572527284) | Passed direct cold `lake build FourRowSolution`, exit 0. Stock 2-CPU runner with swap; not official 16-CPU/32-GB hardware equivalence. |
| `native-diagnostic/` | `c207efc787a7e1c88aae29dc92d4be5e10297bf2` | Local full build, source/metadata/axiom checks, and original Comparator statement/definition-closure comparison passed. The comparison was a **native diagnostic with no sandbox or independent kernel replay**. |
| `final-linux/` | `c207efc787a7e1c88aae29dc92d4be5e10297bf2`, [run 37572525271](https://github.com/JD-Jones-ASES/four-row/actions/runs/37572525271) | **Passed exact-candidate gate.** Original Comparator and all three kernel checks accepted; 16 principal axiom audits and exact Python replay passed. |

Original copied records are retained byte for byte. Their descriptions of then-pending later work are historical. `final-linux/STATUS.json` records the final gate's status in this bundle. The prior cancelled cold diagnostic is contextual evidence only and explicitly records cancellation rather than Lean failure or OOM.

The baseline and candidate local records report the same 395,820,546-byte Solution export, SHA-256 `63f2db60ea902e25dc5f896b0b0c801f7475118c261cce685dd871e1bb4adf29`. This supports the mathematical relation between versions; it is not a replacement for the candidate's exact-commit Linux gate. The baseline Linux artifact itself does not contain an export hash.

## Source, pins and commands

`source/pins.json` records exact source and tree hashes, Lean, Mathlib, elan and Palomar tool pins. The two Git tree inventories identify every tracked source blob. Selected configuration, workflow and verification scripts were copied from the named Git commits, not from potentially modified working files. The entire source remains in the repository at those commits.

The preserved workflows are the authoritative command sequences and setup. Their relevant commands include:

```sh
python3 scripts/fetch_mathlib_cache.py
python3 scripts/build_census.py
python3 scripts/build_grams.py --jobs 1
lake build
python3 scripts/audit_release.py
python3 evidence/probe.py
python3 evidence/audit_census.py
python3 scripts/prepare_comparator.py "$RUNNER_TEMP/four-row-comparator.json"
/usr/bin/time -v lake comparator --config "$RUNNER_TEMP/four-row-comparator.json"
```

The temporary Comparator configuration invokes the unmodified bundled independent checkers with serial resource settings (`con-ron --verified --jobs=1`; NanoDa `num_threads=1`, unpermitted axioms are hard errors). It preserves the input declarations and configured permitted axioms. The intended 16 Challenge placeholders are separate from the Solution axiom audit.

For the cold diagnostic, after fetching only the pinned dependency cache and verifying the project build cache was absent, the command was `lake build FourRowSolution` with `LEAN_NUM_THREADS=16`. The inline workflow monitor collected five-second resource samples and GNU time output; see its source for exact invocation and cancellation handling. Maximum RSS from an individual child or the outer sandbox launcher is not an aggregate checker-memory measurement.

## Integrity and retention

`SHA256SUMS` hashes every payload file, including this README and `PROVENANCE.json`; it excludes itself. Verify from this directory with `sha256sum --check SHA256SUMS` on Linux or `shasum -a 256 -c SHA256SUMS` on macOS. `PROVENANCE.json` additionally records the original bytes and hashes of copied inputs. Compressed logs use deterministic gzip (`mtime=0`); `gzip -cd FILE.gz` restores the original bytes. No build artifacts, tool binaries or large proof exports are included. Copied Actions authentication fields were already masked as `***`; high-confidence credential patterns were checked before packaging.

These records are retained on the private branch `codex/verification-c207efc`, separately from the verified source on `main`. The annotated tag `verified/2026-10-07-c207efc` points to the exact checked **source** commit and identifies this records commit. The separate tag `evidence/2026-10-07-c207efc` pins the records commit. This archive preserves the logs independently of GitHub Actions artifact retention; it makes no public release or Palomar submission.
