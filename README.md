# Sharp robustness and stability of the four-row permanent inequality

This Lean formalization proves the exact total-variation robustness radius
**$1/24$** for the four-row permanent inequality, together with its optimal
variance-deficit bound, equality cases, and entropy consequences.

Let $u$ be uniform on the 24 permutations of four labels. A probability law
$\nu$ is balanced when every coordinate has uniform marginal. For every
balanced real law with $d_{\mathrm{TV}}(\nu,u)\le r\le1/24$ and nonnegative
rows normalized by $\frac14\sum_j f_i(j)^2=1$, we prove

$$
1-\mathbb E_\nu\prod_{i=1}^4 f_i(\sigma(i))
\ge \frac{1-24r}{9}\sum_{i=1}^4\mathrm{Var}_{u_4}(f_i).
$$

Here $u_4$ is the uniform four-point law. The coefficient is optimal for
every $0\le r\le1/24$. The endpoint inequality includes arbitrary
nonnegative matrices, zero rows, and every real balanced law in the closed
ball. The radius $1/24$ is sharp.

The sixteen principal statements also give the complete endpoint equality
classification, an explicit extremal family, the sufficient exponent
$p(r)=2-(1-24r)/36$, the exact threshold for a common exponent below two,
sharp endpoint entropy and observation constants, and tensorization for
adaptive permutation histories. The interior exponent is not claimed
optimal, and no global shuffle mixing theorem is claimed.

## Proof and scope

- [Formal statements](docs/THEOREMS.md): all sixteen claims and their hypotheses.
- [FourRowChallenge.lean](FourRowChallenge.lean): the Mathlib-only statement of record.
- [FourRowSolution.lean](FourRowSolution.lean): the corresponding proved declarations.
- [Endpoint proof](docs/ENDPOINT.md) and [extensions](docs/EXTENSIONS.md): mathematical arguments.
- [Real-law reduction](docs/real-law-reduction.md) and [support census](docs/CENSUS.md): why finite certificates cover every real law.
- [Prior art](docs/PRIOR_ART.md): published antecedents and the contribution boundary.
- [Verification](docs/VERIFICATION.md) and [AI assistance](DISCLOSURE.md): checks, provenance, and review status.

The endpoint proof uses 73 support representatives and 131 oriented
sum-of-squares certificates. Lean proves exhaustive support coverage,
certificate soundness, and transfer to arbitrary real laws. Python prepares
finite witnesses; its computations are not axioms of the Lean proof.

The [complete Linux verification](https://github.com/JD-Jones-ASES/four-row/actions/runs/37572525271)
passed at proof commit `c207efc787a7e1c88aae29dc92d4be5e10297bf2`, including
all sixteen statement comparisons and axiom audits, con-ron, NanoDa, and
Lean kernel replay. The direct cold build also passed. This documentation
revision preserves the verified Lean, dependency, Comparator, and build
inputs; [the verification record](docs/VERIFICATION.md) states the exact scope.

## Build and replay

Use the pinned Lean toolchain and dependencies:

```sh
python3 scripts/fetch_mathlib_cache.py
python3 scripts/build_grams.py --jobs 1
python3 scripts/build_census.py
lake build
python3 scripts/audit_release.py
```

The independent exact evidence replays are:

```sh
python3 evidence/probe.py
python3 evidence/audit_census.py
```

The project uses the [MIT license](LICENSE).
[Submission details](docs/PALOMAR.md) identify the package and the current
Palomar requirements.
