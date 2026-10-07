# Prior art and the contribution boundary

Primary-source audit, 2026-10-06. This is a bounded comparison, not worldwide
novelty clearance or external peer review. The contribution under comparison is the
**exact TV radius and sharp stability for balanced nonuniform laws on S₄**,
together with explicit consequences. Uniform permanent inequalities, entropy
duality, and tensorization have substantial prior literature.

## Direct predecessors

| Primary source | Relevant result | Relationship to this work |
|---|---|---|
| Carlen–Lieb–Loss, [An Inequality of Hadamard Type for Permanents](https://arxiv.org/html/math/0508096v1), Theorem 1.1 (2005 preprint; 2006 publication) | Sharp uniform permanent bound at exponent 2 in every dimension | The uniform endpoint is classical. The present law is allowed to vary inside a balanced TV ball. |
| Bristiel–Caputo, [Entropy inequalities for random walks and permutations](https://arxiv.org/html/2109.06009v3), Corollary 1.14 and §4.3 (2021/2022 preprint; 2024 publication) | Sharp uniform permanent bound for every $p\ge1$, with transition at $p=n\log n/\log(n!)$ | Stronger than needed at the uniform law. It underpins the earlier [local theorem](PROOF.md), but is not a dependency of the exact endpoint or the new explicit stability proof. |
| OpenAI, [A strict four-row permanent inequality and permutation moments](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-strict-four-row-permanent-inequality-and-permutation-moments-September-26-2026), September 26, 2026, §§1–3 and 6 | Existence of some $p_0<2$ and some positive balanced-TV neighborhood; tensorization and a permutation-moment/shuffle application | Closest direct predecessor. Its robustness constants are not optimized. We determine the exact endpoint radius, the sharp linear stability coefficient, and an explicit sufficient exponent throughout the interior. |

The exact source snapshot for the OpenAI comparison is
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`; mathematical definitions and
statements were inspected, not imported as implementation.
The paper's existence theorem and tensorization must be credited in any
subsequent write-up. Its required shuffle exponent is $1-1/p_0<1/2$, so
the endpoint $p=2$ alone does not supply that strict gain.

Cobos–Kühn–Peetre's 2006 Theorem 5.1 is also credited for the uniform norm
bound by [Roos](https://arxiv.org/html/1906.06176v2). The
[publisher record](https://link.springer.com/article/10.1007/s00020-005-1412-2)
was located; the full paper was not inspected here. Do not upgrade this
secondary attribution into a claim that its full contents were audited.

## Entropy, dependence, and permanent refinements

| Primary source | Relevant mechanism and boundary |
|---|---|
| Carlen–Cordero-Erausquin, [Subadditivity of the Entropy and its Relation to Brascamp–Lieb Type Inequalities](https://arxiv.org/html/0710.0870v2), Theorems 2.1–2.2 | General norm/entropy duality and equality correspondence. Our entropy inequality is an instance of this machinery with a new sharp robustness parameter, not a new duality theorem. |
| Barthe–Cordero-Erausquin–Ledoux–Maurey, [Correlation and Brascamp–Lieb inequalities for Markov semigroups](https://arxiv.org/html/0907.2858v1), §4.2.2, Proposition 20 | Correlation inequalities for uniform permutations; singleton blocks recover the exponent-2 permanent inequality. |
| Beigi–Gohari, [On the Duality of Additivity and Tensorization](https://arxiv.org/html/1502.00827v2), Example 6 | Multipartite information ribbons, tensorization and data processing. The four-coordinate consequence fits this established framework. |
| Raginsky, [Strong Data Processing Inequalities and Φ-Sobolev Inequalities for Discrete Channels](https://arxiv.org/abs/1411.3575) | Standard language and theory for channel contraction; the sharp factor $1/2$ for the specified robust law class is the concrete input here. |
| Caputo–Salez, [Entropy factorization via curvature](https://arxiv.org/html/2407.13457v2), Theorem 4 | Permutation block factorization. The reference permutation measure there is uniform; weights on update blocks are not weights on permutation atoms. |
| Roos, [New inequalities for permanents and hafnians and some generalizations](https://arxiv.org/html/1906.06176v2), Theorems 1.2–1.4 | Refined permanent estimates via minors and partitions, and characteristic-function applications. No matching sharp balanced-TV ball theorem was found in the inspected statements. |

The scalar inequality used in [EXTENSIONS](EXTENSIONS.md) is an elementary
sum of classical three-variable Schur inequalities. Its short rational SOS
is an independently derived proof certificate; the scalar inequality is not
advertised as new. The pair estimates, conditional iteration, entropy
variational argument and exponential-moment transfer are elementary or
standard mechanisms. Only their stated quantitative conclusions for the
specified nonuniform law class are candidate contributions.

## What is established and what remains open

**Mathematical results:** the exact radius $R_4(2)=1/24$; the optimal
stability coefficient $(1-24r)/9$ for every $0\le r\le1/24$; complete
nonnegative equality cases for the endpoint row-norm inequality; the sufficient exponent
$p(r)=2-(1-24r)/36$; the exact threshold $r<1/24$ for existence of a
common exponent below two; sharp endpoint entropy/coordinate-observation
constants; and the stated adaptive tensorization and resampling consequences.

**Not established:** worldwide priority; the optimal exponent at an interior
radius; a full formula for $R_4(p)$; arbitrary atom-capped laws without the
TV hypothesis; a higher-dimensional sharp-radius theorem; a shorter analytic
endpoint proof; or external human review. The explicit exponent at
$r=0$ is weaker than the classical optimal uniform exponent. The shuffle
calculation in the application note verifies a particular local input; it
does not independently prove an improved global shuffle mixing theorem.

**Assessment.** This has a plausible audience in permanent inequalities,
finite Brascamp–Lieb inequalities and entropy contraction. A serious short
note should lead with sharp nonuniform robustness and stability, and use
entropy and the concrete shuffle input to demonstrate utility. A catalogue
of routine corollaries alone would add little. Before publication, a
specialist literature check and independent mathematical review remain useful.
The sixteen [formal statements](THEOREMS.md) and their
[verification record](VERIFICATION.md) specify the completed Lean coverage.
Additional informal consequences are distinguished from those claims.
