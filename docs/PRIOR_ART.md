# Related work

This work establishes the exact TV radius and sharp stability for balanced
nonuniform laws on $S_4$, with equality, exponent, entropy, and tensorization
consequences. The references below place these results alongside the
uniform permanent inequalities and their analytic applications.

## Permanent inequalities

| Source | Relevant result | Relationship to this work |
|---|---|---|
| Carlen–Lieb–Loss, [An Inequality of Hadamard Type for Permanents](https://arxiv.org/html/math/0508096v1), Theorem 1.1 (2005 preprint; 2006 publication) | Sharp uniform permanent bound at exponent 2 in every dimension | The uniform endpoint is classical. Here the law varies inside a balanced TV ball. |
| Bristiel–Caputo, [Entropy inequalities for random walks and permutations](https://arxiv.org/html/2109.06009v3), Corollary 1.14 and §4.3 (2021/2022 preprint; 2024 publication) | Sharp uniform permanent bound for every $p\ge1$, with transition at $p=n\log n/\log(n!)$ | Supplies the uniform input to the [local theorem](PROOF.md). The exact endpoint and explicit stability proofs are independent of that input. |
| OpenAI, [A strict four-row permanent inequality and permutation moments](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-strict-four-row-permanent-inequality-and-permutation-moments-September-26-2026), September 26, 2026, §§1–3 and 6 | Existence of some $p_0<2$ and some positive balanced-TV neighborhood; tensorization and a permutation-moment/shuffle application | Establishes qualitative nonuniform robustness. Here the endpoint radius and linear stability coefficient are sharp, with an explicit sufficient exponent throughout the interior. |

The OpenAI source is pinned at `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Its shuffle argument requires $1-1/p_0<1/2$, so the endpoint $p=2$ alone
does not supply that strict gain. [SHUFFLE_INPUT.md](SHUFFLE_INPUT.md)
gives a concrete local input to that argument.

Cobos–Kühn–Peetre, [2006, Theorem 5.1](https://link.springer.com/article/10.1007/s00020-005-1412-2),
is also credited for the uniform norm bound by
[Roos](https://arxiv.org/html/1906.06176v2); this attribution is through Roos.

## Entropy, dependence, and permanent refinements

| Source | Relevant mechanism and boundary |
|---|---|
| Carlen–Cordero-Erausquin, [Subadditivity of the Entropy and its Relation to Brascamp–Lieb Type Inequalities](https://arxiv.org/html/0710.0870v2), Theorems 2.1–2.2 | General norm/entropy duality and equality correspondence. The entropy inequality here applies this machinery with the sharp robustness parameter. |
| Barthe–Cordero-Erausquin–Ledoux–Maurey, [Correlation and Brascamp–Lieb inequalities for Markov semigroups](https://arxiv.org/html/0907.2858v1), §4.2.2, Proposition 20 | Correlation inequalities for uniform permutations; singleton blocks recover the exponent-2 permanent inequality. |
| Beigi–Gohari, [On the Duality of Additivity and Tensorization](https://arxiv.org/html/1502.00827v2), Example 6 | Multipartite information ribbons, tensorization and data processing. The four-coordinate consequence fits this framework. |
| Raginsky, [Strong Data Processing Inequalities and Φ-Sobolev Inequalities for Discrete Channels](https://arxiv.org/abs/1411.3575) | Channel contraction; the sharp factor $1/2$ for the robust law class is the concrete input here. |
| Caputo–Salez, [Entropy factorization via curvature](https://arxiv.org/html/2407.13457v2), Theorem 4 | Permutation block factorization with uniform reference measure; weights on update blocks are distinct from weights on permutation atoms. |
| Roos, [New inequalities for permanents and hafnians and some generalizations](https://arxiv.org/html/1906.06176v2), Theorems 1.2–1.4 | Refined permanent estimates via minors and partitions, with characteristic-function applications. |

The scalar inequality in [EXTENSIONS.md](EXTENSIONS.md) is an elementary
sum of classical three-variable Schur inequalities. The note supplies a
rational sum-of-squares identity for it. The pair estimates, conditional
iteration, entropy variational argument, and exponential-moment transfer
are standard mechanisms; the quantitative conclusions concern the
specified nonuniform law class.

## Scope

The [sixteen formal statements](THEOREMS.md) cover the exact radius
$R_4(2)=1/24$, optimal stability coefficient $(1-24r)/9$ for
$0\le r\le1/24$, complete nonnegative endpoint equality cases, sufficient
exponent $p(r)=2-(1-24r)/36$, exact threshold $r<1/24$ for a common exponent
below two, sharp endpoint entropy and coordinate-observation constants,
and adaptive tensorization. [VERIFICATION.md](VERIFICATION.md) records
their Lean verification.

The interior exponent is sufficient; a full formula for $R_4(p)$ is not
claimed. The explicit exponent at $r=0$ is weaker than the classical optimal
uniform exponent. The theorem concerns four labels and the TV hypothesis;
it makes no claim for arbitrary atom-capped laws or higher dimensions.

The [atom-geometry note](ATOM_GEOMETRY.md) derives the all-radius atom
envelope and small-radius extremal faces from the four-label marginal
equations. Its exponent-four sufficiency is classical Hölder. These results
and the resampling consequences in [EXTENSIONS.md](EXTENSIONS.md) are
supplementary mathematics outside the sixteen compared claims.
