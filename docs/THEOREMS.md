# Formal theorem scope

The statement of record is [FourRowChallenge.lean](../FourRowChallenge.lean).
Its only imports are Mathlib modules. The sixteen corresponding closed proofs
are in [FourRowSolution.lean](../FourRowSolution.lean), under the namespace
`FourRowPrincipal`; [comparator.json](../comparator.json) names each one.
Release verification compares these statements and audits their actual axioms.

Let $S_4$ be the permutations of four labels and $u(\sigma)=1/24$.
A balanced probability law $\nu:S_4\to\mathbb R$ is nonnegative, has mass
one, and satisfies $\nu\{\sigma:\sigma(i)=j\}=1/4$ for every pair $i,j$.
Write

$$
 d_{\rm TV}(\nu,u)=\frac12\sum_{\sigma\in S_4}|\nu(\sigma)-1/24|,
 \qquad
 T_\nu(A)=\sum_{\sigma\in S_4}\nu(\sigma)\prod_{i=1}^4A_{i,\sigma(i)}.
$$

All laws and entries are real. Every matrix in the inequalities is
nonnegative; zeros are allowed. The balls are closed. No principal theorem assumes
rational weights, strictly positive entries, census completeness, a
certificate predicate, or the endpoint inequality itself.

## Sharp endpoint, stability, and equality

For every balanced law with $d_{\rm TV}(\nu,u)\le1/24$, `endpoint` proves

$$
 256\,T_\nu(A)^2\le\prod_{i=1}^4\sum_{j=1}^4 A_{ij}^2.
$$

`radius_sharp` gives an actual balanced law and normalized nonnegative matrix
violating the inequality for every larger radius. Thus the exact robustness
radius at exponent two is $R_4(2)=1/24$.

For probability-L²-normalized rows, $\frac14\sum_j A_{ij}^2=1$, and
$0\le r\le1/24$, `sharp_stability` proves

$$
 1-T_\nu(A)\ge\frac{1-24r}{9}
 \sum_{i=1}^4\left[1-\left(\frac14\sum_{j=1}^4 A_{ij}\right)^2\right].
$$

`stability_optimal` proves that no larger coefficient works throughout the
same ball. `explicit_extremal_family` identifies a witnessing law

$$
 \nu_r=u+r\left(\tfrac12\delta_{\mathrm{id}}
       +\tfrac12\mathrm{Unif}(\text{nine derangements})
       -\mathrm{Unif}(\text{six transpositions})\right).
$$

For $0\le r\le1/4$, this is a balanced probability law with exact TV
distance $r$. On $A=2I$, its value is $2/3+8r$ and the variance sum
is three, so equality holds in the sharp stability bound when $r\le1/24$.

`endpoint_equality` classifies **all** nonnegative equality cases in the
square-root-free endpoint inequality. Their union is:

1. A row is identically zero.
2. Each row is constant across its columns.
3. There is a permutation $\tau$ with $\nu(\tau)=1/16$, and each row
   is supported on its matching entry $(i,\tau(i))$.

Arbitrary nonnegative row scalings are included. The three cases need not
be disjoint. With all rows normalized, the latter two reduce to the all-ones
matrix and twice a permutation matrix of mass $1/16$.

## Exponents and entropy

Set $p(r)=2-(1-24r)/36$. For $0\le r\le1/24$, `explicit_exponent` proves

$$
 T_\nu(A)\le\prod_{i=1}^4
   \left(\frac14\sum_{j=1}^4 A_{ij}^{p(r)}\right)^{1/p(r)}.
$$

`larger_exponents` proves the same bound for every $p\ge p(r)$.
`subcritical_threshold` proves that, for $r\ge0$, a common exponent
$1\le p<2$ works for all laws in the ball exactly when $r<1/24$.
The explicit interior exponent is sufficient; its numerical value is not
claimed optimal.

For any probability law $\rho$ on $S_4$, write $\rho_i$ for its
coordinate marginals, $u_4$ for the uniform four-point law, and $D$ for
relative entropy using natural logarithms. `entropy` proves

$$
 \sum_{i=1}^4 D(\rho_i\Vert u_4)\le p(r)D(\rho\Vert\nu).
$$

Unsupported $\rho$ has $D(\rho\Vert\nu)=+\infty$; the Lean theorem
uses `EReal` and includes this case. `observation_contraction` proves
coefficient $p(r)/4$ for observing an independently uniform row index
together with its image. `entropy_optimal` and `observation_optimal` prove
that the endpoint coefficients two and one half, respectively, cannot be
improved over the endpoint ball. They use $\rho=\delta_{\mathrm{id}}$
against $\nu_{1/24}$, with entropies $\log16$ and $4\log4$.

## Adaptive histories

At each time, a conditional permutation law may depend on the **complete
permutation history**. Assume it lies in the same balanced radius-$r$ ball
on every positive-probability past; null histories impose no condition.
`adaptive_probability` proves that the resulting path weights form a
probability distribution. `adaptive_marginals` proves that each individual
row history has uniform product law on $4^n$ histories.

For arbitrary nonnegative functions $F_i$ of the individual row histories,
`adaptive_tensorization` proves

$$
 \mathbb E\prod_{i=1}^4 F_i(X_i)
 \le\prod_{i=1}^4\|F_i\|_{L^{p(r)}(u_4^{\otimes n})}.
$$

This includes history-dependent kernels and any finite horizon. A global
shuffle mixing theorem is not among the formal claims.

## Proof organization

| Layer | Formal sources | What is checked |
|---|---|---|
| Real-law reduction | `Circuit`, `Relabel`, `Endpoint`, `OrbitTransfer` | Extreme points of a real kernel/l¹ ball reduce to minimal supported kernel vectors |
| Exhaustive support coverage | `Census`, `CensusCoverage`, `CensusData`, `CensusTableChecks` | Exact integer left inverses and explicit support-extension/relabeling witnesses |
| Polynomial certificates | `Grams/G000`–`G130`, `Grams`, `CertificateTransfer` | Explicit rational sum-of-squares identities, including a positive equality defect |
| Boundary and equality | `Normalization`, `Equality`, `EqualityEndpoint`, `EndpointTheorem` | Arbitrary row scaling, zero rows, and the complete product-relation classification |
| Stability and sharpness | `Uniform`, `Stability`, `Sharpness`, `ExtremalFamily` | Uniform coefficient, radial transfer, and exact extremal family |
| Analytic consequences | `Exponent`, `NormMonotonicity`, `Entropy`, `EntropyExponent`, `SharpExponent`, `SharpEntropy`, `Tensorization` | Real powers, zero entries, finite entropy duality, sharp endpoint obstruction, adaptive induction |

The finite tables contain 5,109 independent-support representatives, including
the empty support. Exact left inverses for 1,282 maximal independent supports
certify the smaller ones by explicit inclusion and relabeling. Every one-point
extension is either independently certified or contains a listed circuit.
The 73 primitive support representatives and both orientations map to the
131 polynomial certificates. Exhaustive coverage enters as a proved Lean
theorem, not as a Python result or rank assumption.

[ENDPOINT.md](ENDPOINT.md) and [EXTENSIONS.md](EXTENSIONS.md) give the
mathematical arguments. The [shuffle input](SHUFFLE_INPUT.md) and
[atom geometry](ATOM_GEOMETRY.md), including the all-radius atom envelope
and law-side simplex classification, are supplementary results outside
the sixteen compared declarations.
