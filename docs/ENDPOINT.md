# The sharp four-row robustness radius: R₄(2) = 1/24

This note gives the exact certificate argument for every balanced real
probability law in the closed TV ball and every nonnegative real matrix,
including boundary matrices. The proof uses complete finite support coverage
and rational Gram identities, with no numerical tolerance. It does not depend
on the published critical-exponent theorem used in [the local result](PROOF.md).

The [formal statements](THEOREMS.md), [real-law reduction](real-law-reduction.md),
and [support census](CENSUS.md) describe the Lean proof and its exact scope.
The packaged [evidence](../evidence/) is independently replayable; completed
kernel checks are recorded in [VERIFICATION.md](VERIFICATION.md).

## Statement

Let $`u`$ be uniform on $`S_4`$. A probability law $`\nu`$ is balanced if
$`\nu\{\sigma:\sigma(i)=j\}=1/4`$ for all $`i,j`$. Put

```math
d_{\rm TV}(\nu,u)=\frac12\sum_{\sigma\in S_4}|\nu(\sigma)-1/24|.
```

**Theorem.** If $`\nu`$ is balanced and
$`d_{\rm TV}(\nu,u)\le1/24`$, then for every nonnegative real
$`4\times4`$ matrix $`A=(a_{ij})`$,

```math
\sum_{\sigma\in S_4}\nu(\sigma)\prod_{i=1}^4a_{i,\sigma(i)}
 \le \prod_{i=1}^4\left(\frac14\sum_{j=1}^4a_{ij}^2\right)^{1/2}.
 \qquad\text{(1)}
```

For every $`r\gt 1/24`$ there is a balanced probability law with
$`d_{\rm TV}(\nu,u)\lt r`$ and a nonnegative matrix for which (1) fails.
Consequently, for the radius defined in [PROOF](PROOF.md),

```math
\boxed{R_4(2)=\frac1{24}}.
```

## 1. The exact law polytope

Index the coordinates by the 24 permutations in lexicographic order, and let
$`B_{(i,j),\sigma}=\mathbf1_{\sigma(i)=j}`$. Define
$`x_\sigma=24\nu(\sigma)-1`$. The laws in the theorem correspond exactly to

```math
\mathcal P=\{x\in\mathbb R^{24}:Bx=0,\ \|x\|_1\le2\}.
 \qquad\text{(2)}
```

Indeed, $`Bx=0`$ is precisely balance, implies $`\sum x_\sigma=0`$, and
the TV distance is $`\|x\|_1/48`$. Conversely (2) implies that the positive
and negative masses of $`x`$ are each at most one. Thus every
$`x_\sigma\ge-1`$, so $`\nu=(1+x)/24`$ is nonnegative. Summing the four
marginal equations for one fixed row gives its total mass one.

The matrix $`B`$ has rank ten, independently verified by exact rational
elimination. A **circuit** is a support-minimal nonzero vector in $`\ker B`$.
The vertices of $`\mathcal P`$ are its normalized circuits

```math
x=\frac{2c}{\|c\|_1}.
 \qquad\text{(3)}
```

Here is a proof of this reduction. A vertex is nonzero and has norm two:
zero is a midpoint of two small opposite kernel vectors, and a nonzero
point of smaller norm lies inside a feasible radial segment. For a support
$`S`$, if $`\dim\ker B_S\ge2`$, there is a nonzero $`y\in\ker B_S`$
with $`\sum_{\sigma\in S}\mathrm{sign}(x_\sigma)y_\sigma=0`$.
Then $`x\pm ty`$ stay in the same sign face and have norm two for small
$`t\gt 0`$, contradicting extremality. Thus a vertex spans a one-dimensional
kernel on its support, with no zero coefficient: it is a circuit.
Conversely, equality in the triangle inequality forces any two feasible
points with midpoint (3) to be supported on $`S`$ with the same weak signs
there. The
one-dimensional kernel and the norm bound force them both to equal (3).

This also shows that every circuit has at most eleven coordinates:
$`|S|-1=\mathrm{rank}B_S\le10`$. Since (2) is a bounded polytope,
every point is a convex combination of these vertices. For a primitive
integer circuit $`c`$, write $`m=\sum_{c_\sigma\gt 0}c_\sigma`$; then
$`\|c\|_1=2m`$, and the two oriented vertices are $`\pm c/m`$.

## 2. Complete enumeration, including both orientations

Independent row and column relabelings act on permutations by
$`\sigma\mapsto c\circ\sigma\circ r`$. All 576 such maps are used.
They preserve (2), the row-norm product, and the inequality after relabeling
the entries of $`A`$. No transposition or inversion is used to discard cases.

The census starts with the empty support. At each size, it extends every
independent support representative by each missing permutation, takes the
minimum 24-bit support mask among all group images, and retains all distinct
representatives. It records a dependent extension as a circuit precisely
when its one-dimensional kernel has full support. Only independent supports
are extended further.

This is exhaustive by induction: remove one element from any independent
support, or any element from a circuit. The remaining independent support
has a retained group representative; extending that representative by the
image of the removed element recovers the required orbit. Thus discarding
dependent noncircuits cannot hide a circuit at a later size.

All rank decisions use arithmetic modulo 65521, which is checked prime.
They are exact rational rank decisions: every column of the original
incidence matrix has Euclidean norm two, so every minor of order
$`k\le10`$ has absolute determinant at most $`2^k\le1024\lt 65521`$.
The exact rational rank of the full matrix is ten; hence larger minors vanish.
A rationally nonzero minor therefore cannot vanish modulo this prime.
Minimal dependence is determined by ranks of a set and its deletions, so
the full-support kernel criterion is also preserved. The primitive kernel
of each recorded circuit is additionally reconstructed over $`\mathbb Q`$
and checked against all 16 literal marginal equations.

The complete results are:

| Support size | Support orbits | Oriented orbits | Labelled supports |
|---:|---:|---:|---:|
| 4 | 1 | 1 | 18 |
| 6 | 3 | 3 | 232 |
| 7 | 1 | 2 | 72 |
| 8 | 10 | 13 | 1,086 |
| 9 | 8 | 16 | 2,184 |
| 10 | 15 | 26 | 6,192 |
| 11 | 35 | 70 | 14,400 |
| **Total** | **73** | **131** | **24,184** |

There are 48,368 labelled signed vertices. A support-stabilizing group map
identifies the two signs for 15 of the 73 supports; both signs are retained
for the other 58. The census explicitly tests this vector equality and the
orbit/stabilizer identity for every support. Merely having the same support
does not identify signs.

The [default census](../evidence/census.py)
regenerates these cases with integer and rational arithmetic. A
[separate census audit](../evidence/audit_census.py)
uses exact rational elimination for every candidate and literal group actions,
without the modular rank test or mask lookup tables.

## 3. A quartic certificate suffices

For $`w_\sigma=1+x_\sigma`$, let

```math
W_w(A)=\sum_\sigma w_\sigma\prod_i a_{i,\sigma(i)},\qquad
 F_w(A)=\frac3{32}\left(\sum_{i,j}a_{ij}^2\right)^2-W_w(A).
 \qquad\text{(4)}
```

It suffices to prove $`F_w\ge0`$ for all real matrices for each of the
131 representative laws. In fact, the polynomial identity verified below is
stronger than restricting entries to be nonnegative.

The reduction to the required row product is exact. If a row is zero,
$`W_w(A)=0`$, so (1) is immediate. Otherwise set
$`r_i=(\sum_j a_{ij}^2)^{1/2}\gt 0`$, and apply $`F_w\ge0`$ to the matrix
$`a_{ij}/r_i`$. Its total squared norm is four, whence

```math
W_w(A)\le\frac32\prod_i r_i.
```

Divide by 24: the right side becomes $`\prod_i r_i/16`$, precisely the
right side of (1). For completeness, the converse also holds: the row-product
bound implies (4) by $`\prod_i r_i\le(\sum_i r_i^2/4)^2`$.

## 4. Exact positivity for every representative

Each certificate supplies lists of quadratic monomials $`m_b(A)`$, rational
matrices $`E_b`$, and rational symmetric matrices $`K_b`$, with the identity

```math
F_w(A)=\sum_{b=1}^{31}
       (E_b^{\mathsf T}m_b(A))^{\mathsf T}
       K_b(E_b^{\mathsf T}m_b(A)).
 \qquad\text{(5)}
```

Every $`K_b`$ is positive definite, certified by exact rational symmetric
elimination with strictly positive pivots. Thus every summand is nonnegative
for real $`A`$. This is a rational Gram certificate; factoring its positive
pivots also expresses it as squares with nonnegative rational weights.

The monomials use the literal variable index $`4i+j`$ for $`a_{ij}`$, with
zero-based indices. The numerical discovery grouped the 136 quadratic
monomials into one block of 16 squares and 30 blocks of four monomials using
row/column sign symmetries. Known equality points were removed as Gram
kernels before solving. Neither this symmetry heuristic nor the numerical
solver is trusted by the proof checker: (5) is expanded directly over
$`\mathbb Q`$, with all monomial coefficients compared to (4).

The [certificate file](../evidence/certificates.json)
contains all 131 identities. The independent
[literal verifier](../evidence/verify.py) checks:

1. Each supplied weight is exactly $`1\pm c_\sigma/m`$ for its required
   census record, and the complete set of oriented records is covered once.
2. Every weight is nonnegative, all 16 marginal sums are six, and
   $`\sum|w_\sigma-1|\le2`$.
3. All array lengths, dimensions, variable indices, and symmetry conditions
   are valid, and every Gram block has positive rational pivots.
4. Direct expansion of the quadratic forms equals the literal target (4)
   coefficient by coefficient, including monomials absent from the target.

There are 13,744 positive pivots across the certificates and 196 coefficient
keys in each expansion, some with zero target coefficient. The largest
denominator among saved $`K_b`$ entries is 504,000. The verifier uses only
Python's standard library and exact integers/Fractions. Floating-point
eigenvalues and solver status are used only during discovery, never acceptance.

Equation (5) proves the inequality for every representative. Row and column
relabeling proves it for every circuit vertex. Finally $`W_w`$, and also
$`F_w`$, is affine in $`x`$. Convex combinations therefore prove the same
inequality for every real $`x\in\mathcal P`$, not just rational laws.
This completes the universal lower bound $`R_4(2)\ge1/24`$.

## 5. Sharpness above the endpoint

Let $`D`$ be the nine derangements and $`T`$ the six transpositions in
$`S_4`$, with their uniform laws $`U_D,U_T`$. The signed measure

```math
m=\tfrac12\delta_{\mathrm{id}}+\tfrac12 U_D-U_T
```

has total mass zero, zero coordinate marginals, and signed TV norm one.
For a fixed diagonal cell its positive and negative masses are both
$`1/2`$; for a fixed off-diagonal cell both are $`1/6`$.
Hence $`\nu_\delta=u+\delta m`$ is balanced, nonnegative for
$`0\le\delta\le1/4`$, and has TV distance exactly $`\delta`$.
For $`a_{ij}=2\mathbf1_{i=j}`$, each row has normalized $`L^2`$ norm one,
while the left side of (1) is

```math
16\nu_\delta(\mathrm{id})=\frac23+8\delta.
```

It equals one at $`\delta=1/24`$ and exceeds one whenever
$`\delta\gt 1/24`$. For any $`r\gt 1/24`$, choose
$`\delta=1/24+\min\{(r-1/24)/2,1/48\}`$; then
$`1/24\lt \delta\lt r`$ and $`\delta\lt 1/4`$. This proves sharpness and finishes
the theorem.

## Scope and remaining questions

The theorem includes the exact closed radius, arbitrary real laws satisfying
the finite constraints, and all nonnegative real matrices with zeros allowed.
It is a global computer-assisted proof, not a sample or a family exclusion.
The finite calculations have been independently replayed and internally
reviewed. The subsequent [extension proof](EXTENSIONS.md) establishes the
complete nonnegative equality classification, sharp stability throughout
the ball, an explicit interior exponent, and entropy/tensorization applications.
The [prior-art comparison](PRIOR_ART.md) records the contribution boundary.
The endpoint, sharpness, and equality statements are included in the verified
Lean development. Worldwide priority, external human peer review, and a
shorter analytic endpoint proof remain unestablished.
