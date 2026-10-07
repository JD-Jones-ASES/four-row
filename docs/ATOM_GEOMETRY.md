# Exact atom bounds and the geometry of equality laws

This note proves two extensions of the four-row result: the exact maximum
mass of an atom at every total-variation radius, and the complete simplex
description of laws that attain the small-radius atom bound. The latter
identifies every law permitting nonconstant equality in the permanent
inequality at its sharp endpoint.

**Scope and provenance.** These supplementary results were derived in the
October 7, 2026 GPT-6 Pro pre-submission review and checked mathematically
while incorporating that review. The proofs below are informal mathematical
arguments; they are **not additional Lean-verified claims**. The submission's
formal scope remains the sixteen compared declarations in
[THEOREMS.md](THEOREMS.md). The review also supplied uncompiled candidate
Lean extensions, which are outside that submission contract.

The independent exact replay [atom_geometry.py](../evidence/atom_geometry.py)
checks the finite rational identities, attaining-law endpoints, trade
incidence, and vertex counts. The arbitrary-real statements and equality
classifications rely on the arguments below; finite replay does not replace
those proofs or establish Lean verification. No new circuit census or
permanent certificate is needed for these arguments.

Let $`u`$ be uniform on $`S_4`$. Write $`\mathcal B_r`$ for the balanced probability
laws at total-variation distance at most $`r`$ from $`u`$, using the definitions
in [THEOREMS.md](THEOREMS.md). All permutations below act on the labels
$`1,2,3,4`$. Products such as $`(12)(34)`$ denote disjoint transpositions.

## 1. The exact atom envelope at every radius

For every $`r\ge0`$ and every prescribed permutation $`\tau`$,

```math
\max_{\nu\in\mathcal B_r}\nu(\tau)
=M(r):=\min\left\{\frac1{24}+\frac r2,
                  \frac5{48}+\frac r4,\frac14\right\}.
```

Equivalently,

```math
M(r)=
\begin{cases}
\frac1{24}+\frac r2,&0\le r\le\frac14,\\[2pt]
\frac5{48}+\frac r4,&\frac14\le r\le\frac7{12},\\[2pt]
\frac14,&r\ge\frac7{12}.
\end{cases}
```

All maxima are attained. In particular, $`7/12`$ is the exact minimum TV
distance at which a balanced law can put mass $`1/4`$ on one permutation.

### Upper bounds

Column relabeling reduces to $`\tau=\mathrm{id}`$. Put
$`\mu=\nu-u`$ and $`\delta=d_{\mathrm{TV}}(\nu,u)`$. Let $`h(\sigma)`$ be the
number of fixed points of $`\sigma`$. Balance and total mass imply

```math
\sum_\sigma\mu(\sigma)=0,
\qquad
\sum_\sigma h(\sigma)\mu(\sigma)=0.
```

Define

```math
b(\sigma)=4\mathbf1_{\sigma=\mathrm{id}}-h(\sigma)+1.
```

The coefficient $`b`$ is $`+1`$ on the identity and all derangements, $`-1`$ on
transpositions, and $`0`$ on three-cycles. Thus $`|b|\le1`$, and

```math
4\mu(\mathrm{id})=\sum_\sigma b(\sigma)\mu(\sigma)
\le\sum_\sigma|\mu(\sigma)|=2\delta.
```

This proves the first bound $`\nu(\mathrm{id})\le1/24+\delta/2`$.

For the second bound, let $`a=\nu(\mathrm{id})`$, and let $`T,C,D`$ be the
total masses of transpositions, three-cycles, and derangements. Then

```math
a+T+C+D=1,\qquad 4a+2T+C=1.
```

The uniform mass of the identity together with the nine derangements is
$`10/24=5/12`$. Applying the event definition of TV distance to this set gives

```math
\delta\ge(a+D)-\frac5{12}
=\frac7{12}-T-C
=4a+T-\frac5{12}
\ge4a-\frac5{12}.
```

Hence $`a\le5/48+\delta/4`$. Finally, $`a\le1/4`$ follows by placing the
identity atom inside any one of its uniform coordinate-marginal events.
Replacing $`\delta`$ by $`r`$ proves the envelope upper bound.

### Attaining laws

For $`0\le r\le1/4`$, the existing extremal family

```math
\nu_r=u+r\left(\tfrac12\delta_{\mathrm{id}}
        +\tfrac12\mathrm{Unif}(D)-\mathrm{Unif}(T)\right)
```

has exact TV distance $`r`$ and identity mass $`1/24+r/2`$.

For $`1/4\le r\le7/12`$, use the following weights. The entries in the last
column are the weights of **each individual permutation** in that class.

| Permutation class | Number | Individual weight |
|---|---:|---:|
| Identity | 1 | $`5/48+r/4`$ |
| Transpositions | 6 | $`0`$ |
| Three-cycles | 8 | $`7/96-r/8`$ |
| Derangements | 9 | $`5/144+r/12`$ |

The weights are nonnegative and sum to one. Conjugation invariance makes
all diagonal marginals equal and all off-diagonal marginals equal. Their
fixed-point expectation is one, which gives all sixteen marginals $`1/4`$.
The identity and derangement weights are at least their uniform weights;
the other weights are at most their uniform weights. Direct subtraction
therefore gives exact TV distance $`r`$.

At $`r=1/4`$, this law agrees with the first family. At $`r=7/12`$, it puts
mass $`1/4`$ on the identity, mass $`1/12`$ on each derangement, and zero
elsewhere. The last law also attains the envelope for every larger radius.
Column relabeling places the distinguished atom at any $`\tau`$.

## 2. Saturation forces an exact sign pattern

Fix $`r\gt 0`$ and suppose $`\nu\in\mathcal B_r`$ satisfies

```math
\nu(\mathrm{id})=\frac1{24}+\frac r2.
```

The inequalities proving the first atom bound must all be equalities. In
particular, $`\delta=r`$, and

```math
0=2\delta-4\mu(\mathrm{id})
=\sum_\sigma\bigl(|\mu(\sigma)|-b(\sigma)\mu(\sigma)\bigr).
```

Each summand is nonnegative. Their vanishing gives the complete sign and
support restrictions:

- The identity and derangement deviations are nonnegative.
- The transposition deviations are nonpositive.
- Every three-cycle deviation is zero.

Normalize $`x=\mu/r`$. Then $`x(\mathrm{id})=1/2`$, its total positive and
negative masses are both one, and all its coordinate marginals are zero.
These conclusions are exact; they do not use numerical optimization.

## 3. The six vertices

For a perfect matching $`\{ab,cd\}`$ of the four labels, define

```math
q_{ab\mid cd}
=\frac12\bigl(\delta_{\mathrm{id}}+\delta_{(ab)(cd)}
                         -\delta_{(ab)}-\delta_{(cd)}\bigr).
```

There are three such vectors, indexed by $`12\mid34`$, $`13\mid24`$, and
$`14\mid23`$.

For a four-cycle $`c`$, considered together with its inverse, let $`E(c)`$ be
the four unoriented edges of that cycle and define

```math
q_c=\frac12\delta_{\mathrm{id}}
     +\frac14\bigl(\delta_c+\delta_{c^{-1}}\bigr)
     -\frac14\sum_{ab\in E(c)}\delta_{(ab)}.
```

There are three inverse pairs, represented by $`(1234)`$, $`(1243)`$, and
$`(1324)`$. Each of the six $`q`$ vectors has zero marginals, signed TV norm
one, and identity coordinate $`1/2`$.

For $`0\le r\le1/12`$, every $`u+rq`$ is nonnegative: the largest negative
coefficient among all six vectors is $`-1/2`$, and
$`1/24-r/2\ge0`$. Consequently these are six laws in $`\mathcal B_r`$, all
attaining the atom bound. The first three have four nonzero deviations;
the last three have seven. Throughout this note, four-support and seven-support
refer to the support of the deviation from uniform, not to the number of
atoms with positive probability.

## 4. Every saturating law has unique barycentric coordinates

**Simplex theorem.** For each $`0\lt r\le1/12`$, the face

```math
F_{\mathrm{id}}(r)
=\left\{\nu\in\mathcal B_r:
              \nu(\mathrm{id})=\frac1{24}+\frac r2\right\}
```

is exactly the convex hull of the six laws $`u+rq`$ above. These six laws
are affinely independent, so the face is a five-dimensional simplex and
every law in it has unique barycentric coordinates.

Here is an explicit proof of completeness. The preceding sign restrictions
leave only the identity, six transpositions, and nine derangements in the
support of $`x`$. Write $`\alpha_1,\alpha_2,\alpha_3`$ for its values at

```math
(12)(34),\qquad(13)(24),\qquad(14)(23).
```

First, the deviations at each four-cycle and its inverse are equal. To see
this, write $`z_1,z_2,z_3`$ for their differences for the representatives
$`(1234),(1243),(1324)`$. Subtract the marginal equation for cell $`(j,i)`$
from that for $`(i,j)`$. The transposition and double-transposition terms
cancel. The cell pairs $`12`$, $`34`$, and $`13`$ give, respectively,

```math
z_1+z_2=0,\qquad z_1-z_2=0,\qquad -z_2+z_3=0.
```

Thus all three differences vanish. Let $`\beta_1,\beta_2,\beta_3`$ be the
common values within the three inverse pairs. All six parameters
$`\alpha_i,\beta_i`$ are nonnegative.

The six transposition deviations are now forced by the off-diagonal
marginal equations:

| Transpositions | Deviation of each |
|---|---|
| $`(12),(34)`$ | $`-(\alpha_1+\beta_1+\beta_2)`$ |
| $`(13),(24)`$ | $`-(\alpha_2+\beta_2+\beta_3)`$ |
| $`(14),(23)`$ | $`-(\alpha_3+\beta_1+\beta_3)`$ |

A diagonal marginal equation then gives

```math
\alpha_1+\alpha_2+\alpha_3
       +2(\beta_1+\beta_2+\beta_3)=\frac12.
```

Consequently the six nonnegative numbers

```math
(\lambda_1,\ldots,\lambda_6)
=(2\alpha_1,2\alpha_2,2\alpha_3,
  4\beta_1,4\beta_2,4\beta_3)
```

sum to one and reconstruct $`x`$ as the corresponding combination of the
six $`q`$ vectors. This proves existence of the decomposition.

For uniqueness, each double-transposition coordinate occurs positively in
exactly one of the first three vectors, and each chosen four-cycle
coordinate occurs positively in exactly one of the last three. Those six
coordinates recover all six $`\lambda_i`$ directly. Since $`r\gt 0`$, the same
recovery works for the laws $`u+rx`$. This also proves affine independence.

The necessity of the decomposition remains valid at any larger radius for
which the first atom bound is saturated. For $`r\gt 1/12`$, some displayed
vertices have negative law weights, so probability imposes additional
inequalities on the barycentric coordinates. The full-simplex assertion
above is restricted to its stated range. At $`r=0`$, all six laws coincide
with $`u`$, and uniqueness is not asserted.

For a prescribed $`\tau`$, replace $`\nu`$ by the column-relabelled law
$`\sigma\mapsto\nu(\tau\sigma)`$. This gives the same complete description
of $`F_\tau(r)`$.

## 5. Intersections of the twenty-four atom faces

For $`0\lt r\le1/12`$, two distinct faces $`F_\tau(r)`$ and $`F_\pi(r)`$ meet
if and only if $`\tau^{-1}\pi`$ is a double transposition. In that case
their intersection is the single corresponding four-support vertex law.
No three distinct atom faces meet.

To prove the assertion, relabel $`\tau`$ to the identity and put
$`\gamma=\tau^{-1}\pi`$. Each of the two saturated atoms has positive
deviation $`r/2`$. They exhaust the total positive deviation $`r`$, so all
other positive deviations vanish. The sign pattern from the identity face
forces $`\gamma`$ to be a derangement and all negative deviations to be on
transpositions.

At the cell $`(i,\gamma(i))`$, the negative deviation can come only from
the transposition $`(i\,\gamma(i))`$, since all three-cycle deviations
vanish and the only positive atoms are the identity and $`\gamma`$. That
transposition must have deviation $`-r/2`$. A four-cycle would force four
distinct such transpositions and negative mass $`2r`$, a contradiction.
A double transposition forces exactly its two constituent transpositions,
each with deviation $`-r/2`$. This is the stated unique vertex. Two positive
atoms already exhaust the positive mass budget, excluding any third
saturated atom.

There are therefore exactly:

- $`24`$ five-dimensional atom simplices;
- $`24\cdot3/2=36`$ four-support vertices, each shared by two simplices;
- $`24\cdot3=72`$ seven-support vertices, each belonging to one simplex;
- $`108`$ distinct vertices in their union.

The adjacency graph of these simplices consists of six disjoint copies of
$`K_4`$: adjacency means that the labels lie in the same coset of the normal
Klein four subgroup consisting of the identity and the three double
transpositions. The pairwise intersections within a component are distinct
points; no assertion of a common intersection of three or four simplices
is intended. These intersection and counting statements are mathematical
consequences proved here, not additional mechanically checked Lean claims
in this revision.

## 6. Consequences for permanent and stability equality

At the permanent endpoint $`r=1/24`$, an atom is saturated precisely when
its mass is $`1/16`$. Combining the existing complete matrix-side equality
classification with the simplex theorem describes every law permitting
nonconstant normalized equality: it belongs to one of the twenty-four
simplices above. Its nonconstant equality matrices are exactly twice the
permutation matrices corresponding to its saturated atoms.

Such a law has one or two nonconstant normalized equality matrices. It has
two exactly at one of the thirty-six shared four-support vertices. All
other laws in the union have one. Laws outside the union have only the
all-ones normalized equality matrix. Arbitrary positive row rescaling and
zero-row cases are handled by the original equality theorem.

There is also a complete positive-radius equality description for the sharp
stability inequality. If $`0\lt r\le1/24`$, $`\nu\in\mathcal B_r`$, and the rows
are nonnegative and probability-L²-normalized, then

```math
1-T_\nu(A)=\frac{1-24r}{9}\operatorname{varianceSum}(A)
```

holds exactly when $`A`$ is all ones, or $`A`$ is twice a permutation matrix
for an atom satisfying $`\nu(\tau)=1/24+r/2`$.

For $`0\lt r\lt 1/24`$, the proof of sharp stability writes the deficit as a
nonnegative weighted sum of a uniform stability gap and an endpoint gap
for $`\nu'=u+(\nu-u)/(24r)`$. This is a balanced probability law in
$`\mathcal B_{1/24}`$: its TV distance is at most $`1/24`$, and
$`|\nu(\sigma)-u(\sigma)|\le d_{\rm TV}(\nu,u)\le r`$ ensures
$`\nu'(\sigma)\ge0`$. Equality forces the endpoint gap to vanish,
because its coefficient $`24r`$ is positive. The existing endpoint equality
theorem gives all ones or twice a permutation matrix, and
$`\nu'(\tau)=1/16`$ is equivalent to $`\nu(\tau)=1/24+r/2`$. Both displayed
matrix types also attain the uniform stability bound, proving sufficiency.
At $`r=1/24`$, this is the endpoint equality theorem itself. No equality
classification at radius zero is inferred from this argument.

## 7. Exact atom obstructions and the exponent-four regime

Suppose a common positive exponent $`p`$ satisfies the row-product inequality
for every law in $`\mathcal B_r`$. Take the four matching indicator rows
$`f_i(j)=\mathbf1_{j=\tau(i)}`$. Their product expectation is $`\nu(\tau)`$,
and the product of their four probability-$`L^p`$ norms is $`(1/4)^{4/p}`$.
Applying this to an attaining law from Section 1 gives the necessary condition

```math
M(r)\le(1/4)^{4/p},
\qquad
p\ge\frac{4\log4}{-\log M(r)}.
```

This extends the singleton obstruction through the second facet of the atom
envelope. It is not a sufficiency assertion for the intermediate radii.
At $`r=0`$ it gives the uniform-law singleton obstruction
$`4\log4/\log24`$; at $`r=1/24`$ it gives $`p\ge2`$; at $`r=1/4`$ it gives
$`p\ge4\log4/\log6`$; and at $`r=7/12`$ it gives $`p\ge4`$.

Exponent four is sufficient for every balanced probability law, without any
restriction on total variation. For rows normalized so that
$`\tfrac14\sum_j f_i(j)^4=1`$, average the elementary identity

```math
\sum_{i=1}^4 a_i^4-4a_1a_2a_3a_4
=(a_1^2-a_2^2)^2+(a_3^2-a_4^2)^2
 +2(a_1a_2-a_3a_4)^2\ge0
```

with $`a_i=f_i(\sigma(i))`$. Balance makes the expected sum of fourth
powers equal to four, so the product expectation is at most one. Undoing
row normalization proves the exponent-four inequality; zero rows are
immediate. Probability-$`L^p`$ norm monotonicity gives every $`p\ge4`$.
This is an elementary proof of the usual Hölder mechanism, not a new
Hölder inequality.

At $`r=7/12`$, the attaining law has identity mass $`1/4`$, derangement mass
$`1/12`$ each, and zero mass on other permutations. It belongs to every
larger ball. Its matching rows violate the exponent-$`p`$ inequality for
every $`0\lt p\lt 4`$. Thus, for every $`r\ge7/12`$,

```math
\bigl[\text{the exponent-}p\text{ inequality holds for all laws in }\mathcal B_r\bigr]
\quad\Longleftrightarrow\quad p\ge4
\qquad(p>0).
```

This establishes the exact common-exponent regime on that whole range. It
does not establish that $`7/12`$ is the first radius requiring exponent four,
or determine the optimal exponent at intermediate radii.

The original sharpness family corresponds to the interior barycentric
coordinates $`(1/9,1/9,1/9,2/9,2/9,2/9)`$ in the small-radius atom simplex.
The present classification therefore contains that family and explicitly
describes every other saturating law in the stated range.
