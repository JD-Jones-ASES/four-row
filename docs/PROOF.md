# Exact local robustness of permutation permanent inequalities

This supplementary mathematical note proves a local theorem in arbitrary
dimension using the published uniform-law theorem of Bristiel–Caputo.
Its general local theorem is not one of the sixteen compared Lean statements.
The separate [endpoint proof](ENDPOINT.md) establishes the exact four-row
radius independently of the published input used here; its Lean coverage is
listed in [THEOREMS.md](THEOREMS.md).

## Definitions and theorem

Let $`n\ge3`$, let $`u`$ be uniform on $`S_n`$, and set

```math
a=p_c(n)=\frac{n\log n}{\log(n!)}.
```

A probability law $`\nu`$ is **balanced** if

```math
\nu\{\pi:\pi(i)=j\}=1/n\quad(1\le i,j\le n).
```

Use $`d_{\rm TV}(\nu,u)=\frac12\sum_\pi|\nu(\pi)-u(\pi)|`$, and use
uniform probability measure on $`[n]`$ for all row norms and inner products.
For $`p\gt 1`$, define

```math
K_p(\nu)=\sup_{f_i\ge0,\ f_i\ne0}
 \frac{\mathbb E_\nu\prod_{i=1}^n f_i(\pi(i))}
 {\prod_{i=1}^n\|f_i\|_p}.
```

**Theorem 1.** There is $`\eta_n\gt 0`$ such that, for every balanced $`\nu`$,

```math
|p-a|\lt \eta_n,\qquad d_{\rm TV}(\nu,u)\lt \eta_n
 \quad\Longrightarrow\quad
 K_p(\nu)=\max\{1,n^{n/p}\max_\sigma\nu(\sigma)\}.
 \qquad\text{(1)}
```

The formula holds on both sides of $`a`$ locally. The neighborhood is not
numerically quantified. Constants and single-permutation supports are the
only possible sources of the norm value in this neighborhood; the theorem
does not classify every equality case for every perturbed law.

## Published input and equality normalization

The input is the sharp uniform-law permanent inequality of
[Bristiel–Caputo, Corollary 1.14 and §4.3](https://arxiv.org/html/2109.06009v3):
at $`p=a`$, $`K_a(u)=1`$, with nonzero extremizers given by row-scaled constant
matrices or row-scaled permutation matrices. The proof uses their entropy
inequality and its constant-or-Dirac equality classification. This input is
accepted from the published argument, not re-proved or kernel checked here.

Here is the precise bridge to row-normalized equality; the paper's shorthand
about scalar multiplication should not hide independent row scaling.
Normalize $`\|f_i\|_a=1`$ and suppose $`\mathbb E_u\prod_i f_i=1`$.
Then $`\rho(\pi)=\prod_i f_i(\pi(i))`$ is a density relative to $`u`$.
Write $`\rho_i`$ for its marginal density relative to uniform measure on
$`[n]`$. Nonnegativity of relative entropy and the cited entropy inequality give

```math
a\mathrm{Ent}(\rho)
 =\sum_i\mathbb E[\rho_i\log f_i^a]
 \le\sum_i\mathrm{Ent}(\rho_i)
 \le a\mathrm{Ent}(\rho).
```

The first inequality is equality only if $`\rho_i=f_i^a`$ for every $`i`$.
Zeros cause no difficulty: $`\rho_i`$ vanishes wherever $`f_i`$ vanishes.
The second forces $`\rho`$ to be constant or a Dirac density. Its marginals
then force the corresponding row functions to be constant or matching
singletons. This is also the equality correspondence in
[Carlen–Cordero-Erausquin, Theorem 2.2](https://arxiv.org/html/0710.0870v2).
Merely knowing that a product over permutations is constant would not suffice.

Normalize instead each row mean to one. The domain

```math
X=\{f_i(j)\ge0:\ n^{-1}\sum_j f_i(j)=1\text{ for every }i\}
```

is compact, since each entry is at most $`n`$. Its critical equality set is
exactly the constant point and the $`n!`$ points

```math
f_i(j)=n\mathbf1_{j=\sigma(i)}.
```

Rows identically zero need no separate estimate: both sides of the underlying
inequality vanish. For $`n\ge3`$,

```math
n/(n-1)\lt a\lt 2.
```

The first follows from $`n!\lt n^{n-1}`$. For the second, multiply
$`k(n+1-k)\ge n`$ over $`k`$; an interior factor is strict when $`n\ge3`$,
so $`(n!)^2\gt n^n`$. Fix

```math
n/(n-1)\lt p_-\lt a\lt p_+\lt 2,\qquad I=[p_-,p_+].
```

## Proof near the constant point

Write $`f_i=1+g_i`$, with row means zero, and put

```math
V_i=\|g_i\|_2^2,\qquad V=\sum_iV_i,\qquad
 b=\max_i\|g_i\|_\infty,\qquad\delta=d_{\rm TV}(\nu,u).
```

Exact balanced marginals kill the linear terms. Under $`u`$,

```math
\sum_{i\lt j}\mathbb E_u[g_i(\pi(i))g_j(\pi(j))]
 =\frac{V-\|\sum_i g_i\|_2^2}{2(n-1)}
 \le\frac{V}{2(n-1)}.
 \qquad\text{(2)}
```

Since $`\|g_i\|_\infty\le\sqrt{n-1}\sqrt{V_i}`$, changing the law
changes this quadratic sum by at most

```math
2\delta(n-1)\sum_{i\lt j}\sqrt{V_iV_j}
 \le\delta(n-1)^2V.
 \qquad\text{(3)}
```

For a set $`S`$ of $`k\ge3`$ rows, bound all but two factors by $`b`$, use
Cauchy–Schwarz for the remaining pair, and average over pairs. Balanced
marginals give

```math
\left|\mathbb E_\nu\prod_{i\in S}g_i(\pi(i))\right|
 \le\frac{b^{k-2}}k\sum_{i\in S}V_i.
```

Thus all terms of degree at least three contribute at most

```math
V\sum_{k=3}^n\frac{\binom{n-1}{k-1}}k b^{k-2}=O_n(bV)
 \quad(b\le1).
 \qquad\text{(4)}
```

Uniformly over $`p\in I`$, Taylor expansion for $`b\le1/2`$ gives

```math
\prod_i\|1+g_i\|_p=1+\frac{p-1}{2}V+O_{n,I}(bV).
 \qquad\text{(5)}
```

All derivatives are bounded on $`I\times[1/2,3/2]`$; cross products of row
variances are $`O_n(b^2V)`$. Since
$`(p_--1)/2\gt 1/[2(n-1)]`$, (2)–(5) give fixed $`b_0,\delta_0\gt 0`$ such that

```math
b\lt b_0,\quad\delta\le\delta_0,\quad p\in I
 \quad\Longrightarrow\quad
 \mathbb E_\nu\prod_i f_i(\pi(i))\le\prod_i\|f_i\|_p.
 \qquad\text{(6)}
```

This is one fixed open neighborhood $`U_0\subset X`$ of the constant point.

## Proof near a permutation point

Fix $`\sigma`$ and, by row homogeneity, set $`f_i(\sigma(i))=1`$.
Write $`x_{ij}=f_i(j)`$ off this matching, and suppose $`0\le x_{ij}\lt r\le1`$.
Set

```math
S_2=\sum_{i,j\ne\sigma(i)}x_{ij}^2,\quad
 S_p=\sum_{i,j\ne\sigma(i)}x_{ij}^p,\quad
 s_i=\sum_{j\ne\sigma(i)}x_{ij}^p.
```

Every other permutation moves at least two positions. Use
$`xy\le(x^2+y^2)/2`$ there and bound the other factors by one. For every
probability law, without any balance or closeness requirement,

```math
\mathbb E_\nu\prod_i f_i(\pi(i))\le\nu(\sigma)+S_2/2.
 \qquad\text{(7)}
```

Put $`C=\max\{1,n^{n/p}\max_\tau\nu(\tau)\}`$ and
$`k_0=n^{-n/p_-}`$. Choose $`r`$ with $`(n-1)r^{p_-}\le1`$.
Then $`s_i\le1`$, and for $`s\in[0,1]`$, $`p\in I`$,

```math
(1+s)^{1/p}\ge1+s/(2p_+).
```

Consequently

```math
C\prod_i\|f_i\|_p
 =Cn^{-n/p}\prod_i(1+s_i)^{1/p}
 \ge\nu(\sigma)+\frac{k_0}{2p_+}S_p.
 \qquad\text{(8)}
```

Also $`S_2\le r^{2-p_+}S_p`$. Shrink $`r`$ until
$`r^{2-p_+}\le k_0/p_+`$. Combining (7) and (8) proves the bound by $`C`$
on a fixed open neighborhood $`U_\sigma\subset X`$. The strict inequality
$`p_+\lt 2`$ is essential here; this argument does not reach exponent two.

## Compact complement and completion

The compact set $`Y=X\setminus(U_0\cup\bigcup_\sigma U_\sigma)`$ contains
no equality point at $`(u,a)`$. If nonempty, it has a positive minimum gap

```math
\min_{f\in Y}\left(\prod_i\|f_i\|_a-
                  \mathbb E_u\prod_i f_i(\pi(i))\right)\gt 0.
```

Joint continuity in the finite-dimensional variables $`f,p,\nu`$ preserves
the inequality with constant one throughout $`Y`$ for $`(p,\nu)`$ close
enough to $`(a,u)`$. Shrink the neighborhood to lie in $`I`$ and have
$`\delta\le\delta_0`$. All regions now give the upper bound in (1).
Constants attain one; singleton rows attain $`n^{n/p}\nu(\sigma)`$.
This proves Theorem 1. Compactness is the only nonquantitative step.

## Exact sensitivity of one atom

**Lemma 2.** Every balanced $`\nu`$ satisfies

```math
\nu(\sigma)-1/n!\le\frac{n-2}{n}d_{\rm TV}(\nu,u).
 \qquad\text{(9)}
```

Relabel $`\sigma=\mathrm{id}`$ and let $`\mu=\nu-u`$. If
$`\mu(\mathrm{id})\le0`$, there is nothing to prove. Otherwise use the
fixed-point count $`h(\pi)`$. Balance gives $`\sum_\pi\mu(\pi)h(\pi)=0`$.
The positive part contributes at least $`n\mu(\mathrm{id})`$; every term
in the negative part has $`h\le n-2`$, and its total mass is $`\delta`$.
This proves (9).

The coefficient is attained near $`u`$. Let $`D`$ be the derangements and
$`T`$ the transpositions, with uniform probability laws $`U_D,U_T`$. Put

```math
m=\frac{n-2}{n}\delta_{\mathrm{id}}+\frac2n U_D-U_T.
 \qquad\text{(10)}
```

The supports are disjoint for $`n\ge3`$, its signed TV norm is one, and
all its coordinate marginals are zero: the diagonal masses are $`(n-2)/n`$
on each side, and the off-diagonal masses are $`2/[n(n-1)]`$ on each side.
Thus $`u+\delta m`$ is balanced and nonnegative whenever

```math
0\le\delta\le\binom n2/n!=1/[2(n-2)!].
```

For $`n=4`$, $`m`$ adds $`1/2`$ at the identity and $`1/18`$ at each of nine
derangements, and subtracts $`1/6`$ at each of six transpositions.

## Exact local radius and sharp upper endpoint at exponent two

For $`p\ge a`$, define $`R_n(p)`$ to be the supremum of radii $`r\ge0`$ for
which every balanced law within TV distance $`r`$ of $`u`$ has $`K_p\le1`$.

**Corollary 3.** There is $`\alpha_n\gt 0`$ such that

```math
R_n(p)=\frac n{n-2}\left(n^{-n/p}-\frac1{n!}\right)
 \quad(a\le p\lt a+\alpha_n).
 \qquad\text{(11)}
```

Choose $`\alpha_n`$ small enough that the displayed radius is inside the
neighborhood of Theorem 1 and below the positivity threshold in (10).
Lemma 2 and Theorem 1 prove sufficiency, including the closed-radius
boundary. For any larger radius, take a slightly larger $`\delta`$ still
below that positivity threshold: (10) and singleton rows violate the
inequality. This also proves $`R_n(a)=0`$. For $`p\lt a`$, even $`u`$ fails,
so no nonnegative radius has the property.

In particular, with $`a=4\log4/\log24`$,

```math
R_4(p)=2(4^{-4/p}-1/24)\quad\text{for }a\le p\lt a+\alpha_4,
 \qquad R'_4(a+)=\frac{\log4}{3a^2}.
 \qquad\text{(12)}
```

At $`p=2`$, this construction by itself proves the upper bound

```math
R_4(2)\le1/24.
 \qquad\text{(13)}
```

Indeed $`f_i(j)=2\mathbf1_{j=i}`$ has row $`L^2`$ norm one and expectation
$`16(1/24+\delta/2)=2/3+8\delta`$. It exceeds one as soon as
$`\delta\gt 1/24`$, with feasible laws through $`\delta=1/4`$.
**The matching lower bound is now proved by the separate
[exact certificate argument](ENDPOINT.md).** The local proof above
does not extrapolate to this endpoint.

## An explicit, coarse sufficient radius

**Proposition 4.** For $`n=4`$, every balanced $`\nu`$ satisfies $`K_p(\nu)\le1`$
provided

```math
a\lt p\le2,\qquad d_{\rm TV}(\nu,u)\le\frac{p-a}{324p}.
 \qquad\text{(14)}
```

This uses only the critical uniform inequality, not its equality
classification or compactness. Normalize row means to one, so $`0\le f\le n`$.
Interpolation between $`L^1`$ and $`L^p`$ yields

```math
\log\|f\|_p-\log\|f\|_a
 \ge\frac{p-a}{p(a-1)}\log\|f\|_a.
```

Strong convexity of $`t^a`$ on $`[0,n]`$, using $`a\lt 2`$, gives

```math
\mathbb E f^a\ge1+\frac{a(a-1)n^{a-2}}2\mathrm{Var}(f).
```

Also $`1\le\mathbb E f^a\le n^{a-1}`$, so
$`\log z\ge(z-1)/n^{a-1}`$ in this range implies

```math
\log\|f\|_a\ge\frac{a-1}{2n}\mathrm{Var}(f).
```

Sum over rows and use $`e^t-1\ge t`$ and
$`\prod_i\|f_i\|_a\ge1`$ (Jensen) to obtain

```math
\prod_i\|f_i\|_p-\prod_i\|f_i\|_a\ge\frac{p-a}{2np}V.
 \qquad\text{(15)}
```

For $`n=4`$, set $`g_i=f_i-1`$. Pointwise on permutations the remainder
$`Q=\prod_i(1+g_i)-1-\sum_i g_i`$ is at most $`81V/4`$ in absolute value.
To see this, Taylor expand $`t\mapsto\prod_i(1+tg_i)`$ with integral
remainder, use $`|g_i|\le\sqrt{3V_i}`$, and bound the other two factors by
$`(1+3t)^2`$. The required constants are

```math
2\int_0^1(1-t)(1+3t)^2\,dt=9/2,\qquad
 \sum_{i\lt j}|g_i g_j|\le(9/2)V.
```

Balance cancels the constant and linear perturbations, so the law change
costs at most $`(81/2)\delta V`$. The uniform critical inequality and (15)
give (14). Consequently this argument gives the coarse bracket

```math
\frac{2-a}{648}\le R_4(2)\le\frac1{24}.
```

This coarse lower bound is weaker than the sharp endpoint established by
the separate [endpoint proof](ENDPOINT.md).
