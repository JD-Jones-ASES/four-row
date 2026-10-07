# A concrete four-site shuffle input

This supplementary note verifies an explicit local input to the permutation-moment
argument in OpenAI's *A strict four-row permanent inequality and permutation
moments*, [§3](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-strict-four-row-permanent-inequality-and-permutation-moments-September-26-2026/build/sections/03-recursion.tex).
The tree-parameter comparison uses §6 of the same source. This calculation
is outside the sixteen compared Lean statements and does not establish a
global mixing-time estimate. The exact [finite-group replay](../evidence/shuffle_input.py)
is included in the packaged evidence.

Label the square $`\{0,1,2,3\}`$. Let $`H`$ average the independent fair
switches $`(01),(23)`$, and $`V`$ average $`(02),(13)`$. Products act on the
rightmost permutation first. A two-axis sweep is $`M=VH`$, and its
self-adjoint column operator is $`\mu=M^*M=HVH`$, since the layer averages
are self-adjoint projections. The column law for even moment $`2k`$ is
$`\mu^{*k}`$, with convolution powers understood.

Let $`D`$ be the order-eight subgroup preserving the unordered partition
$`\{\{0,1\},\{2,3\}\}`$. Let $`d`$ and $`u`$ be uniform on $`D`$ and
$`S_4`$, respectively. Direct exact group calculation gives

```math
\mu=\tfrac14d+\tfrac34u,\qquad d*d=d,\quad d*u=u*d=u,\quad u*u=u.
```

Consequently, by induction for every integer $`k\ge1`$,

```math
\mu^{*k}=4^{-k}d+(1-4^{-k})u,\qquad
 d_{\rm TV}(\mu^{*k},u)=\tfrac23\,4^{-k}.
 \qquad\text{(C)}
```

The TV formula follows from the eight positive atom deviations on $`D`$
and sixteen negative deviations off it. The subgroup $`D`$ is transitive,
so all these laws are balanced. The all-$`k`$ assertion follows from the
displayed idempotent algebra, not from checking several numerical powers.

| Column power $`k`$ | Even moment $`2k`$ | Exact TV distance | Input supplied by the robust theorem |
|---:|---:|---:|---|
| 1 | 2 | $`1/6`$ | Outside the proved radius |
| 2 | 4 | $`1/24`$ | Closed endpoint, exponent 2 |
| 3 | 6 | $`1/96`$ | Explicit exponent $`95/48\lt 2`$ |
| $`k\ge3`$ | $`2k\ge6`$ | $`(2/3)4^{-k}\le1/96`$ | Exponent $`95/48`$ works uniformly; $`p((2/3)4^{-k})`$ also works |

Here $`p(r)=2-(1-24r)/36`$, from [Theorem 2](EXTENSIONS.md#2-an-explicit-exponent-below-two).
The table does not rule out a better exponent for the particular $`k=2`$
law; the sharp obstruction at the full endpoint ball concerns another law.
Likewise being outside the ball at $`k=1`$ is not by itself a counterexample.

At $`k=3`$ the predecessor's trace exponent and its strict margin are

```math
\theta=1-1/p=47/95,\qquad \tfrac12-\theta=1/190.
```

In its tree-parameter selection, take
$`\delta=(1/2-\theta)/2=1/380`$. Then
$`b=\theta/(1/2-\delta)=188/189`$ and $`\eta=(1-b)/2=1/378`$.
These are exact positive choices for that stage of the argument.
For $`0\le r\lt 1/24`$, our exponent gives

```math
\theta(r)=\frac{35+24r}{71+24r},\quad
 \tfrac12-\theta(r)=\frac{1-24r}{142+48r},\quad
 \eta(r)=\frac{1-24r}{282+144r}
```

under the same half-margin choice of $`\delta`$. This $`\theta`$ is distinct
from the coordinate-observation contraction coefficient $`p/4`$.

**Application boundary.** Moment six suffices for the *local permanent-input
condition*. The paper's global shuffle theorem also requires sparse-case
bounds, cutoff choices, finite-size spectral gaps, and a moment choice
satisfying those constraints.

Replay:

```bash
python3 evidence/shuffle_input.py
python3 -O evidence/shuffle_input.py
```

The replay checks subgroup orders and closure, adjoint and composition
conventions, every atom of the mixture and idempotent identities, balance,
the first three exact TV values, rational exponent substitutions, and three
deliberately corrupted controls. It uses no floating-point arithmetic.
