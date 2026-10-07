# Why the finite certificates cover every real law

The reduction is proved in `FourRow/Circuit.lean`, with the four-row specialization
in `Endpoint.lean`, `CertificateTransfer.lean`, and `EndpointTheorem.lean`.
There is no restriction to rational probability laws and no approximation of the
closed total-variation ball.

For a finite real vector `x`, `Circuit.mass x` is its sum of absolute values.
For any real linear subspace `K`, the body

```text
{x | x ∈ K and mass x ≤ r}
```

is compact and convex. The generic transfer theorem requires a family `C` of
nonzero kernel vectors such that every nonzero vector of `K` has a vector from
`C` supported inside its own support. This coverage condition is essential; a
list of valid Gram certificates alone is insufficient.

At an extreme point `x ≠ 0`, every supported kernel vector is proportional to
`x`. To prove this, subtract its multiple of `x` that makes the signed coordinate
sum zero. A sufficiently small displacement in this remaining direction stays
in the same closed orthant in both signs, so its absolute-coordinate sum is
unchanged. The two displaced vectors remain feasible and have midpoint `x`.
Extremality forces the direction to vanish. This argument is formalized over
real scalars, including coordinates that are zero.

An absolute linear bound on the support-covering family therefore holds at all
extreme points. The Mathlib Krein–Milman theorem and closedness of a linear
half-space extend the bound to the whole compact convex body. The normalized
interface requires the bound for both signs of each vector normalized to mass
`r`; the zero point is accounted for by the nonnegative bound. This avoids an
unformalized convex-combination or rational-density step.

For the four-row theorem, the independent-support extension census proves the
required support coverage. Exact scaled integer left inverses certify every
independent support, while explicit contained primitive circuits certify every
rejected extension. Row and column relabelings are a proved group action. The
146 signed primitive cases map to the 131 Gram representatives by exact rational
identities checked in Lean. Both signs are checked even where a relabeling
identifies them.

The centered vector of a law is `shiftedLaw ν p = 24 * ν (lexEquiv p) - 1`.
Balance places it in the literal incidence kernel, and its absolute-coordinate
sum is exactly `48 * tvDistance ν`. Thus the closed radius `1/24` maps exactly to
mass at most two. The endpoint is first proved for normalized rows and then
extended to every nonnegative matrix by positive row scaling, with zero rows
handled separately. The equality theorem uses an additional invariant positive
Gram remainder; its vanishing forces the stated product relations.
