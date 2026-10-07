> Imported research note from the Analytic-Lab source snapshot. Historical
> formalization and publication status below predates this spin-out; see
> [the project README](../README.md) for current checked coverage.

# Sharp stability, equality, and entropy for four-row permanents

2026-10-06. These are proved consequences and extensions of the exact
[endpoint theorem](ENDPOINT.md), with its computer-assisted dependency retained.
All measures and matrix entries are real; functions are nonnegative unless
stated otherwise. The exponent bound below is sufficient, not optimal.
[PRIOR_ART](PRIOR_ART.md) distinguishes the new parameter claims from standard
entropy and tensorization mechanisms. No shared RT ticket is claimed.

Write \(u\) for uniform measure on \(S_4\), \(\mu\) for uniform measure on
\([4]\), and \(\mathcal B_r\) for balanced permutation laws at TV distance at
most \(r\) from \(u\). Norms and variances of row functions use \(\mu\).

## 1. A sharp quantitative strengthening

**Theorem 1 (sharp stability).** For \(0\le r\le1/24\), \(\nu\in\mathcal B_r\),
and row functions \(f_i\ge0\) with \(\mathbb E_\mu f_i^2=1\),

\[
 1-\mathbb E_\nu\prod_{i=1}^4 f_i(\sigma(i))
 \ \ge\ \frac{1-24r}{9}\sum_{i=1}^4\operatorname{Var}_\mu(f_i).
 \tag{S}
\]

For each fixed \(r\), the coefficient \((1-24r)/9\) is the largest possible
coefficient valid uniformly over this law class and these row functions.
Thus the result gives an exact stability constant throughout the closed ball.

**Proof of the uniform case.** First take nonnegative Euclidean unit vectors
\(v,w\in\mathbb R^4\). Set

\[
 t(v)=1-\tfrac14(\sum_jv_j)^2,\qquad
 D(v,w)=\tfrac12[1+4\sum_jv_j^2w_j^2-2(v\cdot w)^2].
\]

We claim \(D(v,w)\ge(t(v)+t(w))/3\). The elementary scalar ingredient is

\[
 12p_4+p_1^2p_2-7p_2^2\ge0,\qquad p_k=\sum_{j=1}^4z_j^k,\quad z_j\ge0.
 \tag{Q}
\]

Here is a fully explicit identity. Define
\(q_i=p_1z_i-3z_i^2-(p_1^2-3p_2)/4\) and
\((s_1,s_2,s_3)=(z_1z_2+z_3z_4,z_1z_3+z_2z_4,z_1z_4+z_2z_3)\). Then

\[
 12p_4+p_1^2p_2-7p_2^2
 =6\sum_{i<j}z_iz_j(z_i-z_j)^2+2\sum_iq_i^2
   +\sum_{a<b}(s_a-s_b)^2.                              \tag{Q-SOS}
\]

This is an exact polynomial identity, checked independently over the rationals
by [extensions.py](../evidence/extensions.py).
The scalar inequality is classical in content: its left side also equals

\[
 2\sum_{i<j<k}\operatorname{Schur}_4(z_i,z_j,z_k)
 +6\sum_{i<j}z_iz_j(z_i-z_j)^2,
\]

where \(\operatorname{Schur}_4(x,y,z)=\sum_{\rm cyc}x^2(x-y)(x-z)\ge0\).
For completeness, by symmetry order \(x\ge y\ge z\ge0\); the first two
terms sum to \((x-y)[x^2(x-z)-y^2(y-z)]\ge0\), and the third is nonnegative.
No novelty is claimed for (Q).

To prove the pair claim, let \(c=v\cdot w\) and \(h=\sum_jv_j^2w_j^2\).
Direct expansion gives

\[
 6[D(v,w)-(t(v)+t(w))/3]
 =12h-6c^2+\sum_{j<k}(v_jv_k+w_jw_k).
\]

If \(c=0\), this is nonnegative. Otherwise set
\(y_j=\sqrt{v_jw_j}\), \(z=y/\sqrt c\); then \(\sum z_j^2=1\) and
\(0<c\le1\). AM–GM bounds the last sum below by
\(2\sum_{j<k}y_jy_k\). With \(S=\sum_{j<k}z_jz_k\), the resulting bound is

\[
 2c^2(6\sum_jz_j^4-3+S)+2c(1-c)S\ge0,
\]

because (Q), with \(p_2=1\), gives the first parenthesis nonnegative.

Now let \(A\) have four nonnegative Euclidean unit rows \(v_i\). For a row
pair define its six-vector \(P(v,w)_{jk}=v_jw_k+v_kw_j\), indexed by \(j<k\).
Expansion gives \(\|P(v,w)\|_2^2=3/2-D(v,w)\). Expanding the permanent
along any partition of the rows into two pairs, and applying Cauchy–Schwarz
followed by AM–GM, yields

\[
 \operatorname{per}(A)\le\frac32-\frac12(D_{ij}+D_{k\ell}).
\]

Average over the three pair partitions. Each row pair occurs once, so

\[
 1-\tfrac23\operatorname{per}(A)
 \ge\tfrac19\sum_{i<j}D(v_i,v_j)
 \ge\tfrac19\sum_i t(v_i).                            \tag{U}
\]

Apply this to \(v_i=f_i/2\). Then \(t(v_i)=\operatorname{Var}_\mu(f_i)\)
and \((2/3)\operatorname{per}(A)=\mathbb E_u\prod_i f_i(\sigma(i))\).

For \(r>0\), put \(a=24r\) and \(\nu'=u+(\nu-u)/a\).
It is balanced and has TV at most \(1/24\). Each negative atom deviation is
at most this TV distance, so \(\nu'\ge0\); its total mass is one.
Write \(\nu=(1-a)u+a\nu'\), apply (U) to \(u\) and the endpoint theorem
to \(\nu'\). This proves (S). The case \(r=0\) was already proved.

For sharpness take the [endpoint sharpness trade](ENDPOINT.md#5-sharpness-above-the-endpoint)
\(m=\frac12\delta_{\rm id}+\frac12U_D-U_T\),
\(\nu_r=u+rm\), and \(f_i(j)=2\mathbf1_{j=i}\).
Their variance sum is three and their product expectation is \(2/3+8r\).
Equality in (S) follows for every \(0\le r\le1/24\). \(\square\)

## 2. An explicit exponent below two

**Theorem 2.** Define

\[
 p(r)=2-\frac{1-24r}{36},\qquad 0\le r\le1/24.
\]

Every \(\nu\in\mathcal B_r\) satisfies

\[
 \mathbb E_\nu\prod_i f_i(\sigma(i))
 \le\prod_i\|f_i\|_{p(r)}.                            \tag{P}
\]

This also holds at every larger exponent, by monotonicity of probability
\(L^p\) norms. Equivalently,
\(R_4(p)\ge(36p-71)/24\) for \(71/36\le p\le2\).
This is not an exact determination of the curve \(R_4(p)\).

**Proof.** Normalize each nonzero row in \(L^2\); zero rows are immediate.
For a normalized row \(f\), \(0\le f\le2\). For \(1\le p\le2\),

\[
 \frac{d}{dp}\log\|f\|_p
 =\frac{\operatorname{Ent}_\mu(f^p)}{p^2\mathbb E_\mu f^p}
 \le\frac{\operatorname{Var}_\mu(f^p)}{p^2(\mathbb E_\mu f^p)^2}
 \le4\operatorname{Var}_\mu(f).
\]

The first bound follows from \(\log x\le x-1\); the second uses the
Lipschitz constant \(p2^{p-1}\) of \(x^p\) on \([0,2]\), the independent-copy
formula for variance, and \(\mathbb E f^p\ge2^{p-2}\mathbb E f^2=2^{p-2}\).
At zero entries interpret \(0^p\log0\) as zero; all derivatives remain valid.
Integrating and writing \(V=\sum_i\operatorname{Var}(f_i)\) gives

\[
 \prod_i\|f_i\|_p\ge e^{-4(2-p)V}\ge1-4(2-p)V.
\]

At the stated \(p(r)\), the last expression is the upper bound in (S).
Undo row normalization to finish. \(\square\)

**Exact feasibility threshold.** For \(r\ge0\), a common exponent
\(1\le p<2\) works for every law in \(\mathcal B_r\) **if and only if**
\(r<1/24\). Sufficiency follows from Theorem 2. For necessity the endpoint
law \(\nu_* = u+m/24\) has \(\nu_*({\rm id})=1/16\); the matching functions
\(2\mathbf1_{j=i}\) have expectation one, whereas their product of
\(L^p\) norms is \(2^{4-8/p}<1\).

At \(r=1/48\), for example, \(p=143/72\). The associated exponent
\(1-1/p=71/143<1/2\) supplies an explicit strict margin in the predecessor's
permutation-moment argument. A new shuffle mixing theorem is not proved here.

## 3. All endpoint equality cases

**Theorem 3.** For \(\nu\in\mathcal B_{1/24}\), equality in the endpoint
row-norm inequality occurs exactly in the following cases:

1. A row is zero.
2. Every row is constant across its four columns.
3. There is a permutation \(\tau\) with \(\nu(\tau)=1/16\), and each row
   is supported exactly on its matching column \(\tau(i)\).

In cases 2 and 3 the nonzero row scales may be arbitrary positive numbers.
For \(r<1/24\), case 3 cannot occur, also directly by (S).

**Proof.** Normalize nonzero rows to Euclidean norm one. In every endpoint
SOS certificate, twelve blocks impose precisely these relations at equality:
\(a_{ij}a_{ik}\) is independent of \(i\), for each \(j<k\), and
\(a_{ij}a_{kj}\) is independent of \(j\), for each \(i<k\).
Indeed their reduced Gram matrices are positive definite and their
\(4\times3\) basis matrices \(E\) satisfy
\(\operatorname{rank}E=3\), \(E^{\mathsf T}\mathbf1=0\).
[extensions.py](../evidence/extensions.py)
checks these statements literally for all 1,572 relevant blocks in all
131 certificates, including 4,716 positive rational pivots.

If a row has two positive entries, the first relations force both columns
positive in every row. The second relations then force all entries positive.
Pairwise coordinate products of any two rows agree; using three distinct
columns shows the rows themselves agree. The second relations now force
all four entries of their common row to agree. Otherwise every row has at
most one positive entry, and the second relations ensure every column also
has at most one. Nonzero normalized rows therefore give a permutation matrix.

For any convex combination of vertex laws, zero deficit forces zero in every
positively weighted certificate. Relabeling preserves these twelve relations,
so the argument covers arbitrary real laws, not just the representatives.
The constant matrix always attains equality. A normalized permutation matrix
attains equality exactly when its law mass is \(1/16\). Undo normalization.
\(\square\)

## 4. Entropy and loss of information

Let \(D\) denote relative entropy with natural logarithms and \(0\log0=0\).
Fix \(0\le r\le1/24\), \(\nu\in\mathcal B_r\), and \(p=p(r)\).
Every probability law \(\rho\) on \(S_4\) satisfies

\[
 \sum_{i=1}^4D(\rho_i\|\mu)\le pD(\rho\|\nu),
 \qquad \rho_i=\operatorname{law}_\rho(\sigma(i)).       \tag{E}
\]

For a direct finite proof put
\(g(\sigma)=\prod_i(4\rho_i(\sigma(i)))^{1/p}\).
By (P), \(Z=\mathbb E_\nu g\le1\). When \(D(\rho\|\nu)<\infty\),
\(Z>0\) and \(q=\nu g/Z\) is a probability law supporting \(\rho\).
Nonnegativity of
\(D(\rho\|q)=D(\rho\|\nu)-p^{-1}\sum_iD(\rho_i\|\mu)+\log Z\)
proves (E); an infinite right side is immediate. This is the standard
[Brascamp–Lieb/entropy duality](https://arxiv.org/html/0710.0870v2).

Observe a uniformly chosen coordinate: \(K:\sigma\mapsto(I,\sigma(I))\).
Balance gives \(\nu K=\operatorname{Unif}([4]^2)\), and

\[
 D(\rho K\|\nu K)=\tfrac14\sum_iD(\rho_i\|\mu)
 \le\left(\tfrac12-\tfrac{1-24r}{144}\right)D(\rho\|\nu).
 \tag{I}
\]

At \(r=1/24\), both the entropy coefficient 2 and the observation coefficient
\(1/2\) are optimal over the ball: take \(\nu=\nu_*\) and
\(\rho=\delta_{\rm id}\), giving the ratio \(4\log4/\log16=2\).
For larger radii the same sharpness family violates these constants.
For interior radii the displayed improved coefficients are sufficient;
optimality is not asserted.

Equivalently, if \(U\to\Pi\to(I,\Pi(I))\), \(\Pi\sim\nu\), is a Markov
chain, averaging (I) over the conditional laws of \(\Pi\) given \(U\) gives
\(I(U;I,\Pi(I))\le(p/4)I(U;\Pi)\). This interpretation uses standard
strong data-processing theory, not a new transfer mechanism.

## 5. Adaptive tensorization and applications

Let \(\Pi_1,\ldots,\Pi_m\in S_4\) have an arbitrary history-dependent law
\(P\). Assume the conditional law of \(\Pi_t\) given every positive-probability
full past lies in \(\mathcal B_r\). Put
\(X_i=(\Pi_t(i))_{t=1}^m\). Each \(X_i\) has law \(\mu^{\otimes m}\), by
conditional balance. For every \(F_i:[4]^m\to[0,\infty)\),

\[
 \mathbb E_P\prod_iF_i(X_i)\le\prod_i\|F_i\|_{L^p(\mu^{\otimes m})}.
 \tag{T}
\]

Condition on the full history up to \(m-1\), apply (P) to the four functions
of the last coordinate, and replace each by
\(G_i(x)=(\tfrac14\sum_jF_i(x,j)^p)^{1/p}\). Repeat backwards. The identity
\(\|G_i\|_p=\|F_i\|_p\) proves (T) by induction. Independence between
the permutation steps is unnecessary. Ordinary independent tensorization
and its entropy counterpart are classical; the explicit law class is the input.

Several direct consequences are useful:

- **Rectangles.** For sets \(C_i\subseteq[4]^m\),
  \(P\{X_i\in C_i\ \forall i\}\le\prod_i(|C_i|/4^m)^{1/p}\).
  At the endpoint, singleton matching paths under \(\nu_*^{\otimes m}\)
  attain equality, so the exponent \(1/2\) cannot be increased uniformly.
- **Path entropy.** The same finite entropy proof gives
  \(\sum_iD(Q_{X_i}\|\mu^{\otimes m})\le pD(Q\|P)\).
  Observing \((I,X_I)\) therefore contracts relative entropy by at most \(p/4\).
- **Conditional resampling.** Choose \(i\) uniformly, retain \(X_i\), and
  resample the full path from \(P\) conditional on it. The reversible density
  operator is \(Mf=\frac14\sum_i\mathbb E_P[f\mid X_i]\). Entropy convexity
  and the path inequality give \(\operatorname{Ent}_P(Mf)\le(p/4)\operatorname{Ent}_P(f)\).
  Iteration yields geometric relative-entropy convergence. The path entropy
  inequality equivalently gives the block factorization
  \(\operatorname{Ent}_P(f)\le(4-p)^{-1}\sum_i\mathbb E_P[\operatorname{Ent}_P(f\mid X_i)]\).
  This is a proved Markov-chain bound, not a claim of optimal mixing rate or
  an efficient implementation of conditional sampling.
- **Concentration.** For deterministic functions \(h_{ti}\) on \([4]\),
  let \(Z=\sum_{t,i}h_{ti}(\Pi_t(i))\) and
  \(V_h=\sum_{t,i}(\max h_{ti}-\min h_{ti})^2>0\).
  Taking exponentials in (T) and using the elementary bounded-variable
  exponential-moment bound gives
  \(\Pr\{|Z-\mathbb EZ|\ge s\}\le2\exp[-2s^2/(pV_h)]\) for \(s\ge0\).
  Specifically \(\log\mathbb Ee^{\lambda(Z-\mathbb EZ)}\le p\lambda^2V_h/8\);
  optimization in \(\lambda\) gives the claim. The constants here are not
  asserted optimal. If \(V_h=0\), \(Z\) is deterministic.

The entropy, conditional-resampling, and concentration proofs introduce no
additional finite census. Their universal mathematical transfer arguments
are given here; a Python replay alone is not a verification of those arguments.
