# An all-order permutation-polynomial inequality

Dev D. Goyal directed the AI-generated research.

This is a claimed complete ordinary proof with exact finite certificates. It has no completed Lean formalization or independent human expert review. The [status record](README.md) states the review and prior-work limits.

## Statement

Let n be a positive integer. Let Q be any permutation matrix of order n. For a,b,c >= 0, put

$$
A=aI+bQ+cQ^2,\qquad c_n=\frac{n!}{n^n}.
$$

The claimed inequality is

$$
c_n\operatorname{per}(AA^T)\le\operatorname{per}(A)^2.
$$

The same bound holds with A^T A in place of AA^T. If a+b+c=1, the matrix is doubly stochastic and satisfies Gyires's inequality as stated in the [four-block note](four-block.md#statement).

Set C=AQ^{-1}=aQ^{-1}+bI+cQ. Right multiplication by a permutation matrix preserves the permanent, and CC^T=AA^T. It is therefore sufficient to prove the bound for C. Decomposition into the cycles of Q reduces the proof to cyclic permutation matrices. The constant comparison at the end completes this reduction.

The claim permits cycles of length one and two, zero coefficients, and any number of cycles. It does not cover arbitrary triples of permutation matrices, arbitrary circulants, or all matrices of rank two.

## The cyclic case

Let P_n be the cyclic permutation matrix and C=aP_n^{-1}+bI+cP_n. The proof below uses the permanent formula, an exact transfer representation, an analytic bound for n >= 48, and exact coefficient checks for 3 <= n <= 47. Orders one and two are handled directly.

The permanent formula is classical. See H. Minc, *On permanents of circulants*, Pacific Journal of Mathematics 42 (1972), 477–484, [Theorem 2](https://doi.org/10.2140/pjm.1972.42.477). No novelty is claimed for that formula.

### Permanent formula


Let

$$
\lambda=\frac{b+\sqrt{b^2+4ac}}2,\qquad
\nu=\frac{b-\sqrt{b^2+4ac}}2.
$$

The standard cycle-cover expansion, or the four-state transfer construction below, gives

$$
\operatorname{per}(C)=a^n+c^n+\lambda^n+\nu^n.
$$

This formula includes small n when coincident cyclic diagonals are added in the actual matrix. Define

$$
L=\max(a,c,\lambda).
$$

Then

$$
\operatorname{per}(C)\ge L^n.
$$

The terms a^n and c^n correspond directly to the two cyclic permutations. For the lambda term, if n is even, nu^n>=0. If n is odd, use `|nu|<=sqrt(ac)` and

$$
a^n+c^n\ge2(ac)^{n/2}\ge|\nu|^n.
$$

Thus the possibly negative nu term cannot cancel lambda^n.

If L=0 the theorem is trivial. Otherwise divide a,b,c by L. After this homogeneous normalization,

$$
0\le a,c\le1,\qquad 0\le b\le1-ac.
$$

The second condition is equivalent to lambda<=1, since lambda is the nonnegative root of `x^2-bx-ac`.

### Exact transfer representation

For a cyclic band matrix with offsets -r,...,r and offset weights w_0,...,w_(2r), use states `m=0,...,2^(2r)-1`. At a row, m records occupied columns in the window ending just before the furthest available column. Choose an unused bit j in `{0,...,2r}`, require the outgoing leftmost column to be occupied, and shift the window:

$$
m\longrightarrow (m\mathbin{\mathrm{OR}}2^j)\mathbin{\mathrm{div}}2
$$

with weight w_j, provided bit j was zero and the new mask has bit zero set before shifting.

The permanent is `tr(T^n)`. One can see the bijection by lifting a cyclic perfect matching to a periodic matching of integer-indexed rows and columns. The occupancy state is periodic; conversely a closed sequence of states assigns each row and column exactly once. When offsets coincide modulo small n, choosing the different lifts contributes precisely the multiplicity in the corresponding matrix entry.

The four-state transfer matrix for C splits into scalar blocks a,c and the block

$$
\begin{pmatrix}b&c\\a&0\end{pmatrix},
$$

which proves the permanent formula above.

For the Gram matrix, set

$$
d=a^2+b^2+c^2,\qquad e=b(a+c),\qquad f=ac.
$$

Its offsets -2,-1,0,1,2 have weights `(f,e,d,e,f)`. The sixteen-state transfer matrix splits by mask population count. The two scalar blocks are f. In the increasing-mask orders `(1,2,4,8)` and `(7,11,13,14)`, the population-one and population-three blocks are transposes of one another. Their representative is

$$
T_1=\begin{pmatrix}
e&d&e&f\\
f&0&0&0\\
0&f&0&0\\
0&0&f&0
\end{pmatrix}.
$$

The middle block, in the mask order `(3,5,6,9,10,12)`, is

$$
T_2=\begin{pmatrix}
d&e&0&f&0&0\\
e&0&e&0&f&0\\
f&0&0&0&0&0\\
0&e&d&0&0&f\\
0&f&0&0&0&0\\
0&0&f&0&0&0
\end{pmatrix}.
$$

Therefore

$$
\operatorname{per}(CC^T)
=\operatorname{tr}(T_2^n)+2\operatorname{tr}(T_1^n)+2f^n.
$$

All transfer entries are nonnegative and nondecreasing in b. In the normalized region it is therefore enough to replace b by `1-ac`.


## Sharp analytic bound

In this part, m is the same normalization quantity as L above.

Let

$$
\kappa=1+\sqrt2,\qquad \kappa^2=2\kappa+1.
$$

For nonnegative $a,b,c$, set

$$
d=a^2+b^2+c^2,\qquad e=b(a+c),\qquad f=ac,
$$

and define

$$
T_1(d,e,f)=
\begin{pmatrix}
e&d&e&f\\
f&0&0&0\\
0&f&0&0\\
0&0&f&0
\end{pmatrix},
$$

$$
T_2(d,e,f)=
\begin{pmatrix}
d&e&0&f&0&0\\
e&0&e&0&f&0\\
f&0&0&0&0&0\\
0&e&d&0&0&f\\
0&f&0&0&0&0\\
0&0&f&0&0&0
\end{pmatrix}.
$$

Let

$$
\lambda=\frac{b+\sqrt{b^2+4ac}}2,
\qquad m=\max\{a,c,\lambda\}.
$$

**Lemma.** If $m>0$, then

$$
\rho(T_1(d,e,f))\le\kappa m^2,
\qquad
\rho(T_2(d,e,f))\le\kappa m^2.
$$

The constant $\kappa$ cannot be decreased in the second bound uniformly in $a,b,c$.

### Reduction to one variable

By homogeneity, divide $a,b,c$ by $m$. It suffices to treat $m=1$. Then $0\le a,c\le1$ and $\lambda\le1$. Since $\lambda$ is the nonnegative root of $x^2-bx-ac$, this implies

$$
b+ac\le1.
$$

Both transfer blocks increase entrywise when $d$, $e$, or $f$ increases. Raising $b$ to $1-ac$ increases $d$ and $e$, leaving $f$ fixed. It is therefore enough to consider $b=1-ac$.

Put $u=ac\in[0,1]$. Since

$$
(1-a)(1-c)\ge0,
\qquad a+c\le1+u,
$$

we have

$$
\begin{aligned}
d&=(a+c)^2-2u+(1-u)^2\le2-2u+2u^2=:D(u),\\
e&=(1-u)(a+c)\le1-u^2=:E(u),\\
f&=u.
\end{aligned}
$$

Monotonicity of the spectral radius for nonnegative matrices reduces the proof to

$$
T_j(D(u),E(u),u),\qquad0\le u\le1.
$$

Notice $D(u)\le2$, $E(u)\le1$.

### The four-dimensional block

Use the strictly positive vector

$$
w=(1,\kappa^{-1},\kappa^{-2},\kappa^{-3})^T.
$$

The last three coordinates of $T_1w$ are at most the corresponding coordinates of $\kappa w$, because $0\le u\le1$. Its first coordinate is at most

$$
1+\frac2\kappa+\frac1{\kappa^2}+\frac1{\kappa^3}
=\frac5\kappa<\kappa.
$$

The identity follows from $\kappa^2=2\kappa+1$, and the strict inequality from $\kappa^2>5$. Thus $T_1w\le\kappa w$, so $\rho(T_1)\le\kappa$.

### The six-dimensional block

For $0<u<1$, abbreviate $D=D(u)$, $E=E(u)$, and choose the strictly positive vector

$$
\begin{aligned}
v_1&=1,&
v_2&=\frac{E}{\kappa-u},&
v_3&=\frac{u}{\kappa},\\
v_4&=\frac{E^2}{\kappa(\kappa-u)}
       +\frac{Du}{\kappa^2}+\frac{u^3}{\kappa^3},&
v_5&=\frac{uE}{\kappa(\kappa-u)},&
v_6&=\frac{u^2}{\kappa^2}.
\end{aligned}
$$

Direct substitution gives

$$
(T_2v)_i=\kappa v_i\qquad(i=2,3,4,5,6).
$$

For example, the second row uses

$$
E\left(1+\frac u\kappa\right)
+\frac{u^2E}{\kappa(\kappa-u)}
=\frac{\kappa E}{\kappa-u}.
$$

The first-row residual is

$$
\kappa v_1-(T_2v)_1
=\kappa-D\left(1+\frac{u^2}{\kappa^2}\right)
-\frac{E^2(\kappa+u)}{\kappa(\kappa-u)}
-\frac{u^4}{\kappa^3}
=\frac{P(u)}{\kappa^3(\kappa-u)},
$$

where

$$
\begin{aligned}
P(u)={}&\kappa^4(\kappa-u)
-D\kappa(\kappa-u)(\kappa^2+u^2)\\
&-E^2\kappa^2(\kappa+u)-u^4(\kappa-u).
\end{aligned}
$$

Expanding and using $\kappa^2=2\kappa+1$ yields the exact factorization

$$
P(u)=u(1-u)
\left[(20\kappa+8)-(8\kappa+4)u+(12\kappa+4)u^2\right].
$$

The bracket has the explicitly positive decomposition

$$
(12\kappa+4)+(8\kappa+4)(1-u)+(12\kappa+4)u^2.
$$

Thus $P(u)>0$ on $0<u<1$. We have $T_2v\le\kappa v$, so $\rho(T_2)\le\kappa$. Continuity of the spectral radius extends this bound to $u=0,1$. This use of continuity avoids requiring the displayed vector to remain strictly positive at the endpoints.

At $u=0$, $D=2$, $E=1$, and the first two coordinates contain the block

$$
\begin{pmatrix}2&1\\1&0\end{pmatrix},
$$

whose positive eigenvalue is $\kappa$; all remaining eigenvalues of $T_2(D,E,0)$ are zero. Hence equality is attained in the spectral-radius bound. This endpoint corresponds to $(a,b,c)=(1,1,0)$, for which $m=1$.

Rescaling by $m$ multiplies every transfer-matrix entry by $m^2$, proving the lemma. $\square$

### How the lemma supplies the all-order tail

For $C_n=aP_n^{-1}+bI_n+cP_n$, the Gram transfer matrix has two scalar blocks $f$, two four-dimensional blocks with the same spectral radius as $T_1$, and the six-dimensional block $T_2$. Consequently, once the transfer trace identity is established,

$$
\operatorname{per}(C_nC_n^T)
\le2m^{2n}+14\kappa^nm^{2n}
\le16\kappa^nm^{2n}.
$$

Here $|\operatorname{tr}(T^n)|\le\dim(T)\rho(T)^n$, which follows by summing the $n$-th powers of the eigenvalues. The permanent is nonnegative.

The exact one-cycle permanent formula supplies $\operatorname{per}(C_n)\ge m^n$. Indeed, if $\mu=ac/\lambda$ when $\lambda>0$, that formula is

$$
\operatorname{per}(C_n)=a^n+c^n+\lambda^n+(-\mu)^n.
$$

If $m=a$ or $m=c$, the all-one-direction permutation already gives $\operatorname{per}(C_n)\ge m^n$. If $m=\lambda$, then $\mu\le\min\{a,c\}$. For even $n$ every displayed term is nonnegative; for odd $n$, $a^n+c^n\ge\mu^n$, so the same bound follows. Degenerate cases with $\lambda=0$ are handled directly or by continuity.

Therefore

$$
\frac{c_n\operatorname{per}(C_nC_n^T)}{\operatorname{per}(C_n)^2}
\le16c_n\kappa^n.
$$

Any exact threshold beyond which $16c_n\kappa^n<1$, combined with exact certificates for the finitely many smaller orders, closes this family in every order. The threshold check and finite certificates are separate parts of the full proof and must both be included.

## The exact threshold and finite bridge

The program [round2_sharp_bound_check.py](certificates/round2_sharp_bound_check.py) checks the residual factorization above in Q(sqrt(2)). It also checks

$$
16\cdot48!\cdot169^{48}<3360^{48}.
$$

Since sqrt(2)<99/70, this gives 16 c_48 kappa^48<1. For t_n=16 c_n kappa^n,

$$
\frac{t_{n+1}}{t_n}=\frac{\kappa}{(1+1/n)^n}.
$$

The denominator increases with n. Also kappa<5/2 and 5*6^6<2*7^6. Thus t_n decreases for n>=6. The strict analytic bound covers every n>=48.

For 3<=n<=47, define the homogeneous integer polynomial

$$
D_n(a,b,c)=n^n\operatorname{per}(C)^2-n!\operatorname{per}(CC^T).
$$

In each ordering of a,b,c, write the ordered values as x, x+y, x+y+z. Here x,y,z are nonnegative. The checker constructs D_n in these coordinates and checks every coefficient. Reflection exchanges a and c, so three orderings cover all six.

The program [round2_independent_finite.mjs](certificates/round2_independent_finite.mjs) uses exact JavaScript BigInt arithmetic. It uses the characteristic polynomials of the transfer blocks and Newton trace identities. It constructs the polynomials directly in gap coordinates. Its input 47 covers the full finite bridge. All checked coefficients are nonnegative. For 4<=n<=47, every coefficient is positive. These finite checks cover whole parameter regions, not sampled matrices. Their use as a proof certificate also depends on the transfer identity and the correctness of the checking program.

The program [round2_circ_small_check.py](certificates/round2_circ_small_check.py) computes permanents directly by subsets. It checks both transfer identities for 1<=n<=7 and all six gap orderings for n=3,4. Its two local dependencies are included.

For n=2, set x=b and y=a+c. Direct calculation gives

$$
\operatorname{per}(C)=x^2+y^2,\qquad
\operatorname{per}(CC^T)=(x^2+y^2)^2+4x^2y^2.
$$

Hence

$$
\operatorname{per}(C)^2-\tfrac12\operatorname{per}(CC^T)
=\tfrac12(x^2-y^2)^2\ge0.
$$

Order one is equality. Zero coefficients remain in the closed gap regions. If a=b=c=0, both sides vanish.

## Any permutation matrix

Suppose Q has cycle lengths m_1,...,m_s, with sum n. Simultaneous row and column permutation writes C as a direct sum of the cycle matrices C_i. Permanents multiply over these blocks. The cycle bounds give

$$
\operatorname{per}(C)^2\ge
\left(\prod_i\frac{m_i!}{m_i^{m_i}}\right)\operatorname{per}(CC^T).
$$

The multinomial theorem gives

$$
1=\left(\sum_i\frac{m_i}{n}\right)^n
\ge\frac{n!}{\prod_i m_i!}\prod_i\left(\frac{m_i}{n}\right)^{m_i}.
$$

Therefore the product of the block constants is at least n!/n^n. This proves the claimed bound for every permutation Q and hence for A.

Apply the same argument to A^T, which is a polynomial in Q^T. This proves the other Gram bound. The permanent Cauchy–Schwarz inequality, derived in the [four-block note](four-block.md#the-permanent-inner-product-identity), gives

$$
\operatorname{per}(A^2)\le
\sqrt{\operatorname{per}(AA^T)\operatorname{per}(A^TA)}.
$$

For a doubly stochastic A, the two Gram bounds therefore imply Gyires's inequality. This argument does not use invariance of per(A^2) under independent row and column permutations.

## Reproduction and limits

The [reproduction record](verification.md) gives the commands and completed runs. The source files are identified by hash in [provenance.json](provenance.json). This edited argument uses the sharper analytic tail from the later source note. It omits the superseded tail thresholds 70 and 94.

These programs are not a Lean formalization. The arbitrary-permutation statement has no selected Comparator declaration. Its novelty and independent human expert review remain unresolved.
