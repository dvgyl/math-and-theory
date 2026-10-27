# Gyires's inequality for matrices with two row types and two column types

This note gives an analytic proof for unequal block sizes and boundary values with zero entries. Lean formalization is incomplete. The [reproduction guide](verification.md) gives the certificate commands and their scope.

## Statement

Let A be a nonnegative doubly stochastic matrix of order n>=2. Each row sum and each column sum is one. Suppose A has at most two distinct row vectors and at most two distinct column vectors. Put

$$
d=\operatorname{per}(A),\qquad c_n=\frac{n!}{n^n}.
$$

The contraction bounds are

$$
\operatorname{per}(AA^T)\le d,\qquad
\operatorname{per}(A^TA)\le d,\qquad
\operatorname{per}(A^2)\le d.
$$

The Gyires bound includes the margin

$$
4d^2-c_n\left[\operatorname{per}(AA^T)+\operatorname{per}(A^TA)
+2\operatorname{per}(A^2)\right]\ge4d(d-c_n)\ge0.
$$

Equality in Gyires's inequality holds exactly at J_n, whose entries are all 1/n. The individual contraction bounds can have other equality cases. Here A^2 is a matrix product. The expression per(A)^2 is the square of a real number.

Order one is immediate. The theorem does not cover every matrix of rank two.

## Four-block parameterization

If there is only one row type or only one column type, stochasticity forces A=J_n. Otherwise let the row classes have sizes r,n-r and the column classes have sizes s,n-s. Here 1<=r,s<=n-1. After grouping the classes, the four block entries are

$$
\begin{pmatrix}
\dfrac{h}{rs}&\dfrac{r-h}{r(n-s)}\\[6pt]
\dfrac{s-h}{(n-r)s}&\dfrac{n-r-s+h}{(n-r)(n-s)}
\end{pmatrix},\qquad
\max(0,r+s-n)\le h\le\min(r,s).
$$

Each displayed entry fills its whole block. The number h is the total mass in the first block. The block masses are h,r-h,s-h,n-r-s+h. Their nonnegativity gives the stated closed interval. Row and column stochasticity force these formulas, and the formulas give all such matrices. The uniform matrix has h=rs/n.

The row classes and column classes can occur in any order. The proof treats per(A^2) in the original indexing. It does not assume that independent row and column permutations preserve per(A^2).

## A Poisson-binomial likelihood bound

A Bernoulli variable has value one with probability p and value zero with probability 1-p. A Poisson-binomial law is the distribution of a sum of independent Bernoulli variables.

Let P be such a law for n parameters p_i in [0,1]. Suppose their sum is an integer m with 1<=m<=n-1. Let B be the binomial law with n trials and parameter m/n. All its probabilities B_k are positive. We first prove

$$
\frac{P_k}{B_k}\le\frac{P_m}{B_m}\quad(0\le k\le n).
$$

Consequently,

$$
\sum_{k=0}^n\frac{P_k^2}{B_k}\le\frac{P_m}{B_m},
\qquad \frac{P_m}{B_m}\ge1.
$$

### Reduction of a linear objective

For any real function f on {0,...,n}, maximize E[f(K)] over the compact set of parameter vectors with sum m. Among its maximizers, choose one with maximal sum of squared parameters.

Suppose two distinct parameters p,q are strictly between zero and one. Keep t=p+q fixed and vary z=pq. Their generating polynomial is

$$
(1-t+z)+(t-2z)x+zx^2.
$$

Thus the objective is affine in z. The current z lies strictly between max(0,t-1) and t^2/4. An affine function with an interior maximum on this interval is constant. Move z to the lower endpoint. The objective is unchanged, but p^2+q^2=t^2-2z strictly increases. This contradicts the selected maximizer.

Hence a maximizing law has only deterministic parameters and equal fractional parameters. It has the form

$$
K=a+\operatorname{Bin}(b,q),\qquad q=\frac{m-a}{b}.
$$

The deterministic law at m is a separate permitted case. This extremal reduction is classical. See W. Hoeffding, *On the Distribution of the Number of Successes in Independent Trials*, Annals of Mathematical Statistics 27 (1956), 713–721, [Corollary 2.1](https://doi.org/10.1214/aoms/1177728178). The reduction is proved here and is not claimed as new.

### Adjacent probabilities and the maximum likelihood ratio

Apply the reduction to the linear objective (m+1)P_(m+1)-mP_m. In a nondegenerate maximizing law, put u=m-a. Then 0<u<b and

$$
\frac{P_{m+1}}{P_m}=\frac{u}{u+1}\le\frac{m}{m+1}.
$$

The deterministic law also gives a nonpositive objective. Thus

$$
(m+1)P_{m+1}\le mP_m.
$$

Apply the reduction again to (n-m+1)P_(m-1)-(n-m)P_m. In a nondegenerate maximizing law,

$$
\frac{P_{m-1}}{P_m}=\frac{b-u}{b-u+1}
\le\frac{n-m}{n-m+1},
$$

because b-u=b-m+a<=n-m. The deterministic case again gives a nonpositive objective. Hence

$$
(n-m+1)P_{m-1}\le(n-m)P_m.
$$

The generating polynomial of P is a product of linear factors with real nonpositive zeros. Newton's inequalities imply that P_k/binomial(n,k) is log-concave with interval support. The same holds for R_k=P_k/B_k, because the extra binomial weights form a geometric sequence. Boundary parameters follow by continuity, or by removing deterministic factors.

The binomial ratios satisfy

$$
\frac{B_{m+1}}{B_m}=\frac{m}{m+1},\qquad
\frac{B_{m-1}}{B_m}=\frac{n-m}{n-m+1}.
$$

The adjacent bounds therefore give R_(m-1)<=R_m and R_(m+1)<=R_m. The mean and interval support imply P_m>0. Log-concavity then gives R_k<=R_m for every k. Multiplication by P_k and summation gives the norm bound. Also 1=sum B_k R_k<=R_m.

If R_m=1, positivity of every B_k and the last average force R_k=1 for all k. Thus P=B. Conversely, P=B gives R_m=1. Uniqueness of the linear factors of the generating polynomial then implies p_i=m/n for every i.

Newton's inequalities and the fixed-mean extremal reduction are supporting classical results. The general inequality for arbitrary ultra-log-concave laws is not used here.

## The permanent inner-product identity

For a matrix M, define the degree-n polynomial

$$
p_M(z)=\prod_{i=1}^n\left(\sum_{j=1}^n M_{ij}z_j\right).
$$

Write p_M,alpha for the coefficient with multi-index alpha. Define the coefficient inner product

$$
\langle p,q\rangle_F=\sum_{|\alpha|=n}\alpha!p_\alpha q_\alpha.
$$

Expansion by column multiplicities gives

$$
\langle p_M,p_N\rangle_F=\operatorname{per}(MN^T),
\qquad [z_1\cdots z_n]p_M=\operatorname{per}(M).
$$

To see the first identity, expand each matrix entry in the permanent of MN^T. Fix the chosen column index for each row of M and N. A contribution survives exactly when the two index lists have the same multiplicities alpha. There are alpha! bijections between the occurrences. Summing these contributions gives the coefficient inner product.

All weights alpha! are positive. Cauchy–Schwarz, with M=A and N=A^T, therefore gives

$$
\operatorname{per}(A^2)\le
\sqrt{\operatorname{per}(AA^T)\operatorname{per}(A^TA)}.
$$

## Contraction for two column types

This step needs only two column types. It permits any number of row types. Let the column class sizes be s,n-s. Let u_i be the sum of row i over the first class. Then 0<=u_i<=1 and sum u_i=s.

Let X and Y denote the sums of variables in the two column classes. The row product polynomial is

$$
p_A(z)=\prod_{i=1}^n\left(\frac{u_i}{s}X+
\frac{1-u_i}{n-s}Y\right)
=\sum_{k=0}^n\frac{P_k X^kY^{n-k}}{s^k(n-s)^{n-k}},
$$

where P is the Poisson-binomial law for the parameters u_i. Its mean is s. Let B=Bin(n,s/n).

Only the term k=s contributes to the squarefree coefficient. It gives

$$
\operatorname{per}(A)=\frac{P_s\,s!(n-s)!}{s^s(n-s)^{n-s}}
=c_n\frac{P_s}{B_s}.
$$

For a group of s variables, multinomial expansion gives

$$
\sum_{|\alpha|=k}\alpha!
\left(\frac{k!}{\alpha!}\right)^2=k!s^k.
$$

Distinct group degrees are orthogonal in the coefficient inner product. Apply this identity to both groups. The squared norm becomes

$$
\operatorname{per}(AA^T)
=\sum_{k=0}^n\frac{P_k^2\,k!(n-k)!}{s^k(n-s)^{n-k}}
=c_n\sum_{k=0}^n\frac{P_k^2}{B_k}.
$$

The likelihood norm bound now proves per(AA^T)<=per(A). It also proves d>=c_n. If d=c_n, the equality argument gives u_i=s/n for all i, so A=J_n.

## Completion of the four-block argument

If A also has at most two row types, A^T has at most two column types. Apply the contraction result to A^T to obtain per(A^TA)<=d. The permanent Cauchy–Schwarz inequality then gives per(A^2)<=d. Addition gives

$$
\operatorname{per}(AA^T)+\operatorname{per}(A^TA)+2\operatorname{per}(A^2)\le4d.
$$

Subtract c_n times this bound from 4d^2. The result is the stated margin 4d(d-c_n). We proved d>=c_n>0, with equality only at J_n. Hence Gyires's deficit is strictly positive for A!=J_n. The uniform matrix attains equality directly.

The argument includes h at either endpoint of its feasible interval. The Bernoulli parameters can equal zero or one. No positive-entry approximation is required for the theorem statement.

## References and verification scope

The [manuscript](../../preprints/gyires-circulant-five/paper.pdf) contains this proof and its bibliography. The permanent identities are proved above.

The ordinary proof is analytic. Finite numerical checks are not its justification. No complete Lean proof of this statement is included. No human expert review, peer review, or novelty determination is claimed.
