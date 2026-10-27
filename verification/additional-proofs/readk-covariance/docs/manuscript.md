---
title: "Logarithmic influence bounds and variance counterexamples for Boolean decision-tree covariance"
author: "Dev D. Goyal"
date: "27 October 2026"
lang: en-US
fontsize: 11pt
geometry: margin=1in
header-includes:
  - \usepackage{seqsplit}
colorlinks: true
linkcolor: blue
urlcolor: blue
---

\begin{center}
\small ORCID: \href{https://orcid.org/0009-0009-9132-744X}{0009-0009-9132-744X}
\end{center}

# Abstract {.unnumbered}

For a Boolean decision tree \(T\), let \(k_i(T)\) count the internal nodes querying coordinate \(i\), and let \(I_i(f)\) be its coordinate influence under uniform independent bits. We prove the weighted bound
\[
\sum_{v\in\operatorname{Int}(T)}2^{-d(v)}
 \left|\operatorname{Cov}(f_{v,+},f_{v,-})\right|
\leq \sum_i I_i(f)\log_2\max\{1,k_i(T)\}.
\tag{A}
\]

The standard assumption is that no coordinate is queried twice on a single root-to-leaf path. In particular, the signed tree covariance of Wan, Wright and Wu is at most \(I(f)\log_2 k\) for a read-\(k\) tree. The logarithmic factor has the exact coefficient one along the family \(k=2^d\): the dummy-prefix construction of Wan, Wright and Wu, with a dictator at its base, attains equality.

Shalev proved the earlier covariance bound \(2\sqrt{k}I(f)\). The inequality above replaces the square-root dependence on the read number by a logarithm, with an optimal coefficient for this covariance quantity. The logarithmic potential itself was previously suggested by Shalev; the contribution is a proof of the proposed inequality through a minimum-of-influences estimate.

We give a four-variable read-three tree computing the two-variable AND function with tree covariance \(5/4\) and variance \(3/4\). A second, nine-variable witness has every query relevant and also violates the proposed bound. Since \(\log_2 3<5/3\), this refutes the proposed universal bound \(\mathcal C(T)\leq\operatorname{Var}(f)\log_2 k\). The four-variable tree uses the original convention, which permits dummy queries. The unrestricted Fourier entropy-influence conjecture remains unresolved by this work.

# Definitions and scope

A coordinate influence is the probability that flipping that input bit changes the output. All expectations below are finite uniform averages. For \(f:\{-1,1\}^n\to\{-1,1\}\), write \(x^{\oplus i}\) for \(x\) with coordinate \(i\) flipped and define
\[
I_i(f)=2^{-n}\#\{x:f(x)\ne f(x^{\oplus i})\},
\qquad I(f)=\sum_{i=1}^n I_i(f).
\]

For functions \(g,h\) on the same cube,
\[
\operatorname{Cov}(g,h)=\mathbb E[gh]-(\mathbb E g)(\mathbb E h).
\]

A decision tree is a finite binary tree with signed Boolean leaves and one coordinate label at each internal node. On an input \(x\), the branch at a node labelled \(i\) is chosen by \(x_i\). We assume no variable is queried twice along a root-to-leaf path. This is the same convention used in the decision-tree covariance literature.

For an internal node \(v\), \(f_{v,+}\) and \(f_{v,-}\) denote the two child functions, viewed as functions on the same full input cube by ignoring coordinates the respective subtree does not query. Let \(d(v)\) be its depth, with the root at depth zero. Define signed and absolute tree covariances by
\[
\mathcal C(T)=\sum_v2^{-d(v)}\operatorname{Cov}(f_{v,+},f_{v,-}),
\qquad
\mathcal A(T)=\sum_v2^{-d(v)}|\operatorname{Cov}(f_{v,+},f_{v,-})|.
\]

Both are zero for a leaf. If the two root subtrees \(T_+,T_-\) compute \(g,h\), respectively, then
\[
\mathcal C(T)=\operatorname{Cov}(g,h)+\frac{\mathcal C(T_+)+\mathcal C(T_-)}2,
\]

and the same recurrence with the absolute value of the root covariance holds for \(\mathcal A\). In particular, \(\mathcal C(T)\leq\mathcal A(T)\).

Let \(k_i(T)\) be the total number of internal nodes labelled \(i\) in the entire tree. This is a global node count, not a count along one path. Put
\[
w(r)=\log_2\max\{1,r\}\quad(r\in\mathbb N),
\qquad
P(T)=\sum_i I_i(f)w(k_i(T)).
\]

The convention \(w(0)=w(1)=0\) avoids an undefined logarithm; \(k_i(T)=0\) also implies \(I_i(f)=0\). A tree is read-\(k\) when \(k_i(T)\leq k\) for every \(i\), where \(k\geq1\).

# A Boolean covariance inequality

## Lemma 1 {.unnumbered}
For every two Boolean functions \(g,h:\{-1,1\}^n\to\{-1,1\}\),
\[
|\operatorname{Cov}(g,h)|\leq
\sum_{i=1}^n\min\{I_i(g),I_i(h)\}.
\tag{1}
\]

We first prove the covariance estimate used in the tree induction.

**Proof.** Induct on \(n\). When \(n=0\), the functions are constant, so both sides are zero.

For \(n\geq1\), split the last coordinate and write \(g_+,g_-,h_+,h_-\) for the restrictions to the \((n-1)\)-cube. Put
\[
d_g=\frac{\mathbb E g_+-\mathbb E g_-}{2},
\qquad
d_h=\frac{\mathbb E h_+-\mathbb E h_-}{2}.
\]

Expanding the covariance gives the exact identity
\[
\operatorname{Cov}(g,h)
=\frac{\operatorname{Cov}(g_+,h_+)+\operatorname{Cov}(g_-,h_-)}2+d_gd_h.
\tag{2}
\]

Indeed, the joint expectation is the average of the two restricted joint expectations, while the product of the two full means differs from the average of the two restricted mean-products by \(d_gd_h\).

Since \(g_+,g_-\) take values in \(\{-1,1\}\), their half-difference is in \(\{-1,0,1\}\). Therefore
\[
|d_g|
\leq\mathbb E\left|\frac{g_+-g_-}{2}\right|
=\Pr[g_+\ne g_-]
=I_n(g).
\tag{3}
\]

Also \(|d_g|\leq1\). The same statements hold for \(h\). Hence
\[
|d_gd_h|\leq\min\{I_n(g),I_n(h)\}.
\tag{4}
\]

Apply the triangle inequality and the inductive hypothesis to (2). For every \(i<n\),
\[
I_i(g)=\frac{I_i(g_+)+I_i(g_-)}2,
\qquad
I_i(h)=\frac{I_i(h_+)+I_i(h_-)}2.
\tag{5}
\]

For any nonnegative \(a,b,c,d\),
\[
\frac{\min(a,b)+\min(c,d)}2
\leq\min\left(\frac{a+c}2,\frac{b+d}2\right),
\tag{6}
\]

because the left side is at most both terms inside the minimum. Apply (6) to the two restricted influence pairs, use (5), and add (4). This proves (1). \(\square\)


# The logarithmic split inequality

## Lemma 2 {.unnumbered}
Let \(a,b\) be nonnegative integers and \(A,B\geq0\) real numbers. Suppose \(a=0\) implies \(A=0\), and \(b=0\) implies \(B=0\). Then
\[
2\min(A,B)+A w(a)+B w(b)
\leq(A+B)w(a+b).
\tag{7}
\]

**Proof.** If \(a=0\), then \(A=0\), and both sides reduce to \(B w(b)\). The case \(b=0\) is symmetric.

Suppose \(a,b>0\). Define
\[
u=\log_2\frac{a+b}{a},\qquad
v=\log_2\frac{a+b}{b}.
\]

Both are nonnegative, and
\[
u+v=\log_2\frac{(a+b)^2}{ab}\geq2,
\]

because \((a+b)^2-4ab=(a-b)^2\geq0\). Thus
\[
Au+Bv\geq\min(A,B)(u+v)\geq2\min(A,B).
\]

Expanding \(u,v\) gives (7). \(\square\)

For a Lean implementation using natural logarithms, the nonzero-count form is equivalently
\[
2\ln(2)\min(A,B)+A\ln a+B\ln b
\leq(A+B)\ln(a+b).
\]

# Weighted tree theorem

## Theorem 3 {.unnumbered}
Every Boolean decision tree satisfying the no-repeat-on-a-path convention obeys
\[
\mathcal A(T)\leq P(T)=\sum_i I_i(f)w(k_i(T)).
\tag{8}
\]

Consequently,
\[
\mathcal C(T)\leq\mathcal A(T)\leq\log_2(k)I(f)
\tag{9}
\]

for every read-\(k\) tree and \(k\geq1\).

**Proof.** Use structural induction on \(T\). For a leaf, every influence and both covariance quantities are zero.

Suppose the root queries \(j\), and its subtrees \(T_+,T_-\) compute \(g,h\). Since no path repeats \(j\), neither subtree queries \(j\). Thus \(k_j(T)=1\) and \(I_j(g)=I_j(h)=0\). The root coordinate contributes zero to all three potentials because \(w(1)=0\).

For \(i\ne j\), write
\[
a_i=k_i(T_+),\quad b_i=k_i(T_-),\quad
A_i=I_i(g),\quad B_i=I_i(h).
\]

Then
\[
k_i(T)=a_i+b_i,\qquad
I_i(f)=\frac{A_i+B_i}{2}.
\tag{10}
\]

If \(a_i=0\), then \(g\) does not depend on \(i\), so \(A_i=0\). The analogous statement holds for \(b_i,B_i\). Lemma 2 therefore applies, including every zero-count case. Summing it gives
\[
\begin{aligned}
2P(T)-P(T_+)-P(T_-)
&=\sum_{i\ne j}\left[(A_i+B_i)w(a_i+b_i)-A_iw(a_i)-B_iw(b_i)\right]\\
&\geq2\sum_{i\ne j}\min(A_i,B_i)\\
&\geq2|\operatorname{Cov}(g,h)|,
\end{aligned}
\tag{11}
\]

where the last inequality is Lemma 1; coordinate \(j\) has zero influence on both functions. By the induction hypothesis,
\[
\begin{aligned}
\mathcal A(T)
&=|\operatorname{Cov}(g,h)|+\frac{\mathcal A(T_+)+\mathcal A(T_-)}2\\
&\leq|\operatorname{Cov}(g,h)|+\frac{P(T_+)+P(T_-)}2\\
&\leq P(T).
\end{aligned}
\]

This proves (8). If \(k_i(T)\leq k\), then \(w(k_i(T))\leq\log_2k\). Multiply by the nonnegative influences and sum to get (9). \(\square\)

The signed inequality is all that is needed by the published Fourier coding argument. The absolute version follows because the covariance lemma already contains an absolute value and the potential proof has no cancellations.

# Sharpness of the covariance factor

The following family is the dummy-prefix example of Wan, Wright and Wu, Section 2.4, specialized to a dictator. It is included to verify the exact constant; the construction itself is prior work.

## Proposition 4 {.unnumbered}
For every integer \(d\geq0\), there is a read-\(2^d\) decision tree \(T_d\) computing a dictator and satisfying
\[
I(f_d)=\operatorname{Var}(f_d)=1,\qquad
\mathcal C(T_d)=\mathcal A(T_d)=d,\qquad
P(T_d)=d.
\tag{12}
\]

**Proof.** Use coordinates \(z_1,\ldots,z_d,x\). First query \(z_1,\ldots,z_d\) in a complete binary tree, independently of the answers. At each of the resulting \(2^d\) nodes query \(x\) and output its sign. The function is always \(f_d=x\). Thus \(I_x=1\), all \(I_{z_r}=0\), and its variance is one.

The coordinate \(x\) occurs at \(2^d\) nodes. Coordinate \(z_r\) occurs at \(2^{r-1}\) nodes, so the maximum count is \(2^d\). Every dummy-query node has two identical child functions \(x\), hence covariance one. At each depth \(r=0,\ldots,d-1\), there are \(2^r\) such nodes, each with weight \(2^{-r}\), so that depth contributes one. The \(x\)-query nodes have constant children and contribute zero. The total covariance is therefore \(d\), and the weighted potential is \(I_x\log_2(2^d)=d\). \(\square\)

This proves that the coefficient of \(I(f)\log_2k\) cannot be reduced below one uniformly over all such trees. It does **not** prove that logarithmic dependence is necessary in a Fourier entropy bound: a dictator has Fourier entropy zero. Representation-dependent covariance and function-dependent Fourier entropy must not be conflated.

# A four-variable counterexample to the proposed variance bound

## Proposition 5 {.unnumbered}
There is a read-three Boolean decision tree \(T\) on four coordinates, with no repeated coordinate on a root-to-leaf path, computing the two-variable AND function \(f\), such that
\[
\mathcal C(T)=\mathcal A(T)=\frac54
>\frac34\log_2 3
=\operatorname{Var}(f)\log_2 3.
\tag{13}
\]

**Construction.** Use coordinates \(x,y,z,t\), each taking values in \(\{-1,1\}\). Let \(D_x\) be the one-query dictator tree labelled \(x\), with leaves \(+1\) and \(-1\) in its positive and negative branches, respectively. Define \(D_y\) analogously. Write \(N_i(S_-,S_+)\) for the tree with root query \(i\), negative subtree \(S_-\) first, and positive subtree \(S_+\) second. With \(-\) denoting the leaf labelled \(-1\), put
\[
\begin{aligned}
L&=N_x\bigl(-,N_t(D_y,D_y)\bigr),\\
R&=N_y\bigl(-,N_t(D_x,D_x)\bigr),\\
T&=N_z(L,R).
\end{aligned}
\tag{14}
\]

Thus the negative branch of the root queries \(x\); after a positive answer it asks the irrelevant coordinate \(t\), then asks \(y\), independently of the answer to \(t\). The positive branch does the same with \(x\) and \(y\) interchanged. A negative answer to the first substantive query leads directly to the negative leaf. This branch convention agrees with the Lean witness, whose first child is the false/negative branch.

**Proof.** Each of \(L,R,T\) computes
\[
f(x,y,z,t)=
\begin{cases}
+1,&x=y=+1,\\
-1,&\text{otherwise}.
\end{cases}
\tag{15}
\]

The two possible full query sequences are \((z,x,t,y)\) and \((z,y,t,x)\), together with their shorter terminating prefixes. Therefore no coordinate is repeated along a path. The counts are
\[
k_x(T)=3,\qquad k_y(T)=3,\qquad
k_t(T)=2,\qquad k_z(T)=1.
\tag{16}
\]

The tree has nine internal nodes, and its read number is exactly three. A uniform input gives \(f=+1\) with probability \(1/4\), so
\[
\mathbb E f=-\frac12,\qquad
\operatorname{Var}(f)=1-\left(-\frac12\right)^2=\frac34.
\tag{17}
\]

Both root child functions equal \(f\), so their covariance is \(3/4\). At the root of \(L\), one child computes the dictator \(y\) and the other is constant, hence that node contributes zero covariance. The dummy \(t\)-query has two dictator children, whose covariance is one. Since this node is at depth one within \(L\), it follows that \(\mathcal C(L)=1/2\). Its descendant dictator nodes have constant children and hence zero covariance. The calculation for \(R\) is identical. Consequently,
\[
\mathcal C(T)=\frac34+\frac12\left(\frac12+\frac12\right)=\frac54.
\tag{18}
\]

All node covariances just computed are nonnegative, so \(\mathcal A(T)=\mathcal C(T)\). Finally,
\[
\log_2 3<\frac53
\quad\Longleftrightarrow\quad
3\log_2 3<5
\quad\Longleftrightarrow\quad
27<32,
\]

which is true. Multiplication by \(3/4\) proves (13). \(\square\)

## Scope of the refutation

The proposal appears immediately after Theorem 2.8 in Section 2.4 of Wan, Wright and Wu (2013/2014), and is explicitly called a conjecture in Section 6.2 of Shalev (2018/2019). It concerns the covariance of the given read-\(k\) representation. The original paper's decision-tree convention in Section 2.1 rules out repeated queries along a path; it does not require the tree to have minimum size, to have minimum expected depth, or to omit irrelevant queries. Its Figure 2 and accompanying discussion explicitly use dummy-query layers with identical child functions. The construction (14) respects precisely that scope.

This counterexample does not address an existential statement asserting that every function has *some* suitably efficient representation obeying a logarithmic variance estimate. The AND function itself has a read-once tree with zero tree covariance. The refuted statement quantifies over all given read-\(k\) trees, as in the proposed improvement to the published covariance lemma.


# Counterexample with every query relevant

## Proposition 6 {.unnumbered}
There is a nine-variable read-three tree, with no coordinate repeated on a path and with different child functions at every internal node, for which
\[
\mathcal C(T)=\frac{4863}{4096},\qquad
\operatorname{Var}(f)=\frac{3007}{4096},\qquad
\mathcal C(T)>\log_2(3)\operatorname{Var}(f).
\tag{19}
\]

**Construction.** Use Boolean coordinates \(z,x,y,u,v,r_1,r_2,r_3,r_4\), with false and true encoded as -1 and +1 for computing moments. Let \(R=r_1\lor r_2\lor r_3\lor r_4\), implemented by its short-circuit OR tree. Use \(Q_i\) for a single query of coordinate \(i\), and write \(N_i(A,B)\) with the false branch first and the true branch second, as above. Put
\[
\begin{aligned}
L&=N_x\bigl(-,N_u(Q_y,N_y(-,R))\bigr),\\
M&=N_y\bigl(-,N_v(Q_x,N_x(-,R))\bigr),\\
T&=N_z(L,M).
\end{aligned}
\tag{20}
\]

Thus the left child function is the signed encoding of
\(x\land y\land(\neg u\lor R)\), while the right child function is the signed encoding of
\(x\land y\land(\neg v\lor R)\). The same four OR coordinates are used in both branches. The exact query-count vector, in the displayed coordinate order, is
\[
(1,3,3,1,1,2,2,2,2).
\tag{21}
\]

No path repeats a coordinate. Each OR query has distinct child functions. The \(x\) and \(y\) queries gate a nonconstant positive branch; the \(u\) and \(v\) queries distinguish a dictator from its conjunction with \(R\). At the root, taking \(x=y=1\), all \(r_i=0\), and \(u\ne v\) distinguishes the two child functions. Hence every internal query affects its subtree's output. The Lean theorem checks inequality of the actual child functions, not merely syntactic inequality of the subtrees.

**Exact moment calculation.** Put \(\epsilon=\Pr[R=0]=1/16\). Both child functions \(g,h\) have positive-output probability
\[
p=\frac14\left(1-\frac\epsilon2\right)=\frac{31}{128},
\qquad \mathbb E g=\mathbb E h=2p-1=-\frac{33}{64}.
\]

Since the root bit is independent, \(\mathbb E f=-33/64\), and therefore
\(\operatorname{Var}(f)=1-(33/64)^2=3007/4096\).
The probability that both child outputs are positive is
\[
p_{++}=\frac14\left((1-\epsilon)+\frac\epsilon4\right)=\frac{61}{256}.
\]

Consequently
\[
\mathbb E[gh]=1-4p+4p_{++}=\frac{63}{64},\qquad
\operatorname{Cov}(g,h)=\frac{2943}{4096}.
\]

For a dictator \(Y\) and the signed encoding of \(Y\land R\), the covariance is
\(1-\epsilon=15/16\): the dictator has mean zero, and their product is negative exactly when \(Y=1\) and \(R=0\). The outer query of each child tree has a constant branch and hence covariance zero. Its selector query contributes \(15/16\) at depth one; all remaining nodes also have a constant branch and contribute zero. Thus
\[
\mathcal C(L)=\mathcal C(M)=\frac{15}{32},\qquad
\mathcal C(T)=\frac{2943}{4096}+\frac{15}{32}=\frac{4863}{4096}.
\]

Finally, \(3^5=243<256=2^8\) gives \(\log_2 3<8/5\), and
\[
8\cdot3007=24056<24315=5\cdot4863.
\]

Multiplying these strict inequalities by the appropriate positive denominators proves (19). This counterexample satisfies the additional local relevance condition as well as the original tree convention. It is not asserted to be a tree of minimum size or minimum expected depth. \(\square\)

# Relation to previous work

Wan, Wright and Wu introduced tree covariance to bound the expected length of a protocol for encoding a function's Fourier spectrum. Their Lemmas 1.5 and 1.7 connect this protocol to Fourier entropy. Their covariance estimate is \(\mathcal C(T)\leq(k-1)\operatorname{Var}(f)\). Section 2.4 of their paper proposes the stronger bound \(\mathcal C(T)\leq\log_2(k)\operatorname{Var}(f)\) and gives the dummy-prefix equality construction used in Proposition 4. Propositions 5 and 6 refute that stronger bound for a given tree.

Shalev's Section 6.2, Theorem 31, proves \(\mathcal C(T)\leq2\sqrt{k}I(f)\). The same section proposes the Fourier weight \(\ell_T(S)=\sum_{i\in S}\log_2 k_i(T)\). After interchanging finite sums, this gives the potential in Theorem 3, since \(I_i(f)=\sum_{S\ni i}\widehat f(S)^2\). The logarithmic potential is therefore due to Shalev. Inequality (1) proves its covariance bound through an induction on the tree. The theorem also bounds the sum of absolute node covariances.

## Distinct read parameters and selector hypotheses

Arunachalam et al. prove a logarithmic read-number bound for Fourier min-entropy of disjunctive normal form (DNF) formulas. A DNF is a disjunction of conjunctions of literals. Its read number counts terms that contain a variable. Shmalo's Theorem 5.1 gives Fourier-entropy bounds for unions and intersections of structured gates. Its read parameter counts constituent gates that depend on a coordinate. These parameters differ from the query-node count in a decision tree.

In a tree, \(k_i\) counts query nodes. Converting each accepting root-to-leaf path into a DNF term can repeat a root variable in arbitrarily many terms, even when the tree queries it only once. This conversion does not preserve the read number \(k\).

Shmalo's Proposition 8.6 gives general identities for selectors with shared data. Those identities do not require balanced data functions or disjoint Fourier supports. Corollaries 8.7 and 8.8 impose further hypotheses, including orthogonality conditions between neighboring branches. Arbitrary tree children need not satisfy these conditions. For example, both children can be the same dictator and thus have the same nonempty Fourier support. The general identities alone do not give the covariance estimate (8).

González, MacManus and Pereyra obtain Fourier entropy-influence bounds for further function classes through a restriction inequality. Han bounds Fourier entropy in terms of total influence and coordinate influences with reciprocal-logarithm weights. These results concern Fourier entropy; neither is a statement of the representation-dependent covariance bound proved here.

## Consequences and limits

Theorem 3 replaces the square-root dependence in Shalev's covariance estimate by a logarithm. Proposition 4 shows that its coefficient one is optimal for infinitely many read numbers. The example computes a dictator, whose Fourier entropy is zero. It therefore establishes sharpness of the covariance estimate, not sharpness of a Fourier-entropy bound.

The logarithmic influence estimate and the earlier variance estimate give different information. Influence can be much larger than variance, so Theorem 3 need not improve the earlier variance estimate for every function. Propositions 5 and 6 refute the coefficient-one logarithmic variance proposal. They do not determine the optimal asymptotic bound in terms of variance and read number alone.

The formal development contains no Fourier transform, Shannon entropy, or coding theorem. Its results are the covariance inequalities, their equality family, and the finite counterexamples. The cited encoding protocol gives the motivation. The unrestricted Fourier entropy-influence conjecture is not resolved here.

# Lean verification and reproducibility

The accompanying project formalizes the results proved in this note in Lean 4.19.0, using mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The project defines its own finite Boolean cube, uniform expectation, bit-flip influence, tree syntax, evaluation, global label counts, and signed and absolute tree covariance. The regularity predicate rules out repeated coordinates on a root-to-leaf path. No theorem is replaced by a hypothesis asserting the desired conclusion.

The main correspondence is:

| Result | Formal declaration, within the \texttt{\seqsplit{ReadK}} namespace |
| ------------------ | ------------------------------------------------------------------------- |
| Lemma 1 | \texttt{\seqsplit{abs\_cov\_le\_sum\_min}} |
| Lemma 2 | \texttt{\seqsplit{logCount\_potential}} |
| Theorem 3, weighted | \texttt{\seqsplit{Tree.absoluteCovariance\_le\_potential}} |
| Theorem 3, read bound | \texttt{\seqsplit{Tree.absoluteCovariance\_le\_log\_read\_mul\_influence}} |
| Proposition 4 | \texttt{\seqsplit{Sharpness.full\_equality\_family}} |
| Proposition 5 | \texttt{\seqsplit{Counterexample.variance\_refinement\_false}} and the exact witness statistics |
| Proposition 6 | \texttt{\seqsplit{Nonredundant.violates\_log\_variance}}, with its regularity, relevance, count, and moment theorems |

The development uses no proof holes or new axiom declarations. The transitive axiom audit is included in `verification/axioms.txt`; its permitted foundational axioms are propositional extensionality, classical choice, and quotient soundness. Finite decision proofs and algebraic tactics produce terms checked by Lean's kernel. No native evaluation oracle is used.

\newpage

After installing Lean's standard toolchain manager, reproduce the project from its root directory with:

```bash
lake exe cache get
bash verify.sh
python3 scripts/test_verifiers.py
```

The toolchain file and Lake manifest pin the compiler and dependencies. Keep the supplied manifest when reproducing these results. The optional cache step downloads official compiled mathlib dependencies; the verification script rebuilds this project's proof sources, prints the theorem types and their axiom dependencies, scans the sources, and runs an independent exact-rational check of both finite counterexamples. The Python computation is a supplementary check and does not replace any Lean proof. Omitting the cache step causes dependencies to be built from source.

The verifier tests check that invalid or incomplete evidence produces a nonzero exit status. The package includes a summary of the cited prior work in `docs/related-work.md`. Formal verification establishes the statements in the specified finite model. It does not establish literature priority.

# Authorship and assistance {.unnumbered}

Dev D. Goyal directed the research and is responsible for publication. ChatGPT (OpenAI) contributed mathematical arguments and Lean formalizations. Codex assisted with verification and editing.

# References {.unnumbered}

1. Andrew Wan, John Wright, and Chenggang Wu. *Decision Trees, Protocols, and the Fourier Entropy-Influence Conjecture*. ITCS 2014, pp. 67–80. DOI: <https://doi.org/10.1145/2554797.2554806>. Preprint: <https://arxiv.org/abs/1312.3003>.
2. Guy Shalev. *On the Fourier Entropy Influence Conjecture for Extremal Classes*. arXiv:1806.03646, v2, 24 January 2019. <https://arxiv.org/abs/1806.03646v2>.
3. Srinivasan Arunachalam, Sourav Chakraborty, Michal Koucký, Nitin Saurabh, and Ronald de Wolf. *Improved Bounds on Fourier Entropy and Min-entropy*. ACM Transactions on Computation Theory 13(4), Article 22, 2021. DOI: <https://doi.org/10.1145/3470860>. Preprint: <https://arxiv.org/abs/1809.09819>.
4. María José González, Paul MacManus, and María Cristina Pereyra. *Further evidence towards the Fourier Entropy-Influence conjecture*. arXiv:2606.00246v2, 9 June 2026. <https://arxiv.org/abs/2606.00246v2>.
5. Yitzchak Shmalo. *Fourier entropy of threshold functions and their compositions*. arXiv:2610.16069v1, 12 October 2026. <https://arxiv.org/abs/2610.16069v1>.
6. Xiao Han. *A New Bound for the Fourier-Entropy-Influence Conjecture*. Combinatorica 45, Article 4, 2025. <https://doi.org/10.1007/s00493-024-00133-z>.
