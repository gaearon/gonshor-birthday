# Gonshor's birthday conjecture

Let $\ell(x)$ denote the length of the sign sequence of a surreal number $x$, which
is its birthday, and let $\otimes$ denote the natural product of ordinals.

**Theorem.** For all surreal numbers $x$ and $y$,

```math
\ell(xy)\le\ell(x)\otimes\ell(y).
```

Gonshor states this as a conjecture in *An Introduction to the Theory of Surreal
Numbers*, Chapter 6, p. 96. The bound is attained whenever $x$ and $y$ are
ordinals, so no slack is available in any step below.

**Strategy.** Write $x$ and $y$ in Conway normal form. By Gonshor's sign formula
the sign sequence of a normal form is a concatenation of blocks, one for each
term, so its length is an ordered sum (Section 2). We first replace the
coefficients by positive ones without changing $\ell(x)$ or $\ell(y)$ or decreasing
$\ell(xy)$, so that no terms cancel in the product (Section 3). The block of $xy$
coming from one term of $x$ and one term of $y$ is at most the natural product of
the two blocks; for monomials this is Theorem 4.2, an inequality about the sign
sequence of a sum of two exponents, and it is the heart of the proof (Section 4).
Finally the blocks of $xy$, in their order, form a linear extension of the
product of the block orders of $x$ and $y$, whose order type is at most the
natural product (Section 5).

Each section ends with the Lean names of its statements. Lemma 3.1 is proved in
outline; all other proofs are given. The written proofs in Section 4 use
Gonshor's sign formula for the facts about normal forms, whereas the Lean proves
those facts directly from the definition of surreals as cuts; the statements are
the same.

## 1. Preliminaries

### Ordinals

Sums, products and powers of ordinals are the ordinary ones; $\oplus$ and $\otimes$
are the natural sum and product. We write $\sum_{i\in I}^{\mathrm{ord}}\gamma_i$ for
the ordered sum of ordinals over a well-ordered index set, that is, the order
type of the concatenation. Every ordinal is uniquely a finite sum of powers of
$\omega$ with nonincreasing exponents; these powers are its *Cantor terms*,
counted with multiplicity, and their exponents its *Cantor exponents*. We use
the following facts.

- (O1) If every Cantor exponent of $\nu$ is at least $\gamma$ and $\sigma\lt\nu$,
  then $\sigma+\omega^\gamma\le\nu$.
- (O2) $(\sigma+\tau)\otimes\upsilon\ge\sigma\otimes\upsilon+\tau\otimes\upsilon$.
- (O3) $\otimes$ is strictly increasing in each argument when the other is
  nonzero, and the Cantor exponents of $\sigma\otimes\tau$ are the natural sums
  of those of $\sigma$ and $\tau$.

**Theorem 1.1** (Carruth; de Jongh–Parikh). (a) Let $W$ be a well-ordered set
with maps $f\colon W\to\alpha$ and $g\colon W\to\beta$ into ordinals such that
$f(u)\le f(v)$ and $g(u)\le g(v)$ imply $u\le v$. Then the order type of $W$ is at
most $\alpha\otimes\beta$. (b) The product order on $\alpha\times\beta$ has a linear
extension of order type $\alpha\otimes\beta$.

### Sign sequences

For an ordinal $\delta\le\ell(x)$, let $x\upharpoonright\delta$ be the surreal whose
sign sequence is the initial segment of length $\delta$ of that of $x$. We call it
a *prefix* of $x$, proper if $\delta\lt\ell(x)$. Position $\delta$ of $x$ carries a
plus if $x\upharpoonright\delta\lt x$ and a minus if $x\upharpoonright\delta\gt x$.
Accordingly a proper prefix is a *left prefix* if it is less than $x$ and a
*right prefix* if it is greater; $R(x)$ is the set of right prefixes. The right
prefix *of a minus* is the prefix ending just before it. Longer right prefixes
are smaller. The surreals having a given prefix form a convex class. A set of
positions of $x$, or of proper prefixes of $x$, is *cofinal* in $\ell(x)$ if it
has an element beyond every $\delta\lt\ell(x)$; if $\ell(x)\gt0$ this forces
$\ell(x)$ to be a limit.

Let $p(x)$ be the order type of the set of plus positions of $x$. If $z$ is a
prefix of $x$ then $p(z)\le p(x)$, and $p(z)\lt p(x)$ if $z$ is a left prefix.

**Lemma 1.2** (options). Let $v$ be a right prefix of $a+b$. Then $u+b\le v$ for
some $u\in R(a)$, or $a+u\le v$ for some $u\in R(b)$. In either case $v$ is a
prefix of that sum. The same holds for left prefixes with the inequalities
reversed.

*Proof.* The sum $a+b$ is the simplest surreal greater than every $u+b$, $a+u$ with
$u$ a left prefix, and less than every $u+b$, $a+u$ with $u$ a right prefix. Since
$v$ is simpler than $a+b$ and greater, it is not less than all of the latter.
The chosen sum lies between $a+b$ and $v$, both of which have prefix $v$. $\qquad\square$

**Lemma 1.3** (van den Dries–Ehrlich, Lemma 3.4(1)). $p(a+b)\le p(a)\oplus p(b)$.

*Proof.* By induction on $\ell(a)\oplus\ell(b)$. Each left prefix $z$ of $a+b$ is, by
Lemma 1.2, a prefix of some $u+b$ or $a+u$ with $u$ a left prefix. In the first
case $p(z)\le p(u)\oplus p(b)\lt p(a)\oplus p(b)$, and similarly in the second.
Now $p(a+b)$ is the least ordinal greater than every such $p(z)$. $\qquad\square$

### Normal forms

Every surreal has a unique normal form $x=\sum_{i\lt\theta}r_i\omega^{a_i}$ with
strictly decreasing exponents $a_i$ and nonzero real coefficients $r_i$. Here
$\omega^a$ is Conway's omega-map. We write $c_x(a)$ for the coefficient of
$\omega^a$, which is zero unless $a$ lies in the support $\mathrm{supp}\\,x$, and
$x_{\gt a}$ for the sum of the terms of $x$ with exponent greater than $a$.
We write $\mathrm{supp}\\,x\gt s$ when every exponent of $x$ is greater than $s$.

A real $r$ has $\ell(r)\le\omega$, with $\ell(r)\lt\omega$ exactly when $r$ is dyadic.

**Lemma 1.4** (van den Dries–Ehrlich, Lemma 3.3). For reals $r,t$,
$\ell(rt)\le\ell(r)\otimes\ell(t)$.

We also use $\ell(x+y)\le\ell(x)\oplus\ell(y)$, which holds for all surreals.

| Statement | Lean |
|---|---|
| $\ell(x)$ | `Surreal.birthday` (CombinatorialGames) |
| $x\upharpoonright\delta$ | [`birthdayTruncation x δ`](GonshorBirthday/Surreal/Birthday/Prefix.lean) |
| left prefixes, $R(x)$ | [`leftPrefixes x`](GonshorBirthday/Surreal/Birthday/Canonical.lean), [`rightPrefixes x`](GonshorBirthday/Surreal/Birthday/Canonical.lean) |
| $p(x)$ | [`plusCount x`](GonshorBirthday/Surreal/Birthday/PlusCount.lean) |
| $c_x(a)$, $\mathrm{supp}\\,x$, $x_{\gt a}$ | [`x.coeff a`](GonshorBirthday/Surreal/HahnSeries/Transfer.lean), [`x.support`](GonshorBirthday/Surreal/HahnSeries/Transfer.lean), [`x.normalFormTrunc a`](GonshorBirthday/Surreal/HahnSeries/Transfer.lean) |
| (O1) | [`NatOrdinal.oadd_wpow_le_of_lt_of_le_cantorSupport`](GonshorBirthday/NatOrdinal/CantorSupport.lean) |
| (O2) | [`NatOrdinal.of_oadd_mul_le`](GonshorBirthday/NatOrdinal/ProductSum.lean) |
| (O3), Cantor exponents | [`NatOrdinal.cantorSupport_mul`](GonshorBirthday/NatOrdinal/CantorSupport.lean), [`NatOrdinal.le_cantorSupport_mul`](GonshorBirthday/NatOrdinal/CantorSupport.lean) |
| Theorem 1.1(a) | [`NatOrdinal.of_type_le_mul_of_coordinates`](GonshorBirthday/NatOrdinal/ProductOrder.lean) |
| Theorem 1.1(b) | [`NatOrdinal.exists_monotone_equiv_mul`](GonshorBirthday/NatOrdinal/ProductAttainment.lean) |
| Lemma 1.2, the inequalities | [`exists_rightPrefixes_add_le`](GonshorBirthday/Surreal/Birthday/Addition.lean), [`exists_leftPrefixes_add_ge`](GonshorBirthday/Surreal/Birthday/Addition.lean) |
| Lemma 1.2, the prefix assertion | [`birthdayTruncation_eq_of_right_between`](GonshorBirthday/Surreal/Birthday/Prefix.lean), [`birthdayTruncation_eq_of_left_between`](GonshorBirthday/Surreal/Birthday/Prefix.lean) |
| Lemma 1.3 | [`plusCount_add_le`](GonshorBirthday/Surreal/Birthday/Addition.lean) |
| Lemma 1.4 | [`birthday_real_mul_le`](GonshorBirthday/Surreal/Birthday/RealMultiplication.lean) |
| $\ell(x+y)\le\ell(x)\oplus\ell(y)$ | `Surreal.birthday_add_le` (CombinatorialGames) |

In the Lean source ordinals appear as `NatOrdinal`, on which `+` and `*` are
$\oplus$ and $\otimes$. An ordinary sum is written `NatOrdinal.of (a.val + b.val)`,
and an ordered sum is `typeLT (Σₗ i, (A i).val.ToType)`. A real is called dyadic
by stating that its birthday is less than $\omega$. The prefix
`birthdayTruncation x δ` is defined for every ordinal $\delta$ without reference to
sign sequences, as the simplest surreal on the same side as $x$ of every number
born before day $\delta$.

## 2. The length of a normal form

The sign sequence of $\omega^a$ is a plus followed by one block for each sign of
$a$; the sign at position $\delta$ gives a block of length
$\omega^{p(a\upharpoonright\delta)+1}$ (Gonshor, Theorem 5.11). For a set $S$ of positions
of $a$ put

```math
E(a,S)=1+\sum_{\delta\in S}^{\mathrm{ord}}\omega^{p(a\upharpoonright\delta)+1},
```

so that $\ell(\omega^a)=E(a,S)$ with $S$ the set of all positions. Note that the
exponents refer to the plus count in $a$ itself, whatever $S$ is.

**Definition 2.1.** Let $H$ be a surreal. A surreal $w$ is admissible after $H$
if every exponent of $H$ is at least $w$ and $c_H(w)$ is dyadic; a zero
coefficient counts as dyadic. If $w$ is admissible, so is every $w'\lt w$. A
position of $a$ is retained after $H$ if it carries a plus, or if it carries a
minus whose right prefix is admissible after $H$. Let $G_H(a)=E(a,S)$ for $S$ the
set of retained positions, and for a real $r$ let

```math
L_H(a,r)=G_H(a)+\omega^{p(a)}\bigl(\ell(r)-1\bigr)\quad(r\ne0),\qquad L_H(a,0)=0.
```

**Theorem 2.2** (Gonshor, Theorems 5.11–5.12). Let $\mathrm{supp}\\,H\gt a$ and
$r\ne0$. For $r\gt0$ the sign sequence of $H+r\omega^a$ is that of $H$, followed by
a plus, then for each retained position $\delta$ of $a$, in order,
$\omega^{p(a\upharpoonright\delta)+1}$ copies of the sign of $a$ at $\delta$, then for
each sign of $r$ after the first, in order, $\omega^{p(a)}$ copies of it. For
$r\lt0$ the part after $H$ is that for $-r$ with all signs reversed. In particular
$\ell(H+r\omega^a)=\ell(H)+L_H(a,r)$, and for $x=\sum_{i\lt\theta}r_i\omega^{a_i}$,

```math
\ell(x)=\sum_{i\lt\theta}^{\mathrm{ord}}L_{x_{\gt a_i}}(a_i,r_i).
```

More precisely, the sign sequence of $x$ is the concatenation, in order, of the
blocks of its terms, the block of $r_i\omega^{a_i}$ being the part after
$H=x_{\gt a_i}$ just described; this includes normal forms of limit length. The
formula holds for negative and nondyadic coefficients. The Lean source
formalises the two length statements, and the sign sequences of a single term
and of the coefficient part of a term after a head.

**Examples.** (i) For $x=1+\omega^{-1}$ we have $H=1$ and $a=-1$, a single minus with
right prefix $0$. The only exponent of $H$ is $0$ and its coefficient is dyadic,
so the minus is retained, $G_H(-1)=1+\omega$, and $\ell(x)=1+(1+\omega)=\omega$. Indeed
the sign sequence of $x$ is two pluses followed by $\omega$ minuses.

(ii) For $x=\omega^{-1}+\omega^{-2}$ we have $H=\omega^{-1}$ and $a=-2$, two minuses
with right prefixes $0$ and $-1$. The exponent $-1$ of $H$ is less than $0$, so
the first minus is not retained; the second is. Hence $G_H(-2)=1+\omega$, although
$\ell(\omega^{-2})=1+\omega+\omega$, and $\ell(x)=\omega+\omega$.

| Statement | Lean |
|---|---|
| $E(a,S)$ | [`omegaExpansionLength a S`](GonshorBirthday/Surreal/Birthday/ReducedCost.lean) |
| $\ell(\omega^a)$ | [`birthday_wpow_eq_omegaExpansionLength`](GonshorBirthday/Surreal/Birthday/OmegaLength.lean) |
| admissibility is closed downward | [`support_ge_and_coeff_birthday_lt_of_lt`](GonshorBirthday/Surreal/Birthday/HeadRetention.lean) |
| retained after $H$ | [`headOmegaPositions H a`](GonshorBirthday/Surreal/Birthday/HeadCost.lean) |
| $G_H(a)$, $L_H(a,r)$ | [`headOmegaCost H a`](GonshorBirthday/Surreal/Birthday/HeadCost.lean), [`headCoefficientCost H a r`](GonshorBirthday/Surreal/Birthday/HeadCoefficientCost.lean) |
| Theorem 2.2, one term | [`birthday_head_real_mul_wpow_eq_headCoefficientCost`](GonshorBirthday/Surreal/Birthday/HeadCoefficientLength.lean) |
| Theorem 2.2, all terms | [`birthday_eq_ordered_term_costs`](GonshorBirthday/Surreal/Birthday/NormalFormLength.lean) |

## 3. Reduction to positive coefficients

By Theorem 2.2 the length of $x$ is determined by its support and the lengths of
its coefficients. It is moreover monotone in the latter.

**Lemma 3.1.** If $\ell(c_u(a))\le\ell(c_v(a))$ for every $a$, then $\ell(u)\le\ell(v)$.

Note that $\mathrm{supp}\\,u\subseteq\mathrm{supp}\\,v$, but the lemma is not termwise:
deleting a term of $v$ can cause minuses of later terms to be retained.

*Proof (outline).* By induction along the decreasing support of $v$ one shows

```math
\ell(u_{\gt a})+G_{u_{\gt a}}(a)\le\ell(v_{\gt a})+G_{v_{\gt a}}(a)
\qquad(a\in\mathrm{supp}\,v).
```

The induction hypothesis at the larger exponents first gives
$\ell(u_{\gt a})\le\ell(v_{\gt a})$. One then compares the two sides position by
position along $a$, the claim being that the left side through each position is
at most the right side through it. The only difficulty is a minus, with right
prefix $w$, that is retained after $u_{\gt a}$ but not after $v_{\gt a}$. By
Definition 2.1 there are two cases.

- $v$ has an exponent $a'$ with $a\lt a'\lt w$. Then $a'$ is not an exponent of
  $u$, so $u_{\gt a}=u_{\gt a'}$, and $w$ is also a right prefix of $a'$. The left
  side through the block of this minus is at most
  $\ell(u_{\gt a'})+G_{u_{\gt a'}}(a')$, which by the induction hypothesis at $a'$
  is at most $\ell(v_{\gt a})$.
- $w$ is an exponent of $v$ with nondyadic coefficient, while $c_u(w)$ is dyadic.
  Then the term of $v$ at $w$ ends with $\omega^{p(w)}\cdot\omega=\omega^{p(w)+1}$
  equal signs. If $c_u(w)\ne0$ then $w$ is an exponent of $u_{\gt a}$, so no
  earlier minus of $a$ is retained after $u_{\gt a}$, and the term of $u$ at $w$
  ends with fewer than $\omega^{p(w)+1}$ signs. By the induction hypothesis at
  $w$ and absorption, the left side through the block is again at most
  $\ell(v_{\gt a})$.

In both cases the block is bounded by the right side with no contribution from
$a$, so the comparison continues. Adding the coefficient terms
$\omega^{p(a)}(\ell(c(a))-1)$ and using Theorem 2.2 gives $\ell(u)\le\ell(v)$. The case
$c_u(a)=0$ is included. $\qquad\square$

**Definition 3.2.** Fix a positive transcendental real $\tau$. For a real $r$ let
$\hat r=\ell(r)$ if $r$ is dyadic and $\hat r=\tau$ otherwise. For a surreal $x$ let
$X$ be the surreal with $c_X(a)=\widehat{c_x(a)}$ for all $a$.

**Proposition 3.3.** Let $X,Y$ be obtained from $x,y$ as in Definition 3.2. Then

1. $X$ has the same support as $x$, and $L_{X_{\gt a}}(a,c_X(a))=L_{x_{\gt a}}(a,c_x(a))$
   for every $a$; hence $\ell(X)=\ell(x)$;
2. the coefficients of $X$ and $Y$ are positive, so
   $\mathrm{supp}\\,XY=\mathrm{supp}\\,X+\mathrm{supp}\\,Y$;
3. $\ell(xy)\le\ell(XY)$.

*Proof.* (1) We have $\ell(\hat r)=\ell(r)$: a positive integer $n$ has length $n$, and
$\tau$ is not dyadic. Also $\hat r=0$ only if $r=0$. Definition 2.1 depends only on
the support and on which coefficients are dyadic, so the term lengths agree, and
$\ell(X)=\ell(x)$ by Theorem 2.2. (2) is clear. (3) By Lemma 3.1 it suffices to
show $\ell(c_{xy}(a))\le\ell(c_{XY}(a))$ for each $a$. Both coefficients are sums
over the same finite set of pairs of exponents. If some contributing coefficient
of $x$ or $y$ is nondyadic, then $c_{XY}(a)$ is the value at $\tau$ of a nonconstant
polynomial with nonnegative integer coefficients, so it is transcendental and
has length $\omega$, the largest length of a real. Otherwise $c_{xy}(a)$ is a sum
of products $rt$ of dyadics, and by Lemma 1.4 its length is at most the sum of
the integers $\ell(r)\ell(t)=\hat r\hat t$, which is $c_{XY}(a)=\ell(c_{XY}(a))$. $\qquad\square$

| Statement | Lean |
|---|---|
| Lemma 3.1 | [`birthday_le_of_coeff_birthday_le`](GonshorBirthday/Surreal/Birthday/CoefficientComparison.lean) |
| $\hat r$, $X$ | [`birthdayReplacement τ r`](GonshorBirthday/Surreal/Birthday/CoefficientReplacement.lean), [`normalFormBirthdayReplacement τ x`](GonshorBirthday/Surreal/Birthday/NormalFormReplacement.lean) |
| Proposition 3.3(1), support | [`support_normalFormBirthdayReplacement`](GonshorBirthday/Surreal/Birthday/NormalFormReplacement.lean) |
| Proposition 3.3(1), terms | [`headCoefficientCost_trunc_normalFormBirthdayReplacement`](GonshorBirthday/Surreal/Birthday/HeadCoefficientCost.lean), from [`birthday_coeff_normalFormBirthdayReplacement`](GonshorBirthday/Surreal/Birthday/NormalFormReplacement.lean) and [`headOmegaCost_trunc_normalFormBirthdayReplacement`](GonshorBirthday/Surreal/Birthday/ReplacementCost.lean) |
| Proposition 3.3(1), $\ell(X)=\ell(x)$ | [`birthday_normalFormBirthdayReplacement`](GonshorBirthday/Surreal/Birthday/NormalFormInvariance.lean) |
| Proposition 3.3(2) | [`mem_support_mul_normalFormBirthdayReplacement`](GonshorBirthday/Surreal/Birthday/NormalFormReplacement.lean) |
| Proposition 3.3(3), coefficients | [`birthday_coeff_mul_le_normalFormBirthdayReplacement`](GonshorBirthday/Surreal/Birthday/NormalFormReplacement.lean); the passage to $\ell(xy)\le\ell(XY)$ is inside [`Surreal.birthday_mul_le`](GonshorBirthday/Surreal/Birthday/Multiplication.lean) |

## 4. The monomial estimate

### Statement

**Definition 4.1.** Let $C$ be a surreal and $z$ a prefix of $a$. A position of $z$
is retained below $C$ if it carries a plus, or a minus whose right prefix is at
most $C$. Let $D(C,z)=E(z,S)$ for $S$ the set of these positions, and for a
surreal $d\ge0$ put $F_d(a)=D(a+d,a)$.

Thus a minus is counted in $F_d(a)$ when its right prefix is within $d$ of $a$.
Note that $D(C,z)$ depends on $z$ and $C$ only, a prefix of $z$ being a prefix of
$a$. We record the basic properties.

- (D1) $D(C,a)$ is nondecreasing in $C$, and $D(C,z)\le D(C,a)$ for a prefix $z$
  of $a$.
- (D2) The retained minuses form a final segment of the minuses of $a$, since
  longer right prefixes are smaller.
- (D3) $F_0(a)=\omega^{p(a)}$, and every Cantor exponent of $D(C,a)$ is at least
  $p(a)$.
- (D4) If $w$ is the right prefix of a retained minus of $a$, then
  $D(C,w)+\omega^{p(w)+1}\le D(C,a)$, and if moreover $p(w)\lt p(a)$ then
  $D(C,w)+\omega^{p(w)+1}+\omega^{p(a)}\le D(C,a)$. If $a$ is $z$ followed by
  $\rho\gt0$ pluses, then $D(C,a)=D(C,z)+\omega^{p(a)}$.
- (D5) Let $T$ be a set of surreals greater than $a$. There is $C\gt a$ such that
  an element of $T\cup R(a)$ is admissible after $H$ exactly when it is at most
  $C$. For such $C$, $G_H(a)=D(C,a)$. This holds because admissibility is closed
  downward.
- (D6) Suppose $D(C',z)=\omega^\lambda$ and $C\le C'$, and some minus of $z$ is
  retained below $C$. Then $D(C,z)\ge\omega^\lambda$. Indeed by (D2) both cutoffs
  retain the same positions from that minus onward, and the corresponding final
  part of the sum $D(C',z)$ is nonzero, hence equal to $\omega^\lambda$.

**Theorem 4.2.** For all surreals $a,b$ and all $A\ge a$, $B\ge b$,

```math
D\bigl(\min(A+b,\,a+B),\,a+b\bigr)\le D(A,a)\otimes D(B,b).
```

Equivalently, $F_d(a+b)\le F_d(a)\otimes F_d(b)$ for all $d\gt0$.

The two forms are equivalent by (D1): take $d=\min(A-a,B-b)$, the case $d=0$
being (D3) and Lemma 1.3. With $A$ and $B$ large the theorem reads
$\ell(\omega^{a+b})\le\ell(\omega^a)\otimes\ell(\omega^b)$.

**Example.** The bound is attained in a case where a minus is deleted. Let
$a=\omega-\tfrac12$, with sign sequence $\omega$ pluses, a minus and a plus, and
$A\ge\omega$; then $D(A,a)=\omega^\omega+\omega^{\omega+1}+\omega^{\omega+1}=\omega^{\omega+1}\cdot2$.
Let $b=-1$ and $B=-\tfrac12$; then $D(B,b)=1$. The sum $\omega-\tfrac32$ is $\omega$
pluses, two minuses and a plus, with right prefixes $\omega$ and $\omega-1$, and
the cutoff is $\omega-1$. So the first minus is deleted and the left side is again
$\omega^{\omega+1}\cdot2$.

### Right prefixes of normal forms

This subsection collects what the proof needs about the end of the sign sequence
of a normal form. Nothing here involves the induction. Throughout, a real $r$
*ends in a minus* if it is a nonzero dyadic whose sign sequence has last sign
minus; then $t$ denotes the real obtained by deleting that sign, so $t=0$ exactly
when $r=-1$, and $0\lt t-r\le1$. For a surreal $z$ and $d\ge0$, we say that $d$
*deletes* $z$ if $z+d\lt w$ for every $w\in R(z)$.

Fix an exponent $s$ and put $q=p(s)$, $Q=\omega^q$. For $\alpha\lt q$ let $u_\alpha$ be
the prefix of $s$ ending just before its plus number $\alpha$, counted from zero.
The $u_\alpha$ are exactly the left prefixes of $s$; they increase with $\alpha$, and
$p(u_\alpha)=\alpha$. Every minus of $u_\alpha$ has a right prefix that is also a
right prefix of $s$, hence greater than $s$. For $\eta\lt Q$ with Cantor normal form
$\eta=\omega^{\alpha_1}n_1+\dots+\omega^{\alpha_k}n_k$ put

```math
\Phi_s(\eta)=n_1\omega^{u_{\alpha_1}}+\dots+n_k\omega^{u_{\alpha_k}}.
```

This is a normal form. The map $\Phi_s$ is strictly increasing, $\Phi_s(0)=0$,
and for $\eta\gt0$ we have $\Phi_s(\eta)\le n\omega^{u}$ for some left prefix $u$ of
$s$ and some $n$; in particular $\Phi_s(\eta)$ is infinitesimal relative to
$\omega^s$. The quantities $q$, $Q$, $u_\alpha$ and $\Phi_s$ always refer to the
exponent called $s$ in the statement at hand.

**Lemma 4.3** (prefixes). (a) Every truncation $x_{\gt a}$ is a prefix of $x$, and
so is $x_{\gt a}+c_x(a)\omega^a$. (b) If $w$ is a proper prefix of $x$, then
$|w-x|\ge\varepsilon\omega^a$ for some exponent $a$ of $x$ and some real
$\varepsilon\gt0$. (c) If $\mathrm{supp}\\,K\gt s$ and the real $t$ is a prefix of the
real $r$, then $K+t\omega^s$ is a prefix of $K+r\omega^s$.

*Proof.* (a) and (c) are read off from Theorem 2.2: the blocks of the terms are
concatenated in order, and the block of $t\omega^s$ after $K$ is an initial part
of that of $r\omega^s$; for $t=0$ use (a). (b) Otherwise $w-x$ is infinitesimal
relative to every monomial of $x$, so $x$ is a truncation of $w$ and hence a
prefix of $w$ by (a). $\qquad\square$

**Lemma 4.4** (short runs). Let $z=K+r\omega^s$ with $\mathrm{supp}\\,K\gt s$ and
$r\ne0$. For $\eta\lt Q$, the surreal $z$ followed by $\eta$ pluses is
$z+\Phi_s(\eta)$, and $z$ followed by $\eta$ minuses is $z-\Phi_s(\eta)$.

*Proof.* The normal form of $z+\Phi_s(\eta)$ is that of $z$ followed by the terms
$n_i\omega^{u_{\alpha_i}}$. Consider one such term, with $\alpha=\alpha_i$. The right
prefix of each minus of $u_\alpha$ is greater than $s$, which is an exponent of
the head, so it is not admissible and the minus is not retained. The pluses of
$u_\alpha$ give $1+\sum_{\beta\lt\alpha}\omega^{\beta+1}=\omega^\alpha$ pluses, and the
coefficient $n_i$ gives $\omega^\alpha(n_i-1)$ more. By Theorem 2.2 the term
contributes exactly $\omega^\alpha n_i$ pluses, and the terms together contribute
$\eta$ pluses. The case of minuses is the same with all signs reversed. $\qquad\square$

**Lemma 4.5** (the last block). Let $z=K+r\omega^s$ with $\mathrm{supp}\\,K\gt s$ and
$r$ ending in a minus, and put $W=K+t\omega^s$. Then:

1. $W\in R(z)$, and $W-z=(t-r)\omega^s\le\omega^s$;
2. $W-n\omega^{u}\in R(z)$ for every left prefix $u$ of $s$ and every $n\ge1$;
3. every $w\in R(z)$ satisfies $w\ge W$, or $w\ge W-n\omega^u$ for some left prefix
   $u$ of $s$ and some $n\ge1$;
4. the minuses of $z$ at or after position $\ell(W)$ have order type at most $Q$.

*Proof.* Suppose first $t\ne0$. By Theorem 2.2 the sign sequence of $z$ is that of
$W$ followed by $Q$ minuses, the copies of the last sign of $r$. This gives (1)
and (4). By Lemma 4.4 applied to $W$, the prefixes of $z$ beyond $W$ are the
$W-\Phi_s(\eta)$ with $\eta\lt Q$. Taking $\eta=\omega^\alpha n$ gives (2). For (3), a
right prefix of $z$ that is a prefix of $W$ is at least $W$, shorter right
prefixes being larger, and every nonzero $\eta\lt Q$ is at most some
$\omega^\alpha n$.

Now let $t=0$, so $z=K-\omega^s$ and $W=K$. By Theorem 2.2 the sign sequence of $z$
is that of $K$, then a minus, then the blocks of the retained positions of $s$
with signs reversed. So $K\in R(z)$, and the later minuses of $z$ come from the
pluses of $s$: plus number $\alpha$ gives $\omega^{\alpha+1}$ minuses. Their total
number is $1+\sum_{\alpha\lt q}\omega^{\alpha+1}=Q$, which is (4). The prefix of $z$
just before the block of plus number $\alpha$ is $K-\omega^{u_\alpha}$, the retained
positions of $u_\alpha$ after $K$ being those of $s$ before that plus. Within that
block, the prefix after $\omega^\alpha(n-1)$ further minuses is $K-n\omega^{u_\alpha}$,
again by Theorem 2.2, the coefficient $-n$ contributing $\omega^\alpha(n-1)$
minuses. This gives (2), and (3) because these prefixes are cofinal in each
block, while a right prefix of $z$ that is a prefix of $K$ is at least $K$. $\qquad\square$

**Lemma 4.6** (small gaps). Let $x$ be an exponent of $z$ and $v\in R(x)$. For every
real $\varepsilon\gt0$ there is $w\in R(z)$ with $w-z\lt\varepsilon\omega^v$.

*Proof.* Let $y$ be the largest exponent of $z$ less than $v$; it exists because
$x\lt v$. Since $v$ is a prefix of $x$ and $x\le y\lt v$, also $v\in R(y)$. Every
exponent of $z_{\gt y}$ is at least $v$. Let $c=c_z(y)$ and $T=z_{\gt v}$.

If $c\lt0$, then $z_{\gt y}$ is a right prefix of $z$ by Lemma 4.3(a), and its
distance from $z$ is infinitesimal relative to $\omega^v$.

If $c_z(v)$ is nondyadic, the real right prefixes $c_n$ of $c_z(v)$ decrease to
it, and the $T+c_n\omega^v$ are right prefixes of $z$ by Lemma 4.3(a),(c), at
distance less than $2(c_n-c_z(v))\omega^v$.

Otherwise $c\gt0$ and $v$ is admissible after $z_{\gt y}$, so the minus of $y$ with
right prefix $v$ is retained in the block of the term $c\omega^y$, where it
gives $\omega^{p(v)}\cdot\omega$ minuses. If $v$ is not an exponent of $z$, the
prefix of $z$ just before these minuses is $z_{\gt y}+\omega^v$, and after
$\omega^{p(v)}n$ of them it is $z_{\gt y}+2^{-n}\omega^v$, by Theorem 2.2. If $v$ is
an exponent of $z$, with dyadic coefficient $c_v$, then no earlier minus of $y$
is retained, the pluses of $y$ before $v$ form one block of $\omega^{p(v)}$
pluses, and the prefixes are $T+c_n\omega^v$, where $c_n$ is $c_v$ followed by a
plus and $n$ minuses. In both cases the prefixes are right prefixes of $z$ whose
distance from $z$ is less than a real multiple of $\omega^v$ tending to zero. $\qquad\square$

**Lemma 4.7** (last term). Let $z$ be a prefix of $e$, and suppose that $d$
deletes $z$ and that $w_0\le e+d$ for some $w_0\in R(z)$. Then $z=K+r\omega^s$ with
$\mathrm{supp}\\,K\gt s$ and $r$ a nonzero dyadic. If moreover the right prefixes of
$z$ are cofinal in $\ell(z)$, then $r$ ends in a minus.

*Proof.* For $v\in R(z)$ we have $d\lt v-z$, and $e-z\lt v-z$ since $e$ has prefix
$z$. Hence

```math
w_0-z\le(e-z)+d\lt2(v-z)\quad\text{for all }v\in R(z).\qquad(\ast)
```

*The support has a least element.* It is nonempty, as $R(z)$ is. Suppose
it has no least element. By Lemma 4.3(b),
$w_0-z\ge\varepsilon\omega^a$ for some exponent $a$ of $z$. Choose exponents
$a\gt x_0\gt x_1\gt\cdots$ of $z$. The lengths $\ell(x_i)$ cannot decrease forever,
so some $x_{i+1}$ is not a prefix of $x_i$; then their longest common prefix $v$
is a right prefix of $x_{i+1}$ with $v\le x_i\lt a$. Lemma 4.6 gives $w\in R(z)$
with $w-z\lt\omega^v$, so $2(w-z)\lt w_0-z$, contrary to $(\ast)$.

*The last coefficient is dyadic.* Let $z=K+r\omega^s$ with $r$ nondyadic. By
Lemma 4.3(b), $w_0-z\ge\varepsilon\omega^a$ for an exponent $a\ge s$ of $z$, hence
$w_0-z\ge\varepsilon\omega^s$. The real right prefixes $r_n$ of $r$
decrease to $r$, and $K+r_n\omega^s\in R(z)$ by Lemma 4.3(c), at distance
$(r_n-r)\omega^s$. Again $(\ast)$ fails.

*Cofinal right prefixes force a final minus.* Suppose $r$ ends in a
plus. If $r\ne1$, then by Theorem 2.2 the sign sequence of $z$ ends with $Q$
pluses, so the right prefixes are not cofinal. Let $r=1$. By Theorem 2.2 the
part of the sign sequence of $z$ after $K$ is a plus followed by the blocks of
the retained positions of $s$. Since the right prefixes are cofinal it does not
end in a plus, so $s$ has a retained minus; and the retained minuses of $s$ are
a final segment of its minuses. So either they have no last element, or the
last one is the last sign of $s$. As in the proof of Lemma 4.6, each such minus,
with right prefix $v$, yields right prefixes of $z$ of the form $K+c\omega^v$
with $c\gt0$ real, or $K'+c\omega^v$ with $c\gt c_K(v)$ real, where $K'$ is $K$
without its last term; their distance from $z$ is $c'\omega^v-\omega^s$ with
$c'\gt0$ real, and $v\gt s$. If the retained minuses have no last element, these right
prefixes occur with arbitrarily late $v$, and for $v'\lt v$ the distance at $v'$
is less than half of that at $v$. If there is a last retained minus, with right
prefix $v$, it is the last sign of $s$, and within its block the distances are
$c'2^{-n}\omega^v-\omega^s$, each less than half the preceding one. In both cases
choose such a right prefix below $w_0$ and then a later one at less than half
the distance, contradicting $(\ast)$. $\qquad\square$

**Lemma 4.8** (margin and full block). Let $z=K+r\omega^s$ with $\mathrm{supp}\\,K\gt s$
and $r$ ending in a minus, and suppose $d$ deletes $z$. Then $d\lt\omega^s$. If
moreover $e$ is $z$ followed by $\rho\gt0$ pluses and $w\le e+d$ for some
$w\in R(z)$, then $\rho\ge Q$.

*Proof.* By Lemma 4.5(1), $d\lt W-z\le\omega^s$. Suppose $\rho\lt Q$. Then $q\gt0$,
and $e=z+\Phi_s(\rho)$ by Lemma 4.4, with $\Phi_s(\rho)\le m\omega^{u'}$ for a left
prefix $u'$ of $s$. By Lemma 4.5(3), $w\ge W-n\omega^u$ for some left prefix $u$ of
$s$ and $n\ge1$; if $w\ge W$ any $u$ and $n$ will do. Let $u''$ be the larger of
$u,u'$. Then

```math
W-(n+m)\omega^{u''}\le w-\Phi_s(\rho)=w-(e-z)\le z+d,
```

and the left side is a right prefix of $z$ by Lemma 4.5(2). So $d$ does not
delete $z$. $\qquad\square$

**Lemma 4.9** (final minuses). Let $z=K+r\omega^s$ with $\mathrm{supp}\\,K\gt s$ and
$r$ ending in a minus, and suppose the right prefixes of $z$ are cofinal in
$\ell(z)$. If $D(C,z)=\omega^\lambda$, then $\lambda\le p(z)+1+q$.

*Proof.* If no minus of $z$ is retained below $C$, then $D(C,z)=F_0(z)$ and
$\lambda=p(z)$ by (D3). Otherwise the retained minuses are cofinal by (D2).
Consider the positions of $z$ from a retained minus at or after $\ell(W)$ onward,
and group each further retained minus with the maximal run of pluses
immediately preceding it; every plus lies in the group of the next retained
minus. A run of pluses
contributes at most $\omega^{p'}$, where $p'$ is the plus count at its end, and
the minus after it contributes $\omega^{p'+1}$; so each group contributes at
most $\omega^{p(z)+1}$. By Lemma 4.5(4) there are at most $Q$ groups, so this
final part of the sum $D(C,z)$ is at most $\omega^{p(z)+1}\cdot Q$. Being a
nonzero final part of $\omega^\lambda$, it equals $\omega^\lambda$. $\qquad\square$

**Lemma 4.10** (appending a block). If $z=K+r\omega^s$ with $\mathrm{supp}\\,K\gt s$
and $r$ a nonzero dyadic, then $z$ followed by $Q$ pluses is $K+r'\omega^s$, where
$r'$ is $r$ followed by a plus; in particular $r'$ is dyadic.

*Proof.* By Theorem 2.2, each sign of the coefficient after the first
contributes $Q$ equal signs, and for $r=-1$ the same holds for the second sign
of $r'=-\tfrac12$. $\qquad\square$

**Lemma 4.11** (sharp plus count). Suppose $p(a+b)=p(a)\oplus p(b)$ and
$a+b=K+r'\omega^s$ with $\mathrm{supp}\\,K\gt s$ and $r'$ dyadic, possibly zero.
Then no exponent of $a$ or $b$ is less than $s$, and $c_a(s)$ and $c_b(s)$ are
dyadic.

*Proof.* Suppose $a$ or $b$ has an exponent below $s$, and let $j$ be the largest
one. The coefficients of $a$ and $b$ at $j$ cancel, so one is positive, say that
of $a$. By Lemma 4.3(a), $a_{\gt j}$ is a left prefix of $a$ and $b_{\gt j}$ a prefix
of $b$, and their sum is $a+b$. Then
$p(a+b)\le p(a_{\gt j})\oplus p(b_{\gt j})\lt p(a)\oplus p(b)$ by Lemma 1.3.

So $a=A+c\omega^s$ and $b=B+c'\omega^s$ with $\mathrm{supp}\\,A,\mathrm{supp}\\,B\gt s$
and $c+c'=r'$. It suffices to show that $c$ is dyadic, since then so is
$c'=r'-c$. Suppose $c$ is nondyadic. The reals having the dyadic $r'$ as a prefix
form an open interval containing $r'$, and a nondyadic real is the limit of its
real left prefixes. So there is a real left prefix $c_0$ of $c$
such that $r'$ is a prefix of $c_0+c'$. Then $a'=A+c_0\omega^s$ is a left prefix
of $a$, and $a+b$ is a prefix of $a'+b=K+(c_0+c')\omega^s$, both by Lemma 4.3(c).
Hence $p(a+b)\le p(a'+b)\le p(a')\oplus p(b)\lt p(a)\oplus p(b)$. $\qquad\square$

**Lemma 4.12** (the input). Suppose no exponent of $a$ is less than $s$, $c_a(s)$
is dyadic, $d\le\omega^s$, $F_d(a)=\omega^{p(a)}$, and the minuses of $a$ retained
below $a+d$ are nonempty and cofinal in $\ell(a)$. Then $a=H-\omega^s$ with
$\mathrm{supp}\\,H\gt s$.
Moreover, if $d$ deletes some $K+r\omega^s$ with $\mathrm{supp}\\,K\gt s$ and $r$
ending in a minus, then $d$ deletes $H-\omega^s$.

*Proof.* The pluses of $a$ are cofinal in $\ell(a)$: otherwise some retained minus
comes after every plus, and alone contributes $\omega^{p(a)+1}\gt F_d(a)$.

Write $a=H+c\omega^s$ with $\mathrm{supp}\\,H\gt s$ and $c$ dyadic. If $c=0$, then by
Lemma 4.3(b) every $w\in R(a)$ has $w-a\ge\varepsilon\omega^{a'}$ for an exponent
$a'\gt s$ of $a$, so $w-a\gt\omega^s\ge d$ and no minus is retained. If
$c\ne\pm1$, then by Theorem 2.2 the sign sequence of $a$ ends with $Q$ equal
signs, so pluses and minuses are not both cofinal. If $c=1$, let $w\in R(a)$ and
$\delta=w-a$. If $\delta\le k\omega^s$ for some real $k$, write
$\delta=c_0\omega^s+\delta_0$ with $c_0\ge0$ real and $\delta_0$ infinitesimal
relative to $\omega^s$. Then $w=H+(1+c_0)\omega^s+\delta_0$, and $a=H+\omega^s$ is a
prefix of $H+(1+c_0)\omega^s$ by Lemma 4.3(c), which is a prefix of $w$ by
Lemma 4.3(a). This contradicts $w\in R(a)$. So again $w-a\gt\omega^s\ge d$ and no
minus is retained. Hence $c=-1$.

For the last assertion let $z=K+r\omega^s$ and $W=K+t\omega^s$ as in Lemma 4.5,
and let $w\in R(a)$. By Lemma 4.5(3) for $a$, either $w\ge H$, and then
$w-a\ge\omega^s\gt d$ by the first assertion of Lemma 4.8 for $z$; or $w\ge H-n\omega^u$ for a left prefix $u$ of
$s$ and $n\ge1$. In that case $W-n\omega^u\in R(z)$ by Lemma 4.5(2), so

```math
d\lt W-n\omega^u-z=(t-r)\omega^s-n\omega^u\le\omega^s-n\omega^u\le w-a.
```

$\qquad\square$

### Proof of Theorem 4.2

We prove the second form by induction on $\ell(a)\oplus\ell(b)$. Fix $a,b$, assume
the theorem for all pairs of smaller $\ell(a)\oplus\ell(b)$ and all cutoffs, and
write $e=a+b$. A margin $d\gt0$ *fails* if $F_d(e)\gt F_d(a)\otimes F_d(b)$. We
assume that some margin fails and derive a contradiction. The idea is in
Claims 1 and 2: the induction hypothesis controls $e$ through each retained
minus, so a failure must exhaust the bound along a limit of retained minuses and
then continue with a plus.

Claim 1 holds for every margin $d\gt0$; we write $N_d=F_d(a)\otimes F_d(b)$.

**Claim 1.** Let $v\in R(e)$ with $v\le e+d$. Then there is $u\in R(a)$ with
$u\le a+d$, $u+b\le v$ and $D(e+d,v)\le D(a+d,u)\otimes F_d(b)$, or the same holds
with $a$ and $b$ interchanged. Moreover

```math
D(e+d,v)+\omega^{p(v)+1}+\varepsilon\le N_d,
\qquad\varepsilon=\omega^{p(e)}\ \text{if }p(v)\lt p(e),\quad\varepsilon=0\ \text{otherwise}.
```

*Proof.* By Lemma 1.2 we may assume $u+b\le v$ with $u\in R(a)$, and $v$ is a
prefix of $u+b$. Then $u\le a+d$ since $v\le e+d$. The induction hypothesis for
the pair $(u,b)$ with cutoffs $a+d$ and $b+d$ bounds $D(C',u+b)$ by
$D(a+d,u)\otimes F_d(b)$, where $C'=\min(e+d,u+b+d)=e+d$. With (D1) this gives
the first assertion. For the second, (D4) for $a$ and (O2) give

```math
N_d\ge D(a+d,u)\otimes F_d(b)+\bigl(\omega^{p(u)+1}+\varepsilon'\bigr)\otimes F_d(b),
```

with $\varepsilon'=\omega^{p(a)}$ if $p(u)\lt p(a)$ and $0$ otherwise. By (D3),
$F_d(b)\ge\omega^{p(b)}$, and by Lemma 1.3, $p(v)\le p(u)\oplus p(b)$ and
$p(e)\le p(a)\oplus p(b)$. If $p(u)\lt p(a)$ the second summand is at least
$\omega^{p(u)\oplus p(b)+1}+\omega^{p(a)\oplus p(b)}\ge\omega^{p(v)+1}+\varepsilon$. If
$p(u)=p(a)$ it is at least $\omega^{p(a)\oplus p(b)+1}$. This is at least
$\omega^{p(v)+1}$, which settles the case $\varepsilon=0$. If $p(v)\lt p(e)$ then
$\omega^{p(v)+1}+\omega^{p(e)}\le\omega^{p(e)}\cdot2\lt\omega^{p(a)\oplus p(b)+1}$. $\qquad\square$

The argument does not apply to a plus of $e$. A left prefix of $e$ lies below a
left option $u+b$ with $u\lt a$, and then the cutoff $u+b+d$ for that option is
smaller than $e+d$, so the induction hypothesis no longer counts every retained
minus of $e$.

**Claim 2.** Let $d$ fail. There is a proper prefix $z$ of $e$, of limit length,
such that

1. $e$ is $z$ followed by $\rho\gt0$ pluses, so $z$ is a left prefix of $e$ and
   $p(z)\lt p(e)$;
2. the right prefixes $v\in R(z)$ with $v\le e+d$ are cofinal in $\ell(z)$;
3. $D(e+d,z)=N_d$.

*Proof.* By (D3), (O3) and Lemma 1.3, $\omega^{p(e)}\le N_d$ and every Cantor
exponent of $N_d$ is at least $p(e)$. Hence $e$ has a retained minus, as otherwise
$F_d(e)=\omega^{p(e)}$. If there were a last retained minus, with right prefix
$v$, then only pluses would follow it by (D2), and $F_d(e)$ would equal the left
side of the inequality in Claim 1. So there is none. Let $z$ be the shortest
prefix of $e$ containing every retained minus. It has limit length and satisfies
(2), and $D(e+d,z)$ is the supremum of the $D(e+d,v)$ over the retained $v$, so
$D(e+d,z)\le N_d$ by Claim 1. Thus $z\ne e$. By (D2) no minus of $e$ lies beyond
$z$, which gives (1), and $F_d(e)=D(e+d,z)+\omega^{p(e)}$ by (D4). If
$D(e+d,z)\lt N_d$ this would be at most $N_d$ by (O1). $\qquad\square$

**Claim 3.** Let $d$ fail. Then, for $a$ or for $b$ in its place, the following
holds: $F_d(b)=\omega^\beta$ for some $\beta$, and for every $\sigma\lt F_d(a)$ there is
$u\in R(a)$ with $u\le a+d$ and $\sigma\lt D(a+d,u)$. In particular the retained
minuses of $a$ are cofinal in $\ell(a)$.

*Proof.* By Claim 2, $N_d$ is the supremum of $D(e+d,v)$ over the retained
$v\in R(z)$. By the first part of Claim 1 each of these is at most
$D(a+d,u)\otimes F_d(b)$ or $F_d(a)\otimes D(b+d,u)$ for a retained $u$. One of the
two kinds occurs cofinally, say the first. So the products $D(a+d,u)\otimes F_d(b)$,
in which $D(a+d,u)\lt F_d(a)$, are cofinal in $F_d(a)\otimes F_d(b)$. By (O3) the
$D(a+d,u)$ are then cofinal in $F_d(a)$; taking $\sigma=0$ shows that $a$ has a
retained minus. If $F_d(b)$ had more than one Cantor term, write $F_d(a)=\mu+\omega^\gamma$ with $\omega^\gamma$ the last term and let
$\omega^{\beta_1}$ be the first term of $F_d(b)$; every product would be less than
$\mu\otimes F_d(b)\oplus\omega^{\gamma\oplus\beta_1}\lt N_d$. $\qquad\square$

**Claim 4.** There is a failing margin $d$ with $F_d(a)=\omega^\alpha$ and
$F_d(b)=\omega^\beta$.

*Proof.* Let $d_0$ fail, with $z$ as in Claim 2, and by Claim 3 assume
$F_{d_0}(b)=\omega^\beta$ and that the costs of the retained right prefixes of $a$
are cofinal in $F_{d_0}(a)$. Write $F_{d_0}(a)=\mu+\omega^\alpha$ with $\omega^\alpha$
the last Cantor term, so that $N_{d_0}=\mu\otimes\omega^\beta\oplus\omega^{\alpha\oplus\beta}$
has last term $\omega^{\alpha\oplus\beta}$. Choose a retained $u_0\in R(a)$ with
$D(a+d_0,u_0)\gt\mu$.

*Right prefixes below the option.* The retained right prefixes of $z$ lie
cofinally below $u_0+b$. Otherwise
$z\lt u_0+b\lt v$ for all $v\in R(z)$, so $u_0+b$ has prefix $z$, and the induction
hypothesis for $(u_0,b)$ gives
$N_{d_0}=D(e+d_0,z)\le D(a+d_0,u_0)\otimes F_{d_0}(b)\lt N_{d_0}$.

Choose such a right prefix $v_1\lt u_0+b$ of $z$, so late that also $v_1\lt e+d_0$
and $D(e+d_0,v_1)$ exceeds the part of $N_{d_0}$ before its last term. Put
$d=v_1-e$, so that $0\lt d\lt d_0$ and the cutoff $e+d$ is $v_1$.

- $D(e+d,z)=\omega^{\alpha\oplus\beta}$: the positions retained below $v_1$ are the
  pluses before $v_1$ and everything from $v_1$ onward. The latter sum to the
  last term of $N_{d_0}$, which absorbs the former because $p(v_1)\lt p(e)\le\alpha\oplus\beta$.
- $F_d(a)\le\omega^\alpha$ and $F_d(b)\le\omega^\beta$: the second is (D1). For the
  first, the positions of $a$ from the minus after $u_0$ onward sum to
  $\omega^\alpha$ in $F_{d_0}(a)$, because $D(a+d_0,u_0)\gt\mu$; as this sum contains
  the block $\omega^{p(u_0)+1}$, we get $p(u_0)\lt\alpha$. Since $a+d\lt u_0$, every
  minus of $a$ retained below $a+d$ lies beyond $u_0$. So $F_d(a)$ consists of
  pluses before $u_0$, contributing at most $\omega^{p(u_0)}$, and of part of that
  final sum. If no minus is retained, $F_d(a)=\omega^{p(a)}\le\omega^\alpha$ by (D3).
- $\omega^{\alpha\oplus\beta}\le N_d$: by Claim 1 for the margin $d$, each
  $D(e+d,v)$ with $v\in R(z)$ retained is at most $N_d$, and $D(e+d,z)$ is their
  supremum.

Hence $\omega^{\alpha\oplus\beta}\le F_d(a)\otimes F_d(b)\le\omega^\alpha\otimes\omega^\beta$,
and (O3) gives $F_d(a)=\omega^\alpha$ and $F_d(b)=\omega^\beta$. Finally
$F_d(e)=D(e+d,z)+\omega^{p(e)}\gt N_d$ by (D4), so $d$ fails. $\qquad\square$

From now on $d$ is as in Claim 4, $N=N_d=\omega^\lambda$ with
$\lambda=\alpha\oplus\beta$, and $z$ and $\rho$ are as in Claim 2 for this $d$. By
Claim 3 for this $d$, and the symmetry of everything that follows in $a$ and
$b$, we may assume that the retained minuses of $a$ are nonempty and cofinal in
$\ell(a)$. Note that $p(z)\lt p(e)\le p(a)\oplus p(b)\le\lambda$ by Claim 2(1), Lemma 1.3 and
(D3).

**Claim 5.** The margin $d$ deletes $z$: every $w\in R(z)$ satisfies $z+d\lt w$.

*Proof.* By Lemma 1.2 the left prefix $z$ of $e$ is a prefix of a left option, say
$u+b$ with $u$ a left prefix of $a$, and $z\le u+b$. The induction hypothesis for
$(u,b)$ with cutoffs $a+d$ and $b+d$ gives

```math
D(u+b+d,\,z)\le D(a+d,u)\otimes F_d(b)\lt N=\omega^\lambda,
```

the last inequality because $a$ has a plus after $u$. The case of a left option
$a+u$ with $u$ a left prefix of $b$ is the same, with the bound
$F_d(a)\otimes D(b+d,u)\lt N$. If some $w\in R(z)$ had
$w\le z+d$, then $w\le u+b+d\le e+d$, and (D6) with $C=u+b+d$ and $C'=e+d$ would
give $D(u+b+d,z)\ge\omega^\lambda$. $\qquad\square$

**Claim 6.** $z=K+r\omega^s$ with $\mathrm{supp}\\,K\gt s$ and $r$ ending in a minus,
and $d\lt\omega^s$.

*Proof.* By Claim 5 and Claim 2(2), Lemma 4.7 applies and gives the form of $z$.
Then Lemma 4.8 applies by Claim 5. $\qquad\square$

**Claim 7.** Let $q=p(s)$. Then $\rho=\omega^q$, and

```math
F_d(a)=\omega^{p(a)},\qquad F_d(b)=\omega^{p(b)},\qquad p(e)=p(a)\oplus p(b).
```

*Proof.* Put $P=p(z)$. By Claims 2(1), 2(2), 5 and 6, Lemma 4.8 gives $\rho\ge\omega^q$,
and Lemma 4.9 with Claim 2(3) gives $\lambda\le P+1+q$. Now

```math
\lambda\le P+1+q\le P+\omega^q\le P+\rho=p(e)\le p(a)\oplus p(b)\le\lambda,
```

using $1+q\le\omega^q$, Claim 2(1) for $P+\rho=p(e)$, Lemma 1.3, and (D3) for the
last step. Equality holds
throughout. In particular $\alpha\oplus\beta=p(a)\oplus p(b)$ with $\alpha\ge p(a)$
and $\beta\ge p(b)$, so $\alpha=p(a)$ and $\beta=p(b)$. $\qquad\square$

**Conclusion.** By Claim 7 and Lemma 4.10, $e=K+r'\omega^s$ with $r'$ dyadic, and
$p(e)=p(a)\oplus p(b)$. So Lemma 4.11 applies: no exponent of $a$ is less than $s$
and $c_a(s)$ is dyadic. Also $d\lt\omega^s$ by Claim 6, $F_d(a)=\omega^{p(a)}$ by
Claim 7, and the retained minuses of $a$ are nonempty and cofinal. So Lemma 4.12
applies: $a=H-\omega^s$, and since $d$ deletes $z=K+r\omega^s$ by Claim 5, it
deletes $a$. That is, $a$ has no retained minus, a contradiction. This proves
Theorem 4.2. $\qquad\square$

| Statement | Lean |
|---|---|
| $D(C,a)$, $F_d(a)$ | [`reducedOmegaCost C a`](GonshorBirthday/Surreal/Birthday/ReducedCost.lean), `reducedOmegaCost (a + d) a` |
| $z$ followed by $\rho$ pluses | [`appendPluses z ρ`](GonshorBirthday/Surreal/Birthday/Constant.lean) |
| $r$ ends in a minus | `(r : Surreal) = appendMinus (t : Surreal)`, see [`appendMinus`](GonshorBirthday/Surreal/Birthday/Append.lean) |
| (D1) | [`reducedOmegaCost_mono`](GonshorBirthday/Surreal/Birthday/ReducedCost.lean), [`reducedOmegaCost_birthdayTruncation_le`](GonshorBirthday/Surreal/Birthday/ReducedCost.lean) |
| (D2) | [`rightPrefix_le_cutoff_of_birthday_le`](GonshorBirthday/Surreal/Birthday/ReducedCostEndpoint.lean) |
| (D3) | [`reducedOmegaCost_self_eq_wpow`](GonshorBirthday/Surreal/Birthday/ReducedCost.lean), [`plusCount_le_cantorSupport_reducedOmegaCost`](GonshorBirthday/Surreal/Birthday/ReducedCost.lean) |
| (D4) | [`reducedOmegaCost_rightPrefix_budget`](GonshorBirthday/Surreal/Birthday/ReducedCostPlus.lean), [`reducedOmegaCost_appendPluses`](GonshorBirthday/Surreal/Birthday/ReducedCostPlus.lean) |
| (D5) | [`exists_head_retention_cutoff_on`](GonshorBirthday/Surreal/Birthday/ProductHeadCost.lean), [`headOmegaCost_eq_reducedOmegaCost`](GonshorBirthday/Surreal/Birthday/HeadCost.lean) |
| (D6) | [`reducedOmegaCost_eq_wpow_of_le_of_retained`](GonshorBirthday/Surreal/Birthday/ReducedCostLower.lean), which assumes $p(z)\lt\lambda$ and gives equality |
| Theorem 4.2 | [`reducedOmegaCost_add_le`](GonshorBirthday/Surreal/Birthday/ReducedCostBound.lean), [`reducedOmegaCost_add_common_margin_le`](GonshorBirthday/Surreal/Birthday/ReducedCostBound.lean) |
| equivalence of the two forms | [`reducedOmegaCost_add_iff_common_margin`](GonshorBirthday/Surreal/Birthday/ReducedCostAddition.lean) |
| Lemma 4.3(a) | [`birthdayTruncation_trunc`](GonshorBirthday/Surreal/HahnSeries/BirthdayAdd.lean), [`birthdayTruncation_trunc_add_coeff_wpow`](GonshorBirthday/Surreal/Birthday/SupportGap.lean) |
| Lemma 4.3(b) | [`lt_wlog_sub_of_birthday_lt`](GonshorBirthday/Surreal/Birthday/Head.lean), [`exists_real_mul_wpow_lt_rightPrefix_gap`](GonshorBirthday/Surreal/Birthday/Head.lean) |
| Lemma 4.3(c) | [`birthdayTruncation_head_real_mul_wpow_of_prefix`](GonshorBirthday/Surreal/Birthday/Head.lean) |
| Lemma 4.4, for $\eta=\omega^{\alpha}n$ | [`appendPluses_head_real_mul_wpow`](GonshorBirthday/Surreal/Birthday/HeadRun.lean), [`appendMinuses_head_real_mul_wpow`](GonshorBirthday/Surreal/Birthday/HeadRun.lean) |
| Lemma 4.4, in the form: $z$ followed by $p(a)$ pluses is $z+a$, for a left prefix $a$ of $\omega^s$ | [`appendPluses_eq_add_leftPrefix_wpow`](GonshorBirthday/Surreal/Birthday/HeadRun.lean), [`appendMinuses_eq_sub_leftPrefix_wpow`](GonshorBirthday/Surreal/Birthday/HeadRun.lean); $\Phi_s$ itself is not defined in the Lean |
| Lemma 4.5(1)–(2) | [`head_real_mul_wpow_sub_leftPrefix_mem_rightPrefixes`](GonshorBirthday/Surreal/Birthday/HeadPerturbation.lean), [`head_sub_natCast_mul_wpow_mem_rightPrefixes`](GonshorBirthday/Surreal/Birthday/HeadPerturbation.lean), [`real_sub_le_one_of_eq_appendMinus`](GonshorBirthday/Surreal/Birthday/CoefficientStep.lean) |
| Lemma 4.5(3) | [`exists_head_real_mul_wpow_sub_natCast_mul_wpow_le`](GonshorBirthday/Surreal/Birthday/LastMinusFamily.lean) |
| Lemma 4.5(4) | [`appendMinuses_head_real_mul_wpow_of_appendMinus`](GonshorBirthday/Surreal/Birthday/CoefficientRun.lean), [`minus_suffix_le_of_eq_appendMinuses`](GonshorBirthday/Surreal/Birthday/ReducedCostInterval.lean), [`minus_suffix_type_head_sub_wpow`](GonshorBirthday/Surreal/Birthday/HeadSuffix.lean) |
| Lemma 4.6 | [`exists_rightPrefix_sub_lt_real_mul_wpow_of_support`](GonshorBirthday/Surreal/Birthday/SupportGap.lean) |
| Lemma 4.7 | [`exists_last_coefficient_minus_of_gap_window`](GonshorBirthday/Surreal/Birthday/ReducedCostClassification.lean), [`exists_dyadic_last_term_of_gap_window`](GonshorBirthday/Surreal/Birthday/ReducedCostHead.lean) |
| Lemma 4.7, $(\ast)$ | [`not_coinitial_halving_rightPrefixes_of_gap_window`](GonshorBirthday/Surreal/Birthday/ReducedCostLower.lean) |
| Lemma 4.7, no least exponent | [`exists_rightPrefix_lt_of_no_min_set`](GonshorBirthday/Surreal/Birthday/SupportGap.lean), [`not_gap_window_of_no_min_support`](GonshorBirthday/Surreal/Birthday/ReducedCostHead.lean) |
| Lemma 4.7, nondyadic coefficient | [`not_gap_window_of_nondyadic_last_coefficient`](GonshorBirthday/Surreal/Birthday/ReducedCostHead.lean) |
| Lemma 4.7, $r=1$ | [`not_gap_window_of_head_add_wpow_cofinal`](GonshorBirthday/Surreal/Birthday/ReducedCostPositive.lean) |
| Lemma 4.8 | [`shifted_cutoff_lt_wpow_of_last_minus_head`](GonshorBirthday/Surreal/Birthday/ReducedCostPaired.lean), [`wpow_plusCount_le_plus_interval_of_gap_window`](GonshorBirthday/Surreal/Birthday/ReducedCostInterval.lean) |
| Lemma 4.9 | [`pure_reducedOmegaCost_exponent_le_of_minus_suffix`](GonshorBirthday/Surreal/Birthday/ReducedCostSuffix.lean), [`reducedOmegaCost_eq_wpow_of_no_retained_rightPrefixes`](GonshorBirthday/Surreal/Birthday/ReducedCostEndpoint.lean) |
| Lemma 4.10 | [`exists_dyadic_head_coefficient_plus_block`](GonshorBirthday/Surreal/Birthday/CoefficientRun.lean) |
| Lemma 4.11 | [`support_subset_Ici_of_plusCount_add_eq`](GonshorBirthday/Surreal/HahnSeries/BirthdayAdd.lean), [`birthday_real_coefficient_lt_omega0_of_sharp_add`](GonshorBirthday/Surreal/Birthday/CoefficientCancellation.lean) |
| Lemma 4.12 | [`exists_head_sub_wpow_of_retained_baseline`](GonshorBirthday/Surreal/Birthday/ReducedCostInput.lean), [`rightPrefixes_gt_shifted_cutoff_of_last_minus_head`](GonshorBirthday/Surreal/Birthday/ReducedCostPaired.lean) |
| Lemma 4.12, pluses cofinal; $c=\pm1$ | [`leftPrefixes_cofinal_of_baseline_cost`](GonshorBirthday/Surreal/Birthday/ReducedCostBaseline.lean), [`head_real_coefficient_eq_one_or_neg_one_of_both_cofinal`](GonshorBirthday/Surreal/Birthday/CoefficientBlock.lean) |
| Claim 1 | [`exists_retained_rightPrefix_mul_bound_of_smaller`](GonshorBirthday/Surreal/Birthday/ReducedCostCofinality.lean), [`reducedOmegaCost_rightPrefix_add_le_of_smaller`](GonshorBirthday/Surreal/Birthday/ReducedCostAddition.lean), [`reducedOmegaCost_rightPrefix_add_budget_of_smaller`](GonshorBirthday/Surreal/Birthday/ReducedCostBudget.lean) |
| Claim 2 | [`exists_limit_prefix_of_common_margin_failure`](GonshorBirthday/Surreal/Birthday/ReducedCostReduction.lean) |
| Claim 3 | [`pure_factor_or_of_common_margin_failure`](GonshorBirthday/Surreal/Birthday/ReducedCostPure.lean), [`retained_rightPrefixes_cofinal_of_costs_cofinal`](GonshorBirthday/Surreal/Birthday/ReducedCostCofinality.lean) |
| Claim 4 | [`exists_smaller_margin_pure_costs_of_cofinal_direction`](GonshorBirthday/Surreal/Birthday/ReducedCostNormalize.lean), [`exists_smaller_margin_pure_costs_of_common_margin_failure`](GonshorBirthday/Surreal/Birthday/ReducedCostNormalize.lean) |
| Claim 4, right prefixes below $u_0+b$ | [`exists_later_retained_rightPrefix_lt_add_of_eq`](GonshorBirthday/Surreal/Birthday/ReducedCostCofinality.lean) |
| Claim 5 | [`rightPrefixes_gt_shifted_cutoff_of_pure_eq`](GonshorBirthday/Surreal/Birthday/ReducedCostLower.lean) |
| Claims 2 and 5 after Claim 4 | [`exists_deleted_limit_prefix_of_pure_common_margin_failure`](GonshorBirthday/Surreal/Birthday/ReducedCostLower.lean) |
| Claims 6–7, except $d\lt\omega^s$ | [`exists_full_block_last_term_of_pure_gap_window`](GonshorBirthday/Surreal/Birthday/ReducedCostClassification.lean) |
| Claim 7, assembled from Lemmas 4.8 and 4.9 | [`full_block_and_baseline_of_head_coefficient_minus`](GonshorBirthday/Surreal/Birthday/ReducedCostInterval.lean) |
| Claim 7, the chain of inequalities | [`full_block_and_baseline_of_pure_suffix`](GonshorBirthday/Surreal/Birthday/ReducedCostEquality.lean) |
| Conclusion | [`not_retained_baseline_of_last_minus_output`](GonshorBirthday/Surreal/Birthday/ReducedCostInput.lean) |
| everything after Claim 4, assembled | [`not_pure_common_margin_failure`](GonshorBirthday/Surreal/Birthday/ReducedCostBound.lean) |

## 5. Proof of the Theorem

Let $X,Y$ be as in Definition 3.2, with normal forms
$X=\sum_{i\lt\theta}r_i\omega^{a_i}$ and $Y=\sum_{j\lt\eta}t_j\omega^{b_j}$, and let

```math
L_i=L_{X_{\gt a_i}}(a_i,r_i),\qquad M_j=L_{Y_{\gt b_j}}(b_j,t_j)
```

be the lengths of their terms. By Theorem 2.2 and Proposition 3.3(1),
$\ell(x)=\sum_i^{\mathrm{ord}}L_i$ and $\ell(y)=\sum_j^{\mathrm{ord}}M_j$. Write $Z=XY$.
Below, $L_H(a,r)$ is used as in Definition 2.1 also when $r$ is not the
coefficient of a term.

**Lemma 5.1.** For all $i,j$, with $s=a_i+b_j$,

```math
L_{Z_{\gt s}}(s,\,r_it_j)\le L_i\otimes M_j.
```

*Proof.* We first show: if $w$ is admissible after $Z_{\gt s}$, then $w-b_j$ is
admissible after $X_{\gt a_i}$. Let $k\lt i$. By Proposition 3.3(2), $a_k+b_j$ is
an exponent of $Z_{\gt s}$, so $a_k+b_j\ge w$, that is, $a_k\ge w-b_j$. If
$a_k=w-b_j$, then $c_Z(w)$ is dyadic and is a sum of positive products one of
which is $r_kt_j$; so no product involves $\tau$, and $r_k$ is dyadic.

By (D5) choose $A\gt a_i$ such that an element of
$R(a_i)\cup\\{w-b_j:w\in R(s)\\}$ is admissible after $X_{\gt a_i}$ exactly when
it is at most $A$; then $G_{X_{\gt a_i}}(a_i)=D(A,a_i)$. Choose $B$ likewise for
$b_j$. If a minus of $s$ with right prefix $w$ is retained after $Z_{\gt s}$, then
$w-b_j\le A$ and $w-a_i\le B$ by the first paragraph. So the retained positions
of $s$ are retained below $\min(A+b_j,a_i+B)$, and by Theorem 4.2

```math
G_{Z_{\gt s}}(s)\le D\bigl(\min(A+b_j,a_i+B),s\bigr)\le D(A,a_i)\otimes D(B,b_j).
```

For the coefficients, $\ell(r_it_j)\le\ell(r_i)\otimes\ell(t_j)$ by Lemma 1.4 and
$p(s)\le p(a_i)\oplus p(b_j)$ by Lemma 1.3. Expanding the product
$L_i\otimes M_j$ with (O2) gives the claim, the cases of an integer product
and of a product involving $\tau$, of length $\omega$, being treated separately. $\qquad\square$

**Lemma 5.2.** For each $s$, the set of pairs $(i,j)$ with $a_i+b_j=s$ is finite,
and for any enumeration $(i_1,j_1),\dots,(i_n,j_n)$ of it,

```math
L_{Z_{\gt s}}\bigl(s,c_Z(s)\bigr)\le L_{i_1}\otimes M_{j_1}+\dots+L_{i_n}\otimes M_{j_n}.
```

*Proof.* Finiteness holds because the supports are reverse well-ordered. For
reals $r,t$ we have $L_H(s,r+t)\le L_H(s,r)+L_H(s,t)$. If $r$, $t$ or $r+t$ is
zero this is clear. If $r$ and $t$ are dyadic it follows from
$\ell(r+t)\le\ell(r)\oplus\ell(t)$ (Section 1), the extra block $\omega^{p(s)}$ being
dominated by $G_H(s)\ge\omega^{p(s)}$ in the second summand. Otherwise one summand
has length $\omega$, which bounds $\ell(r+t)$. Apply this repeatedly
to $c_Z(s)=\sum_kr_{i_k}t_{j_k}$ and then Lemma 5.1 to each summand. $\qquad\square$

*Proof of the Theorem.* By Theorem 2.2 and Lemma 5.2, $\ell(Z)$ is at most the
order type of the following well-ordered set $W$. Order the pairs $(i,j)$ by
decreasing $a_i+b_j$, breaking ties arbitrarily, and replace each pair by a well
order of type $L_i\otimes M_j$ that is a linear extension of the product order on
$L_i\times M_j$; such an extension exists by Theorem 1.1(b). Each point of $W$
thereby has a first coordinate in the ordered sum $\sum_i^{\mathrm{ord}}L_i$ and a
second in $\sum_j^{\mathrm{ord}}M_j$. If $u,v\in W$ have both coordinates of $u$ at
most those of $v$, then either they belong to the same pair, and $u\le v$ there,
or the pair $(i,j)$ of $u$ and the pair $(i',j')$ of $v$ satisfy $i\le i'$ and
$j\le j'$ with one inequality strict, so $a_i+b_j\gt a_{i'}+b_{j'}$ and $u\lt v$.
Theorem 1.1(a) gives

```math
\ell(xy)\le\ell(XY)\le\mathrm{type}(W)
\le\Bigl(\sum^{\mathrm{ord}}_iL_i\Bigr)\otimes\Bigl(\sum^{\mathrm{ord}}_jM_j\Bigr)
=\ell(x)\otimes\ell(y),
```

where the first inequality is Proposition 3.3(3). $\qquad\square$

| Statement | Lean |
|---|---|
| Lemma 5.1, admissibility | [`head_retention_left_of_replacement_product`](GonshorBirthday/Surreal/Birthday/ProductHeadCost.lean) |
| Lemma 5.1, monomial part | [`headOmegaCost_mul_replacement_le`](GonshorBirthday/Surreal/Birthday/ProductHeadCost.lean) |
| Lemma 5.1 | [`headCoefficientCost_mul_replacement_le`](GonshorBirthday/Surreal/Birthday/ProductCoefficientCost.lean) |
| Lemma 5.2, subadditivity | [`headCoefficientCost_add_le`](GonshorBirthday/Surreal/Birthday/HeadCoefficientCost.lean) |
| Lemma 5.2 | [`headCoefficientCost_mul_replacement_fibre_le`](GonshorBirthday/Surreal/Birthday/ProductCoefficientCost.lean) |
| the bound on $\mathrm{type}(W)$ | [`NatOrdinal.of_type_sigma_mul_le_of_fibres`](GonshorBirthday/NatOrdinal/ProductFibre.lean), [`NatOrdinal.of_type_sigma_mul_le`](GonshorBirthday/NatOrdinal/ProductSum.lean) |
| $\ell(XY)\le\ell(x)\otimes\ell(y)$ | [`birthday_mul_normalFormBirthdayReplacement_le`](GonshorBirthday/Surreal/Birthday/ProductGrid.lean) |
| the Theorem | [`Surreal.birthday_mul_le`](GonshorBirthday/Surreal/Birthday/Multiplication.lean) |

## References

- P. W. Carruth,
  [“Arithmetic of ordinals with applications to the theory of ordered Abelian groups”](https://doi.org/10.1090/S0002-9904-1942-07649-X),
  *Bulletin of the AMS* **48** (1942), 262–271, Theorem 2.
- D. H. J. de Jongh and R. Parikh, “Well-partial orderings and hierarchies”,
  *Indagationes Mathematicae* **39** (1977), 195–207.
- L. van den Dries and P. Ehrlich,
  [“Fields of surreal numbers and exponentiation”](https://www.impan.pl/shop/en/publication/transaction/download/product/89226),
  *Fundamenta Mathematicae* **167** (2001), 173–188, Section 3.
- H. Gonshor, [*An Introduction to the Theory of Surreal Numbers*](https://doi.org/10.1017/CBO9780511629143),
  Cambridge University Press, 1986. Theorems 5.11–5.12 and Chapter 6, p. 96.
