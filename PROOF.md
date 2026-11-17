# Gonshor's birthday conjecture

Let $b(x)$ denote the birthday of a surreal number $x$, or equivalently the length
of its sign sequence. We prove

```math
b(xy)\le b(x)\otimes b(y)\qquad(x,y\in\mathbf{No}),
```

where $\otimes$ is natural ordinal multiplication. Gonshor states this conjecture
in *An Introduction to the Theory of Surreal Numbers*, Chapter 6, p. 96.

This is an outline of the proof, with links to its formal details. Write $\oplus$
for natural ordinal addition; all other ordinal sums, products, and powers below
are ordinary ordinal operations. For a surreal exponent $a$, $\omega^a$ denotes
Conway's omega-map. Let $p(a)$ be the order type of the plus positions of $a$.
A right prefix of $a$ means a proper initial segment of its sign sequence whose
value is greater than $a$; write $R(a)$ for their set.

## 1. Lengths of normal-form terms

Write a surreal in normal form as

```math
x=\sum_{i\lt \theta}r_i\omega^{a_i},
```

where the exponents decrease strictly and the coefficients are nonzero reals.
Gonshor's sign formula, Theorems 5.11–5.12, expresses the sign sequence of $x$ as
an ordinal concatenation of modified term sequences. The modification depends
on the preceding terms: some minus signs in an exponent are deleted before its
sign sequence is expanded.

Here is the length formula we use. Suppose every exponent of a head $H$ is greater
than $a$. Retain all plus signs of $a$. Retain a minus with right prefix $w$ precisely
when every exponent of $H$ is at least $w$ and the coefficient of $\omega^w$ in $H$
is dyadic; an absent coefficient is zero. Each retained sign at position $\delta$
contributes a block of length $\omega^{p(a\upharpoonright\delta)+1}$. Let $G_H(a)$
be the ordinary ordered sum of these blocks, preceded by an initial unit.

For $r\ne0$, put

```math
L_H(a,r)=G_H(a)+\omega^{p(a)}\bigl(b(r)-1\bigr),
```

and put $L_H(a,0)=0$. The exact length formula is

```math
b(H+r\omega^a)=b(H)+L_H(a,r).
```

Consequently, if $H_i=\sum_{k<i}r_k\omega^{a_k}$, then

```math
b(x)=\sum_{i\lt \theta}^{\mathrm{ord}}L_{H_i}(a_i,r_i).
```

The formula includes negative and nondyadic coefficients and heads of arbitrary
ordinal length. See [the single-term formula](GonshorBirthday/Surreal/Birthday/HeadCoefficientLength.lean)
and [the normal-form length formula](GonshorBirthday/Surreal/Birthday/NormalFormLength.lean).

## 2. Coefficient comparison

Write $c_x(a)$ for the coefficient at exponent $a$, taking it to be zero outside
the support.

**Lemma 1.** If $b(c_u(a))\le b(c_v(a))$ for every $a$, then $b(u)\le b(v)$.

Deleting terms can restore minus blocks in later terms, so the lemma requires a
comparison of whole prefixes. Let $x_{>a}$ denote the truncation of $x$ to
exponents greater than $a$. Induction over the decreasing support of $v$ proves

```math
b(u_{>a})+G_{u_{>a}}(a)
\le b(v_{>a})+G_{v_{>a}}(a)
\qquad(a\in\mathrm{supp}\,v).
```

For a minus block retained on the left and deleted on the right, there are two
possibilities. Either a term of $v$ below its right prefix has disappeared from
$u$, or the coefficient at that prefix has changed from nondyadic to dyadic.
In the first case, the inductive bound at the disappeared term bounds the entire
prefix through the restored block. In the second, the nondyadic coefficient's
infinite tail supplies that bound. An induction through the exponent's sign
sequence now gives the displayed inequality. Adding the coefficient tails and
taking suprema proves the lemma. The argument applies also when $c_u(a)=0$.
See [coefficient comparison](GonshorBirthday/Surreal/Birthday/CoefficientComparison.lean).

Fix a positive transcendental real $\tau$. Replace each dyadic coefficient $r$ by
the integer $b(r)$ and each nondyadic coefficient by $\tau$. Denote the resulting
series by $X$ and $Y$. The replacement preserves coefficient birthdays, so Lemma 1
gives

```math
b(X)=b(x),\qquad b(Y)=b(y).
```

Every coefficient of $XY$ is a polynomial in $\tau$ with nonnegative integer
coefficients. If this polynomial is nonconstant, its value is transcendental
and has birthday $\omega$, an upper bound for the birthday of any real number.
If it is constant, the contributing original coefficients were all dyadic, and
the finite birthday bounds for their sums and products apply. Thus

```math
b(c_{xy}(a))\le b(c_{XY}(a))\quad\text{for every }a,
\qquad b(xy)\le b(XY).
```

It remains to prove the product bound for $X,Y$. Their nonzero coefficients are
positive, so every pair of supported exponents contributes to the support of
$XY$. See [the replacement construction](GonshorBirthday/Surreal/Birthday/NormalFormReplacement.lean).
The real-coefficient multiplication estimate is van den Dries–Ehrlich, Lemma 3.3.

## 3. The reduced monomial estimate

For a surreal cutoff $C\ge a$, retain every plus of $a$ and exactly those minuses
whose right prefix is at most $C$. Define

```math
D(C,a)=1+\sum_{\substack{\delta\lt b(a)\\
 a(\delta)=+\ \text{or}\ a\upharpoonright\delta\le C}}^{\mathrm{ord}}
 \omega^{p(a\upharpoonright\delta)+1}.
```

The prefix values and plus counts are those of the original sign sequence.
Every $G_H(a)$ from Section 1 is $D(C,a)$ for a suitable $C\ge a$.
For $d>0$, set $F_d(a)=D(a+d,a)$.

**Lemma 2.** For all surreal numbers $a,b$ and $d>0$,

```math
F_d(a+b)\le F_d(a)\otimes F_d(b).
```

The equivalent form used for normal-form products is

```math
D\bigl(\min(A+b,a+B),a+b\bigr)
\le D(A,a)\otimes D(B,b),\qquad A\ge a,\ B\ge b.
```

We outline the proof of Lemma 2, which is the main part of the argument.
Induct on $b(a)\oplus b(b)$. The induction bounds the lengths through retained
right prefixes of $a+b$. A failure can occur only if these lengths exhaust the
proposed bound before a final nonempty sequence of plus signs.
The [reduction](GonshorBirthday/Surreal/Birthday/ReducedCostNormalize.lean)
allows us to decrease $d$ so that, writing $e=a+b$,

```math
F_d(a)=\omega^\alpha,\qquad F_d(b)=\omega^\beta,\qquad
D(e+d,z)=\omega^\lambda,\qquad \lambda=\alpha\oplus\beta,
```

where $e$ is obtained from a proper limit prefix $z$ by appending $\rho>0$ plus
signs. Retained right prefixes are cofinal in $b(z)$. Lowering the cutoff to
$z+d$ deletes every right prefix of $z$:

```math
z+d\lt w\quad(w\in R(z)),\qquad
w\le e+d\quad\text{for some }w\in R(z).
```

The [normal-form classification](GonshorBirthday/Surreal/Birthday/ReducedCostClassification.lean)
of this configuration gives

```math
z=K+r\omega^s,
```

where $K$ has support strictly above $s$ and $r$ is a nonzero dyadic whose sign
sequence ends in a minus. The classification uses comparisons between the gaps
$w-z$ for right prefixes $w$. Normal forms without a last term, and those with
a nondyadic last coefficient, admit arbitrarily halved right gaps. To see the
contradiction, take $w\le e+d$ and a right prefix $v$ with
$2(v-z)<w-z$. Since $e$ extends $z$, both $e-z$ and $d$ are less than $v-z$,
whereas $w-z\le e-z+d$. Cofinality and a further gap comparison exclude the
other possible final coefficients.

Put $q=p(s)$ and $P=p(z)$. The final plus sequence has length at least $\omega^q$,
while a suffix of $z$ has at most $\omega^q$ minus positions. The latter estimate
gives $\lambda\le P+1+q$. Together with the plus-count addition bound of
van den Dries–Ehrlich, Lemma 3.4(1), this yields

```math
\lambda\le P+1+q\le P+\omega^q\le P+\rho
=p(e)\le p(a)\oplus p(b)\le\lambda.
```

Here $1+q\le\omega^q$, including $q=0$. Equality holds throughout. Hence

```math
\rho=\omega^q,\qquad \alpha=p(a),\qquad \beta=p(b),\qquad
p(a+b)=p(a)\oplus p(b).
```

See [the interval bounds](GonshorBirthday/Surreal/Birthday/ReducedCostInterval.lean)
and [the equality argument](GonshorBirthday/Surreal/Birthday/ReducedCostEquality.lean).
Appending this full plus block leaves $e$ with a dyadic final coefficient at $s$.

Equality in the plus-count bound excludes cancellation of terms below $s$.
It also forces the input coefficient needed below to be dyadic. Indeed, if that
coefficient were nondyadic, choose a sufficiently close canonical left prefix of
it. This gives a proper left prefix $a'$ of the input such that $e$ remains a
canonical prefix of $a'+b$. But then

```math
p(e)\le p(a'+b)\le p(a')\oplus p(b)
\lt p(a)\oplus p(b)=p(e),
```

a contradiction. The construction is proved in
[coefficient cancellation](GonshorBirthday/Surreal/Birthday/CoefficientCancellation.lean).

The reduction also provides an input with cofinally retained right prefixes;
interchange $a,b$ if necessary so that it is $a$. Since $F_d(a)=\omega^{p(a)}$,
its left prefixes are cofinal as well. The dyadic coefficient classification
then leaves

```math
a=H-\omega^s,\qquad \mathrm{supp}\,H\subseteq(s,\infty).
```

Finally, the right-prefix families of $K+r\omega^s$ and $H-\omega^s$ give

```math
\bigl(\forall w\in R(z),\ z+d\lt w\bigr)
\quad\Longrightarrow\quad
\bigl(\forall v\in R(a),\ a+d\lt v\bigr).
```

This contradicts the existence of a retained right prefix of $a$. See
[the input classification](GonshorBirthday/Surreal/Birthday/ReducedCostInput.lean)
and [the comparison of prefix gaps](GonshorBirthday/Surreal/Birthday/ReducedCostPaired.lean).
This completes [Lemma 2](GonshorBirthday/Surreal/Birthday/ReducedCostBound.lean).

## 4. The product order

Apply the preceding results to the positive replacements $X,Y$. Let $L_i,M_j$
be their normal-form term lengths, so that

```math
b(X)=\sum_i^{\mathrm{ord}}L_i,\qquad
b(Y)=\sum_j^{\mathrm{ord}}M_j.
```

Lemma 2, with cutoffs determined by the preceding terms, bounds the reduced
monomial contribution at $a_i+b_j$ by the natural product of the corresponding
input lengths. Incorporating the real coefficient tails gives a bound
$L_i\otimes M_j$ for the complete contribution. For each exponent $s$, the set
of pairs with $a_i+b_j=s$ is finite, and the complete term at $s$ has length at
most the ordinary sum of these bounds, in any order. This is the
[product coefficient estimate](GonshorBirthday/Surreal/Birthday/ProductCoefficientCost.lean).

Order the pairs $(i,j)$ by decreasing $a_i+b_j$, choosing any order within a tie.
This is a linear extension of their coordinatewise order. Replace each pair by
a linear extension of the rectangle $L_i\times M_j$ of order type
$L_i\otimes M_j$. Concatenation gives a linear extension of

```math
\left(\sum_i^{\mathrm{ord}}L_i\right)
\times\left(\sum_j^{\mathrm{ord}}M_j\right).
```

Carruth's maximal-order-type theorem therefore gives

```math
b(xy)\le b(XY)
\le\sum_{(i,j)}^{\mathrm{ord}}(L_i\otimes M_j)
\le b(X)\otimes b(Y)=b(x)\otimes b(y).
```

The zero cases are immediate. The well orders used here may have arbitrary
ordinal length. See [the product-order proof](GonshorBirthday/Surreal/Birthday/ProductGrid.lean)
and [the final theorem](GonshorBirthday/Surreal/Birthday/Multiplication.lean).

## References

- H. Gonshor, [*An Introduction to the Theory of Surreal Numbers*](https://doi.org/10.1017/CBO9780511629143),
  Cambridge University Press, 1986. Theorems 5.11–5.12 and Chapter 6, p. 96.
- L. van den Dries and P. Ehrlich,
  [“Fields of surreal numbers and exponentiation”](https://www.impan.pl/shop/en/publication/transaction/download/product/89226),
  *Fundamenta Mathematicae* **167** (2001), 173–188, Section 3.
- P. W. Carruth,
  [“Arithmetic of ordinals with applications to the theory of ordered Abelian groups”](https://doi.org/10.1090/S0002-9904-1942-07649-X),
  *Bulletin of the AMS* **48** (1942), 262–271, Theorem 2.
