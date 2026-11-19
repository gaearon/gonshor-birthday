# Gonshor’s birthday conjecture

Write $\ell(x)$ for the length of the sign sequence of a surreal number $x$. For ordinals
write $\oplus,\otimes$ for natural sum and product. We use ordinary ordinal arithmetic
when we put lengths end to end.

**Theorem.** For all surreal numbers $x,y$,

```math
\ell(xy)\leq\ell(x)\otimes\ell(y).
```

Equality holds for every pair of ordinals. Their surreal product is their natural product.
Gonshor posed the general question in Chapter 6, p. 96.
[Gonshor, Chapter 6](https://www.cambridge.org/core/books/an-introduction-to-the-theory-of-surreal-numbers/lengths-and-subsystems-which-are-sets/D19E3D2FC8D2902696B163A2D67FC7D1) ·
[Theorem in Lean](GonshorBirthday/Surreal/Birthday/Multiplication.lean)

Van den Dries and Ehrlich proved the bound when each factor has a single normal-form
term. In a longer series an earlier term can suppress minus signs in the exponent of
a later one. We first count the signs of a product term in the presence of one earlier
exponent. The same estimate will apply to arbitrary series.
[Van den Dries and Ehrlich, Proposition 3.6](https://www.impan.pl/shop/en/publication/transaction/download/product/89226)

## The last term of a binomial product

Consider $(\omega^{a+d}+\omega^a)(\omega^{b+d}+\omega^b)$, where $d>0$. The exponent
immediately before the last term $\omega^{a+b}$ is $a+b+d$, with coefficient $2$.
The distance between these exponents is the same $d$ as in each factor. This observation
gives the estimate we will use for arbitrary normal forms.

Let $p(a)$ be the order type of the plus signs in $a$. A *right prefix* $v$ is the word
obtained by stopping just before a minus of $a$, so $v>a$. Write $R(a)$ for these prefixes.
They decrease in value as we read further. The left prefixes $L(a)$ stop before a plus.

For $C\ge a$, form a word of length $D(C,a)$ as follows. Start with one sign. Each sign of
$a$ with preceding prefix $v$ adds a block of length $\omega^{p(v)+1}$. Keep all plus blocks.
Keep the minus at $v$ if $v\le C$. By Gonshor’s sign rule, $F_d(a)=D(a+d,a)$ is exactly
the length added by $\omega^a$ after $\omega^{a+d}$ for $d>0$. The initial sign and the
plus blocks by themselves have length $\omega^{p(a)}$. In particular $F_0(a)=\omega^{p(a)}$.
[Gonshor, Theorems 5.11–5.12](https://www.cambridge.org/core/books/abs/an-introduction-to-the-theory-of-surreal-numbers/normal-form/67644DE1ECF6D0C846D9774DD994C9E5) ·
[The exponent word](GonshorBirthday/Surreal/Birthday/ReducedCost.lean)

We shall prove

**(1)** $F_d(a+b)\le F_d(a)\otimes F_d(b) \qquad(d\ge0)$.

For unequal cutoffs $A\ge a$, $B\ge b$, take $d=\min(A-a,B-b)$. By monotonicity this gives

**(2)** $D(\min(A+b,a+B),a+b)\le D(A,a)\otimes D(B,b)$.

Two facts about signs will be used. First, $p(a+b)\le p(a)\oplus p(b)$. This follows from
Gonshor’s theorem that the signs of a sum form a subshuffle of the signs of the summands.
It also follows directly by induction from the addition cut. Second, every Cantor exponent
of $D(C,a)$ is at least $p(a)$. Indeed, for each $\eta<p(a)$ take the plus with exactly
$\eta$ pluses before it. Its block and every subsequent retained block have exponent at
least $\eta+1$. No Cantor term of exponent at most $\eta$ survives this ordinal sum.
[Gonshor, Theorem 7.1](https://www.cambridge.org/core/books/abs/an-introduction-to-the-theory-of-surreal-numbers/sums-as-subshuffles-unsolved-problems/9E4538F498086012A7A534E656B35CAD) ·
[Plus counts](GonshorBirthday/Surreal/Birthday/Addition.lean) ·
[Cantor exponents](GonshorBirthday/Surreal/Birthday/ReducedCost.lean)

## Splitting a prefix on a dyadic grid

Every sign prefix $y$ of $a+b$ has the form $x+x'$ for prefixes $x$ of $a$ and $x'$ of
$b$. For example, if $y>a+b$, the addition cut gives a right option $u+b$ or $a+u$ between
$a+b$ and $y$, inclusive at $y$. If the option equals $y$ we are done. Otherwise $y$
is still a right prefix of that option, since the extensions of a sign word form a convex
class. Repeat. Each step decreases the natural sum of the two birthdays. Negation gives
the assertion on the left. Fornasiero uses this descent to show that the sum of two
initial sets is initial.
[Fornasiero, Lemma 4.7](https://era.ed.ac.uk/handle/1842/12194) ·
[Prefixes of a sum](GonshorBirthday/Surreal/Birthday/PrefixSums.lean)

Suppose $y=H+qM$, with $M=\omega^s$, all exponents of $H$ greater than $s$, and $q$
dyadic. Let $D$ be the denominator of $q$ in lowest terms and put $h=1/D$. We can choose
**both input prefixes to end on the same grid** $h\mathbb Z$ at $M$. Indeed, in $x+x'=y$ the coefficients $r,t$ at $s$
sum to $q$ and the tails below $s$ cancel. Discard both tails. Round $r$ down to
$h\lfloor r/h\rfloor$ and $t$ up to the complementary grid point. The rounded numbers
$A,B$ still sum to $y$. They are prefixes. A grid point with reduced denominator $m$ has
its nearest dyadic option on either side at distance at least $1/m\ge h$ whenever that
option exists. Thus both endpoints of a grid interval are prefixes of each real in its
interior. Keeping a higher head and multiplying the coefficient by $M$ preserves prefixes.
[Rounding the coefficients](GonshorBirthday/Surreal/Birthday/CoefficientCancellation.lean)

For $1/4+1/4=1/2$ the rounded coefficients are $0$ and $1/2$, both prefixes of $1/4$.
In particular, adding two quarter coefficients at $M$ gives strict inequality in the
plus-count bound, even with arbitrary higher terms. Indeed, whenever $y=a+b$ and
$p(y)=p(a)\oplus p(b)$, rounding must leave both inputs unchanged. Losing a plus would
strictly decrease the natural sum of their plus counts. Cutting off only minuses can
only increase each number, and the two increases sum to zero.
[The quarter example](GonshorBirthday/Surreal/Birthday/Tests/CoefficientCancellation.lean)

Here is the estimate we need at a limit. Suppose retained minuses occur arbitrarily
late in $a$ at cutoff $C$, and $\alpha$ occurs in the Cantor normal form of $D(C,a)$
as an exponent. Suppose also that some $u\in R(a)$ satisfies $u-a\le cM$, with
$0<c<1$ real. For every prefix $y=H+qM$ of $a+b$ as above,

**(3)** $p(y)<\alpha\oplus p(b)$.

Take the rounded prefixes $A,B$. If $A$ is a proper prefix of $a$, take a retained
minus after $A$. From there on every retained block has exponent at least $p(A)+1$,
so $p(A)<\alpha$. If $A=a$, we already know $p(a)\le\alpha$. Equality would imply
that pluses too occur arbitrarily late. Otherwise eventually every retained block
would have exponent $p(a)+1$.

But $a=A=K+jM$ with $j$ dyadic. After the first sign of a nonzero dyadic coefficient,
each further sign contributes one constant block of length $\omega^{p(s)}$. With both
signs occurring arbitrarily late there can be no such final block. Hence $j$ is $0$,
$1$ or $-1$. Each of these integers is a prefix of $j+c$. It follows that $a+cM$
extends $a$ and lies below every right option of $a$, contradicting the choice of $u$.
Thus $p(A)<\alpha$ in either case. Now use $p(y)\le p(A)\oplus p(B)$ and $p(B)\le p(b)$.
[Coefficient blocks](GonshorBirthday/Surreal/Birthday/CoefficientRun.lean) ·
[Strict inequality at the given cutoff](GonshorBirthday/Surreal/Birthday/ReducedCostGap.lean)

## The common margin

Put $e=a+b$, $C=e+d$, $X=F_d(a)$, $Y=F_d(b)$ and $N=X\otimes Y$. The case $d=0$ is the
plus-count inequality. For $d>0$ induct on $\ell(a)\oplus\ell(b)$, allowing all margins
for the smaller pairs.

Stop before a retained minus at $v$ in $e$. The cut for addition gives, say,
$e<u+b\le v$ for some right prefix $u$ of $a$. Thus $u\le a+d$ and $v$ is a prefix of
$u+b$. Apply (2) for the smaller pair $(u,b)$ at the original input cutoffs. Its output
cutoff is still $C$. The part before $v$ has length at most $D(a+d,u)\otimes Y$.
The block at $v$ fits in the next input block times $Y$, since
$p(v)\le p(u)\oplus p(b)$ and $Y\ge\omega^{p(b)}$.

If a plus follows $v$, the same calculation allows a further $\omega^{p(e)}$ positions
after this block. When $p(u)<p(a)$ the later input pluses supply them. Otherwise
$p(v)<p(e)\le p(u)\oplus p(b)$, so the block at $v$ and the extra power both fit in
$\omega^{(p(u)\oplus p(b))+1}$. The two coordinates play the same role.
[Induction at a right prefix](GonshorBirthday/Surreal/Birthday/ReducedCostBudget.lean)

This proves (1) if there is a last retained minus, or if retained minuses occur cofinally
in $e$. With no retained minus, the plus count suffices. The remaining case is a limit $z$
of retained minuses followed by a nonempty run of pluses up to $e$. Once one minus survives
the cutoff, all later minuses survive, so these are all the right prefixes of $e$ from
some position onwards. Taking the supremum through $z$ gives $D(C,z)\le N$. If this
inequality is strict, the final pluses fit. They add $\omega^{p(e)}$, and every Cantor
exponent of $N$ is at least $p(e)$. Suppose, then, that $D(C,z)=N$.
[Reduction to the limit](GonshorBirthday/Surreal/Birthday/ReducedCostReduction.lean)

## The last Cantor power

One summand, say $a$, supplies right options $u+b$ at or below
every right prefix of $z$. Otherwise each summand would miss some right prefix and the
smaller of the two would be missed by both. As $v$ runs out along $z$, the bounds
$D(a+d,u)\otimes Y$ for its prefixes must approach $N$. In particular the surviving
minuses in $a$ are cofinal there. Conversely, for each retained $u$ some right prefix
of $z$ lies strictly below $u+b$. Otherwise this single $u$ bounds all of $z$ by
$D(a+d,u)\otimes Y<N$.

Write $X=X_0+\omega^\alpha$ by taking off one copy of its last Cantor power. Then
$Y=\omega^\beta$ is a single power. Indeed, if $\beta$ is the largest exponent of $Y$,
any $\eta<\omega^\alpha$ satisfies $\eta\otimes Y<\omega^{\alpha\oplus\beta}$.
Products approaching $N$ from below along $X$ can therefore reach at most
$(X_0\otimes Y)\oplus\omega^{\alpha\oplus\beta}$, which is strictly less than $N$
if $Y>\omega^\beta$. The last power of $N$ is now $\omega^\lambda$ with
$\lambda=\alpha\oplus\beta$.
[Right options and their costs](GonshorBirthday/Surreal/Birthday/ReducedCostCofinality.lean) ·
[Natural products at a limit](GonshorBirthday/NatOrdinal/FinalPower.lean)

There is a simple way to isolate that power. In a word with cofinal retained minuses,
cut at a right prefix $u$ already inside the last Cantor power. Lower the cutoff to $u$.
The part before $u$ now has only pluses, of total length $\omega^{p(u)}$. The first
remaining minus has length $\omega^{p(u)+1}$ and absorbs them. The unchanged tail is
exactly the last power. Every smaller cutoff that still retains a minus gives that same
power. [Changing the cutoff](GonshorBirthday/Surreal/Birthday/ReducedCostCutoff.lean)

Choose such a late $u$ in $a$, then a late $v\in R(z)$ below $u+b$, and put $d'=v-e$.
At this smaller margin the inputs cost at most $\omega^\alpha,\omega^\beta$, while
$D(e+d',z)=\omega^\lambda$. Yet **all** right options of $z$ exceed $z+d'$. Indeed,
$z$ is a left prefix of $e$, so some left addition option $x+b$ or $a+x$ lies between
$z$ and $e$. In the first case induction at $(x,b)$, with input cutoffs $a+d',b+d'$, gives
$D(x+b+d',z)<\omega^\lambda$. The inequality is strict because $x$ is a proper left
prefix and its next plus is always retained. If even one minus survived at $z+d'$,
the preceding paragraph would give the full $\omega^\lambda$ at $x+b+d'$.
[Left addition options](GonshorBirthday/Surreal/Birthday/ReducedCostLower.lean)

## The next plus

We now have $v=e+d'\in R(z)$ and every $w\in R(z)$ exceeds both $e$ and $z+d'$.
In particular $v-z<2(w-z)$ for every $w$. Let $M=\omega^s$ be the leading monomial
of $v-z$. Let $H$ be the part of $z$ above $s$ and $r$ its real coefficient at $s$.
Put $T(k)=H+kM$.

Let $\gamma$ be the leading coefficient of $(v-z)/2$. For every real $r<k<r+\gamma$,
the number $T(k)$ lies strictly between $z$ and $z+(v-z)/2$, hence above all left
options and below all right options of $z$. So $z$ is a proper left prefix of $T(k)$.
Also $T(r)$ is a normal-form truncation of $z$. Simplicity on a fixed head and monomial agrees with
simplicity of real coefficients, so $r$ is a proper prefix of $k$. A real has at most
$\omega$ signs. Its proper prefixes have finite length and are therefore dyadic.
[Coefficient cuts](GonshorBirthday/Surreal/Birthday/Head.lean)

Take the simplest real $k$ in that interval of coefficients. After $r$ its word has one
plus followed only by minuses. Stopping before a second plus would give a simpler real
in the same interval. Write $q$ for $r$ with that first plus appended. Between $T(q)$
and $T(k)$ only minuses are appended, so $z$ is a left prefix of $T(q)$. The case
$r=0$ is impossible. It would put $z$ on the path to $T(1)$, whose right prefixes
exceed $T(t)$ for every positive real $t$, whereas $v-z$ is only of order $M$.
For $r\ne0$, the sign word from $T(r)$ to $T(q)$ is a single plus block. Since minuses
occur cofinally in $z$, we have $z=T(r)$. Its last coefficient sign must be a minus.
A final coefficient plus gives a final plus block, with the sole exception $r=1$,
already excluded by the same right-option argument.
[The gap argument](GonshorBirthday/Surreal/Birthday/GapWindow.lean)

Let $t$ be the dyadic obtained by removing the last minus of $r$. Put $W=T(t)$,
$y=T(q)$ and $U=L(M)$, the left prefixes of $M$. Gonshor’s coefficient cut reads

```math
y=\{\,z+U\mid W-U\,\}.
```

The family $W-U$ also consists of coinitial right options of $z$. To see why $y$ is a
prefix of $e$, take $W-u_0\le e+d'$. For each $u\in U$ choose $u_1\in U$ with
$u_1\ge u_0+u$. This is possible because $0$ and the finite multiples of $\omega^h$,
$h\in L(s)$, are cofinal in $U$. Then $z+d'<W-u_1\le e+d'-u$ gives $z+u<e$.
Every $W-u$ is above $e$, so $e$ fits the cut.
[The coefficient cut at a minus](GonshorBirthday/Surreal/Birthday/ReducedCostInterval.lean)

The block from $z$ to $y$ has $Q=\omega^{p(s)}$ pluses. Since the signs after $z$
in $e$ are all pluses and $y$ is a prefix of $e$, we have $y\le e$. A final segment
of $z$ contains at most $Q$ minuses. For $t\ne0$ this is the last coefficient block.
For $t=0$ we have $z=H-M$ and these minuses come from the $Q$ pluses of $M$. Group each
plus with the next retained minus. Its block absorbs the pluses in the group. Each group
therefore has length at most $\omega^{p(z)+1}$. A tail of $\omega^\lambda$ has type
$\omega^\lambda$ and fits in $\omega^{p(z)+1}Q$. Consequently

```math
\lambda\le p(z)+1+p(s)\le p(z)+Q=p(y).
```

The middle inequality uses $1+\nu\le\omega^\nu$ for ordinals $\nu$.
[Counting the coefficient block](GonshorBirthday/Surreal/Birthday/ReducedCostClassification.lean)

On the other hand $W$ itself is a right option of $z$. Take $u\in R(a)$ with
$u+b\le W$. Then

```math
u-a\le W-e\le W-y=(t-q)M,\qquad 0 \lt t-q \lt t-r\le1.
```

Apply (3) to this $y$ at the original cutoff $a+d$. Since $p(b)\le\beta$, we obtain

```math
\lambda\le p(y)<\alpha\oplus p(b)\le\alpha\oplus\beta=\lambda .
```

This contradiction proves (1). The distinction between a weak and a strict bound matters
even for a single monomial. At an ordinal epsilon number $E$, the old minus blocks of
$-E$ at cutoff $0$ occupy $E$ positions, and the plus run to $-E/2$ contributes another $E$.
[The unrestricted estimate](GonshorBirthday/Surreal/Birthday/ReducedCostBound.lean) ·
[Epsilon-number example](GonshorBirthday/Surreal/Birthday/Tests/ReducedCostSuffix.lean)

## Products of arbitrary normal forms

A zero factor gives the theorem immediately. Otherwise write $x=\sum_i r_i\omega^{a_i}$
and $y=\sum_j t_j\omega^{b_j}$ in decreasing order of exponents. Normal-form truncations
are sign prefixes, so the terms cut the sign words
into intervals of lengths $L_i,M_j$. At exponent $s=a_i+b_j$ the inputs supply a
rectangle $L_i\times M_j$. The exponent sums are reverse well-ordered. Ordering the
rectangles by decreasing sum respects both coordinates. Each tie is finite since
decreasing one exponent in a tie increases the other.

After a head $H$, Gonshor’s rule keeps the exponent minus at $w$ precisely when every
exponent in $H$ is at least $w$ and the coefficient at $w$ is dyadic. An absent
coefficient counts as zero. Cancellation can therefore restore an exponent minus.
In $(1-\omega^{-1})(1+\omega^{-1})$, for instance, the term at $-1$ vanishes, so
the term at $-2$ keeps both exponent minuses.

If each coefficient of a series $U$ has birthday at most that of the corresponding
coefficient of $V$, then $\ell(U)\le\ell(V)$. Induct through the support of $V$.
Suppose $U$ restores a minus at $w$ in an exponent $a$. If $V$ has an exponent $a'$
strictly between $a$ and $w$, then $w$ is also a right prefix of $a'$ and the head of
$U$ has no term in that interval. The induction estimate through $a'$ already includes
the block at $w$. Otherwise $V$ suppressed the minus by a nondyadic coefficient at
$w$. Its coefficient tail has length $\omega^{p(w)}\omega=\omega^{p(w)+1}$, exactly
the missing block. The finite coefficient tail of $U$ at $w$, if present, is absorbed
by that block. After comparing the exponent words, the coefficient tails at $a$ are
ordered by hypothesis. Take suprema at limits.
[Coefficient comparison](GonshorBirthday/Surreal/Birthday/CoefficientComparison.lean)

Form a series $Z$ on all exponent sums. At $s$ choose a coefficient of greatest birthday
among the actual product coefficient and the input coefficients of all pairs at $s$.
Thus $\ell(xy)\le\ell(Z)$, and a dyadic coefficient in $Z$ at $s$ implies that every
input coefficient there is dyadic. If $v$ is the first retained right prefix of $s$ in
$Z$, every preceding $a_k$ in $x$ gives an exponent $a_k+b_j$ in the head of $Z$,
so $a_k+b_j\ge v$. Equality requires a dyadic $r_k$, by the preceding observation and
Gonshor’s sign rule. Thus $v-b_j$ retains only minuses allowed at $a_i$ in $x$, and
likewise $v-a_i$ in $y$. Formula (2) bounds
the exponent blocks added by $s$ by the product of the available exponent lengths.
If there is no retained minus, the plus-count inequality does this directly.
[The term estimate](GonshorBirthday/Surreal/Birthday/ProductHeadCost.lean)

Finally each real coefficient sign after the first adds a block of length $\omega^{p(s)}$.
For a single pair these blocks fit along with its exponent word whenever the coefficient
birthday is at most $\ell(r_i)\otimes\ell(t_j)$. Indeed for finite input birthdays
$m+1,n+1$ the two input tails and their product supply $m+n+mn$ further blocks.
An infinite input tail supplies $\omega$ blocks. The condition holds for either input
coefficient and for $r_it_j$, by van den Dries and Ehrlich’s real product bound. If the
chosen coefficient is the sum of several products, add their bounds in the finite tie.
For a fixed head, the length added by a sum of two real coefficients is at most the
ordinary sum of their term lengths, by the real addition bound for dyadics and the
infinite tail for a nondyadic summand.
[Real products, Lemma 3.3](https://www.impan.pl/shop/en/publication/transaction/download/product/89226) ·
[Coefficient lengths](GonshorBirthday/Surreal/Birthday/HeadCoefficientCost.lean)

Give each rectangle a well-order of its maximal type $L_i\otimes M_j$ and concatenate
in the indicated order, breaking ties in their finite order. This well-order of all sign
pairs extends the coordinatewise order. By Carruth’s theorem its type is at most
$\ell(x)\otimes\ell(y)$. It covers all the term lengths of $Z$, also at a limit of
exponents. This proves the theorem.
[Carruth’s theorem](https://doi.org/10.1090/S0002-9904-1942-07649-X) ·
[Assembly in Lean](GonshorBirthday/Surreal/Birthday/ProductGrid.lean)

For an ordinal exponent $\gamma$, (2) has an independent proof. Every right prefix of
$a+\gamma$ is exactly $u+\gamma$ for a right prefix $u$ of $a$ and keeps its gap $u-a$.
This follows by descending through the addition cut, since $\gamma$ has no right
options. This proves the bound term by term whenever one factor has only ordinal
exponents, in particular for every ordinal factor by Cantor normal form.
[Ordinal translation](GonshorBirthday/Surreal/Birthday/OrdinalTranslation.lean) ·
[Ordinal factors](GonshorBirthday/Surreal/Birthday/OrdinalMultiplication.lean)
