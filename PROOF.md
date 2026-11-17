# Gonshor's birthday conjecture

Let $\ell(x)$ denote the length of the sign sequence of a surreal number $x$, which
is its birthday, and let $\otimes$ denote the natural product of ordinals.

**Theorem.** For all surreal numbers $x$ and $y$,

```math
\ell(xy)\le\ell(x)\otimes\ell(y).
```

Gonshor states this conjecture in *An Introduction to the Theory of Surreal
Numbers*, Chapter 6, p. 96. Equality holds for every pair of ordinals, since
their surreal product is their natural product.

Write the factors in Conway normal form. The terms in the product with a given
exponent come from finitely many pairs of input terms. They can cancel, and
deleting an earlier term can lengthen a later one. We handle both effects by
choosing one real coefficient of maximal birthday at each exponent sum
(Section 3). The main estimate is then about the sign sequence of a sum of
two exponents (Section 4). It bounds the contribution of each pair, and
Carruth's theorem on products of well orders combines the bounds (Section 5).

## 1. Preliminaries

### Ordinals

Ordinary ordinal sums, products and powers use the usual symbols. Write
$\oplus,\otimes$ for natural sum and product, and $\sum^{\mathrm{ord}}$ for
concatenation in the indicated order. We use three facts about Cantor normal
form. If all Cantor exponents of $\nu$ are at least $\gamma$ and $\sigma\lt\nu$,
then $\sigma+\omega^\gamma\le\nu$. Natural multiplication satisfies
$(\sigma+\tau)\otimes\upsilon\ge(\sigma\otimes\upsilon)+(\tau\otimes\upsilon)$.
The Cantor exponents of a natural product are the natural sums of exponents
from the two factors, and multiplication by a nonzero factor is strictly
increasing.

**Theorem 1.1** (Carruth and de Jongh–Parikh). (a) Let $W$ be a well-ordered set
with maps $f\colon W\to\alpha$ and $g\colon W\to\beta$ into ordinals such that
$f(u)\le f(v)$ and $g(u)\le g(v)$ imply $u\le v$. Then the order type of $W$ is at
most $\alpha\otimes\beta$. (b) The product order on $\alpha\times\beta$ has a linear
extension of order type $\alpha\otimes\beta$.

### Sign sequences

A *prefix* $z$ of $a$ is an initial segment of its sign sequence, denoted by
$a\upharpoonright\delta$ when it has length $\delta$. A proper prefix is a
*left prefix* if the next sign is plus, so $z\lt a$, or a *right prefix* if it
is minus, so $z\gt a$. Write $R(a)$ for the right prefixes. They decrease in
value as their lengths increase. The numbers extending any fixed prefix form
a convex class. Let $p(a)$ be the order type of its plus positions. Every
prefix has plus count at most $p(a)$, strictly less for a left prefix.

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
$\omega^a$, which is zero unless $a$ lies in the support $\mathrm{supp}\,x$, and
$x_{\gt a}$ for the sum of the terms of $x$ with exponent greater than $a$.
We write $\mathrm{supp}\,x\gt s$ when every exponent of $x$ is greater than $s$.

A real $r$ has $\ell(r)\le\omega$, with $\ell(r)\lt\omega$ exactly when $r$ is dyadic.

**Lemma 1.4** (van den Dries–Ehrlich, Lemma 3.3). For reals $r,t$,
$\ell(rt)\le\ell(r)\otimes\ell(t)$.

We also use $\ell(x+y)\le\ell(x)\oplus\ell(y)$, which holds for all surreals.

The cut calculation and the real multiplication bound appear in
[Addition.lean](GonshorBirthday/Surreal/Birthday/Addition.lean) and
[RealMultiplication.lean](GonshorBirthday/Surreal/Birthday/RealMultiplication.lean).

## 2. The length of a normal form

The sign sequence of $\omega^a$ is a plus followed by one block for each sign of
$a$. The sign at position $\delta$ gives a block of length
$\omega^{p(a\upharpoonright\delta)+1}$ (Gonshor, Theorem 5.11). For a set $S$ of positions
of $a$ put

```math
E(a,S)=1+\sum_{\delta\in S}^{\mathrm{ord}}\omega^{p(a\upharpoonright\delta)+1},
```

so that $\ell(\omega^a)=E(a,S)$ with $S$ the set of all positions. Note that the
exponents refer to the plus count in $a$ itself, whatever $S$ is.

**Definition 2.1.** Let $H$ be a surreal. A surreal $w$ is admissible after $H$
if every exponent of $H$ is at least $w$ and $c_H(w)$ is dyadic, including
when it is zero. If $w$ is admissible, so is every $w'\lt w$. A
position of $a$ is retained after $H$ if it carries a plus, or if it carries a
minus whose right prefix is admissible after $H$. Let $G_H(a)=E(a,S)$ for $S$ the
set of retained positions, and for a real $r$ let

```math
L_H(a,r)=G_H(a)+\omega^{p(a)}\bigl(\ell(r)-1\bigr)\quad(r\ne0),\qquad L_H(a,0)=0.
```

**Theorem 2.2** (Gonshor, Theorems 5.11–5.12). Let $\mathrm{supp}\,H\gt a$ and
$r\ne0$. For $r\gt0$ the sign sequence of $H+r\omega^a$ is that of $H$, followed by
a plus, then for each retained position $\delta$ of $a$, in order,
$\omega^{p(a\upharpoonright\delta)+1}$ copies of the sign of $a$ at $\delta$, then for
each sign of $r$ after the first, in order, $\omega^{p(a)}$ copies of it. For
$r\lt0$ the part after $H$ is that for $-r$ with all signs reversed. In particular
$\ell(H+r\omega^a)=\ell(H)+L_H(a,r)$, and for $x=\sum_{i\lt\theta}r_i\omega^{a_i}$,

```math
\ell(x)=\sum_{i\lt\theta}^{\mathrm{ord}}L_{x_{\gt a_i}}(a_i,r_i).
```

At a limit of terms the lengths of the truncations approach the ordered sum.
The factor $\ell(r)-1$ counts the signs after the first and equals $\omega$ for
a nondyadic real. Taking $H=0$ gives the sign sequence of a single monomial
for both finite and infinite coefficient birthdays. The block length
$\omega^{p(a)}$ equals $p(\omega^a)$. For each ordinal below this length there
is a left prefix of $\omega^a$ with at least that many pluses. This gives the
same lower bound for a full coefficient block of either sign.
[CoefficientWord.lean](GonshorBirthday/Surreal/Birthday/CoefficientWord.lean) and
[NormalFormLength.lean](GonshorBirthday/Surreal/Birthday/NormalFormLength.lean).

For example, in $\omega^{-1}+\omega^{-2}$ the exponent $-2$ has two minuses,
with right prefixes $0$ and $-1$. The head has exponent $-1$, so it deletes the
first minus and retains the second. The second term contributes $1+\omega$,
giving total length $\omega+\omega$.

## 3. Coefficient comparison and cancellation

**Lemma 3.1.** If $\ell(c_u(a))\le\ell(c_v(a))$ for all $a$, then
$\ell(u)\le\ell(v)$.

Deleting terms can restore minus blocks in later terms. To take that into
account, induct along the decreasing support of $v$ to prove

```math
\ell(u_{\gt a})+G_{u_{\gt a}}(a)
\le\ell(v_{\gt a})+G_{v_{\gt a}}(a)
\qquad(a\in\mathrm{supp}\,v).
```

The induction first bounds $\ell(u_{\gt a})$ by $\ell(v_{\gt a})$. Compare the
signs of $a$ in order. Suppose a minus with right prefix $w$ is retained on
the left and deleted on the right. Two events can account for it.

- An exponent $a'$ of $v$ lies strictly between $a$ and $w$. Admissibility on
  the left forces $u_{\gt a}=u_{\gt a'}$. Also $w$ is a right prefix of $a'$,
  since $a\lt a'\lt w$. The bound at $a'$ therefore accounts for the whole
  prefix through the restored block.
- The coefficient of $v$ at $w$ is nondyadic and that of $u$ is dyadic. The
  former contributes a tail of length $\omega^{p(w)}\cdot\omega
  =\omega^{p(w)+1}$, exactly the length of the restored minus block. The
  shorter coefficient tail and the preceding pluses are absorbed in that
  length.

In either case the right-hand head already covers the restored block. Adding
the coefficient tails and taking suprema gives the lemma, including at absent
coefficients of $u$.
[CoefficientComparison.lean](GonshorBirthday/Surreal/Birthday/CoefficientComparison.lean).

Let $P_s$ be the pairs $(a,b)\in\mathrm{supp}\,x\times\mathrm{supp}\,y$ with
$a+b=s$. Each $P_s$ is finite. Infinitely many different first exponents would
have a strictly decreasing subsequence, making the corresponding second
exponents strictly increasing in a reverse well-ordered support. Choose
$c_Z(s)$ of greatest **birthday** among

```math
\{c_{xy}(s)\}\ \cup\! \bigcup_{(a,b)\in P_s}\{c_x(a),c_y(b)\}.
```

Ties can be settled arbitrarily. For an empty fibre the only candidate is
zero. Every nonempty fibre contains a nonzero input coefficient, so its winner
has positive birthday. The support of $Z$ is thus the set of all exponent
sums, a small reverse well-ordered set. These coefficients define a surreal,
and Lemma 3.1 gives $\ell(xy)\le\ell(Z)$. Moreover, if $c_Z(s)$ is dyadic,
every input coefficient contributing at $s$ has finite birthday and is
dyadic too.

For example, $(1-\omega^{-1})(1+\omega^{-1})$ has coefficient zero at $-1$.
The candidates there are $0,1,-1$, so $Z$ keeps a coefficient of birthday one.
[Construction](GonshorBirthday/Surreal/Birthday/ProductCoefficientCost.lean) and
[cancellation example](GonshorBirthday/Surreal/Birthday/Tests/ProductCoefficientCost.lean).

## 4. The monomial estimate

**Definition 4.1.** For any cutoff $C$, let $D(C,a)$ be $E(a,S)$ with all pluses retained and
exactly those minuses whose right prefix is at most $C$. Write
$F_d(a)=D(a+d,a)$ for $d\ge0$. The retained minuses form a final segment of the
minuses. For a head $H$ above $a$, take $C$ to be the greatest right prefix
retained after $H$, or $a$ if there is none. The greatest one exists because
the shortest retained prefix is the largest in value. By downward closure of
admissibility, $G_H(a)=D(C,a)$.

**Theorem 4.2.** For all surreal $a,b$ and all $A\ge a$, $B\ge b$,

```math
D\bigl(\min(A+b,a+B),a+b\bigr)\le D(A,a)\otimes D(B,b).
```

It suffices to prove $F_d(a+b)\le F_d(a)\otimes F_d(b)$ for $d\gt0$. Take
$d=\min(A-a,B-b)$ and use monotonicity in the cutoff. At zero margin only
pluses contribute, so $F_0(a)=\omega^{p(a)}$ and Lemma 1.3 gives the result.

### Induction through a retained minus

Induct on $\ell(a)\oplus\ell(b)$, for all cutoffs at once. Fix $e=a+b$ and
write $N_d=F_d(a)\otimes F_d(b)$. Every Cantor exponent of $F_d(a)$ is at
least $p(a)$ by the expansion formula. Consequently every Cantor exponent of
$N_d$ is at least $p(a)\oplus p(b)\ge p(e)$.

Let $v\in R(e)$ with $v\le e+d$. By Lemma 1.2 it is a prefix of some $u+b$
with $u\in R(a)$ and $u+b\le v$, or symmetrically of $a+u$. In the first
case $u\le a+d$. The induction hypothesis for $(u,b)$ with cutoffs $a+d,b+d$
has output cutoff $e+d$, since $u\gt a$. Thus

```math
D(e+d,v)\le D(a+d,u)\otimes F_d(b).
```

The next minus of $a$ contributes $\omega^{p(u)+1}$, followed by a contribution
of at least $\omega^{p(a)}$ if $p(u)\lt p(a)$. Multiplying these bounds by
$F_d(b)\ge\omega^{p(b)}$, and using the ordinal inequalities of Section 1,
gives

```math
D(e+d,v)+\omega^{p(v)+1}+\varepsilon\le N_d,\qquad
\varepsilon=
\begin{cases}\omega^{p(e)}&p(v)\lt p(e),\\0& p(v)=p(e).\end{cases}
```

Indeed $p(v)\le p(u)\oplus p(b)$. When $p(u)=p(a)$ and $p(v)\lt p(e)$, the
one block $\omega^{(p(a)\oplus p(b))+1}$ already bounds both output terms.

Suppose $F_d(e)\gt N_d$. If there were a last retained minus, the displayed
bound would cover it and all remaining pluses. If there were none, the
plus-only bound would suffice. Let $z$ be the shortest prefix containing all
retained minuses. Their positions are cofinal in $\ell(z)$, and taking the
supremum of the prefix bounds gives $D(e+d,z)\le N_d$. Thus $z$ is proper
and $e$ is $z$ followed by $\rho\gt0$ pluses. These pluses contribute
$\omega^{p(e)}$. If $D(e+d,z)\lt N_d$, adding this contribution still gives
at most $N_d$, since every Cantor exponent of $N_d$ is at least $p(e)$.
Hence $D(e+d,z)=N_d$.
[Prefix bounds](GonshorBirthday/Surreal/Birthday/ReducedCostAddition.lean) and
[limit reduction](GonshorBirthday/Surreal/Birthday/ReducedCostReduction.lean).

### Reducing the margin

One input supplies the preceding prefix bounds cofinally, say $a$. Thus
$D(a+d,u)\otimes F_d(b)$ approaches $N_d$ for retained $u\in R(a)$, with
$D(a+d,u)\lt F_d(a)$. The prefix costs must be cofinal in $F_d(a)$, and
$F_d(b)$ must be a single Cantor term $\omega^\beta$. To see the latter, write
$F_d(a)=\mu+\omega^\alpha$, displaying its last Cantor term. If $F_d(b)$
had a second term, even the contribution of its leading term multiplied by
$\omega^\alpha$, together with $\mu\otimes F_d(b)$ under natural addition,
would be a strict upper bound below $N_d$ for all these products.

Choose a retained $u_0\in R(a)$ with $D(a+d,u_0)\gt\mu$. There are arbitrarily
late retained right prefixes of $z$ below $u_0+b$. Otherwise $u_0+b$ would
extend $z$ and induction at $(u_0,b)$ would bound $D(e+d,z)=N_d$ strictly
below $N_d$. Choose such a $v$ with $v\lt e+d$ after the part of $N_d$ before
its last Cantor term, and reduce the margin to $d'=v-e$.

The newly retained part of $z$ consists of its earlier pluses and the suffix
starting at $v$. That suffix has length $\omega^{\alpha\oplus\beta}$ and
absorbs the earlier pluses since $p(v)\lt p(e)\le\alpha\oplus\beta$. On the
input side $a+d'\lt u_0$, so the retained minuses of $a$ lie in the last
Cantor term $\omega^\alpha$ of its old cost. Their cost together with the
earlier pluses is at most $\omega^\alpha$ because $p(u_0)\lt\alpha$. The
second input still costs at most $\omega^\beta$. But the prefix bounds for
$d'$ give $D(e+d',z)\le N_{d'}$. Equality is forced on both inputs, and the
final pluses still exceed the bound.
[Cantor term reduction](GonshorBirthday/Surreal/Birthday/ReducedCostNormalize.lean).

Use this new margin, again called $d$. We have, with $\lambda=\alpha\oplus\beta$,

```math
F_d(a)=\omega^\alpha,\qquad F_d(b)=\omega^\beta,\qquad D(e+d,z)=\omega^\lambda.
```

At this margin one input again has cofinally many retained minuses. Interchange
the inputs if necessary so that it is $a$. The smaller cutoff $z+d$ deletes
**every** right prefix of $z$. Indeed $z$ is a left prefix of $e$, so it extends
to a left option, say $u+b$ with $u$ a left prefix of $a$. Induction bounds
$D(u+b+d,z)$ strictly below $\omega^\lambda$, since $u$ precedes a plus of
$a$. Any right prefix retained at $z+d$ would also be retained at $u+b+d$.
From that minus onward the cost would agree with a nonempty final part of
$\omega^\lambda$, which itself has length $\omega^\lambda$.

### The last term of the limit prefix

Choose $w_0\in R(z)$ with $w_0\le e+d$. For each $v\in R(z)$, both $e-z$ and
$d$ are less than $v-z$, by the prefix relation and deletion at $z+d$. Hence

```math
w_0-z\le(e-z)+d\lt2(v-z)\qquad(v\in R(z)).
```

This forces a last term $z=K+r\omega^s$. Here is how the normal form rules out
the alternatives. A proper prefix of $z$ differs from $z$ by at least
$\varepsilon\omega^h$ for some supported $h$ and positive real $\varepsilon$.
Otherwise $z$ itself would be a truncation of that prefix. If $x$ is a
supported exponent and $v\in R(x)$, right-prefix gaps of $z$ can be made
smaller than any positive real multiple of $\omega^v$. To see this, take the
largest supported exponent below $v$. A negative coefficient gives such a
gap by truncation. A nondyadic coefficient at $v$ can be approximated from
above by its real prefixes. In the remaining case the retained minus with
prefix $v$ gives successively halved increments on scale $\omega^v$.

If the support had no least exponent, choose a decreasing sequence of its
exponents below the scale $h$ of $w_0-z$. Their birthdays cannot decrease
forever. For some successive pair, the smaller exponent therefore has a right
prefix at or below the larger one (take their common prefix). The small gaps
at this scale contradict the displayed inequality. If the last coefficient
were nondyadic, its real right prefixes would give arbitrarily small gaps on
scale $\omega^s$, again a contradiction. Finally, a dyadic ending in a plus
other than $1$ ends the term with a full plus block, contradicting cofinality
of the minuses. For $r=1$, cofinally many minuses must come from minus blocks
of the exponent. Within its last such block the gaps can be halved, or later
blocks give strictly smaller scales. Thus $r$ ends in a minus.
[Classification of the last term](GonshorBirthday/Surreal/Birthday/ReducedCostClassification.lean).

Let $t$ be $r$ with that last minus removed, $W=K+t\omega^s$, and
$Q=\omega^{p(s)}=p(\omega^s)$. The sign formula gives two facts about the
last block. For a left prefix $u$ of $\omega^s$, $z+u$ appends $p(u)$ pluses
to $z$. Also $W-u$ is a right prefix of $z$, and these right prefixes are
coinitial in $R(z)$, meaning each right prefix lies at or above one of them. When
$t\ne0$, $z$ extends $W$ by $Q$ minuses. When $t=0$, the initial minus after
$K$ and the reversed plus blocks of $s$ contribute
$1+\sum_{\gamma\lt p(s)}^{\mathrm{ord}}\omega^{\gamma+1}=Q$ minuses. In
either case the part after $W$ has at most $Q$ minus positions, and
$d\lt W-z=(t-r)\omega^s\le\omega^s$.
[Right prefixes of the last block](GonshorBirthday/Surreal/Birthday/LastMinusFamily.lean).

We claim $\rho\ge Q$. If $\rho\lt Q$, some left prefix $u$ of $\omega^s$ has
at least $\rho$ pluses, so $e\le z+u$. Choose a left prefix $v$ of $\omega^s$
with $W-v\le w_0$. Take a left prefix $c$ bounding twice the larger of $u,v$,
so $u+v\le c$. Indeed $0$ and the multiples $n\omega^h$ for left prefixes
$h$ of $s$ and positive integers $n$ are cofinal among the left prefixes of
$\omega^s$, and doubling preserves that family. Deletion gives
$z+d\lt W-c$. Now $e+d\le z+u+d\lt W-c+u\le W-v\le w_0$, contradicting
$w_0\le e+d$.
[Full-block bound](GonshorBirthday/Surreal/Birthday/ReducedCostInterval.lean).

Put $P=p(z)$ and $q=p(s)$. Starting at a retained minus after $W$, group
each subsequent minus with the pluses since the preceding minus. Each group
costs at most $\omega^{P+1}$ and there are at most $Q$ groups. They exhaust a
nonempty final part of $\omega^\lambda$, so $\lambda\le P+1+q$. It follows that

```math
\lambda\le P+1+q\le P+\omega^q\le P+\rho=p(e)
\le p(a)\oplus p(b)\le\lambda.
```

Equality throughout gives $\rho=Q$, $\alpha=p(a)$, $\beta=p(b)$ and
$p(e)=p(a)\oplus p(b)$. Appending exactly $Q$ pluses to $z$ appends one plus
to the coefficient $r$, so $e=K+r'\omega^s$ with $r'$ dyadic.

### Why equality is impossible here

If either input has an exponent below $s$, take the greatest such exponent.
Its coefficients cancel, so one is positive. Truncating both inputs above it
preserves their sum $e$ and takes a left prefix of the input with positive
coefficient. Lemma 1.3 then gives $p(e)\lt p(a)\oplus p(b)$. The coefficients
at $s$ must also be dyadic. Otherwise approximate a nondyadic one from below
by a real left prefix. The reals extending the dyadic $r'$ contain an open
interval around $r'$, so the approximation gives a left prefix $a'$ of one
input with $e$ still a prefix of $a'+b$. Again
$p(e)\le p(a')\oplus p(b)\lt p(a)\oplus p(b)$.
[Equality and cancellation](GonshorBirthday/Surreal/Birthday/CoefficientCancellation.lean).

The retained minuses of $a$ are cofinal. Its pluses must also be cofinal,
since one later retained minus would cost $\omega^{p(a)+1}\gt F_d(a)$.
Write $a=H+c\omega^s$ with all exponents of $H$ greater than $s$. For $c=0$
every right-prefix gap exceeds $\omega^s$. A dyadic $c\ne0,\pm1$ ends the
sign sequence with a constant block, preventing both signs from being
cofinal. For $c=1$, any right prefix within $\omega^s$ would have the form
$H+k\omega^s$ plus smaller terms, with $k\ge1$. Such a number extends $a$,
so it cannot be a proper prefix of $a$. This leaves $a=H-\omega^s$.

For any right prefix $w$ of $a$, the last-block description gives a left
prefix $v$ of $\omega^s$ with $H-v\le w$. Deletion of $W-v$ at $z+d$ now gives

```math
d\lt(W-v)-z=(t-r)\omega^s-v\le\omega^s-v=(H-v)-a\le w-a.
```

Thus $a$ has no retained right prefix at $a+d$, contradicting cofinality.
This proves Theorem 4.2.
[Input classification](GonshorBirthday/Surreal/Birthday/ReducedCostInput.lean) and
[conclusion of the induction](GonshorBirthday/Surreal/Birthday/ReducedCostBound.lean).

## 5. From one pair of terms to the product

Write $L_i=L_{x_{\gt a_i}}(a_i,r_i)$ and $M_j=L_{y_{\gt b_j}}(b_j,t_j)$
for the term lengths of the original inputs. Fix a pair, write $a=a_i$,
$b=b_j$, $s=a+b$, and put $H=Z_{\gt s}$.

Suppose $v\in R(s)$ is retained after $H$. For every earlier exponent
$a_k\gt a$ of $x$, the sum $a_k+b$ occurs in $H$, so $a_k+b\ge v$.
Equality forces $r_k$ to be dyadic by maximality of the birthday of $c_Z(v)$.
Thus $v-b$ is admissible after $x_{\gt a}$. Likewise $v-a$ is admissible
after $y_{\gt b}$.

Choose the greatest retained output right prefix $C$, or $C=s$ if there is
none. In the first case the shifted cutoffs $C-b$ and $C-a$ retain only
positions allowed by the two input heads. Theorem 4.2 bounds $G_H(s)$ by the
natural product of their head lengths. For $C=s$ the bound follows directly
from $p(a+b)\le p(a)\oplus p(b)$. Including the coefficient tails gives an
estimate for **any** real $r$.

```math
\ell(r)\le\ell(r_i)\otimes\ell(t_j)
\quad\Longrightarrow\quad L_H(s,r)\le L_i\otimes M_j.
```

Indeed a repeated output block has length $\omega^{p(s)}\le
\omega^{p(a)}\otimes\omega^{p(b)}$. With finite input birthdays $m+1,n+1$,
the product of the two input term lengths bounds the head and $m+n+mn$
such blocks. Expand the two concatenations by the ordinal product inequality
of Section 1, using that each input head is at least as long as its repeated
block. If either input birthday is $\omega$, the same argument repeated along
that input bounds $\omega$ blocks, enough for any real $r$.
[Head estimate](GonshorBirthday/Surreal/Birthday/ProductHeadCost.lean) and
[coefficient estimate](GonshorBirthday/Surreal/Birthday/HeadCoefficientCost.lean).

Either input coefficient satisfies the displayed hypothesis since the other
has birthday at least one. Their product satisfies it by Lemma 1.4. Thus if
$c_Z(s)$ is an input coefficient, the entire term at $s$ fits in one pair's
bound. If it is the convolution coefficient, use
$L_H(s,r+t)\le L_H(s,r)+L_H(s,t)$. For dyadic summands this follows from
$\ell(r+t)\le\ell(r)\oplus\ell(t)$ and $G_H(s)\ge\omega^{p(s)}$ for the extra
block. A nondyadic summand already supplies an infinite coefficient tail.
Consequently in either case

```math
L_H(s,c_Z(s))\le\sum_{(i,j):a_i+b_j=s}^{\mathrm{ord}}(L_i\otimes M_j)
```

for any ordering of the finite fibre.
[Finite fibre estimate](GonshorBirthday/Surreal/Birthday/ProductCoefficientCost.lean).

Order the pairs by decreasing $a_i+b_j$ and break ties arbitrarily. Replace
each pair by a linear extension of $L_i\times M_j$ of type $L_i\otimes M_j$
(Theorem 1.1). The resulting well order $W$ extends the product order on
$(\sum_i^{\mathrm{ord}} L_i)\times(\sum_j^{\mathrm{ord}}M_j)$. Indeed within
a pair this is how its order was chosen. Between different pairs, increasing
the two indices, at least one strictly, strictly decreases the exponent sum.
Carruth's upper bound now gives

```math
\ell(xy)\le\ell(Z)\le\mathrm{type}(W)
\le\Bigl(\sum_i^{\mathrm{ord}}L_i\Bigr)\otimes\Bigl(\sum_j^{\mathrm{ord}}M_j\Bigr)
=\ell(x)\otimes\ell(y).
```

This includes empty supports and arbitrary ordinal lengths.
[Product order](GonshorBirthday/Surreal/Birthday/ProductGrid.lean) and
[the native multiplication theorem](GonshorBirthday/Surreal/Birthday/Multiplication.lean).

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
