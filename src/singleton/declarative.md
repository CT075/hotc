# Singleton kinds, declaratively

The singleton kind calculus relevant to us is syntactically an extension of
$F_\omega$ (plus products), with identical constructors and terms. The kinds,
of course, are extended with the $S(c)$ singleton kind. But to fully represent
modules, we need more power.

Consider the signature

```ocaml
sig
  type t
  type u = t * int
end
```

Intuitively, we might write this kind as $\* \times S(t \times \texttt{int})$,
but this isn't well-formed (the type variable $t$ is not in scope). This
necessitates the use of *dependent kinds*, $\Sigma$- and $\Pi$-kinds. These
subsume normal arrow and (non-dependent) product kinds, giving us

$$k := \* \mid S(c) \mid \Sigma(\alpha:k).k \mid \Pi(\alpha:k).k$$

Of course, we will still use $k \rightarrow k'$ and $k \times k'$ as shorthand
for $\Pi(\alpha:k).k'$ and $\Sigma(\alpha:k).k'$ respectively if $k$ is not
free in $k'$.

The judgments we will use are

| Judgment | Meaning |
|---|---|
| $\Gamma \vdash k:\text{kind}$ | Kind validity |
| $\Gamma \vdash k \equiv k' : \text{kind}$ | Kind equivalence |
| $\Gamma \vdash k \le k'$ | Subkinding |
| $\Gamma \vdash c: k$ | Kinding |
| $\Gamma \vdash c \equiv c' : k$ | Constructor equivalence |
| $\Gamma \vdash e : \tau$ | Typing (same as $F_\omega$) |
| $\phantom{\Gamma} \vdash \Gamma\ ok$ | Context well-formedness |

The addition of singleton kinds necessitates subkinding to handle cases like
`int`, which has kind $\*$ but *also* kind $S(\texttt{int})$.

**Rules 2.1 (Kind validity):** $\Gamma \vdash k:\text{kind}$

$$
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$\Gamma \vdash \* : \text{kind}$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c:\*$}
\UnaryInfC{$\Gamma \vdash S(c): \text{kind}$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash k_1:\text{kind}$}
\AxiomC{$\Gamma, \alpha:k_1 \vdash k_2:\text{kind}$}
\BinaryInfC{$\Gamma \vdash \Pi(\alpha:k_1).k_2:\text{kind}$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash k_1:\text{kind}$}
\AxiomC{$\Gamma, \alpha:k_1 \vdash k_2:\text{kind}$}
\BinaryInfC{$\Gamma \vdash \Sigma(\alpha:k_1).k_2:\text{kind}$}
\end{prooftree}
$$

**Rules 2.2 (Kind equivalence):** $\Gamma \vdash k \equiv k' : \text{kind}$

$$
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$\Gamma \vdash \* \equiv \* : \text{kind}$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c \equiv c' : \*$}
\UnaryInfC{$\Gamma \vdash S(c) \equiv S(c') :\text{kind}$}
\end{prooftree}
$$

$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash k_1 \equiv k_1' : \text{kind}$}
\AxiomC{$\Gamma, \alpha:k_1 \vdash k_2 \equiv k_2' : \text{kind}$}
\BinaryInfC{$\Gamma \vdash \Pi(\alpha:k_1).k_2 \equiv \Pi(\alpha:k_1').k_2'$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash k_1 \equiv k_1' : \text{kind}$}
\AxiomC{$\Gamma, \alpha:k_1 \vdash k_2 \equiv k_2' : \text{kind}$}
\BinaryInfC{$\Gamma \vdash \Sigma(\alpha:k_1).k_2 \equiv \Sigma(\alpha:k_1').k_2'$}
\end{prooftree}
$$

Before moving onward, we'll need some more machinery. By the above rules, we
can only define singleton kinds for *types* (constructors kinded at $\*$). As
a typechecking mechanism, this is important, lest someone write `type t =
list`. When declaring our whole system, however, this can be inconvenient.
Let us define the
*generalized singleton* $S(c:k)$ be defined as follows:

$$
\begin{aligned}
S(c:\*) &\triangleq S(c) \\\\
S(c:\Pi(\alpha:k_1).k_2) &\triangleq \Pi(\alpha:k_1).S(c\ \alpha : k_2) \\\\
S(c:\Sigma(\alpha:k_1).k_2) &\triangleq
  S(\pi_1c : k_1) \times S(\pi_2c:[\pi_1c/\alpha]k_2) \\\\
S(c:S(c')) &\triangleq S(c)
\end{aligned}
$$

Note that the $\Sigma$ clause could be more concisely written as
$\Sigma(\alpha:S(\pi_1c:k_1)).S(\pi_2c:k_2)$, but we choose to expand it out
for clarity. Ideally, this definition should fit to the following condition
(written as a derived rule):

$$
\begin{prooftree}
\alwaysDashedLine
\AxiomC{$\Gamma \vdash c:k$}
\AxiomC{$\vdash \Gamma\ ok$}
\BinaryInfC{$\Gamma \vdash S(c:k)\ ok$}
\end{prooftree}
$$

which it does.

Why is all this necessary? Previously, when checking constructor equivalence,
neither $\Gamma$ nor $k$ were used. But what about in this system?

$$
\lambda (\alpha:\*) . \alpha \overset{?}{=} \lambda (\alpha:\*) . \texttt{int}
$$

Before, we would say that this is "obviously false". Calling one on a type that
is not `int` demonstrates this. But now, with
subkinding, we might say that

$$\cdot \vdash \lambda (\alpha:\*) . \alpha : S(\texttt{int}) \rightarrow \*$$

because $S(\texttt{int}) \le \*$. But then, these two lambdas should be
equivalent, because if $\alpha : S(\texttt{int})$, then $\alpha$ must be
(equivalent to) $\texttt{int}$ itself! So clearly the kind we are checking at
matters.

Similarly, we need the context as well. Consider

$$
\beta (\lambda(\alpha:\*).\alpha) \overset{?}{=} \beta(\lambda(\alpha:\*).\texttt{int})
$$

Now, the kind of $\beta$ fixes the kinds of the lambdas (which, as we saw
above, matters).

**Rules 2.3 (Subkinding):** $\Gamma \vdash k \le k'$

*Preorder*:
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash k \equiv k':\text{kind}$}
\UnaryInfC{$\Gamma \vdash k \le k'$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash k_1 \le k_2$}
\AxiomC{$\Gamma \vdash k_2 \le k_3$}
\BinaryInfC{$\Gamma \vdash k_1 \le k_3$}
\end{prooftree}
$$

*Other*:
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c:\*$}
\UnaryInfC{$\Gamma \vdash S(c) \le \*$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c \equiv c' : \*$}
\RightLabel{$\*$}
\UnaryInfC{$\Gamma \vdash S(c) \le S(c')$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash k_1' \le k_1$}
\AxiomC{$\Gamma, \alpha:k_1' \vdash k_2 \le k_2'$}
\AxiomC{$\Gamma, \alpha:k_1 \vdash k_2 : \text{kind}$}
\TrinaryInfC{$\Gamma \vdash \Pi(\alpha:k_1).k_2 \le \Pi(\alpha:k_1').k_2'$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash k_1 \le k_1'$}
\AxiomC{$\Gamma, \alpha:k_1 \vdash k_2 \le k_2'$}
\AxiomC{$\Gamma, \alpha:k_1' \vdash k_2' : \text{kind}$}
\TrinaryInfC{$\Gamma\vdash\Sigma(\alpha:k_1).k_2\le\Sigma(\alpha:k_1').k_2'$}
\end{prooftree}
$$

The starred rule is actually unnecessary, as it falls out from the symmetry
rule.

The rule for $\Pi$ types flips the direction of the input kind, as functions
are known to be contravariant. When checking the dependent parts of $\Pi$ and
$\Sigma$, it is important that our context holds that $\alpha$ is the *larger*
kind, as it will work for both comparands. Finally, we must check that certain
subkinds are well-formed, as this won't necessarily fall out from proving other
premises.

**Rules 2.4.1 (Kinding, incomplete):** $\Gamma \vdash c:k$

$$
\begin{prooftree}
\AxiomC{$\Gamma(\alpha) = k$}
\UnaryInfC{$\Gamma \vdash \alpha : k$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma, \alpha:k \vdash c:k'$}
\AxiomC{$\Gamma \vdash k:\text{kind}$}
\BinaryInfC{$\Gamma \vdash \lambda(\alpha:k).c : \Pi(\alpha:k).k'$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1:\Pi(\alpha:k).k'$}
\AxiomC{$\Gamma \vdash c_2:k$}
\BinaryInfC{$\Gamma \vdash c_1\ c_2:[c_2/\alpha]k'$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c:\Sigma(\alpha:k_1).k_2$}
\UnaryInfC{$\Gamma \vdash \pi_1c : k_1$}
\end{prooftree}\qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c:\Sigma(\alpha:k_1).k_2$}
\UnaryInfC{$\Gamma \vdash \pi_2c : [\pi_1c/\alpha]k_2$}
\end{prooftree}
$$

The major missing rule is the one kinding type-level tuples. There is one
obvious candidate:

$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1:k_1$}
\AxiomC{$\Gamma \vdash c_2:[c_1/\alpha]k_2$}
\AxiomC{$\Gamma, \alpha:k_1 \vdash k_2:\text{kind}$}
\TrinaryInfC{$\Gamma \vdash \langle c_1,c_2 \rangle:\Sigma(\alpha:k_1).k_2$}
\end{prooftree}
$$

There is also the rule for non-dependent tuples:

$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1:k_1$}
\AxiomC{$\Gamma \vdash c_2:k_2$}
\BinaryInfC{$\Gamma \vdash \langle c_1,c_2 \rangle : k_1 \times k_2$}
\end{prooftree}
$$

which clearly falls out from the first rule. It turns out, however, that these
two formulations are actually *equivalent* (under subsumption). Suppose we are
given $\Gamma \vdash c_1:k_1$, $\Gamma \vdash c_2:[c_1/alpha]k_2$ and that the
kinds are well-formed. Then

- We have $\Gamma \vdash c_1:S(c_1:k_1)$ by how we defined generalized singletons
- $\Gamma \vdash \langle c_1, c_2 \rangle : S(c_1:k_1) \times [c_1/\alpha]k_2$
    by the non-dependent product rule.
- $\alpha$ is not free in $[c_1/\alpha]k_2$, so $\Gamma, \alpha:S(c_1:k_1) \vdash
    [c_1/\alpha]k_2 \le k_2$.
- So $\Gamma \vdash S(c_1:k_1) \times [c_1/\alpha]k_2 \le \Sigma(\alpha:k_1).k_2$.
- Then by subsumption, $\Gamma \vdash \langle c_1, c_2 \rangle : \Sigma(\alpha:k_1).
    k_2$.  It turns out that using the non-dependent product rule is ultimately much
simpler, so we will use it over the dependent version.

We complete rules 2.4 (for now) with singletons, arrows and $\forall$:

**Rules 2.4.2 (Kinding continued, still incomplete):**

$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1:k_1$}
\AxiomC{$\Gamma \vdash c_2:k_2$}
\BinaryInfC{$\Gamma \vdash \langle c_1,c_2 \rangle : k_1 \times k_2$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c \equiv c': \*$}
\UnaryInfC{$\Gamma \vdash c : S(c')$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash \tau_1:\*$}
\AxiomC{$\Gamma \vdash \tau_2:\*$}
\BinaryInfC{$\Gamma \vdash \tau_1 \rightarrow \tau_2:\*$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash k:\text{kind}$}
\AxiomC{$\Gamma, \alpha:k \vdash \tau:\*$}
\BinaryInfC{$\Gamma \vdash \forall(\alpha:k).\tau : \*$}
\end{prooftree}
$$

The rule for singletons should be unsurprising, and the rules for arrow and
$\forall$ types are unchanged from system $F_\omega$.

At last, then, we come to constructor equivalence. The general theme will be
to use dependent versions of the rules we had before.

**Rules 2.5 (Constructor equivalence):** $\Gamma \vdash c \equiv c'$

*Equivalence:*
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c:k$}
\UnaryInfC{$\Gamma \vdash c \equiv c:k$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c \equiv c' : k$}
\UnaryInfC{$\Gamma \vdash c' \equiv c : k$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1 \equiv c_2:k$}
\AxiomC{$\Gamma \vdash c_2 \equiv c_3:k$}
\BinaryInfC{$\Gamma \vdash c_1 \equiv c_3:k$}
\end{prooftree}
$$

*Compatibility:*
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash k_1 \equiv k_1' : \text{kind}$}
\AxiomC{$\Gamma, \alpha:k_1 \vdash c \equiv c':k_2$}
\BinaryInfC{$\Gamma \vdash \lambda(\alpha:k_1).c \equiv \lambda(\alpha:k_1').c':
  \Pi(\alpha:k_1).k_2$}
\end{prooftree} \quad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1 \equiv c_1' : \Pi(\alpha:k_1).k_2$}
\AxiomC{$\Gamma \vdash c_2 \equiv c_2' : k_2$}
\BinaryInfC{$\Gamma \vdash c_1\ c_2 \equiv c_1'\ c_2' : [c_2/\alpha]k_2$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1 \equiv c_1' : k_1$}
\AxiomC{$\Gamma \vdash c_2 \equiv c_2' : [c/\alpha]k_2$}
\BinaryInfC{$\Gamma \vdash \langle c_1, c_2 \rangle \equiv \langle c_1', c_2' \rangle
  : \Sigma(\alpha:k_1).k_2$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c \equiv c' : \Sigma(\alpha:k_1).k_2$}
\UnaryInfC{$\Gamma \vdash \pi_1c \equiv \pi_1c':k_1$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c \equiv c' : \Sigma(\alpha:k_1).k_2$}
\UnaryInfC{$\Gamma \vdash \pi_2c \equiv \pi_2c':[\pi_1c/\alpha]k_2$}
\end{prooftree}
$$

*Types constructors:*
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1 \equiv c_1' : \*$}
\AxiomC{$\Gamma \vdash c_2 \equiv c_2' : \*$}
\BinaryInfC{$\Gamma \vdash c_1\rightarrow c_2 \equiv c_1' \rightarrow c_2':\*$}
\end{prooftree}\qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash k \equiv k' : \text{kind}$}
\AxiomC{$\Gamma, \alpha:k \vdash c \equiv c' : \*$}
\BinaryInfC{$\Gamma \vdash \forall(\alpha:k).c\equiv\forall(\alpha:k').c':\*$}
\end{prooftree}
$$

*Beta-reduction:*
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1:k_1$}
\AxiomC{$\Gamma, \alpha:k_1 \vdash c_2:k_2$}
\BinaryInfC{$\Gamma \vdash (\lambda(\alpha:k_1).c_2)\ c_1
  \equiv [c_1/\alpha]c_2 : [c_1/\alpha]k_2$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1 : k_1$}
\AxiomC{$\Gamma \vdash c_2 : k_2$}
\BinaryInfC{$\Gamma \vdash \pi_1 \langle c_1, c_2 \rangle \equiv c_1$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1 : k_1$}
\AxiomC{$\Gamma \vdash c_2 : k_2$}
\BinaryInfC{$\Gamma \vdash \pi_2 \langle c_1, c_2 \rangle \equiv c_2$}
\end{prooftree}
$$

*Extensionality:*
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c:\Pi(\alpha:k_1).k_2'$}
\AxiomC{$\Gamma \vdash c':\Pi(\alpha:k_1).k_2''$}
\AxiomC{$\Gamma, \alpha:k_1 \vdash c\ \alpha \equiv c'\ \alpha : k_2$}
\TrinaryInfC{$\Gamma \vdash c \equiv c' : \Pi(\alpha:k_1).k_2$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash \pi_1c \equiv \pi_1c' : k_1$}
\AxiomC{$\Gamma \vdash \pi_2c \equiv \pi_2c' : [\pi_1c/\alpha]k_2$}
\AxiomC{$\Gamma, \alpha:k_1 \vdash k_2:\text{kind}$}
\TrinaryInfC{$\Gamma \vdash c \equiv c' : \Sigma(\alpha:k_2)$}
\end{prooftree}
$$

Finally, we may choose to include a singleton rule:

$$
\begin{prooftree}
\alwaysDashedLine
\AxiomC{$\Gamma \vdash c:S(c')$}
\UnaryInfC{$\Gamma \vdash c \equiv c':S(c')$}
\end{prooftree}
$$

but it's unnecessary, as it arises inversion of the singleton rule from 2.4.2.

It turns out, however, that our formulation of constructor kinding isn't quite
complete. Consider the following situation.

Recall that $S(c:\Pi(\alpha:k_1).k_2 = \Pi(\alpha:k_1).S(c\ \alpha : k_2)$.
Then consider the type constructor $\lambda(\alpha:\*).\texttt{int}$:

$$
\begin{aligned}
\lambda(\alpha:\*).\texttt{int} &: S(\lambda(\alpha:\*).\texttt{int}:\* \rightarrow \*)
  \\\\
&= \Pi(\alpha:\*).S((\lambda(\alpha:\*).\texttt{int})\ \alpha : \*) \\\\
&= \Pi(\alpha:\*).S((\lambda(\alpha:\*).\texttt{int})\ \alpha) \\\\
&= \Pi(\alpha:\*).S(\texttt{int})
\end{aligned}
$$

(where the $=$ above are kind equality)

By this, we should be able to derive $\lambda(\alpha:\*).\texttt{int}:
\Pi(\alpha:\*).S(\texttt{int})$. This can be done easily:

$$
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$\alpha:\* \vdash \texttt{int} : S(\texttt{int})$}
\UnaryInfC{$\cdot \vdash \lambda(\alpha:\texttt{int}).\texttt{int}
  : \Pi(\alpha:\*).S(\texttt{int})$}
\end{prooftree}
$$

which should follow from our existing rules.

However, this doesn't generalize. Namely, we should be able to show that, if
$\beta:S(\* \rightarrow \*)$, then $\beta:\Pi(\alpha:\*).S(\beta\ \alpha)$.
As our rules currently are, however, we can't do this -- our rules currently
only allow type lambdas and beta- or pi-redexes to have $\Pi$-types, and the
singular variable $\beta$ is neither. A similar issue arises with product kinds.
We can resolves this by giving up the
structural-only property of the constructor kinding rules and adding
extensionality there as well:

**Rules 2.4.3 (Kinding finalized)**

$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c:\Pi(\alpha:k_1).k_2'$}
\AxiomC{$\Gamma, \alpha:k_1 \vdash c\ \alpha:k_2$}
\BinaryInfC{$\Gamma \vdash c:\Pi(\alpha:k_1).k_2$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash \pi_1c:k_1$}
\AxiomC{$\Gamma \vdash \pi_2c:[\pi_1c/\alpha]k_2$}
\AxiomC{$\Gamma, \alpha:k_1 \vdash k_2:\text{kind}$}
\TrinaryInfC{$\Gamma \vdash c:\Sigma(\alpha:k_1).k_2$}
\end{prooftree}
$$

## Remarks

- I'm a bit sketched on how the proof of non-dependent products implying dependent
    products works. The moral reason is that the dependent argument must have a
    fully instantiated kind, so it doesn't matter whether the actual sum kind
    is dependent, but the subtyping via the generalized singleton doesn't quite
    make sense to me. Maybe I'll do the full proof out later.

