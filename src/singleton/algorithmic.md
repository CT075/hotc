# Typechecking the SKC

Typechecking will act similarly to what we've done before; many of these
judgements should look familiar (for ease of typesetting I'm choosing to use
superscripts for modes instead of writing it on top of the character from here
onwards).

| Judgment | Meaning |
|---|---|
| $\Gamma^+ \vdash k^+ \Leftarrow \text{kind}$ | Kind validity |
| $\Gamma^+ \vdash k^+ \Leftrightarrow k'^+ : \text{kind}$ | Kind equivalence |
| $\Gamma^+ \vdash k^+ \unlhd k'^+$ | Subkinding |
| $\Gamma^+ \vdash c^+ \Rightarrow k^-$ | Kind synthesis |
| $\Gamma^+ \vdash c^+ \Leftarrow k^+$ | Kind checking |
| $\Gamma^+ \vdash c^+ \uparrow k^- $ | Natural kind |
| $\Gamma^+ \vdash c^+ \Leftrightarrow c'^+ : k^+$ | Algorithmic equivalence |
| $\Gamma^+ \vdash c^+ \leftrightarrow c'^+ : k^-$ | Structural path equivalence |
| $\Gamma^+ \vdash c^+ \rightsquigarrow c'^-$ | Weak-head reduction |
| $\Gamma^+ \vdash c^+ \Downarrow c'^-$ | Weak-head normalization |
| $\Gamma^+ \vdash e^+ \Rightarrow \tau^-$ | Type synthesis |
| $\Gamma^+ \vdash e^+ \Leftarrow \tau^+$ | Type checking |

As our term and constructor language is entirely unchanged from $F_\omega$, we
can import the type checking/synthesis rules nearly wholesale. The only change
is that we now need to check that the kind introduced by a $\forall$ introduction
is well-formed, via adding a kind validity premise:

$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash k \Leftarrow \text{kind}$}
\AxiomC{$\Gamma, \alpha:k \vdash e \Rightarrow \tau$}
\BinaryInfC{$\Gamma \vdash \Lambda(\alpha:k).e \Rightarrow \forall(\alpha:k).\tau$}
\end{prooftree}
$$

## Kinds

Next, we introduce the idea of a *principal kind*. In the presence of subkinding,
it may be possible infer many non-equivalent kinds for a given constructor, so we
want to produce the one that is "most specific". A kind $k$ is principal for a
type constructor $c$ in context $\Gamma$ if:

- $\Gamma \vdash c:k$
- For all kinds $k'$, if $\Gamma \vdash c:k'$, then $\Gamma \vdash k \le k'$.

For example, if $\alpha$ has kind $\*$, then its principal kind is $S(\alpha)$.
This is where higher order singletons become see their main use -- if $c:k$,
then the principal kind of $c$ is $S(c:k)$.

**Rules 2.6 (Kind validity):** $\Gamma \vdash k \Leftarrow \text{kind}$

$$
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$\Gamma \vdash \* \Leftarrow \text{kind}$}
\end{prooftree}\qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c \Leftarrow \*$}
\UnaryInfC{$\Gamma \vdash S(c) \Leftarrow \text{kind}$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash k_1 \Leftarrow \text{kind}$}
\AxiomC{$\Gamma, \alpha:k_1 \vdash k_2 \Leftarrow \text{kind}$}
\BinaryInfC{$\Gamma \vdash \Sigma(\alpha:k_1).k_1 \Leftarrow \text{kind}$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash k_1 \Leftarrow \text{kind}$}
\AxiomC{$\Gamma, \alpha:k_1 \vdash k_2 \Leftarrow \text{kind}$}
\BinaryInfC{$\Gamma \vdash \Pi(\alpha:k_1).k_1 \Leftarrow \text{kind}$}
\end{prooftree}
$$

Should be largely unsurprising.

**Rules 2.7 (Kind synthesis):** $\Gamma \vdash c \Rightarrow k$

$$
\begin{prooftree}
\AxiomC{$\Gamma(\alpha) = k$}
\UnaryInfC{$\Gamma \vdash \alpha \Rightarrow S(\alpha:k)$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash \tau_1 \Leftarrow \*$}
\AxiomC{$\Gamma \vdash \tau_2 \Leftarrow \*$}
\BinaryInfC{$\Gamma \vdash \tau_1 \rightarrow \tau_2 \Rightarrow
  S(\tau_1 \rightarrow \tau_2)$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash k \Leftarrow \text{kind}$}
\AxiomC{$\Gamma, \alpha:k \vdash \tau \Leftarrow \*$}
\BinaryInfC{$\Gamma \vdash \forall(\alpha:k).\tau \Rightarrow S(\forall(\alpha:k).\tau)$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash k \Leftarrow \text{kind}$}
\AxiomC{$\Gamma, \alpha:k\vdash c \Rightarrow k'$}
\BinaryInfC{$\Gamma \vdash \lambda(\alpha:k).c \Rightarrow \Pi(\alpha:k).k'$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1 \Rightarrow k_1$}
\AxiomC{$\Gamma \vdash c_2 \Rightarrow k_2$}
\BinaryInfC{$\Gamma \vdash \langle c_1,c_2 \rangle \Rightarrow k_1 \times k_2$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c \Rightarrow \Sigma(\alpha:k_1).k_2$}
\UnaryInfC{$\Gamma \vdash \pi_1c \Rightarrow k_1$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c \Rightarrow \Sigma(\alpha:k_1).k_2$}
\UnaryInfC{$\Gamma \vdash \pi_2c \Rightarrow [\pi_1c/\alpha]k_1$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1 \Rightarrow \Pi(\alpha:k).k'$}
\AxiomC{$\Gamma \vdash c_2 \Leftarrow k$}
\BinaryInfC{$\Gamma \vdash c_1\ c_2: [c_2/\alpha]k$}
\end{prooftree}
$$

Recall that the formation rules for dependent and non-dependent tuples are actually
equivalent, so we take the simpler one.

Kind checking only has one rule, which details subsumption.

**Rules 2.8 (Kind checking):** $\Gamma \vdash c \Leftarrow k$

$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c \Rightarrow k'$}
\AxiomC{$\Gamma \vdash k' \unlhd k$}
\BinaryInfC{$\Gamma \vdash c \Leftarrow k$}
\end{prooftree}
$$

**Rules 2.9 (Subkinding):** $\Gamma \vdash k \unlhd k'$

$$
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$\Gamma \vdash \* \unlhd \*$}
\end{prooftree}\qquad
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$\Gamma \vdash S(c) \unlhd \*$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c \Leftrightarrow c' :\*$}
\UnaryInfC{$\Gamma \vdash S(c) \unlhd S(c')$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash k_1' \unlhd k_1$}
\AxiomC{$\Gamma \alpha:k_1' \vdash k_2' \unlhd k_2$}
\BinaryInfC{$\Gamma \vdash \Pi(\alpha:k_1).k_2 \unlhd \Pi(\alpha:k_1').k_2'$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash k_1 \unlhd k_1'$}
\AxiomC{$\Gamma, \alpha:k_1 \vdash k_2 \unlhd k_2'$}
\BinaryInfC{$\Gamma \vdash \Sigma(\alpha:k_1).k_2 \unlhd \Sigma(\alpha:k_1').k_2'$}
\end{prooftree}
$$

Once again, in the rules for $\Pi$- and $\Sigma$-kinds, the kind of the type
variable is set to be that of the superkind, as it will be valid in both
of the dependent kinds.

**Rules 2.10 (Algorithmic equivalence):** $\Gamma \vdash c \Leftrightarrow c':k$

$$
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$\Gamma \vdash c \Leftrightarrow c' : S(c'')$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1 \Downarrow c_1'$}
\AxiomC{$\Gamma \vdash c_2 \Downarrow c_2'$}
\AxiomC{$\Gamma \vdash c_1' \leftrightarrow c_2' : k$}
\TrinaryInfC{$\Gamma \vdash c_1 \Leftrightarrow c_2 : \*$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma, \alpha:k_1 \vdash c\ \alpha \Leftrightarrow c'\ \alpha:k_2$}
\UnaryInfC{$\Gamma \vdash c \Leftrightarrow c' : \Pi(\alpha:k_1).k_2$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash \pi_1c \Leftrightarrow \pi_1c' : k_1$}
\AxiomC{$\Gamma \vdash \pi_2c \Leftrightarrow \pi_2c' : [\pi_1c/\alpha]k_2$}
\BinaryInfC{$\Gamma \vdash c \Leftrightarrow c' : \Sigma(\alpha:k_1).k_2$}
\end{prooftree}
$$

The singleton rule follows via regularity (soundness). In the rule at kind
$\*$, we can ignore the kinds returned from $\leftrightarrow$ for the same
reason -- if, in the resultant code, we ever query $\Gamma \vdash c_1 \equiv
c_2 : k$, we'd better have that $\Gamma \vdash c_1:k$ and $\Gamma \vdash c_2:k$.

## Natural Kinds

Structural equality is about the same as $F_\omega$, with one major caveat.
Consider the following:

$$\beta:\*, \alpha:S(\beta) \vdash \alpha \Leftrightarrow \beta : \*$$

This should certainly be derivable by the definition of the singleton kinds.
However, we need some extra machinery to be able to express this -- $\alpha$
is *certainly* not structurally equal to $\beta$, as they are different
free variables. We will define
the "natural kind" of a constructor to be the "obvious" result, without trying
to be clever or more specific. But first, weak head reduction:

**Rules 2.11 (Weak head reduction and normalization)**

$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1 \rightsquigarrow c_2$}
\AxiomC{$\Gamma \vdash c_2 \Downarrow c_3$}
\BinaryInfC{$\Gamma \vdash c_1 \Downarrow c_3$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c \not\rightsquigarrow$}
\UnaryInfC{$\Gamma \vdash c \Downarrow c$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash p \uparrow S(c)$}
\UnaryInfC{$\Gamma \vdash p \rightsquigarrow c$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1 \rightsquigarrow c_1'$}
\UnaryInfC{$\Gamma \vdash c_1\ c_2 \rightsquigarrow c_1'\ c_2$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c \rightsquigarrow c'$}
\UnaryInfC{$\Gamma \vdash \pi_1c \rightsquigarrow \pi_1c'$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c \rightsquigarrow c'$}
\UnaryInfC{$\Gamma \vdash \pi_2c \rightsquigarrow \pi_2c'$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$\Gamma \vdash (\lambda(\alpha:k).c_1)\ c_2 \rightsquigarrow
  [c_2/\alpha]c_1$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$\Gamma \vdash \pi_1 \langle c_1, c_2 \rangle \rightsquigarrow c_1$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$\Gamma \vdash \pi_2 \langle c_1, c_2 \rangle \rightsquigarrow c_2$}
\end{prooftree}
$$

As before, we will restrict structural equality and natural kinding to only
apply to those tycons that are weak head normalized. Recall that such constructors
are either lambdas, $\forall$-types, or paths. We don't want to natural kind
lambdas or $\forall$, since they will give us $\*$, which isn't what we're
looking for with these rules. As such, we have used $p$ to represent path
constructors.

**Rules 2.12 (Natural Kind):** $\Gamma \vdash p \uparrow k$

$$
\begin{prooftree}
\AxiomC{$\Gamma(\alpha) = k$}
\UnaryInfC{$\Gamma \vdash \alpha \uparrow k$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash p \uparrow \Pi(\alpha:k_1).k_2$}
\UnaryInfC{$\Gamma \vdash p\ c \uparrow [c/\alpha]k_2$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash p \uparrow \Sigma(\alpha:k_1).k_2$}
\UnaryInfC{$\Gamma \vdash \pi_1p \uparrow k_1$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash p \uparrow \Sigma(\alpha:k_1).k_2$}
\UnaryInfC{$\Gamma \vdash \pi_2p \uparrow [\pi_1p/\alpha]k_2$}
\end{prooftree}
$$

Note that we don't bother looking up a natural kind for $c_1\ c_2$, because it
will never be a singleton, so why bother?

Now, we can derive the earlier example. Letting $\Gamma = \beta:\*, \alpha:
S(\beta)$, we have

$$
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$\Gamma(\alpha) = S(\beta)$}
\UnaryInfC{$\Gamma \vdash \alpha \uparrow S(\beta)$}
\UnaryInfC{$\Gamma \vdash \alpha \rightsquigarrow \beta$}
\AxiomC{}
\UnaryInfC{$\Gamma \vdash \beta \not\rightsquigarrow$}
\BinaryInfC{$\Gamma \vdash \alpha \Downarrow \beta$}
\AxiomC{}
\UnaryInfC{$\Gamma \vdash \beta \not\rightsquigarrow$}
\UnaryInfC{$\Gamma \vdash \beta \Downarrow \beta$}
\AxiomC{}
\UnaryInfC{$\Gamma(\beta) = \*$}
\UnaryInfC{$\Gamma \vdash \beta \leftrightarrow \beta:\*$}
\TrinaryInfC{$\Gamma \vdash \alpha \Leftrightarrow \beta : \*$}
\end{prooftree}
$$

## Structural Equivalence, at last

For completeness, the structural equality rules, which are largely unchanged
from $F_\omega$:

**Rules 2.13 (Structural equality):** $\Gamma \vdash p \leftrightarrow p'$

$$
\begin{prooftree}
\AxiomC{$\Gamma(\alpha) = k$}
\UnaryInfC{$\Gamma \vdash \alpha \leftrightarrow \alpha : k$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash \tau_1 \Leftrightarrow \tau_1':\*$}
\AxiomC{$\Gamma \vdash \tau_2 \Leftrightarrow \tau_2':\*$}
\BinaryInfC{$\Gamma \vdash \tau_1 \rightarrow \tau_2 \leftrightarrow
  \tau_1' \rightarrow \tau_2' : \*$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash k \Leftrightarrow k' : \text{kind}$}
\AxiomC{$\Gamma, \alpha:k \vdash c \Leftrightarrow c' : \*$}
\BinaryInfC{$\Gamma \vdash \forall(\alpha:k).c \leftrightarrow
  \forall(\alpha:k').c'$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash p \leftrightarrow p' : \Sigma(\alpha:k_1).k_2$}
\UnaryInfC{$\Gamma \vdash \pi_1p \leftrightarrow \pi_1p'$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash p \leftrightarrow p' : \Sigma(\alpha:k_1).k_2$}
\UnaryInfC{$\Gamma \vdash \pi_2p \leftrightarrow \pi_2p'$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash p_1 \leftrightarrow p_2:\Pi(\alpha:k_1).k_2$}
\AxiomC{$\Gamma \vdash c_1 \Leftrightarrow c_2:k_1$}
\BinaryInfC{$\Gamma \vdash p_1\ c_1 \leftrightarrow p_1\ c_2:[c_1/\alpha]k_2$}
\end{prooftree}
$$

## Remarks

- Professor Crary glossed over or entirely skipped some of the rules mentioned
    here, particularly kind equivalence (which made the homework extra fun...).
    I have included those rules from
    Nick Roberts' notes for the sake of completeness.

