# Typechecking $F_\omega^{++}$

Algorithmically typechecking $F_\omega$ is more complex. The existence of the
reflexive, symmetric and transitive equivalence rules may make proof search more
difficult. For example, if the current proof obligations are to show that
$c_1 \equiv c_3 : k$, to use the transitivity rule we would need to guess a
$c_2$ to pass through.

The type system of $F_\omega$ is equivalent to the simply-typed lambda calculus,
so one approach for checking whether two constructors are equivalent is to
beta-normalize them, then compare them structurally. This would work, but does
not generalize well to later systems.

The immediately relevant judgments are:

| Judgment | Meaning |
|---|---|
| $\overset{+}{\Gamma} \vdash \overset{+}{c} \Rightarrow \overset{-}{k}$ | kind synthesis |
| $\overset{+}{\Gamma} \vdash \overset{+}{c} \Leftarrow \overset{+}{k}$ | kind checking |
| $\overset{+}{\Gamma} \vdash \overset{+}{e} \Rightarrow \overset{-}{\tau}$ | type sythesis |
| $\overset{+}{\Gamma} \vdash \overset{+}{e} \Leftarrow \overset{+}{\tau}$ | type checking |

The $+$ and $-$ symbols denote modality ($+$ is input and $-$ is output), but
are not otherwise necessary. These
judgments form a standard bidirectional typechecking (and kind-checking) algorithm.

In the process, we will also need four more judgments:

| Judgment | Meaning |
|---|---|
| $\overset{+}{\Gamma} \vdash \overset{+}{c} \Leftrightarrow \overset{+}{c'} : \overset{+}{k}$ | algorithmic equivalence |
| $\overset{+}{\Gamma} \vdash \overset{+}{c} \leftrightarrow \overset{+}{c'} : \overset{-}{k}$ | structural equivalence |
| $\overset{+}{\Gamma} \vdash \overset{+}{c} \Downarrow \overset{-}{c'}$ | weak-head normalization |
| $\overset{+}{\Gamma} \vdash \overset{+}{c} \rightsquigarrow \overset{-}{c'}$ | weak-head reduction |

## Inference Rules

**Rules 1.5 (Type synthesis):** $\Gamma \vdash e \Rightarrow \tau$

$$
\begin{prooftree}
\AxiomC{$\Gamma(x) = \tau$}
\UnaryInfC{$\Gamma \vdash x \Rightarrow \tau$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash \tau \Leftarrow \*$}
\AxiomC{$\Gamma, x:\tau \vdash e \Rightarrow \tau'$}
\BinaryInfC{$\Gamma \vdash \lambda(x:\tau).e \Rightarrow \tau \rightarrow \tau'$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash e_1 \Rightarrow \tau$}
\AxiomC{$\Gamma \vdash \tau \Downarrow \tau_1 \rightarrow \tau_2$}
\AxiomC{$\Gamma \vdash e_1 \Leftarrow \tau_1$}
\TrinaryInfC{$\Gamma \vdash e_1\ e_2 \Rightarrow \tau_2$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma, \alpha:k \vdash e \Rightarrow \tau$}
\UnaryInfC{$\Gamma \vdash \Lambda(\alpha:k).e \Rightarrow \forall(\alpha:k).\tau$}
\end{prooftree}\qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash e \Rightarrow \tau$}
\AxiomC{$\Gamma \vdash \tau \Downarrow \forall(\alpha:k).\tau'$}
\AxiomC{$\Gamma \vdash c \Leftarrow k$}
\TrinaryInfC{$\Gamma \vdash e[c] \Rightarrow [c/\alpha]\tau'$}
\end{prooftree}
$$

Unlike in 15-317, we mandate the type annotation on the parameter of a lambda,
so we can synthesize its type. In the last two rules, we cannot "pattern match"
on the synthesized type of the candidate function, because it could have beta
redexes. Instead, we normalize it.

**Rules 1.6 (Type checking):** $\Gamma \vdash e \Leftarrow \tau$

$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash e \Rightarrow \tau'$}
\AxiomC{$\Gamma \vdash \tau \Leftrightarrow \tau' : \*$}
\BinaryInfC{$\Gamma \vdash e \Leftarrow \tau$}
\end{prooftree}
$$

We don't yet have a way to construct an invalid kind, so we don't need to
ensure that kinds are well-formed (*yet*).

**Rules 1.7 (Kind synthesis):** $\Gamma \vdash c \Rightarrow k$

$$
\begin{prooftree}
\AxiomC{$\Gamma(\alpha) = k$}
\UnaryInfC{$\Gamma \vdash \alpha \Rightarrow k$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash \tau_1 \Leftarrow \*$}
\AxiomC{$\Gamma \vdash \tau_2 \Leftarrow \*$}
\BinaryInfC{$\Gamma \vdash \tau_1 \rightarrow \tau_2 \Rightarrow \*$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma, \alpha:k \vdash \tau \Leftarrow \*$}
\UnaryInfC{$\Gamma \vdash \forall(\alpha:k).\tau \Rightarrow \*$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma, \alpha:k \vdash c \Rightarrow k'$}
\UnaryInfC{$\Gamma \vdash \lambda(\alpha:k).c \Rightarrow k \rightarrow k'$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1 \Rightarrow k_1 \rightarrow k_2$}
\AxiomC{$\Gamma \vdash c_2 \Rightarrow k_1$}
\BinaryInfC{$\Gamma \vdash c_1\ c_2 \Rightarrow k_2$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1 \Rightarrow k_1$}
\AxiomC{$\Gamma \vdash c_2 \Rightarrow k_2$}
\BinaryInfC{$\Gamma \vdash \langle c_1, c_2 \rangle \Rightarrow k_1 \times k_2$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c \Rightarrow k_1 \times k_2$}
\UnaryInfC{$\Gamma \vdash \pi_1c \Rightarrow k_1$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c \Rightarrow k_1 \times k_2$}
\UnaryInfC{$\Gamma \vdash \pi_2c \Rightarrow k_2$}
\end{prooftree}
$$

**Rules 1.8 (Kind checking):** $\Gamma \vdash c \Leftarrow k$

$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c \Rightarrow k'$}
\AxiomC{$k = k'$}
\BinaryInfC{$\Gamma \vdash c \Leftarrow k$}
\end{prooftree}
$$

The rule for kind checking could be written more compactly to use the same
variable $k$ in both premise and conclusion (thus dropping the $k = k'$ premise),
but we write it this way so it can generalize to later calculi (particularly
the notion of equality).

When writing the equivalence rules, we will use extensionality to recurse on
the *kind* via the appropriate projections or function application. What we
*don't* do is normalize both types and check equivalence, because this doesn't
generalize to the calculus of singleton kinds.

**Rules 1.9 (Algorithmic Equivalence)**: $\Gamma \vdash c \Leftrightarrow c' : k$

$$
\begin{prooftree}
\AxiomC{$\Gamma, \alpha:k \vdash c\ \alpha \Leftrightarrow c'\ \alpha:k_2$}
\UnaryInfC{$\Gamma \vdash c \Leftrightarrow c' : k_1 \rightarrow k_2$}
\end{prooftree}\qquad
\begin{prooftree}
\AxiomC{$\Gamma\vdash \pi_1c \Leftrightarrow \pi_1c' : k_1$}
\AxiomC{$\Gamma\vdash \pi_2c \Leftrightarrow \pi_2c' : k_2$}
\BinaryInfC{$\Gamma \vdash c \Leftrightarrow c':k_1 \times k_2$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1 \Downarrow c_1'$}
\AxiomC{$\Gamma \vdash c_2 \Downarrow c_2'$}
\AxiomC{$\Gamma \vdash c_1' \leftrightarrow c_2':\*$}
\TrinaryInfC{$\Gamma \vdash c_1 \Leftrightarrow c_2:\*$}
\end{prooftree}
$$

Normalization only happens once we reach the kind $\*$.

A normal form is one that has contracted all $\beta$-redices. We will instead
use *weak-head* normal form, in which an arrow constructor or a universal
constructor is at the outermost level (we don't recursively normalize).

**Rules 1.10 (Weak-head normalization):** $\Gamma \vdash c \Downarrow c'$

$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c \rightsquigarrow c'$}
\AxiomC{$\Gamma \vdash c' \Downarrow c''$}
\BinaryInfC{$\Gamma \vdash c \Downarrow c''$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c \not\rightsquigarrow$}
\UnaryInfC{$\Gamma \vdash c \Downarrow c$}
\end{prooftree}
$$

Although we could formally defined the judgment $\Gamma \vdash c
\not\rightsquigarrow$, we will choose not to for brevity. This could be
implemented in ML by raising an exception or returning a `NONE` option if none
of the stepping rules apply.

**Rules 1.11 (Weak-head reduction):** $\Gamma \vdash c \rightsquigarrow c'$

$$
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$\Gamma \vdash
  (\lambda (\alpha:k).c)\ c' \rightsquigarrow [c'/\alpha]c$}
\end{prooftree}\qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1 \rightsquigarrow c_1'$}
\UnaryInfC{$\Gamma \vdash c_1\ c_2 \rightsquigarrow c_1'\ c_2$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$\Gamma \vdash \pi_1 \langle c_1, c_2 \rangle \rightsquigarrow c_1$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$\Gamma \vdash \pi_2 \langle c_1, c_2 \rangle \rightsquigarrow c_2$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1 \rightsquigarrow c_1'$}
\UnaryInfC{$\Gamma \vdash \langle c_1, c_2 \rangle \rightsquigarrow
  \langle c_1', c_2 \rangle$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_2 \rightsquigarrow c_2'$}
\UnaryInfC{$\Gamma \vdash \langle c_1, c_2 \rangle \rightsquigarrow
  \langle c_1, c_2' \rangle$}
\end{prooftree}
$$

When weak-head normalizing, we only reduce under application and projection.
This way, when we encounter types such as $((\lambda \alpha.\alpha)
\ (\lambda \alpha.\alpha)) c$, we can reduce them.

A weak-head normalized constructor can only take certain forms. Those which
could be normalized further but are not we'll call "paths".

$$
\begin{aligned}
\text{whnf}\ \hat{c} &:= c \rightarrow c \mid \forall(\alpha:k).c \mid p \\\\
\text{path}\ p &:= \alpha \mid p\ c \mid \pi_1p \mid \pi_2p
\end{aligned}
$$

By the extensionality rules, we ensure that we reach kind $\*$, so this grammar
is exhaustive.
Paths are obviously
neutral, and whnf terms are almost neutral, except that the subterms (bodies
of universal type and arrow) may contain redices.

**Rules 1.12 (Structural Equivalence):** $\Gamma \vdash \hat{c_1}
  \rightarrow \hat{c_2}: k$

$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1 \Leftrightarrow c_1': \*$}
\AxiomC{$\Gamma \vdash c_2 \Leftrightarrow c_2': \*$}
\BinaryInfC{$\Gamma \vdash c_1 \rightarrow c_2 \leftrightarrow
  c_1' \rightarrow c_2'$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma, \alpha:k \vdash \tau \Leftrightarrow \tau': \*$}
\UnaryInfC{$\Gamma \vdash \forall(\alpha:k).\tau \leftrightarrow
  \forall(\alpha:k).\tau':\*$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma(\alpha) = k$}
\UnaryInfC{$\Gamma \vdash \alpha \leftrightarrow \alpha : k$}
\end{prooftree}\qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1 \leftrightarrow c_1' : k_1 \rightarrow k_2$}
\AxiomC{$\Gamma \vdash c_2 \Leftrightarrow c_2' : k_1$}
\BinaryInfC{$\Gamma \vdash c_1\ c_2 \leftrightarrow c_1'\ c_2' : k_2$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c \leftrightarrow c' : k_1 \times k_2$}
\UnaryInfC{$\Gamma \vdash \pi_1c \leftrightarrow \pi_1c':k_1$}
\end{prooftree}\qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c \leftrightarrow c' : k_1 \times k_2$}
\UnaryInfC{$\Gamma \vdash \pi_2c \leftrightarrow \pi_2c':k_2$}
\end{prooftree}
$$

Algorithmic structural equivalence is not too surprising. The kind is
synthesized as an output, which allows it to be put back in as an input to the
algorithmic equivalence judgment.

