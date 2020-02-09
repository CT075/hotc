# System F$_\omega^{++}$

$F_\omega$ is the calculus of higher-kinded type constructors, combining two
axes of the lambda cube (polymorphism and type operators).

The syntax of $F_\omega$ is an extension of $F$. First, we need to
adjust our syntax to use type constructors (or just "constructors") instead of
just types. By convention, we will use $\tau$ to denote a nullary constructor,
a constructor kinded at $\*$ (see below).

$$
c, \tau := \alpha \mid c \rightarrow c \mid \forall (\alpha : k).c
  \mid \lambda (\alpha : k) .c \mid c\ c
$$

where $\alpha$ is a type variable used in quantification and type abstraction.

Next, we will add $k$, to denote kinds:

$$
k := \* \mid k \rightarrow k
$$

We also need terms to inhabit those types:

$$
e := x \mid \lambda (x:\tau).e \mid \Lambda(\alpha:k).e \mid e[\tau]
$$

Our context, $\Gamma$, may contain judgments about types and terms.

$$
\Gamma := e \mid \Gamma, x:\tau \mid \Gamma : \alpha:k
$$

You may also see the kinding judgment written as $\alpha :: k$.

Finally, as noted earlier, we will need to extend $F_\omega$ with primitive
product kinds to handle ML modules (hence the ++ in $F_\omega^{++}$):

$$
\begin{aligned}
k &:= \dots \mid k \times k \\\\
c &:= \dots \mid \langle c, c \rangle \mid \pi_1 c \mid \pi_2 c
\end{aligned}
$$

This language is defined statically as follows:

**Rules 1.1 (Kinding)**: $\Gamma \vdash c:k$

$$
\begin{prooftree}
\AxiomC{$\Gamma(\alpha) = k$}
\UnaryInfC{$\Gamma \vdash \alpha : k$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1:\*$}
\AxiomC{$\Gamma \vdash c_2:\*$}
\BinaryInfC{$\Gamma \vdash c_1 \rightarrow c_2 : \*$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma, \alpha:k \vdash c:\*$}
\UnaryInfC{$\Gamma \vdash \forall(\alpha:k).c:\*$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1:k \rightarrow k'$}
\AxiomC{$\Gamma \vdash c_2:k$}
\BinaryInfC{$\Gamma \vdash c_1\ c_2 : k'$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma, \alpha:k \vdash c:k'$}
\UnaryInfC{$\Gamma \vdash \lambda (\alpha:k).c : k \rightarrow k'$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1:k_1$}
\AxiomC{$\Gamma \vdash c_2:k_2$}
\BinaryInfC{$\Gamma \vdash \langle c_1, c_2 \rangle : k_1 \times k_2$}
\end{prooftree}\qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c:k_1 \times k_2$}
\UnaryInfC{$\Gamma \vdash \pi_1 c : k_1$}
\end{prooftree}\qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c:k_1 \times k_2$}
\UnaryInfC{$\Gamma \vdash \pi_2 c : k_2$}
\end{prooftree}
$$

**Rules 1.2 (Typing)**: $\Gamma \vdash e:\tau$

$$
\begin{prooftree}
\AxiomC{$\Gamma(x) = \tau$}
\UnaryInfC{$\Gamma \vdash x:\tau$}
\end{prooftree}\qquad
\begin{prooftree}
\AxiomC{$\Gamma, x:\tau \vdash e:\tau'$}
\AxiomC{$\Gamma \vdash \tau:\*$}
\BinaryInfC{$\Gamma \vdash \lambda(x:\tau).e : \tau \rightarrow \tau'$}
\end{prooftree}\qquad
\begin{prooftree}
\AxiomC{$\Gamma, \vdash e_1:\tau \rightarrow \tau'$}
\AxiomC{$\Gamma \vdash e_2:\tau$}
\BinaryInfC{$\Gamma \vdash e_1\ e_2 : \tau'$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma, \alpha:k \vdash e:\tau$}
\UnaryInfC{$\Gamma \vdash \Lambda(\alpha:k).e : \forall(\alpha:k).\tau$}
\end{prooftree}\qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash e:\forall(\alpha:k).\tau'$}
\AxiomC{$\Gamma \vdash \tau:k$}
\BinaryInfC{$\Gamma \vdash e[\tau] : [\tau/\alpha]\tau'$}
\end{prooftree}
$$

Note that these rules aren't sufficient -- If we have $f : \forall(\beta:\*
\rightarrow \*). \beta\ \texttt{int} \rightarrow \texttt{unit}$, we'd want to
have $f[\lambda(\alpha:\*).\alpha]\ 12 : \texttt{unit}$. However, by the above
rules, we type $f[\lambda(\alpha:\*):\alpha]$ at $((\lambda \alpha.\alpha)
\ \texttt{int}) \rightarrow \texttt{unit}$, not $\texttt{int} \rightarrow
\texttt{unit}$.

To remedy this, we need some way to express that $(\lambda \alpha.\alpha)
\ \texttt{int}$ is equivalent to $\texttt{int}$, which we will accomplish by
defining a new judgment $\Gamma \vdash c \equiv c' : k$, then adding to rules
1.2 the equivalence rule

$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash e:\tau$}
\AxiomC{$\Gamma \vdash \tau \equiv \tau':\*$}
\BinaryInfC{$\Gamma \vdash e:\tau'$}
\end{prooftree}
$$

**Rules 1.3 (Constructor Equivalence):** $\Gamma \vdash c \equiv c':k$

*Equivalence*
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c:k$}
\UnaryInfC{$\Gamma \vdash c \equiv c:k$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c \equiv c':k$}
\UnaryInfC{$\Gamma \vdash c' \equiv c:k$} \qquad
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1 \equiv c_2:k$}
\AxiomC{$\Gamma \vdash c_2 \equiv c_3:k$}
\BinaryInfC{$\Gamma \vdash c_1 \equiv c_3:k$}
\end{prooftree}
$$

*Compatibility*
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash \tau_1 \equiv \tau_1' : \*$}
\AxiomC{$\Gamma \vdash \tau_2 \equiv \tau_2' : \*$}
\BinaryInfC{$\Gamma \vdash \tau_1 \rightarrow \tau_2 \equiv
  \tau_1' \rightarrow \tau_2' : \*$}
\end{prooftree}\qquad
\begin{prooftree}
\AxiomC{$\Gamma, \alpha:k \vdash \tau \equiv \tau' : \*$}
\UnaryInfC{$\Gamma \vdash \forall(\alpha:k).\tau \equiv \forall(\alpha:k).\tau':\*$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma, \alpha:k \vdash c \equiv c':k'$}
\UnaryInfC{$\Gamma \vdash \lambda(\alpha:k).c \equiv \lambda(\alpha:k).c':
  k \rightarrow k'$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma, \alpha:k \vdash c_1 \equiv c_1':k \rightarrow k'$}
\AxiomC{$\Gamma \vdash c_2 \equiv c_2':k$}
\BinaryInfC{$\Gamma \vdash c_1\ c_2 \equiv c_1'\ c_2':k'$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1 \equiv c_1':k_1$}
\AxiomC{$\Gamma \vdash c_2 \equiv c_2':k_2$}
\BinaryInfC{$\Gamma \vdash \langle c_1, c_2 \rangle \equiv
  \langle c_1', c_2' \rangle : k_1 \times k_2$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c \equiv c' : k_1 \times k_2$}
\UnaryInfC{$\Gamma \vdash \pi_1c \equiv \pi_1c' : k_1$}
\end{prooftree}\qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c \equiv c' : k_1 \times k_2$}
\UnaryInfC{$\Gamma \vdash \pi_2c \equiv \pi_2c' : k_2$}
\end{prooftree}
$$

*Reduction/beta*
$$
\begin{prooftree}
\AxiomC{$\Gamma, \alpha:k \vdash c:k'$}
\AxiomC{$\Gamma \vdash c':k$}
\BinaryInfC{$\Gamma \vdash (\lambda (\alpha:k).c)\ c' \equiv [c'/\alpha]c:k'$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_1:k_1$}
\UnaryInfC{$\Gamma \vdash \pi_1\langle c_1, c_2\rangle \equiv c_1:k_1$}
\end{prooftree}\qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash c_2:k_2$}
\UnaryInfC{$\Gamma \vdash \pi_2\langle c_1, c_2\rangle \equiv c_2:k_2$}
\end{prooftree}
$$

*Extensionality/eta*
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c:k_1 \rightarrow k_2$}
\AxiomC{$\Gamma \vdash c':k_1 \rightarrow k_2$}
\AxiomC{$\Gamma, \alpha:k_1 \vdash c\ \alpha \equiv c'\ \alpha:k_2$}
\TrinaryInfC{$\Gamma \vdash c \equiv c' : k_1 \rightarrow k_2$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash \pi_1 c \equiv \pi_1 c':k_1$}
\AxiomC{$\Gamma \vdash \pi_2 c \equiv \pi_2 c':k_2$}
\BinaryInfC{$\Gamma \vdash c \equiv c':k_1 \times k_2$}
\end{prooftree}
$$

Note that in many cases, we enforce that some
constructors are types (kind $\*$) -- we certainly can't have tuples or lambda
abstractions underlying a $\forall$ type, for example.

The first set of rules, labeled "equivalence", ensure that this is indeed an
equivalence/congruence relation.

The beta rules are the interesting ones. With them, we can prove (assuming
we've defined the relevant primitive types):

$$
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$\vdash \texttt{int}:\*$}
\AxiomC{}
\UnaryInfC{$\beta:\* \vdash \beta:\*$}
\BinaryInfC{$\vdash (\lambda \beta.\beta)\ \texttt{int} \equiv\texttt{int}:\*$}
\UnaryInfC{$\vdash (\lambda \beta.\beta)\ \texttt{int} \rightarrow
  \texttt{unit} \equiv \texttt{int} \rightarrow \texttt{unit}:\*$}
\end{prooftree}
$$

Finally, the extensionality rules allow us to evaluate "underneath" tuples and
lambda abstractions. You might think of these as conducting an "experiment" to
see whether the relevant constructors behave equivalently.

## Remarks

- As it turns out, in this system, the $:k$ annotation on equivalence is
  unnecessary, as they are uniquely determined by the kinding rules.

  **Theorem (Regularity)**.
  1. If $\vdash \Gamma\ ok$ and $\Gamma \vdash e:\tau$, then $\Gamma \vdash \tau:\*$.
  2. If $\vdash \Gamma\ ok$ and $\Gamma \vdash c \equiv c':k$, then $\Gamma \vdash
    c:k$ and $\Gamma \vdash c':k$

  *Proof*.
  1. By induction over the judgment $\Gamma \vdash e:\tau$.
  2. By induction over the judgment $\Gamma \vdash c \equiv c':k$.

    $\square$

  where $\vdash \Gamma\ ok$ is a judgment ensuring that all types in $\Gamma$
  are well-formed.

  **Rules 1.4 (Well-formed contexts)**: $\vdash \Gamma\ ok$
  $$
  \begin{prooftree}
  \AxiomC{}
  \UnaryInfC{$\vdash \cdot\ ok$}
  \end{prooftree}\qquad
  \begin{prooftree}
  \AxiomC{$\Gamma\ ok$}
  \AxiomC{$\Gamma \vdash \tau:\*$}
  \BinaryInfC{$\vdash \Gamma, x:\tau\ ok$}
  \end{prooftree}\qquad
  \begin{prooftree}
  \AxiomC{$\vdash \Gamma\ ok$}
  \UnaryInfC{$\vdash \Gamma, \alpha:k\ ok$}
  \end{prooftree}
  $$

