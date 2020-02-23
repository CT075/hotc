# Basic Translation

Our initial discussion of CPS transformation centers around "direct-style" code,
which features no abnormal control flow operators (exceptions, continuations,
etc).

We discussed this a bit briefly in the last section, but here are the collected
type translation rules for IL-CPS:

$$
\begin{aligned}
\overline{\alpha} &= \alpha \\\\
\overline{\tau_1 \times \tau_2} &= \neg(\overline{\tau_1} \times \overline{\tau_2}) \\\\
\overline{\tau_1 \rightarrow \tau_2} &= \neg(\overline{\tau_1} \times \neg
  \overline{\tau_2}) \\\\
\overline{\forall(\alpha:k).\tau} &= \neg(\exists(\alpha:\overline{k}).
  \neg\overline{\tau})
\end{aligned}
$$

**Rules 3.1 (CPS-conversion):** $\Gamma \vdash e:\tau \rightsquigarrow k.e'$

$$
\begin{prooftree}
\AxiomC{$\Gamma(x) = \tau$}
\UnaryInfC{$\Gamma \vdash x:\tau \rightsquigarrow k.k\ x$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash e_1:\tau_1 \rightsquigarrow k_1.e_1'$}
\AxiomC{$\Gamma \vdash e_2:\tau_2 \rightsquigarrow k_2.e_2'$}
\BinaryInfC{$
  \begin{aligned}
  \Gamma \vdash \langle e_1, e_2 \rangle :\tau_1 \times \tau_2 \rightsquigarrow k.&
    let\ k_1= \lambda(x_1:\overline{\tau_1}).\\\\
      &\quad (let\ k_2=\lambda(x_2:\overline{\tau_2}).k \langle x_1, x_2 \rangle
      \ in\ e_2') \\\\
    &in\ e_1'
  \end{aligned}
$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash e : \tau_1 \times \tau_2 \rightsquigarrow k.e'$}
\UnaryInfC{$
  \begin{aligned}
  \Gamma \vdash \pi_ie : \tau_i \rightsquigarrow k'.&
    let\ k=\lambda(x:\overline{\tau_1} \times \overline{\tau_2}). \\\\
    &\quad (let\ y = \pi_ix\ in\ k'\ y) \\\\
    &in\ e'
  \end{aligned}
$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash \tau:\*$}
\AxiomC{$\Gamma, x:\tau \vdash e:\tau' \rightsquigarrow k.e'$}
\BinaryInfC{$
  \begin{aligned}
  \Gamma \vdash \lambda(x:\tau).e: \tau \rightarrow \tau' \rightsquigarrow k'.
    &k' (\lambda(y:\overline{\tau} \times \neg\overline{\tau'}). \\\\
    &\qquad let\ x=\pi_1y\ in \\\\
    &\qquad let\ k=\pi_2y\ in\ e')
  \end{aligned}
$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash e_1:\tau_1 \rightarrow \tau_2 \rightsquigarrow
  k_1.e_1'$}
\AxiomC{$\Gamma \vdash e_2:\tau_1 \rightsquigarrow k_2.e_2'$}
\BinaryInfC{$
  \begin{aligned}
  \Gamma \vdash e_1\ e_2:\tau' \rightsquigarrow k.&let\ k_1 =
    \lambda(x_1:\neg(\overline{\tau_1}\times \neg\overline{\tau_2})). \\\\
    &\quad (let\ k_2 = \lambda(x_2:\tau_1).x_1\langle x_2,k \rangle\ in\ e_2') \\\\
    &in\ e_1'
  \end{aligned}
$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash k: \text{kind}$}
\AxiomC{$\Gamma, \alpha:k \vdash \tau:\*$}
\AxiomC{$\Gamma, \alpha:k \vdash e:\tau \rightsquigarrow k.e'$}
\TrinaryInfC{$
  \begin{aligned}
  \Gamma \vdash \Lambda(\alpha:k).e : \forall(\alpha:k).\tau \rightsquigarrow k'.
    &k'( \lambda(y:\exists(\alpha:\overline{k}).\neg \overline{\tau}).\\\\
      &\quad unpack [\alpha,k] = y\ in\ e')
  \end{aligned}
$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash e:\forall(\alpha:k).\tau \rightsquigarrow k.e'$}
\AxiomC{$\Gamma \vdash c:k$}
\BinaryInfC{$
  \begin{aligned}
  \Gamma \vdash e[c]:[c/\alpha]\tau \rightsquigarrow k'.&
    let\ k=\lambda(f:\neg(\exists(\alpha:\overline{k}).\neg\overline{\tau})). \\\\
    &\quad f(pack\ [\overline{c},k']\ as\ \exists(\alpha:\overline{k}).
      \neg \overline{\tau}) \\\\
    &in\ e'
  \end{aligned}
$}
\end{prooftree}
$$

The important thing to keep in mind while devising these rules is that, when we
recursively translate a
sub-expression $e$, we are given some bound term $k.e'$, in which the bound $k$
is a continuation taking the "result" of $e'$ as input. When we *use* this
result, then, $k$ is *free*! To complete the translation, then, we have to
re-bind $k$ to be a continuation of the correct type
(particularly, $k$ has type $\neg \overline\tau$ if $e$ has type $\tau$).

## Remarks

- I personally found it easier to chase types rather than try to reason through
    the control flow. The two main patterns I used for intuition are that
    $let\ k=\dots\ in\ e$ is the translation of "evaluate $e \rightsquigarrow
    k.e$" and $k\ v$ is the translation of "$v$ is a value".

