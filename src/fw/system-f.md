# System F

As a warmup to \\(F_\omega\\), a brief review of the rules for
System F.

$$
\begin{aligned}
\tau &:= \alpha \mid \tau \rightarrow \tau \mid \forall \alpha . \tau \\\\
e &:= x \mid \lambda (x:\tau).e \mid e\ e \mid \Lambda \alpha.e \mid e[\tau]
\end{aligned}
$$

When typechecking System F, we use two judgments, $\Gamma \vdash x:
\tau$ and \\(\Gamma \vdash \tau:*\\)[^1]. The latter is often written
$\Gamma \vdash \tau\ type$, but we will use this notation so it becomes
familiar for the future.

$$\require{bussproofs}
\begin{prooftree}
\AxiomC{$\Gamma(\alpha)= \* $}
\UnaryInfC{$\Gamma \vdash \alpha: \* $}
\end{prooftree}\qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash \tau_1: \* $}
\AxiomC{$\Gamma \vdash \tau_2: \* $}
\BinaryInfC{$\Gamma \vdash \tau_1 \rightarrow \tau_2: \* $}
\end{prooftree}\qquad
\begin{prooftree}
\AxiomC{$\Gamma, \alpha:\* \vdash \tau : \*$}
\UnaryInfC{$\Gamma \vdash \forall \alpha.\tau : \*$}
\end{prooftree}
$$

$$
\begin{prooftree}
\AxiomC{$\Gamma(x) = \tau$}
\UnaryInfC{$\Gamma \vdash x : \tau$}
\end{prooftree}\qquad
\begin{prooftree}
\AxiomC{$\Gamma, x:\tau_1 \vdash e:\tau_2$}
\UnaryInfC{$\Gamma \vdash \lambda (x:\tau_1) . e : \tau_1 \rightarrow \tau_2$}
\end{prooftree}\qquad
\begin{prooftree}
\AxiomC{$\Gamma, \alpha:\* \vdash e:\tau$}
\UnaryInfC{$\Gamma \vdash \Lambda \alpha. e : \forall \alpha . \tau$}
\end{prooftree}
$$

The defining feature of System F is the $\Lambda \alpha.e$ syntax form, with
its corresponding $\forall \alpha.e$ type, the so-called "type-lambdas" or
"polymorphic values". Just as value lambdas annotate their argument, we may
also choose to do so with type lambdas, as $\Lambda (\alpha : \*).e$. Then the
rule for typing big lambda expressions becomes

$$
\begin{prooftree}
\AxiomC{$\Gamma, \alpha:\* \vdash e:\tau$}
\UnaryInfC{$\Gamma \vdash \Lambda \alpha. e : \forall \alpha . \tau$}
\end{prooftree}
$$

[^1]: The kind of base types is officially \\(T\\) for \\(type\\), but I'm going to follow the Haskell convention of writing it as \\(*\\).

