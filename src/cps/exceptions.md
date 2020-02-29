# Exception passing

A more involved form of advanced control flow is that of exceptions that
automatically propagate up the call stack until being handled.

## Aside: Typed exceptions

In ML, the type `exn` is special in that new variants can be added to it at
runtime. This is the so-called *extensible* type, a dynamically-growing sum
type.

This extensibility is actually entirely separate from the concept of exceptions
as a control flow tool, despite the two being often conflated. To sidestep
dealing with this issue, we will assume the existence of a type $\tau_{ex}$,
the type of *exception objects*. This type could be `int`, `void`, `exn`, or so
on, it doesn't matter.

## Syntax of exceptions

Statically, we will define exception handling as follows:

$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash e_1:\tau$}
\AxiomC{$\Gamma, x:\tau_{ex} \vdash e_2:\tau$}
\BinaryInfC{$\Gamma \vdash try\ e_1\ with\ x.e_2:\tau$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash e:\tau_{ex}$}
\AxiomC{$\Gamma \vdash \tau : \*$}
\BinaryInfC{$\Gamma \vdash raise\ e:\tau$}
\end{prooftree}
$$

Because every expression may now have a separate evaluation condition (namely,
"raising an exception"), we also need to change some our translation strategy.
Previously, we only bound the one continuation `k` for the singular exit
condition. Now, we'll also have a continuation `k_ex`, which is called with the
raised exception of a given expression. For the obvious reason, this style of
evaluation is often described as "double-barrelled CPS".

We also need to adjust our type translation:

$$\overline{\tau_1 \rightarrow \tau_2} \rightsquigarrow \neg(\overline{\tau_1}
\times \neg \overline{\tau_2} \times \neg \overline{\tau_{ex}})$$

The translation judgment, then, becomes

$$\Gamma \vdash e:\tau \rightsquigarrow k.k_{ex}.e'$$

with coherence condition

- If $\Gamma \vdash e:\tau \rightsquigarrow k.k_{ex}.e'$, and $\vdash \Gamma
    \ ok$, then $\overline{\Gamma}, k:\neg \overline{\tau}, k_{ex}:\neg
    \overline{\tau_{ex}} \vdash e':0$

In most cases, we will simply thread the same $k_{ex}$ through the same
translations developed in the previous section. For example, we might have

$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash e_1:\tau_1 \rightsquigarrow k_1.k_{ex}.e_1'$}
\AxiomC{$\Gamma \vdash e_2:\tau_2 \rightsquigarrow k_2.k_{ex}.e_2'$}
\BinaryInfC{$
  \begin{aligned}
  \Gamma \vdash \langle e_1, e_2 \rangle :\tau_1 \times \tau_2 \rightsquigarrow
    k.k_{ex}.&
    let\ k_1= \lambda(x_1:\overline{\tau_1}).\\\\
      &\quad (let\ k_2=\lambda(x_2:\overline{\tau_2}).k \langle x_1, x_2 \rangle
      \ in\ e_2') \\\\
    &in\ e_1'
  \end{aligned}
$}
\end{prooftree}
$$

where we use the same exception handler for the premises as the conclusion.

**Rules 3.3 (Double-barrelled CPS, selected rules only)**: $\Gamma \vdash e:\tau
\rightsquigarrow k.k_{ex}.e'$

$$
\begin{prooftree}
\AxiomC{$\Gamma(x) = \tau$}
\UnaryInfC{$\Gamma \vdash x:\tau \rightsquigarrow k.k_{ex}.k\ x$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash \tau:\*$}
\AxiomC{$\Gamma, x:\tau \vdash e:\tau' \rightsquigarrow k'.k_{ex}'.e'$}
\BinaryInfC{$
  \begin{aligned}
  \Gamma \vdash \lambda(x:\tau).e: \tau \rightarrow \tau' \rightsquigarrow
    k.k_{ex}.
    &k (\lambda (y:\overline{\tau} \times \neg\overline{\tau'} \times
      \neg\overline{\tau_{ex}}). \\\\
    &\qquad let\ x=\pi_1y\ in \\\\
    &\qquad let\ z=\pi_2y\ in \\\\
    &\qquad let\ k'=\pi_1z\ in \\\\
    &\qquad let\ k_{ex}'=\pi_2z\ in\ e')
  \end{aligned}
$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash e_1:\tau \rightarrow \tau' \rightsquigarrow k_1.k_{ex}.e_1'$}
\AxiomC{$\Gamma \vdash e_2:\tau \rightarrow \tau' \rightsquigarrow k_2.k_{ex}.e_2'$}
\BinaryInfC{$
  \begin{aligned}
  \Gamma \vdash e_1\ e_2 : \tau' \rightsquigarrow k.k_{ex}.
    &let\ k_1' = \lambda(f:\neg(\overline{\tau} \times \neg\overline{\tau'} \times
      \neg\overline{\tau_{ex}})). \\\\
    &\qquad (let\ k_2 = \lambda(x:\overline{\tau}).f \langle x,
      \langle k, k_{ex} \rangle \rangle\ in\ e_2') \\\\
    &in\ e_1'
  \end{aligned}
$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash e:\tau \rightsquigarrow k.k_{ex}.e'$}
\AxiomC{$\Gamma, x:\tau_{ex} \vdash e_{ex} : \tau \rightsquigarrow
  k.k_{ex}'.e_{ex}'$}
\BinaryInfC{$
  \begin{aligned}
  \Gamma \vdash try\ e\ with\ x.e_{ex}:\tau \rightsquigarrow k.k_{ex}'.
    let\ k_{ex}=\lambda(x:\overline{\tau_{ex}}).e_{ex}'\ in\ e'
  \end{aligned}
$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash \tau:\*$}
\AxiomC{$\Gamma \vdash e:\tau_{ex} \rightsquigarrow k.k_{ex}.e'$}
\BinaryInfC{$\Gamma \vdash raise_\tau\ e:\tau \rightsquigarrow k'.k_{ex}.[k_{ex}/k]e'$}
\end{prooftree}
$$

Note that we are treating products as right-associative for the purpose of the
$\pi_1$ and $\pi_2$ expressions. In the `raise` case, we can simply evaluate the
exception expression $e$, passing $k_{ex}$ as its regular continuation. For
`try...catch`, we need to replace the exception handler of $e$ with a function
that evaluates $e_{ex}$, using an outer exception handler on the overall
expression.

## Remarks

- It's more explicit how the `raise` rule works if we instead translate to
    `let k = (fn (x:t_ex) => k_ex x) in e'`. This is eta-reduced in the rule
    given.

