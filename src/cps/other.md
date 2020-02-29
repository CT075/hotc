# Miscellaneous Other Notes

## Extensible Variants

To complete our discussion of ML-like languages, we need a theory of extensible
variants. We will do this by adding a new type constructor $\tau\ tag$, a reified
type tag that will be used to differentiate dynamically-added variants. It, and
the `exn` type, is defined by the rules

$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash \tau:\*$}
\UnaryInfC{$\Gamma \vdash \tau\ tag:\*$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash \tau:\*$}
\UnaryInfC{$\Gamma \vdash newtag[\tau]:\tau\ tag$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash e_1:\tau\ tag$}
\AxiomC{$\Gamma \vdash e_2:\tau$}
\BinaryInfC{$\Gamma \vdash tag(e_1, e_2):exn$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash e_1:\tau\ tag$}
\AxiomC{$\Gamma \vdash e_2:exn$}
\AxiomC{$\Gamma, x:\tau \vdash e_3:\tau'$}
\AxiomC{$\Gamma \vdash e_4:\tau'$}
\QuaternaryInfC{$\Gamma \vdash iftag(e_1,e_2,x.e_3,e_4)$}
\end{prooftree}
$$

Evaluating `iftag` checks if the expression `e_2` is tagged with `e_1`. If so,
bind the captured $\tau$ value to `x` in `e_3`, otherwise, evaluate `e_4`.

## The initial continuation

One issue with our CPS-conversion translation is that we currently produce, as
our final program, a strange expression $k.k_{ex}.e$, with these bound $k$ and
$k_{ex}$. At the top level, these are effectively free! To resolve this, we will
define the judgment

$$\Gamma \vdash_{prod} e:\tau \rightsquigarrow e'$$

for use on the top level program. We can then define

$$
\begin{prooftree}
\AxiomC{$\cdot \vdash e:\overline{\tau} \rightsquigarrow k.k_{ex}.e'$}
\UnaryInfC{$
  \begin{aligned}
  \cdot \vdash_{prod} e:\tau \rightsquigarrow
    &let\ k=\lambda(x:\overline{\tau}).halt\ in\\\\
    &let\ k_{ex} = \lambda(x:\overline{\tau_{ex}}).
     (print\ \unicode{x201C}\text{uncaught exception}\unicode{x201D}; halt)\ in\\\\
    &e'
  \end{aligned}
$}
\end{prooftree}
$$

(where `;` represents obvious sequencing)

Note that we simply throw the result of the entire program on the floor and
halt. With this setup, a program's practical usage is in its IO behavior, not
in the result of its evaluation. It is possible to set it up otherwise, but
that requires more complicated translations at the top level.

