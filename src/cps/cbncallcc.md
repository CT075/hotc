# Other evaluation strategies

In this section, we discuss CPS conversion for a few other evaluation schemes.

## Call by Name

The primary counterpart to so-called "strict" evaluation is "lazy" evaluation,
otherwise known as "call by name" (as opposed to "call by value") semantics.
The key difference, of course, is that sub-expressions aren't evaluated until
they are eliminated, leading to things like function arguments being passed as
thunks, and so on.

As the key idea behind CPS is to make ccontrol flow very explicit, it stands to
reason that it doesn't matter whether IL-CPS is by name or by value, something
that the expression-value divide enforces. The difference, then, is expressed
in the *translation* from a call-by-name language to continuation passing style.

Conceptually, this works out with bound variables in contexts having a moral
type of $\neg \neg \tau$ (taking in the "what do I do next" continuation),
rather than $\tau$. The primary place this manifests is in the translation of
contexts:

$$\overline{\Gamma, x:\tau} = \overline{\Gamma}, x:\neg\neg\overline\tau$$

We also need to adjust our translation of function types to account for this:

$$\overline{\tau_1 \rightarrow \tau_2} =
  \neg(\neg \neg \overline{\tau_1} \times \neg \overline{\tau_2})
$$

Now, as it turns out, we can get away with only changing a few rules from their
previous definitions:

**Rules 3.2 (Call by name translation)**

$$
\begin{prooftree}
\AxiomC{$\Gamma(x) = \tau$}
\UnaryInfC{$\Gamma \vdash x:\tau \rightsquigarrow x\ k$}
\end{prooftree}
$$

Remember that here, the translated $x$ has type $\neg\neg \tau$, so instead of
passing the final value $x$ to $k$, we pass the continuation $k$ to $x$.

*Rules 3.2 cont'd*

$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash \tau_1:\*$}
\AxiomC{$\Gamma, x:\tau \vdash e:\tau_2 \rightarrow k.e'$}
\BinaryInfC{$
  \begin{aligned}
  \Gamma \vdash \lambda(x:\tau).e:\tau_1 \rightarrow \tau_2 \rightsquigarrow k'.
    k'(&\lambda(y:\neg\neg\overline{\tau_1} \times \neg\overline{\tau_2}).\\\\
      &\quad let\ x=\pi_1y\ in \\\\
      &\quad let\ k=\pi_2y\ in\ e')
  \end{aligned}
$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash e_1:\tau_1 \rightarrow \tau_2 \rightsquigarrow k_1.e_1'$}
\AxiomC{$\Gamma \vdash e_2:\tau_1 \rightsquigarrow k_2.e_2'$}
\BinaryInfC{$
  \begin{aligned}
  \Gamma \vdash e_1\ e_2:\tau_2 \rightsquigarrow k.&
    let\ k_1 = \lambda(f:\neg(\neg \neg \overline{\tau_1}\times \neg\overline{\tau_2})).
      \\\\
    &\quad f \langle (\lambda(k_2:\neg\overline{\tau_1}).e_2'), k\rangle \\\\
    &in\ e_1'
  \end{aligned}
$}
\end{prooftree}
$$

The function rule is actually almost completely the same, but is reproduced to
demonstrate the type change. In the application rule, instead of evaluating the
argument $e_2'$, we reify it as a thunk to pass as the first argument to the
resultant jump.

In fact, these are all the changes we need to change the previous translation
into a call by name version! There are often other lazy constructs (such as lazy
tuples), but we won't discuss them here.

### Aside: Call by "need"

One issue with naive call by name is that, if a given input is used multiple
times, it may need to be evaluated multiple times. These *can* be optimized out
in some cases, but in the presence of effects this doesn't help in the general
case. Instead, we can use some memoization to cache the results of computations
after they've been used once. This is the evaluation strategy used by Haskell,
which has the name "call by need".

Under the hood, this is used by storing a datatype `UNFORCED of unit -> 'a
| FORCED of 'a` for the lazy thunks, and then internally using a ref to track
them, replacing `UNFORCED` with `FORCED` when necessary. This, ironically, leads
to Haskell being less naively parallelizable than ML, as there are now mutable
data dependencies to worry about (in an ostensibly completely pure language).
To get around this, GHC actually does some strictness analysis, compiling what
code it can to a call-by-value language, then leaving the rest as call by need.

## Call/cc

Scheme popularized the idea of reified first-class continuations with the
`callcc` construct. For use of this concept, SMLNJ exposes two functions:

```ocaml
callcc: ('a cont -> 'a) -> 'a
throw: 'a cont * 'a -> 'b
```

Instead of using functions, however, we're going to make these primitive
constructs in our source language, defined statically as:

$$
\begin{prooftree}
\AxiomC{$\Gamma, x:\tau\ cont \vdash e:\tau$}
\AxiomC{$\Gamma \vdash \tau:\*$}
\BinaryInfC{$\Gamma \vdash letcc\ x\ in\ e:\tau$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash e_1:\tau$}
\AxiomC{$\Gamma \vdash e_2:\tau\ cont$}
\AxiomC{$\Gamma \vdash \tau':\*$}
\TrinaryInfC{$\Gamma \vdash throw\ e_1\ to\ e_2:\tau'$}
\end{prooftree}
$$

Suggestively, the target language is *continuation passing style* for a reason,
which suggests the translation of $\tau\ cont$ to $\neg \tau$. We can translate
these two new constructs as

$$
\begin{prooftree}
\AxiomC{$\Gamma, x:\tau\ cont \vdash e:\tau \rightsquigarrow k.e'$}
\AxiomC{$\Gamma \vdash \tau:\*$}
\BinaryInfC{$\Gamma \vdash letcc\ x\ in\ e:\tau \rightsquigarrow k.
  let\ x=k\ in\ e'$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash e_1:\tau \rightsquigarrow k_1.e_1'$}
\AxiomC{$\Gamma \vdash e_2:\tau\ cont \rightsquigarrow k_2.e_2'$}
\AxiomC{$\Gamma \vdash \tau':\*$}
\TrinaryInfC{$
  \begin{aligned}
  \Gamma \vdash throw\ e_1\ to\ e_2:\tau' \rightsquigarrow k.&
    let\ k_1=\lambda(x:\overline{\tau}).\\\\
    &\quad let\ k_2=\lambda(f:\neg\overline{\tau}).f\ x\ in\ e_2'\\\\
    &in\ e_1'
  \end{aligned}
$}
\end{prooftree}
$$

Unsurprisingly, $letcc$ involves capturing the current continuation, which is
*conveniently* passed as the bound $k$. For $throw$, we evaluate both $e_1$ and
$e_2$, and then pass the result of $e_2$ to the continuation hidden in $e_2$.

## Remarks

- I'm not entirely sure what the issue is with refs in parallel for Haskell.
    Even if multiple threads try to write to the ref cell at once (assuming
    atomic reads and writes, of course), there would be no correctness issues,
    as both threads would be writing the same value anyway (in a pure language).
    Prof. Crary said that this kind of strategy causes issues with garbage
    collection but didn't go into detail.

