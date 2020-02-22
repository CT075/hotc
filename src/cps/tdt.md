# Type-directed Translation

As usual, before we get into a full discussion of CPS, we'll need to develop
some more machinery.

Usually, language translations are "syntax-directed", a translation judgment
defined inductively over the syntax tree. Between two types of lambda calculi,
for example, we might define our translation like this:

$$
\begin{aligned}
\overline{x} &= x \\\\
\overline{\lambda (x:\tau).e} &= \lambda(x:\overline{\tau}).\overline{e} \\\\
\overline{e_1\ e_2} &= \overline{e_1}\ \overline{e_2}
\end{aligned}
$$

where the the translation can be determined solely by looking at the particular
syntactic form.

One problem: This doesn't always work.

For example, consider translating a language with booleans into System
$F_\omega$. Under a standard Church encoding, we'd translate the type `bool` as

$$
\overline{bool} = \forall(\alpha:\*).(\alpha \rightarrow \alpha \rightarrow \alpha)
$$

with the corresponding introduction forms

$$
\begin{aligned}
\overline{true} &= \Lambda \alpha.\lambda(x:\alpha).\lambda(y:\alpha).x \\\\
\overline{false} &= \Lambda \alpha.\lambda(x:\alpha).\lambda(y:\alpha).y \\\\
\end{aligned}
$$

A problem, however, comes when trying to translate the elimination form:

$$
\overline{if\ e_1\ then\ e_2\ else\ e_3} = \overline{e_1}[\tau]\ \overline{e_2}
\ \overline{e_3}
$$

What type should we use for $\tau$? It should be the type of $e_1$ and $e_2$,
but without actually running a typechecker, we won't know what type that is! To
deal with this, we can use a *type-directed* translation, which couples the
translation step with the typechecking/type synthesis process.

Of course, there are really *two* typing judgments here, one for the source and
one for the target language. These are usually notated

$$
\begin{aligned}
\Gamma \vdash_S e:\tau \\\\
\Gamma \vdash_T e:\tau
\end{aligned}
$$

for **s**ource and **t**arget, respectively. However, we will elide the
subscripts in cases where the context makes it clear, typically when we know
what language the given term is in.

Our translation judgment, then, becomes

$$\Gamma \vdash_S e:\tau \rightsquigarrow e'$$

where $e$ is in the source and $e'$ is in the target language.

Note that we can actually use a syntax-directed translation of constructors,
kinds and contexts. For a more complex constructor language, we may need to
perform a *kind*-directed translation, but thankfully that is not the case here.

A translation, then, should have the following regularity conditions:

1. $\Gamma \vdash_S \tau: \*$ if and only if $\overline{\Gamma} \vdash_T
    \overline{\tau}: \*$.
2. $\Gamma \vdash_S e:\tau$ if and only if there exists some $e'$ such that
    $\Gamma \vdash_S e:\tau \rightsquigarrow e'$.
3. If $\Gamma \vdash_S e:\tau \rightsquigarrow e'$, then $\overline{\Gamma}
    \vdash_T e':\overline{\tau}$ (static correctness).

You might think that, since we have a notion of static correctness, we may also
have some form of *dynamic* correctness to preserve. Loosely, this might be
phrased as "If $\Gamma \vdash e:\tau \rightsquigarrow e'$, then $e$ and $e'$
'do the same thing'". However, it is actually quite difficult to even state
this formally! Certainly, we can't state this without having some formal notion
of dynamic behavior, which we won't be dealing with in this class. It turns out
that these proofs are also quite involved, which is another reason we don't
bother.

A type-directed translation rule will always follow the same form of the
associated regular typing rule, where the premises are also a translation. The
variable translation rule, for example might look like this:

$$
\begin{prooftree}
\AxiomC{$\Gamma(x) = \tau$}
\UnaryInfC{$\Gamma \vdash x:\tau \rightsquigarrow x$}
\end{prooftree}
$$

In general, it is best not to touch variable names. If we do start messing with
variable names, we'll need to ensure freshness, perform substitutions on
subterms, and so on -- not worth it at all.

Returning to the if-then-else example, we can now express the correct
translation (assuming the usual rule for typing if-then-else):

$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash e_1:bool \rightsquigarrow e_1'$}
\AxiomC{$\Gamma \vdash e_2:\tau \rightsquigarrow e_2'$}
\AxiomC{$\Gamma \vdash e_3:\tau \rightsquigarrow e_3'$}
\TrinaryInfC{$\Gamma \vdash if\ e_1\ then\ e_2\ else\ e_3:\tau
  \rightsquigarrow e_1'[\overline{\tau}]\ e_2'\ e_3'$}
\end{prooftree}
$$

Finally, note that these rules will need to be adjusted somewhat to work with
the algorithmic type synthesis and type checking rules.

Although we have not given a full formal system, we can sketch out what a proof
of the regularity conditions may look like:

1. Depends on the specifics of the kind system, but often follows via
    induction on the kinding judgment (in both directions).
2. The forward direction is fairly clear, as we design our rules to follow
    from the source typing judgment. The backwards direction is even easier,
    as we can simply delete the translations from every premise and conclusion
    to show what we need.
3. Was not given in lecture; can be proven relatively easily for yourself.

## Remarks

- In lecture, Prof. Crary chose to use $\overline{e}$ as the "output" of the
    translation judgment, where $\overline{\cdot}$ here is not acting as an
    operator, just taking the symbol $\overline{e}$ as a suggestive variable
    name. I have taken the liberty of rephrasing the rules to use something
    else for the sake of my own confusion.
- I did a few cases of the proof of the translation from IL-Direct to IL-CPS
    and it seems to be fairly straightforward. The third condition can be shown
    by induction over the translation rules, but is muddied by the presence of
    different syntactic classes.

