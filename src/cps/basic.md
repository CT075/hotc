# Introduction to Continuation Passing Style

Before we can discuss the translation, we must specify our source and target
languages.

## Source: IL-Direct

| Sort |  |  |
|---|---|---|
| Kinds | $k:=$ | $\* \mid S(c) \mid \Pi(\alpha:k).k \mid \Sigma(\alpha:k).k$ |
| Tycons | $c:=$ | $\alpha \mid \lambda(\alpha:k).c \mid c\ c \mid \langle c, c\rangle \mid \pi_1c \mid \pi_2c$ |
| (Types) | $(\tau)$ | $\phantom{\alpha} \mid \forall(\alpha:k).\tau \mid \tau \rightarrow \tau \mid \tau \times \tau$ |
| Terms | $e:=$ | $x \mid \Lambda(\alpha:k).e \mid e[c] \mid \lambda(x:\tau).e \mid e\ e$ |
|       |     | $\phantom{x} \mid \langle e, e \rangle \mid \pi_1e \mid \pi_2e$

For the most part, the kinds and the non-$\tau$ type constructors will be the
same for the rest of the class. The *types*, on the other hand, will be changing
quite frequently, as will the terms (obviously). In a real implementation, we'll
also be adding some *actual* base types, like `int`, `bool`, `exn`, `ref`, etc.

## Target: IL-CPS

| Sort | | |
|---|---|---|
| Kinds | $k:=$ | same |
| Tycons | $c:=$ | same |
| (Types) | $(\tau)$ | $\dots \mid \exists(\alpha:k).\tau \mid \neg\tau \mid \tau \times \tau$ |
| Values | $v:=$ | $x \mid \lambda(x:\tau).e \mid \langle v, v \rangle \mid pack\ [c,v]\ as\ \exists(\alpha:k).\tau$ |
| Expressions | $e:=$ | $let\ x=v\ in\ e \mid v\ v \mid let\ x = \pi_1v\ in\ e \mid let\ x = \pi_2v\ in\ e$ |
| | | $\phantom{x} \mid unpack\ [\alpha,x] = v\ in\ e \mid halt$ |

Properly, we might notate $\neg\tau$ as $\tau \rightarrow answer$ or $\tau
\rightarrow 0$, to notate that lambdas (really, continuations) don't return.
However, by marking it as $\neg\tau$, some of the type relationships become more
obvious. Similarly, the $v\ v$ syntactic form is more of a jump than a function
call.

If we had booleans (particularly if-then-else), we might add $if\ v\ then\ e\ else\ e$
for this. Instead of nesting expressions, we need to *bind* them into values
before they can be used. For this reason, this is a "monadic form".

## Basic Principles

When translating kinds and contexts, we can largely do the obvious thing. With
types, on the other hand, we have some work to do. We have

$$\overline{\tau_1 \rightarrow \tau_2} = \neg(\overline{\tau_1} \times \neg
\overline{\tau_2})$$

Intuitively, we can think of a function, in CPS, as a jump taking the standard
parameter ($\overline{\tau_1}$) and also a continuation argument telling where
to jump with the result ($\neg\overline{\tau_2}$). In the theory, the slick way
to see it is that $A \implies B$ is equivalent to $\neg A \lor B$, which is
in turn equivalent to $\neg (A \land \neg B)$ by De Morgan's law. It turns out
that programming in the presence of continuations actually encodes *classical*
logic under Curry-Howard, where the proof of a proposition $\tau$ can be
contradicted with (thrown to) a *continuation* $\neg \tau$, which diverges
(produces $\bot$). Classical and constructive logic coincide on $\Pi_2$
sentences, which are sentences of the form $\forall \dots \forall . \exists
\dots \exists . p$ (either of the quantifier prefix lists can be empty), where
$p$ is a decidable proposition.

By Curry-Howard, the translation $M:A \rightsquigarrow \overline{M}:
\overline{A}$ transforms the proof $M$ to remove uses of double negation
elimination (known in PL parlance as `callcc`). If $A$ is $\Pi_2$, we can
extract a proof of $A$ from a proof of $\overline{A}$ in this way.

You may also notice that IL-CPS does not have $\forall$ types, only $\exists$.
We use the translation

$$\overline{\forall(\alpha:k).\tau} = \neg(\exists(\alpha:\overline{k}).\neg
\overline{\tau})$$

again using the classical tautology $\forall x.p \Leftrightarrow \neg \exists
x. (\neg p)$. Computationally, this transforms a *function* taking the
constructor $\alpha$ and returning a value into a continuation that takes an
*existential* holding $\alpha$ and an internal continuation taking the resulting
$\tau$ value. We don't actually want to have $\forall(\alpha:k).\tau$ as a
type in our CPS language. It is workable, but very strange -- some function
calls become *values*, and so on. Doing this actually produces better code at
the expense of some unfortunate semantics (for example, the value restriction
resurfaces).

Some regularity conditions:

1. If $\Gamma \vdash k:\text{kind}$, then $\overline{\Gamma} \vdash \overline{k}
    :\text{kind}$
2. If $\Gamma \vdash c:k$, then $\overline{\Gamma} \vdash \overline{c}:\overline{k}$

A third property that's nice to have is that the translation commutes with
substitution:

$$\overline{[c_1/\alpha]c_2} = [\overline{c_1}/\alpha]\overline{c_2}$$

which holds if we don't mess with the variables.

The translation judgment itself will need to be a little weird to accommodate
the CPS property. Instead of using the typical $\Gamma \vdash e:\tau \rightsquigarrow
e'$, we're going to bind an explicit continuation argument $\Gamma \vdash
e:\tau \rightsquigarrow x.e'$, where $x$ is a bound continuation of type $\neg
\overline\tau$. We can think of this translation as assuming a continuation
to pass the "result" of evaluating the expression $e$ to.

Properly, of course, continuation arguments are named $k$ by convention. We
already use $k$ for kinds, but the two appear in different contexts, so there's
no possibility of confusion.

## Statics of IL-CPS

Because of the value-expression modality, we need to adjust our definition of
static correctness:

- If $\Gamma \vdash e:\tau \rightsquigarrow k.e'$ and $\vdash \Gamma\ ok$, then
    $\overline{\Gamma}, k:\neg \overline{\tau} \vdash e':0$

The $0$ in this expression typing judgment denotes that, in this language,
expressions diverge -- they have type `void`, effectively. Values, of course,
are typed as usual.

IL-CPS, then, is defined statically as follows:

$$
\begin{prooftree}
\AxiomC{$\Gamma(x) = \tau$}
\UnaryInfC{$\Gamma \vdash x:\tau$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash \tau:\*$}
\AxiomC{$\Gamma, x:\tau \vdash e:0$}
\BinaryInfC{$\Gamma \vdash \lambda(x:\tau).e : \neg \tau$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash v_1:\tau_1$}
\AxiomC{$\Gamma \vdash v_2:\tau_2$}
\BinaryInfC{$\Gamma \vdash \langle v_1, v_2 \rangle : \tau_1 \times \tau_2$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c:k$}
\AxiomC{$\Gamma \vdash v:[c/\alpha]\tau$}
\AxiomC{$\Gamma, \alpha:k \vdash \tau:\*$}
\TrinaryInfC{$\Gamma \vdash pack\ [c,v]\ in\ \exists(\alpha:k).\tau$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash v_1:\neg \tau$}
\AxiomC{$\Gamma \vdash v_2:\tau$}
\BinaryInfC{$\Gamma \vdash v_1\ v_2:0$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash v:\tau$}
\AxiomC{$\Gamma, x:\tau \vdash e:0$}
\BinaryInfC{$\Gamma \vdash let\ x=v\ in\ e:0$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash x:\tau_1 \times \tau_2$}
\AxiomC{$\Gamma, x:\tau_1 \vdash e:0$}
\BinaryInfC{$\Gamma \vdash let\ x=\pi_1v\ in\ e:0$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{$\Gamma \vdash x:\tau_1 \times \tau_2$}
\AxiomC{$\Gamma, x:\tau_2 \vdash e:0$}
\BinaryInfC{$\Gamma \vdash let\ x=\pi_2v\ in\ e:0$}
\end{prooftree}
$$
$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash v:\exists(\alpha:k).\tau$}
\AxiomC{$\Gamma,\alpha:k,x:\tau \vdash e:0$}
\BinaryInfC{$\Gamma \vdash unpack\ [\alpha,x]=v\ in\ e:0$}
\end{prooftree} \qquad
\begin{prooftree}
\AxiomC{}
\UnaryInfC{$\Gamma \vdash halt:0$}
\end{prooftree}
$$

