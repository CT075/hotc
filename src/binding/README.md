# Binding

Up to now, when writing rules "on the whiteboard", we have been blase about our
syntactic representation of variables and binding. In particular, all the rules
given only make sense if we implicitly assume that all rules apply up to alpha
equivalence, and that all substitutions are capture-avoiding. In doing so,
however, we necessarily gloss over any details of what an actual program
implementing these algorithms may need to ensure these invariants are upheld.

We now give some discussion on how these may be implemented in an actual
compiler. In the structural code for this class, we will use a hybrid of the
techniques discussed here -- terms will use explicit variables and constructors
will use De Bruijin indices. Past this explanation, we will continue to use the
notation for explicit variables everywhere, which should be implicitly converted
to De Bruijin where appropriate.

## Explicit Variables

Consider (syntactically) the lambda calculus whose terms consist of variables,
lambda abstractions, and applications. Variables and bindings are "explicit",
represented and differentiated with a literal string of characters (say $x$).
This has the example of being extremely simple to read, and has comparatively
few pitfalls to other approaches.

What would a substitution function on these terms look like? Certainly,
substituting into a variable or an application is easy. What about the lambda
case?

$$
\begin{aligned}[]
[M/x]\lambda x.N &= \lambda x.N \hfill& \\\\
[M/x]\lambda y.N &= \lambda y.[M/x]N \hfill& (y \not\in FV(M)) \\\\
[M/x]\lambda y.N &= \lambda y'.[M/x][y/y']N \hfill& (y' \ne x, y \in FV(M),
  y' \not\in FV(M))
\end{aligned}
$$

In the first case, we ignore the substitution -- the variable $x$ is bound in
the lambda, so any suboccurrences of $x$ aren't free (and thus shouldn't be
subbed). In the other two cases, we are forced to check whether $y$ is free in
the substitutee $M$, traversing the entire term each time. Then, if it is free
in $M$, we *also* need to traverse the subterm $N$ to alpha-vary it properly.

This is, as you may have surmised, not an ideal state of affairs. One
alternative is to just *always* alpha-vary the bound term, giving us the clause

$$
\begin{aligned}[]
[M/x]\lambda y.N &= \lambda y'.[M/x][y/y']N \hfill& (x \ne y, y' \ne x, y' \ne FV(M))
\end{aligned}
$$

where we generate a fresh variable each time. This is marginally better for
simplicity, but now requires us to traverse the subterm $N$ every time.

## De Bruijin Indices

Clearly, we need a better way. Another alternative we can use is *De Bruijin
indices*, in which a variable is represented by the number of binders between
the variable itself and its introduction. So the term $\lambda x.x\ (\lambda y.
x\ y)$ would be written as $\lambda . 0\ (\lambda. 1\ 0)$.

Related is the idea of De Bruijin *levels*, which count the indices backwards,
from the *outermost* binder. However, these are unwieldy and nobody uses them,
so we won't either.

Our substitution function, then, will look like this (remember that $i$ and $j$
are *natural numbers* here):

$$
\begin{aligned}[]
[M/i]i &= M \\\\
[M/i]j &= j-1 \hfill& (j > i) \\\\
[M/i]j &= j   \hfill& (j \lt i) \\\\
[M/i](N_1\ N_2) &= [M/i]N_1\ ([M/i]N_2) \\\\
[M/i]\lambda.N &= \lambda.[M\uparrow^1_0/i+1]N
\end{aligned}
$$

where $\uparrow$ is an operation that shifts the variables in a subterm (to be
defined). If $j \lt i$, on the other hand, we can leave it be, as there isn't
an intermediate binding that has been removed.

In the $j > i$ case, we need to lower the variable by 1, because if we're
substituting for it, it means we've removed a binding site (namely, the binding
$i$).

When going underneath a binder (in the $\lambda$-abstraction case), we need to
adjust any variables in the substitutee $M$ to account for the extra binder --
if $M$ refers to some free variable at index $0$, then that needs to become
index $1$ once we go underneath the lambda binder. This is where the $\uparrow$
operation comes in:

$$
\begin{aligned}[]
i \uparrow^j_k &= i + j \hfill& (i \ge k) \\\\
i \uparrow^j_k &= i \hfill& (\text{otherwise}) \\\\
(M\ N) \uparrow^j_k &= (M \uparrow^j_k)\ (N \uparrow^j_k) \\\\
(\lambda.M) \uparrow^j_k &= \lambda.(M \uparrow^j_{k+1})
\end{aligned}
$$

Let's try this on some concrete examples. Consider the eta rule for $\Pi$-kinds:

$$
\begin{prooftree}
\AxiomC{$\Gamma, \alpha:k_1 \vdash c\ \alpha:k_2$}
\UnaryInfC{$\Gamma \vdash c : \Pi(\alpha:k_1).k_2$}
\end{prooftree}
$$

Under De Bruijin, this becomes

$$
\begin{prooftree}
\AxiomC{$\Gamma, k_1 \vdash c\uparrow^1_0\ 0 : k_2$}
\UnaryInfC{$\Gamma \vdash c : \Pi(k_1).k_2$}
\end{prooftree}
$$

In the premise, we need to upshift any variables in the constructor $c$, because
we're adding a new variable (namely, $\alpha$) without going underneath an
explicit binding site.

What about application?

$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c:\Pi(\alpha:k_1).k_2$}
\AxiomC{$\Gamma \vdash c':k_1$}
\BinaryInfC{$\Gamma \vdash c\ c' : [c'/\alpha]k_2$}
\end{prooftree}
$$

This becomes

$$
\begin{prooftree}
\AxiomC{$\Gamma \vdash c:\Pi(k_1).k_2$}
\AxiomC{$\Gamma \vdash c':k_1$}
\BinaryInfC{$\Gamma \vdash c\ c' : [c'/0]k_2$}
\end{prooftree}
$$

Here, because of how we defined substitution, we can avoid needing to do the
explicit downshift that comes from instantiating the $\alpha$ binding.

## Explicit substitutions

When working with such a representation, it can often be extremely unwieldy to
need to use the above definition for every substitution. Instead, we can use a
compositional representation acting on terms. Let $\sigma$ be the syntactic
class of substitutions, which are, spiritually, functions from term to term,
applied as $M[\sigma]$ (the reverse of the usual notation). Some presentations
of this system may even add $M[\sigma]$ to the grammar as a term itself (called
a "closure", confusingly), but we will not, for simplicit. We have

$$
\begin{aligned}
\sigma &:= \uparrow^i \mid M.\sigma \\\\
\end{aligned}
$$

where $M.\sigma$ is the substitution replacing variable $0$ with $M$ and
performing $\sigma$ to $i-1$ for each other variable $i$. We will also define
the substitution $id$ to be $\uparrow^0$.

The substitution $[M_0/0, M_1/1, M_2/2]$, then, will be represented by the
operation $M_0.M_1.M_2.id$.

With substitutions now represented as first-class, it makes sense to define the
composition of substitutions. Namely, we want $\sigma \circ \sigma'$ to be
the transformation such that $M[\sigma \circ \sigma'] = (M[\sigma])[\sigma']$.

Our application rules become:

$$\begin{aligned}
0[M.\sigma] &= M \\\\
i+1[M.\sigma] &= i[\sigma] \\\\
i [\uparrow^j] &= i+j \\\\
(N\ P)[\sigma] &= (N[\sigma]\ P[\sigma]) \\\\
(\lambda.M)[\sigma] &= \lambda.(M[0.(\sigma \circ \uparrow^1)])
\end{aligned}
$$

with composition defined as

$$\begin{aligned}
(M.\sigma) \circ \sigma' &= (M[\sigma']) . (\sigma \circ \sigma') \\\\
\uparrow^i \circ \uparrow^j &= \uparrow^{i+j} \\\\
id \circ M.\sigma &= M.\sigma \\\\
\uparrow^{i+1} \circ M.\sigma &= \uparrow^i \circ \sigma
\end{aligned}
$$

Suppose, then, that we wanted to apply an operation $\sigma$ to the second
variable in our binding list. To do that with what we have, we'd need to leave
all $0$s and $1$s untouched. We can do that with

$$
\sigma \rightsquigarrow 0.(\sigma \circ \uparrow) \rightsquigarrow
0.((0.(\sigma \circ \uparrow)) \circ \uparrow)
$$

where $\rightsquigarrow$ is a transformation shifting a substitution to act
under one binding, and the last term is equal to

$$
0.(0[\uparrow].(\sigma \circ \uparrow) \circ \uparrow) =
0.1.(\sigma \circ \uparrow^2)
$$

This suggests a pattern:

$$
under_i(\sigma) = 0.1.\dots.i-1.\sigma \circ \uparrow^i
$$

which is to apply the operation $\sigma$ under $i$ bindings.

A typical use case may look like

$$
0.1.\dots.i-1.M_1[\uparrow^i].\dots.M_j[\uparrow^i].\uparrow^{i+k}
$$

In the starter code, this pattern is implemented for us as the function

```ocaml
subst_term : nat -> term list -> nat -> subst
```

## Remarks

- I always find it simplest to think of the variable $0$ as being an index into
    the ordered context list. In this way, any time something is added to the
    context *without* an explicit binder, it makes sense to increment the
    internal vars.

