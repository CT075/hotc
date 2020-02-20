# The Singleton Kind Calculus

The next type theory we'll be exploring is the calculus of singleton kinds.
This is necessary to represent type-fixed signatures, like

```ocaml
sig
  type t = int
  type u
  val a : t
end
```

How do we kind this? We can't kind the `t` tycon at $\*$, because that would
allow nonconformant structures (say, those assigning `t` to `string`) to
ascribe.

The answer is to add a new kind constructor `S(c)` of *singleton kinds*, kinds
with only one inhabitant. Set-theoretically, `S(c)` represents the singleton
set $\{c\}$, but that's about where the similarities end.

It turns out that this simple construct (and its intuitive properties) require
*a lot* more power in its machinery.

