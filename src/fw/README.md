# System Fw

System $F_\omega$ is a system of higher-kinded types and type-constructors. It
is relevant to compiling SML in the way that it relates to the module system.
If we extend the kind system of "true" $F_\omega$ with product kinds, we might
represent the module signature

```ocaml
sig
  type t
  type 'a u
end
```

as the kind $\* \times (\* \rightarrow \*)$, and so on. This even
extends to functors that act on modules via type-level lambdas.

