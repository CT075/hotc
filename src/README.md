# 15-417 HOT Compilation, Spring 2020

- Professor: Karl Crary
- Scribe: Cameron Wong
- Carnegie Mellon University

Joining a grand tradition, I'm going to attempt and inevitably give up at
typesetting the notes for this class.

Material is grouped by subject and is roughly ordered by when we covered them
in class. There is no separation by individual lectures. The order of material
in a given subsection is, roughly following class presentation order, but may
be reordered according to what I personally find to be clearer.

These are somewhat inspired by Nick Roberts' attempt, and a lot of the early
material is... well, not lifted, but definitely influenced by his explanations.

I will do my best to keep my personal comments restricted to the remarks. Any
mistakes are mine. These notes will include no more SML code than was presented
in lecture.

[source](https://github.com/CT075/hotc)

## Structure of the Compiler

The compiler developed by this class will follow the following progression:

```bob
+-----------+
|    SML    | (AST)
+-----+-----+
      |
      | Elaboration
      |
+-----+-----+
|  IL-Module|
+-----+-----+
      |
      | Phase-splitting
      |
+-----+-----+
|  IL-Direct|
+-----+-----+
      |
      | CPS Conversion
      |
+-----+-----+
|   IL-CPS  |
+-----+-----+
      |
      | "Closure Conversion"
      |
+-----+------+
|  IL-Closure|
+-----+------+
      |
      | Hoisting
      |
+-----+-----+
|  IL-Hoist |
+-----+-----+
      |
      | "Allocation/Type Erasure"
      |
+-----+-----+
|  IL-Alloc |
+-----+-----+
      |
      | Code generation
      |
+-----+-----+
|     C     |
+-----------+
```

where each `IL-` language is some intermediate form. Until IL-Alloc, each
intermediary language is also typed, which will aid in ensuring that the passes
are well-formed.

It is possible to preserve types all the way down, foregoing the type erasure
leading into IL-Alloc. Such compilers often have an "hourglass effect", in
which the intermediary typesystems get increasingly simple down to a point, at
which they become more complex again. Consider a typed memory representation of
the sum type $A+B$, for example. We have to store a tag (for which variant)
along with the object itself, giving us a layout of

```bob
+-----+-----+
| tag | obj |
+-----+-----+
```

Our typesystem must be powerful enough to express these layouts
accurately, hence the extra complexity. This may continue all the
way down to, say, a typed assembly language. In this class, however, we only
have enough time to cover up to IL-Alloc, and will thus generate C from there.

