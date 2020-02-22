# Continuation Passing Style

The next language we'll be covering is `IL-CPS`, whose purpose is to make
control flow explicit in the syntax of the language.

In particular, this language will have the following three properties:

1. No implicit control flow -- procedure calls, returns, exceptions, etc. are
    all represented as jumps.
2. All intermediate values are named.
3. Continuations are reified as 1st class values.

To explain the second condition, instead of compound expressions like `x+y+z`,
in CPS form we would use something akin to `let x' = x+y in x'+z`.

There are some compilers whose CPS transformation pass only conforms to the
first two conditions. This is known as "A-normal form", or "monadic form". Or,
very creatively, "2/3rds CPS".

