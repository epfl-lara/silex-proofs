# Proving `silex` correct
## Coq Proofs on Lexing with Derivatives and Zippers

This project is a collection of Coq proofs showing the correctness of the approach taken by the [silex](https://github.com/epfl-lara/silex) lexing library.
The lexing algorithm of silex is based on a novel combination of Brzozowski's derivatives and Huet's zippers.
In this approach, regular expressions and their derivatives are represented as zippers.
Each zipper is a set, which represents a disjunction of contexts.
Contexts are themselves sequences of regular expressions, represented as lists.

The first main result is that Brzozowski's derivation adapted to zippers is correct with respect to regular expressions' semantics ([Zippers.v, line 584](Zippers.v#L584)).

```coq
Theorem derive_correct : forall z c w,
  zipper_matches z (c :: w) <->
  zipper_matches (derive c z) w.
```

The correctness of the recogniser follows almost immediately after ([Zippers.v, line 684](Zippers.v#L684)).

```coq
Theorem accepts_correct : forall e w,
  accepts e w = true <->
  matches e w.
```

The second main result shows a bound on the number of different zippers that can be encountered by successive derivation ([Zippers.v, line 1035](Zippers.v#L1035)).

```coq
Theorem finiteness:
  forall z,
  exists Z,
  forall w,
  forall ctx,
  set_In ctx (derive_word w z) ->
  set_In ctx Z.
```

## Dependencies

The project only relies on a relatively recent installation of Coq.
The project does not depend on any Coq extensions.


## Compiling the Proofs

Once you have a relatively recent installation of Coq, simply call the following commands to compile the project's proofs:

```
./configure
make
```







