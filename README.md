Iota Type Theory
===================

This is a simple prototype implementation of a pure type system
with dependent intersections, a heterogeneous equality, and 
implicit products. This allows one to have a pure-type-system
capable of expressing dependent elimination principals.

This branch has types and kinds unified, using `* : *` instead
of a universe hierarchy, for now.

Right now, the language only supports adding declarations
and type checking them. All files must begin with a module
declaration;

```
module Nat where
```

After that, a declaration of the form `<NAME> : <TYPE> = <TERM>`
can be declared;
```
cNat : * = (a : *) (a -> a) -> a -> a

cZ : cNat = \ a s z . z
```

Implicit products are denoted with curly braces;
```
{<NAME> : <TYPE>} -> <TYPE>
```

And implicit lambda binders are denoted with a forward slash
```
/ <NAME> . <TERM>
```

To issue an implicit argument, use `<TERM> - <TERM>`

Lambda terms are denoted with a back-slash. Type annotations
are optional, but are sometimes necessary for type inference.

Dependent intersections are denoted
```
i (<NAME> : <TYPE>) . <TYPE>
```

Square braces are used for constructing dependent intersections;
```
[ <TERM> | <TERM> ]
```

Any term `c` of a dependent intersection  ` i (x : A) . B x` can
then be typed as `A` via `c.1`, and typed as `B c.1` with
`c.2`.

Heterogeneous identity is denoted `a ~ b`.

Elimination is denoted `r(<NAME> . <TYPE>) <EQUATION> . <TERM>`.

This is one of the main differences between this implementation and
the Stump paper. Here, `r` binds a variable, and one must provide a type
which acts as any possible intermediate substitution. For example, say
we had a proof that `e : t1 ~ t2`, and we knew that `p : P t1`, and we
want to obtain `P t2`. We have, as an intermediate form, `x . P x`.
We use this in the full elimination
```
r(x . P x) e . p
```

Which will be of type `P t2`. Note that x is only bound in the intermediate
type-form, not in anything else. Additionally, reflexive proofs are denoted
`B`.

Install
-------

At some point, a proper Cabal makefile should be made, but
for now, do the following;

* Make sure you have bnfc, happy, and alex (You can get this with Cabal)
* run `bnfc -m -haskell Exp.cf`
* run alex and happy on the generated .x and .y files, respectively
* compile Main.hs
* load a file with something like `Main.exe Nat.itt`

References
--------------------

 * [From Realizability to Induction via Dependent Intersection](http://homepage.divms.uiowa.edu/~astump/papers/from-realizability-to-induction-aaron-stump.pdf), Aaron Stump. This
   paper describes the type theory that this language is based on, as well as a different implementation.

 * [Simply Easy!](http://strictlypositive.org/Easy.pdf), Andres Loh, Conor McBride, Wouter Swierstra.
   I used the lambda-Pi system described on page 6 as a reference when unifying types and kinds.

Authors
-------

Anthony Hart
