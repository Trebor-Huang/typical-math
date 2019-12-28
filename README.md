# TypicalMath
A **general-purpose** type theory and proof checker **generator**. By specifying the derivation rules, this tool can act as a type-checker for the type system.
The relevant theory is introduced in [this column (Chinese)](https://zhuanlan.zhihu.com/typical-math).

## Bidirectional Inference Rules

In mathematical notation, they are of the form:

```
 J1 J2 J3 ...
-------------- Rule-Name
      J
```

Where each judgment `J` is of the form

```
In-expr ~> Out-expr
```

If a formal system is specified with such rules, then it is very easy to devise an algorithmic
derivation process (other than recursively enumerating all the possibilities, which is very
inefficient).
The `~>` arrow seperates the "input" and "output" parts of the judgment. In the language as used
in *Practical Foundations of Programming Languages*, the "mode" of the judgment is 
(∀, ∀,..., ∀, ∃!).

First match the judgment to be derived against the input part of the conclusions of the rules.
If it matched, then try to derive the corresponding premises. A successful derivation of a premise,
as the mode suggests, will return some unique expression on the right of the `~>`. We can then piece
the return values together and form the output of the judgment to be derived. More can be found in
the very well-written book *The Little Typer*.

## Main function

However, our program uses a much more flexible approach. We do not *require* a bidirectional formalism,
but works best under it. We utilize **unification** instead of matching, which is cleaner and more
uniform. We simply do (syntactic) unification all the time, and fill in the meta-variables as they are solved.

> TODO: give some examples

But to be honest, our more liberal approach also causes some problems: if the order of the rules are
inadequate, the unification process sometimes over-specialize the meta-variables. For instance, if we
want to derive `S(?n) nat`, meaning "the successor of some expression `?n` is a natural number", the
program will use the `Snat` rule, stating that the successor of an expression is a natural
number when the expression itself is one; therefore we arrive at the goal premise `?n nat`, in which
the meta-variable `?n` is obviously not solvable. But the program will go on and try the first rule,
`Znat`, stating that zero is a natural number, and after unification happily announce that the problem
is solved and `?n` is simply `Z`. This can be avoided by phrasing the judgments the right way, but it
is very subtle. I'm still pondering it.

## Parsing system

I plan to use a concrete grammar similar to Agda. But there is no work on it yet.

## Pretty printing

Since much math talk is likely to be involved, I used TeX as the pretty-printing format. Right now,
the program contains no front-end, and you must somehow compile the TeX code in order to properly
view the output.

## [Deprecated] Python

Under the `python-archive` tag.
This part contains python code that I abandoned :(

### Miscellaneous Components

This part is stored in the `/Misc` directory under the `python-archive` tag.
It contains the code used for demonstration purposes in the column.

The `/Misc/LambdaCalculus` folder contains an implementation of
simply typed and untyped lambda calculus. It also contains a
fun implementation of the [Iota and Jot language](https://en.wikipedia.org/wiki/Iota_and_Jot).

The `/Misc/unification` folder contains a demonstrative system
of a unification algorithm.
