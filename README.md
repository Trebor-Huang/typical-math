# TypicalMath
A **general-purpose** type theory and proof checker **implementer**. By specifying the derivation rules, this tool can act as a type checker for the type system.
 The supporting theory is introduced in 
 [this column (Chinese)](https://zhuanlan.zhihu.com/typical-math).

## Type system

Since this project aims for a *general-purpose* *implementer*, we have a way of specifying a set of bidirectional derivation rules. In mathematical notation, they are of the form:

```
 J1 J2 J3 ...
-------------- Rule-Name
      J
```

Where each judgment `J` is of the form

```
Gamma |- In-expr ~> Out-expr
```

The program runs the classic bidirectioal type-checking technique:
it first **matches** the judgment to be derived with the conclusions of the rules *in order*,
and after the first match, it tries to derive all the premises, with a monadic structure
recording the meta-variable assignment and log data.

## Parsing system

## [Deprecated] Python

Under the `python-archive` tag.
This part contains python code that I abandoned :(

## Miscellaneous Components

This part is stored in the `/Misc` directory under the `python-archive` tag.
It contains the code used for demonstration purposes in the column.

The `/Misc/LambdaCalculus` folder contains an implementation of
simply typed and untyped lambda calculus. It also contains a
fun implementation of the [Iota and Jot language](https://en.wikipedia.org/wiki/Iota_and_Jot).

The `/Misc/unification` folder contains a demonstrative system
of a unification algorithm.
