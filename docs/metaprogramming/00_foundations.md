# How metaprogramming works. Part 0: Foundations of provers

This document is for a mathematician who wants to gain an understanding of what is going on under the hood rather than for pro type theorists or pro computer scientists.
I am going to assume that readers are familiar with dependent type theory and proving things in Lean, but not with how these things are implemented on a computer.
I will also assume that the reader is comfortable with the topics covered [here](monad-tutorial.md).

I hope that this doc will be more of a wiki page and people should feel free to edit it.

### About this doc

The current version of this doc is pulled together from a number of places: answers on [Zulip](https://leanprover.zulipchat.com);  [my thesis](https://edayers.com/thesis/background) (in particular [§2.1](https://www.edayers.com/thesis/background#prover-arch) and [§2.4](https://www.edayers.com/thesis/background#mvars)); [an unfinished tutorial I wrote for Lean 3](https://github.com/EdAyers/edlib/tree/master/docs); and the Lean 3 and Lean 4 source code.
I would like to thank Mario Carneiro, Leo de Moura, Gabriel Ebner, Simon Hudon, Sebastian Ullrich, Kevin Buzzard, Rob Lewis and everyone else in the Lean community chat for helping me out with these.

## Other things to read

- Andrej Bauer gave a very good [MathOverflow answer](https://mathoverflow.net/questions/376839/what-makes-dependent-type-theory-more-suitable-than-set-theory-for-proof-assista/376973#376973) giving an overview of what a proof assistant does and why dependent type theory is good for doing mathematics.
- [Mario Carneiro's master's thesis](https://github.com/digama0/lean-type-theory/releases/download/v0.21/main.pdf) has a formal definition of the type theory that Lean uses. It was written for Lean 3 but my understanding is that it applies to Lean 4 too.

## What is a logical foundation?


The essential purpose of a proof assistant is to represent mathematical theorems, definitions and proofs in a language that can be robustly checked by a computer. This language is called the __foundation language__. The language defines the set of objects that formally represent mathematical statements and proofs, and the inference rules and axioms provide the valid ways in which these objects can be manipulated.
Some examples of foundations are [first-order logic (FOL)](https://en.wikipedia.org/wiki/First-order_logic), [higher-order logic (HOL)](https://en.wikipedia.org/wiki/Higher-order_logic), and various forms of dependent type theory (DTT).

### Defining a foundation in general

Most of the time, defining a new logical foundation follows a recipe:

#### 1. __Define an language structure__:

A definition of trees of symbols that the foundation will talk about.
- "if `s` and `t` are terms, then `s t` is a term"
- "if `s` is a term dependent on a variable `x`, then `λ x => s` is a term.

In the case of Lean, the main structure is defined in the `Expr` datatype and supported by other datatypes such as `Level`, `Name` and so on.

#### 2. __Define inference rules__:

"if `s : A → B` and `t : A`, then `s t : B`".
These are often written as `(s : A -> B) (t : A) ⊢ (s $ t :  B)` or as
```
s : A → B
t : A
----------
s t : B
```
Type theory papers have lots of these inference rules.
They define what it means for a term to be well-typed.

The statements that the inference rules talk about are sometimes called __judgements__. For example, in Lean, the main judgements are `Γ ⊢ s : α` for expressions `s` and `α`, and also a 'definitional equality judgement' `Γ ⊢ s ≡ t : α`.
What does the `Γ` do? `Γ` is called a __context__ and consists of an ordered list of typed variables that are in scope. You need to include context for variables, for example if `x` is a variable, then `x : Nat` is not generally true but depends on the type of `x`. So the judgement for typing variables looks like `(Γ, (x : α)) ⊢ x : α`.

[Mario Carneiro's master's thesis](https://github.com/digama0/lean-type-theory/releases/download/v0.21/main.pdf) contains the definitions for the foundations of Lean 3.

Now we have specified the type theory, we need to write a computer program which will be able to construct elements of this type theory and perform reductions on them.

## Making a computer program that can work with a foundation

Lean uses a version of type theory called the _Calculus of Inductive Constructions_ or _CIC_.
Lean has a module called the _kernel_ which checks whether terms are built correctly using the inference rules.
There are a few different ways to write kernels (eg [LCF-style](https://en.wikipedia.org/wiki/Logic_for_Computable_Functions)), but the way that Lean works (I am simplifying here) is with a function `inferType : Expr → LocalContext → Option Expr` which returns the type of the given expression if it type-checks or otherwise `none` if there is an error. If your theorem statement is `P` and you have a proof `p`, Lean will accept your proof if `inferType p ≡ P`.

It is really important that the kernel (ie the `inferType` function) really does follow the inference rules of CIC, because otherwise you might end up proving things that are false or not proving what you think you are proving.
You have to trust the kernel, but once you do trust it, you can prove theorems and know that they are correct (conditional on the kernel not having bugs).

## What does it mean to be meta?

The idea of logic is to construct mathematical structures within which we can do mathematics.
In type theory, the structures are trees of terms which obey the given inference rules.

But in order to construct these objects, we need to do activities that are _outside_ the structure: deciding what type theory to use, writing the code that manipulates trees of terms, applying reductions to terms, parsing strings of text into terms, checking that the inference rules are being applied correctly and so on.
Here I will refer to these as __meta-level__ activities. Anything to do with the mathematics: proving a theorem, writing a definition, defining an inductive type ... is called __object-level__.

In most systems, the meta-level activities are done in a different language to the one that we use to do mathematics. In Isabelle, the meta-level language is ML and Scala. In Coq, it's OCAML. In AGDA it's Haskell. In Lean 4, the meta code is mostly written in Lean itself, with a few components written in C++.

Now, the cool thing about Lean is that it exposes structures within the _object-level_ which can manipulate the _meta-level_.
So for example, there is an inductive type called `Expr`, which just looks like any other inductive type. But if we write an _object-level_ function that manipulates `Expr` in some way, then Lean can compile this to _meta-level_ function that can be used to create proofs. The general term for this is [__reflection__](https://en.wikipedia.org/wiki/Reflective_programming). One often says that we _reflect_ the meta-level stuff to the object-level.

This means that we can write code within Lean that changes how Lean performs its meta-level activities.

Since this meta-level code is not the stuff we are trying to prove, it can sometimes be overly tedious to prove that they are type correct.
For example, we don't care about proving that our `Expr` recursion function is well founded. But in Lean, you get an error if you try to write a recursive function where it can't prove that it will terminate.

Lean relaxes these constraints with trust levels. You can add `unsafe` or `partial` keywords to your declaration to flag that you don't care about soundness for this function. Most of the time in Lean 4, you can write your metaprogramming code without these keywords though, only use them as a last resort.


[Read on to part 1!](01_datatypes.md)
