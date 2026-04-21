/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Init
public import Batteries.Util.LibraryNote

/-!
# Documentation concerning the continuous functional calculus

A library note giving advice on developing and using the continuous functional calculus, as well
as the organizational structure within Mathlib.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


library_note «continuous functional calculus» /--
# The continuous functional calculus

In Mathlib, there are two classes --- `NonUnitalContinuousFunctionalCalculus` and
`ContinuousFunctionalCalculus`, indexed by the scalar ring `R` and the predicate `p : A → Prop`
which must be satisfied --- which are used to provide the interface to the continuous functional
calculus. This allows us to reason about the continuous functional calculus in both unital and
non-unital algebras, using functions, `ℂ → ℂ`, `ℝ → ℝ`, or `ℝ≥0 → ℝ≥0`, as appropriate.

These classes are designed to be used even in contexts where no norm is present, such as for
`Matrix n n ℝ`, and indeed, an instance of `ContinuousFunctionalCalculus ℝ A IsSelfAdjoint` already
exists in this context. However, when a norm is present (i.e., in the context of C⋆-algebras), the
continuous functional calculus is an isometry. In order not to lose this information, we provide
two additional classes `IsometricNonUnitalContinuousFunctionalCalculus` and
`IsometricContinuousFunctionalCalculus`, extending the classes above. We encode this as a class
for two reasons:

1. to provide a uniform interface for multiple scalar rings
2. to allow for generalization to real C⋆-algebras

This means that there are twelve different classes, corresponding to the choices of scalar ring
(`ℂ`, `ℝ`, or `ℝ≥0`), unital or non-unital algebras, isometric or not. The relationship between
these is documented in the diagram below, with arrows indicating always available instances.
The dotted arrow requires the presence of instances `PartialOrder A`, `StarOrderedRing A` and
`NonnegSpectrumClass ℝ A`. Note that the instances which change scalar rings occur *within* each
class (i.e., `ContinuousFunctionalCalculus`, `IsometricContinuousFunctionalCalculus`, etc.), so a
more accurate diagram would have the chain on the left embedded within each node of the graph
on the right.

```
┌─────────┐     ┌──────────────────────┐
│         │     │                      │
│ Complex │     │   Isometric unital   ├──────────┐
│         │     │                      │          │
└────┬────┘     └───────────┬──────────┘          │
     │                      │                     │
     │                      │                     │
     ▼                      ▼                     ▼
┌─────────┐     ┌──────────────────────┐     ┌────────┐
│         │     │                      │     │        │
│   Real  │     │ Isometric non-unital │     │ Unital │
│         │     │                      │     │        │
└────┬────┘     └───────────┬──────────┘     └────┬───┘
     :                      │                     │
     :                      │                     │
     ▼                      ▼                     │
┌─────────┐     ┌──────────────────────┐          │
│         │     │                      │          │
│  NNReal │     │      Non-unital      │◄─────────┘
│         │     │                      │
└─────────┘     └──────────────────────┘
```

## Developing general theory

When developing general theory of the continuous functional calculus, users should work in the
appropriate general class. For example, the positive and negative parts of a selfadjoint element
are defined using the continuous functional calculus via the functions `(·⁺ : ℝ → ℝ)` and
`(·⁻ : ℝ → ℝ)`. These functions both take the value `0` at `0`, and so work equally well in the
non-unital setting. Moreover, the only scalar ring needed is `ℝ`, not `ℂ`. Therefore, the correct
context in which to develop the basic theory of positive and negative parts is:

```lean
variable {A : Type*} [NonUnitalRing A] [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
  [StarRing A] [TopologicalSpace A] [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
```

One pattern that should *never* be used is to directly assume `ContinuousFunctionalCalculus`
(or the non-unital version) over the scalar ring `ℝ≥0`. Doing so only complicates the setup, for
no benefit. Indeed, in practice the only available instance of
`ContinuousFunctionalCalculus ℝ≥0 A (0 ≤ ·)` is the one stemming from an instance over `ℝ`, along
with `NonnegSpectrumClass ℝ A`, `PartialOrder A`, `StarOrderedRing A`. Therefore, directly assuming
the `ℝ≥0` version makes Lean do more work in type class inference, and makes the structure of the
source code less readable. Instead, the correct pattern is to assume the version over `ℝ`, and then
add these extra three classes as needed to get the instance over `ℝ≥0`.

There are three questions that an author should ask themselves when developing general theory
in order to determine the correct `variable`s to have in context. These are:

1. Does this work for arbitrary scalar (semi)rings? Only `ℂ`, or is `ℝ` sufficient?

  For arbitrary scalar rings, use `R` with a predicate `p : A → Prop`, and assume that `A` is an
  `R`-algebra. For `ℂ` use `IsStarNormal` and assume `A` is a `ℂ`-algebra. For `ℝ` use
  `IsSelfAdjoint` and assume `A` is an `ℝ`-algebra. Reminder, if you need the functional calculus
  over `ℝ≥0`, simply use the `ℝ` setup with the three extra classes.

2. Does this work in non-unital algebras?

  This determines whether you should use the unital or `NonUnital` variation, and whether your
  algebra should be unital or non-unital.

3. Does this require norm properties of the algebra?

  This determines whether you should use the standard version or the `Isometric` variation.
  If you are not using the `Isometric` variation, you should generally only assume that `A` is a
  `TopologicalSpace` (or potentially a topological algebra). If you are using the `Isometric`
  variation, you should assume that `A` is a `NormedAlgebra` (in the unital case) or a `NormedSpace`
  (in the non-unital case).

Of course, sometimes one needs to have different sections which make different assumptions, even
for the same functions considered. For instance, although theory of positive and negative parts
should be developed in the maximum generality of non-unital `ℝ`-algebras without a norm, certain
results require stronger assumptions. A typical example is that there should be lemmas which
say `cfcₙ (·⁺ : ℝ → ℝ) (1 : A) = 1` and `cfcₙ (·⁻ : ℝ → ℝ) (1 : A) = 0`, but obviously these lemmas
require `A` to be a unital algebra. For these results (which work over `ℝ`, only in unital algebras,
and don't reference the norm), the correct context is (note the unital version of the functional
calculus despite the fact that the lemmas are about `cfcₙ`):

```lean
variable {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A] [TopologicalSpace A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
```

The only context in which general theory should be developed with a `NonUnitalCStarAlgebra` or
`CStarAlgebra` hypothesis is when the norm structure is required and the only scalar ring which
works is `ℂ`.

## Uniqueness

Unless you are developing theory over arbitrary scalar rings, it should never be necessary to
assume `ContinuousMap.UniqueHom` or `ContinuousMapZero.UniqueHom`, despite the fact that these
hypotheses are necessary for certain lemmas (in particular, `cfc_comp`). Over `ℝ` and `ℂ`, this
instance should always be available, and for `ℝ≥0`, one needs only to have the additional
assumptions `T2Space A` and `IsTopologicalRing A` (as before, the algebra `A` should still be an
`ℝ`-algebra).

## Using `autoParam`

Mathlib makes heavy use of `autoParam`s in the continuous functional calculus. There are three
different tactics which are used:

1. `cfc_tac` for proving goals of the form `IsStarNormal a`, `IsSelfAdjoint a` or `0 ≤ a`.
2. `cfc_cont_tac` for proving goals of the form `ContinuousOn (spectrum R a) f`.
3. `cfc_zero_tac` for proving goals of the form `f 0 = 0`.

In general, lemmas about the continuous functional calculus should be written using `autoParam`s
wherever possible for these kinds of goals. These arguments should be placed *last*, at least among
the explicit arguments. Moreover, if the arguments `f` and `a` cannot be inferred from other
explicit arguments (i.e., those which are not `autoParam`s), then they should also be *explicit*
rather than implicit, despite the fact that they appear in the types of the `autoParam` arguments.
The reason is that it is often necessary to supply these arguments in order for the `autoParam`
arguments to fire.

As to argument order, we generally prefer functions before elements of the algebra (i.e., `f` and
then `a`) to match the order of application (i.e., `cfc f a`). Likewise, we generally place the
`autoParam`s for the continuity conditions before the others because these are the most likely to
require manual intervention.

## Location in Mathlib

The criterion for determining where to place files about general theory of functions pertaining to
the continuous functional calculus is whether the import
`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Basic.lean` is needed, which contains
the instances of the continuous functional calculus for `CStarAlgebra`, and therefore pulls in many
imports. If this import is not needed, then the file should be placed in the directory
`Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/`. If this import is needed
then the appropriate location is `Mathlib/Analysis/CStarAlgebra/SpecialFunctions/`.
If, as is often the case, some results need the import and others do not, there should be two files,
one in each location.
-/
