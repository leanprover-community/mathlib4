/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Eric Wieser
-/
import Std.Util.LibraryNote
import Mathlib.Mathport.Rename

#align_import algebra.hierarchy_design from "leanprover-community/mathlib"@"41cf0cc2f528dd40a8f2db167ea4fb37b8fde7f3"

/-!
# Documentation of the algebraic hierarchy

A library note giving advice on modifying the algebraic hierarchy.
(It is not intended as a "tour".) This is ported directly from the Lean3 version, so may
refer to files/types that currently only exist in mathlib3.

TODO: Add sections about interactions with topological typeclasses, and order typeclasses.

-/


library_note "the algebraic hierarchy"/-- # The algebraic hierarchy

In any theorem proving environment,
there are difficult decisions surrounding the design of the "algebraic hierarchy".

There is a danger of exponential explosion in the number of gadgets,
especially once interactions between algebraic and order/topological/etc structures are considered.

In mathlib, we try to avoid this by only introducing new algebraic typeclasses either
1. when there is "real mathematics" to be done with them, or
2. when there is a meaningful gain in simplicity by factoring out a common substructure.

(As examples, at this point we don't have `Loop`, or `UnitalMagma`,
but we do have `LieSubmodule` and `TopologicalField`!
We also have `GroupWithZero`, as an exemplar of point 2.)

Generally in mathlib we use the extension mechanism (so `CommRing` extends `Ring`)
rather than mixins (e.g. with separate `Ring` and `CommMul` classes),
in part because of the potential blow-up in term sizes described at
https://www.ralfj.de/blog/2019/05/15/typeclasses-exponential-blowup.html
However there is tension here, as it results in considerable duplication in the API,
particularly in the interaction with order structures.

This library note is not intended as a design document
justifying and explaining the history of mathlib's algebraic hierarchy!
Instead it is intended as a developer's guide, for contributors wanting to extend
(either new leaves, or new intermediate classes) the algebraic hierarchy as it exists.

(Ideally we would have both a tour guide to the existing hierarchy,
and an account of the design choices.
See https://arxiv.org/abs/1910.09336 for an overview of mathlib as a whole,
with some attention to the algebraic hierarchy and
https://leanprover-community.github.io/mathlib-overview.html
for a summary of what is in mathlib today.)

## Instances

When adding a new typeclass `Z` to the algebraic hierarchy
one should attempt to add the following constructions and results,
when applicable:

* Instances transferred elementwise to products, like `Prod.Monoid`.
  See `Mathlib.Algebra.Group.Prod` for more examples.
  ```
  instance Prod.Z [Z M] [Z N] : Z (M × N) := ...
  ```
* Instances transferred elementwise to pi types, like `Pi.Monoid`.
  See `Mathlib.Algebra.Group.Pi` for more examples.
  ```
  instance Pi.Z [∀ i, Z $ f i] : Z (Π i : I, f i) := ...
  ```
* Instances transferred to `MulOpposite M`, like `MulOpposite.Monoid`.
  See `Mathlib.Algebra.Opposites` for more examples.
  ```
  instance MulOpposite.Z [Z M] : Z (MulOpposite M) := ...
  ```
* Instances transferred to `ULift M`, like `ULift.Monoid`.
  See `Mathlib.Algebra.Group.ULift` for more examples.
  ```
  instance ULift.Z [Z M] : Z (ULift M) := ...
  ```
* Definitions for transferring the proof fields of instances along
  injective or surjective functions that agree on the data fields,
  like `Function.Injective.monoid` and `Function.Surjective.monoid`.
  We make these definitions `@[reducible]`, see note [reducible non-instances].
  See `Mathlib.Algebra.Group.InjSurj` for more examples.
  ```
  @[reducible]
  def Function.Injective.Z [Z M₂] (f : M₁ → M₂) (hf : f.Injective)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) : Z M₁ := ...

  @[reducible]
  def Function.Surjective.Z [Z M₁] (f : M₁ → M₂) (hf : f.Surjective)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) : Z M₂ := ...
  ```
* Instances transferred elementwise to `Finsupp`s, like `Finsupp.semigroup`.
  See `Mathlib.Data.Finsupp.Pointwise` for more examples.
  ```
  instance FinSupp.Z [Z β] : Z (α →₀ β) := ...
  ```
* Instances transferred elementwise to `Set`s, like `Set.monoid`.
  See `Mathlib.Algebra.Pointwise` for more examples.
  ```
  instance Set.Z [Z α] : Z (Set α) := ...
  ```
* Definitions for transferring the entire structure across an equivalence, like `Equiv.monoid`.
  See `Mathlib.Data.Equiv.TransferInstance` for more examples. See also the `transport` tactic.
  ```
  def Equiv.Z (e : α ≃ β) [Z β] : Z α := ...
  /- When there is a new notion of `Z`-equiv: -/
  def Equiv.ZEquiv (e : α ≃ β) [Z β] : by { letI := Equiv.Z e, exact α ≃Z β } := ...
  ```

## Subobjects

When a new typeclass `Z` adds new data fields,
you should also create a new `SubZ` `structure` with a `carrier` field.

This can be a lot of work; for now try to closely follow the existing examples
(e.g. `Submonoid`, `Subring`, `Subalgebra`).
We would very much like to provide some automation here, but a prerequisite will be making
all the existing APIs more uniform.

If `Z` extends `Y`, then `SubZ` should usually extend `SubY`.

When `Z` adds only new proof fields to an existing structure `Y`,
you should provide instances transferring
`Z α` to `Z (SubY α)`, like `Submonoid.toCommMonoid`.
Typically this is done using the `Function.Injective.Z` definition mentioned above.
```
instance SubY.toZ [Z α] : Z (SubY α) :=
  coe_injective.Z coe ...
```

## Morphisms and equivalences

## Category theory

For many algebraic structures, particularly ones used in representation theory, algebraic geometry,
etc., we also define "bundled" versions, which carry `category` instances.

These bundled versions are usually named by appending `Cat`,
so for example we have `AddCommGroupCat` as a bundled `AddCommGroup`, and `TopCommRingCat`
(which bundles together `CommRing`, `TopologicalSpace`, and `TopologicalRing`).

These bundled versions have many appealing features:
* a uniform notation for morphisms `X ⟶ Y`
* a uniform notation (and definition) for isomorphisms `X ≅ Y`
* a uniform API for subobjects, via the partial order `Subobject X`
* interoperability with unbundled structures, via coercions to `Type`
  (so if `G : AddCommGroupCat`, you can treat `G` as a type,
  and it automatically has an `AddCommGroup` instance)
  and lifting maps `AddCommGroupCat.of G`, when `G` is a type with an `AddCommGroup` instance.

If, for example you do the work of proving that a typeclass `Z` has a good notion of tensor product,
you are strongly encouraged to provide the corresponding `MonoidalCategory` instance
on a bundled version.
This ensures that the API for tensor products is complete, and enables use of general machinery.
Similarly if you prove universal properties, or adjunctions, you are encouraged to state these
using categorical language!

One disadvantage of the bundled approach is that we can only speak of morphisms between
objects living in the same type-theoretic universe.
In practice this is rarely a problem.

# Making a pull request

With so many moving parts, how do you actually go about changing the algebraic hierarchy?

We're still evolving how to handle this, but the current suggestion is:

* If you're adding a new "leaf" class, the requirements are lower,
  and an initial PR can just add whatever is immediately needed.
* A new "intermediate" class, especially low down in the hierarchy,
  needs to be careful about leaving gaps.

In a perfect world, there would be a group of simultaneous PRs that basically cover everything!
(Or at least an expectation that PRs may not be merged immediately while waiting on other
PRs that fill out the API.)

However "perfect is the enemy of good", and it would also be completely reasonable
to add a TODO list in the main module doc-string for the new class,
briefly listing the parts of the API which still need to be provided.
Hopefully this document makes it easy to assemble this list.

Another alternative to a TODO list in the doc-strings is adding Github issues.


-/


library_note "reducible non-instances"/--
Some definitions that define objects of a class cannot be instances, because they have an
explicit argument that does not occur in the conclusion. An example is `Preorder.lift` that has a
function `f : α → β` as an explicit argument to lift a preorder on `β` to a preorder on `α`.

If these definitions are used to define instances of this class *and* this class is an argument to
some other type-class so that type-class inference will have to unfold these instances to check
for definitional equality, then these definitions should be marked `@[reducible]`.

For example, `Preorder.lift` is used to define `Units.Preorder` and `PartialOrder.lift` is used
to define `Units.PartialOrder`. In some cases it is important that type-class inference can
recognize that `Units.Preorder` and `Units.PartialOrder` give rise to the same `LE` instance.
For example, you might have another class that takes `[LE α]` as an argument, and this argument
sometimes comes from `Units.Preorder` and sometimes from `Units.PartialOrder`.
Therefore, `Preorder.lift` and `PartialOrder.lift` are marked `@[reducible]`.
-/
