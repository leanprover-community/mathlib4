/-
Copyright (c) 2024 Charlie Conneen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Conneen
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
import Mathlib.CategoryTheory.Functor.ReflectsIso.FullyFaithful

/-!

# Subobject Classifier

We define what it means for a morphism in a category to be a subobject classifier
as `CategoryTheory.HasClassifier`.

c.f. the following Lean 3 code, where similar work was done:
https://github.com/b-mehta/topos/blob/master/src/subobject_classifier.lean

## Main definitions

Let `C` refer to a category with a terminal object.

* `CategoryTheory.Classifier C` is the data of a subobject classifier in `C`.

* `CategoryTheory.HasClassifier C` says that there is at least one subobject classifier.
  `Ω C` denotes a choice of subobject classifier.

## Main results

* It is a theorem that the truth morphism `⊤_ C ⟶ Ω C` is a (split, and
  therefore regular) monomorphism, simply because its source is the terminal object.

* An instance of `IsRegularMonoCategory C` is exhibited for any category with
  a subobject classifier.

## References

* [S. MacLane and I. Moerdijk, *Sheaves in Geometry and Logic*][MLM92]

## TODO

* Exhibit the equivalence between having a classifier and the functor `B => Subobject B`
  being representable.

* Make API for constructing a subobject classifier without reference to limits (replacing
  `⊤_ C` with an arbitrary `Ω₀ : C` and including the assumption `mono truth`)

-/

universe u v u₀ v₀

open CategoryTheory Category Limits Functor

variable (C : Type u) [Category.{v} C] [HasTerminal C]

namespace CategoryTheory

/-- A morphism `truth : ⊤_ C ⟶ Ω` from the terminal object of a category `C`
is a subobject classifier if, for every monomorphism `m : U ⟶ X` in `C`,
there is a unique map `χ : X ⟶ Ω` such that the following square is a pullback square:
```
      U ---------m----------> X
      |                       |
terminal.from U               χ
      |                       |
      v                       v
    ⊤_ C ------truth--------> Ω
```
An equivalent formulation replaces the object `⊤_ C` with an arbitrary object, and instead
includes the assumption that `truth` is a monomorphism.
-/
structure Classifier where
  /-- The target of the truth morphism -/
  Ω : C
  /-- the truth morphism for a subobject classifier -/
  truth : ⊤_ C ⟶ Ω
  /-- For any monomorphism `U ⟶ X`, there is an associated characteristic map `X ⟶ Ω`. -/
  χ {U X : C} (m : U ⟶ X) [Mono m] : X ⟶ Ω
  /-- `χ m` forms the appropriate pullback square. -/
  isPullback {U X : C} (m : U ⟶ X) [Mono m] : IsPullback m (terminal.from U) (χ m) truth
  /-- `χ m` is the only map `X ⟶ Ω` which forms the appropriate pullback square. -/
  uniq {U X : C} (m : U ⟶ X) [Mono m] (χ' : X ⟶ Ω)
      (hχ' : IsPullback m (terminal.from U) χ' truth) :
    χ' = χ m

/-- A category `C` has a subobject classifier if there is at least one subobject classifier. -/
class HasClassifier : Prop where
  /-- There is some classifier. -/
  exists_classifier : Nonempty (Classifier C)

namespace HasClassifier

variable [HasClassifier C]

noncomputable section

/-- Notation for the object in an arbitrary choice of a subobject classifier -/
abbrev Ω : C := HasClassifier.exists_classifier.some.Ω

/-- Notation for the "truth arrow" in an arbitrary choice of a subobject classifier -/
abbrev truth : ⊤_ C ⟶ Ω C := HasClassifier.exists_classifier.some.truth

variable {C}
variable {U X : C} (m : U ⟶ X) [Mono m]

/-- returns the characteristic morphism of the subobject `(m : U ⟶ X) [Mono m]` -/
def χ : X ⟶ Ω C :=
  HasClassifier.exists_classifier.some.χ m

/-- The diagram
```
      U ---------m----------> X
      |                       |
terminal.from U              χ m
      |                       |
      v                       v
    ⊤_ C -----truth C-------> Ω
```
is a pullback square.
-/
lemma isPullback_χ : IsPullback m (terminal.from U) (χ m) (truth C) :=
  HasClassifier.exists_classifier.some.isPullback m

/-- The diagram
```
      U ---------m----------> X
      |                       |
terminal.from U              χ m
      |                       |
      v                       v
    ⊤_ C -----truth C-------> Ω
```
commutes.
-/
@[reassoc]
lemma comm : m ≫ χ m = terminal.from _ ≫ truth C := (isPullback_χ m).w

/-- `χ m` is the only map for which the associated square
is a pullback square.
-/
lemma unique (χ' : X ⟶ Ω C) (hχ' : IsPullback m (terminal.from _) χ' (truth C)) : χ' = χ m :=
  HasClassifier.exists_classifier.some.uniq m χ' hχ'

/-- `truth C` is a regular monomorphism (because it is split). -/
noncomputable instance truthIsRegularMono : RegularMono (truth C) :=
  RegularMono.ofIsSplitMono (truth C)

/-- The following diagram
```
      U ---------m----------> X
      |                       |
terminal.from U              χ m
      |                       |
      v                       v
    ⊤_ C -----truth C-------> Ω
```
being a pullback for any monic `m` means that every monomorphism
in `C` is the pullback of a regular monomorphism; since regularity
is stable under base change, every monomorphism is regular.
Hence, `C` is a regular mono category.
It also follows that `C` is a balanced category.
-/
instance isRegularMonoCategory : IsRegularMonoCategory C where
  regularMonoOfMono :=
    fun m => ⟨regularOfIsPullbackFstOfRegular (isPullback_χ m).w (isPullback_χ m).isLimit⟩

/-- If the source of a faithful functor has a subobject classifier, the functor reflects
  isomorphisms. This holds for any balanced category.
-/
instance reflectsIsomorphisms (D : Type u₀) [Category.{v₀} D] (F : C ⥤ D) [Functor.Faithful F] :
    Functor.ReflectsIsomorphisms F :=
  reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms F

/-- If the source of a faithful functor is the opposite category of one with a subobject classifier,
  the same holds -- the functor reflects isomorphisms.
-/
instance reflectsIsomorphismsOp (D : Type u₀) [Category.{v₀} D] (F : Cᵒᵖ ⥤ D)
    [Functor.Faithful F] :
    Functor.ReflectsIsomorphisms F :=
  reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms F

end
end CategoryTheory.HasClassifier
