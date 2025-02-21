/-
Copyright (c) 2024 Charlie Conneen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Conneen
-/

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.Tactic.ApplyFun

/-!

# Subobject Classifier

We define what it means for a morphism in a category to be a subobject
classifier as `CategoryTheory.Classifier.IsClassifier`.

## Main definitions

Let `C` refer to a category with a terminal object.

* `CategoryTheory.Classifier.IsClassifier` describes what it means for a
  pair of an object `Ω : C` and a morphism `t : ⊤_ C ⟶ Ω` to be a subobject
  classifier for `C`.

* `CategoryTheory.Classifier.HasClassifier C` is the data of `C` having a
  subobject classifier.

## Main results

* It is a theorem that the truth morphism `⊤_ C ⟶ Ω C` is a (split, and
  therefore regular) monomorphism.

* `Classifier.balanced` shows that any category with a subobject classifier
  is balanced. This follows from the fact that every monomorphism is the
  pullback of a regular monomorphism (the truth morphism).

## Notation

* if `m` is a monomorphism, `χ_ m` denotes characteristic map of `m`,
  which is the corresponding map to the subobject classifier.

## References

* [S. MacLane and I. Moerdijk, *Sheaves in Geometry and Logic*][MLM92]

-/


universe u v u₀ v₀

open CategoryTheory Category Limits Functor

variable {C : Type u} [Category.{v} C] [HasTerminal C]

namespace CategoryTheory.Classifier

/-- A morphism `t : ⊤_ C ⟶ Ω` from the terminal object of a category `C`
is a subobject classifier if, for every monomorphism `m : U ⟶ X` in `C`,
there is a unique map `χ : X ⟶ Ω` such that the following square is a pullback square:
```
      U ---------m----------> X
      |                       |
terminal.from U               χ
      |                       |
      v                       v
    ⊤_ C --------t----------> Ω
```
-/
class IsClassifier {Ω : C} (t : ⊤_ C ⟶ Ω) where
  /-- For any monomorphism `U ⟶ X`, there is exactly one map `X ⟶ Ω`
  making the appropriate square a pullback square. -/
  char {U X : C} (m : U ⟶ X) [Mono m] :
    Unique { χ : X ⟶ Ω // IsPullback m (terminal.from (U : C)) χ t }

variable (C)

/-- A category C has a subobject classifier if there is some object `Ω` such that
a morphism `t : ⊤_ C ⟶ Ω` is a subobject classifier (`CategoryTheory.Classifier.IsClassifier`). -/
class HasClassifier where
  /-- the target of a subobject classifier -/
  Ω : C
  /-- a subobject classifier -/
  t : ⊤_ C ⟶ Ω
  /-- the pair `Ω` and `t` form a subobject classifier -/
  is_classifier : IsClassifier t

variable [HasClassifier C]

/-- shorthand for `HasClassifier.Ω` -/
abbrev Ω : C := HasClassifier.Ω

/-- shorthand for `HasClassifier.t` -/
abbrev t : ⊤_ C ⟶ Ω C := HasClassifier.t

/-- helper definition for destructuring `IsClassifier` -/
def Classifier_IsClassifier : IsClassifier (t C) :=
  HasClassifier.is_classifier

variable {C}
variable {U X : C} (χ : X ⟶ Ω C) (m : U ⟶ X) [Mono m]

/-- returns the characteristic morphism of the subobject `(m : U ⟶ X) [Mono m]` -/
def ClassifierOf : X ⟶ Ω C :=
  ((Classifier_IsClassifier C).char m).default

/-- shorthand for the characteristic morphism, `ClassifierOf m` -/
abbrev χ_ := ClassifierOf m

/-- The diagram
```
      U ---------m----------> X
      |                       |
terminal.from U              χ_ m
      |                       |
      v                       v
    ⊤_ C -------t C---------> Ω
```
is a pullback square.
-/
lemma ClassifierPb : IsPullback m (terminal.from U) (χ_ m) (t C) :=
  ((Classifier_IsClassifier C).char m).default.prop

/-- The diagram
```
      U ---------m----------> X
      |                       |
terminal.from U              χ_ m
      |                       |
      v                       v
    ⊤_ C -------t C---------> Ω
```
commutes.
-/
lemma ClassifierComm : m ≫ (χ_ m) = terminal.from _ ≫ t C := (ClassifierPb m).w

/-- `ClassifierOf m` is the only map for which the associated square
is a pullback square.
-/
lemma unique (χ : X ⟶ Ω C) (hχ : IsPullback m (terminal.from _) χ (t C)) : χ = χ_ m := by
  have h := ((Classifier_IsClassifier C).char m).uniq (Subtype.mk χ hχ)
  apply_fun (fun x => x.val) at h
  assumption

/-- The underlying `PullbackCone` from the pullback diagram. -/
noncomputable def ClassifierCone : PullbackCone (χ_ m) (t C) :=
  PullbackCone.mk m (terminal.from _) (ClassifierComm m)

/-- The underlying `IsLimit` from `ClassifierPb`. -/
noncomputable def ClassifierPullback :
    IsLimit (PullbackCone.mk m (terminal.from _) (ClassifierComm m)) :=
  (ClassifierPb m).isLimit'.some

/-- If a map `g : Z ⟶ X and the following diagram commutes:
```
      Z ---------g----------> X
      |                       |
terminal.from U              χ_ m
      |                       |
      v                       v
    ⊤_ C -------t C---------> Ω
```
then this is shorthand for the lift of `g` to `U`.
-/
noncomputable def ClassifierCone_into {Z : C} (g : Z ⟶ X)
(comm' : g ≫ (χ_ m) = (terminal.from Z ≫ t C)) :
    Z ⟶ U :=
  IsPullback.lift (ClassifierPb m) _ _ comm'

/-- If a map `g : Z ⟶ X and the following diagram commutes:
```
      Z ---------g----------> X
      |                       |
terminal.from U              χ_ m
      |                       |
      v                       v
    ⊤_ C -------t C---------> Ω
```
then `ClassifierCone_into` is the lift of `g` to `U`;
the following is a proof that it is indeed a lift, i.e.
that lift composed with `m` is `g`.
-/
lemma ClassifierCone_into_comm {Z : C} (g : Z ⟶ X) (comm' : g ≫ χ_ m = (terminal.from Z ≫ t C)) :
    ClassifierCone_into (comm' := comm') ≫ m = g :=
  IsPullback.lift_fst (ClassifierPb m) _ _ comm'

end CategoryTheory.Classifier

-- note: linter error caused an issue with `[HasClassifier C]`,
-- requiring namespace split.

namespace CategoryTheory.Classifier

variable (C) [HasClassifier C]

/-- `t C` is a regular monomorphism (because it is split). -/
noncomputable instance truth_is_RegularMono : RegularMono (t C) :=
  RegularMono.ofIsSplitMono (t C)

/-- The following diagram
```
      U ---------m----------> X
      |                       |
terminal.from U              χ_ m
      |                       |
      v                       v
    ⊤_ C -------t C---------> Ω
```
being a pullback for any monic `m` means that every monomorphism
in `C` is the pullback of a regular monomorphism; since regularity
is stable under base change, every monomorphism is regular.
-/
noncomputable instance Mono_is_RegularMono {A B : C} (m : A ⟶ B) [Mono m] : RegularMono m :=
  regularOfIsPullbackFstOfRegular (ClassifierPb m).w (ClassifierPb m).isLimit


/-- A category with a subobject classifier satisfies the condition
that a map which is both monic and epic is an isomorphism.
-/
lemma balanced {A B : C} (f : A ⟶ B) [ef : Epi f] [Mono f] : IsIso f :=
  isIso_of_epi_of_strongMono f

/-- `C` is a balanced category.  -/
instance : Balanced C where
  isIso_of_mono_of_epi := fun f => balanced _ f

/-- Since `C` is balanced, so is `Cᵒᵖ`. -/
instance : Balanced Cᵒᵖ := balanced_opposite

/-- If the source of a faithful functor has a subobject classifier, the functor reflects
  isomorphisms. This holds for any balanced category.
-/
theorem reflectsIsomorphisms (D : Type u₀) [Category.{v₀} D] (F : C ⥤ D) [Functor.Faithful F] :
    Functor.ReflectsIsomorphisms F :=
  reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms F

/-- If the source of a faithful functor is the opposite category of one with a subobject classifier,
  the same holds -- the functor reflects isomorphisms.
-/
theorem reflectsIsomorphismsOp (D : Type u₀) [Category.{v₀} D] (F : Cᵒᵖ ⥤ D) [Functor.Faithful F] :
    Functor.ReflectsIsomorphisms F :=
  reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms F

end CategoryTheory.Classifier
