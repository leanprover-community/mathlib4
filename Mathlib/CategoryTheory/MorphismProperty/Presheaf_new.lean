/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Joël Riou, Ravi Vakil
-/

import Mathlib.CategoryTheory.MorphismProperty.Representable

/-!

# Representable morphisms of presheaves

In this file we define and develop basic results on the representability of morphisms of presheaves.

## Main definitions

* `Presheaf.representable` is a `MorphismProperty` expressing the fact that a morphism `f : F ⟶ G`
  of presheaves is representable, i.e. for any `g : yoneda.obj X ⟶ G`, there exists a pullback
  square of the following form
```
  yoneda.obj Y --yoneda.map snd--> yoneda.obj X
      |                                |
     fst                               g
      |                                |
      v                                v
      F ------------ f --------------> G
```

## API

Given `hf : Presheaf.representable f`, with `f : F ⟶ G` and `g : yoneda.obj X ⟶ G`, we provide:
* `hf.pullback g` which is the object in `C` such that `yoneda.obj (hf.pullback g)` forms a
  pullback square of `f` and `g`.
* `hf.snd g` is the morphism `hf.pullback g ⟶ X`
* `hf.fst g` is the morphism `yoneda.obj (hf.pullback g) ⟶ F`
*  Whenever `f` is of type `yoneda.obj Y ⟶ G`, we also have `hf.fst' g : hf.pullback g ⟶ Y`
which is the preimage under `yoneda` of `hf.fst g`.
* `hom_ext`, `hom_ext'`, `lift`, `lift'` are variants of the universal property of
  `yoneda.obj (hf.pullback g)`, where as much as possible has been formulated internally to `C`.
* `symmetry` and `symmetryIso` are variants of the fact that pullbacks are symmetric for
  representable morphisms, formulated internally to `C`.

-/


namespace CategoryTheory

open Category Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-- A morphism of presheaves `f : F ⟶ G` is representable if for any `X : C`, and any morphism
`g : yoneda.obj X ⟶ G`, there exists a pullback square
```
yoneda.obj Y --yoneda.map snd--> yoneda.obj X
    |                                |
   fst                               g
    |                                |
    v                                v
    F ------------ f --------------> G
``` -/
abbrev Presheaf.representable : MorphismProperty (Cᵒᵖ ⥤ Type v) :=
  yoneda.relativelyRepresentable

namespace Presheaf.representable

section

variable {F G : Cᵒᵖ ⥤ Type v} {f : F ⟶ G} (hf : Presheaf.representable f)
  {Y : C} {f' : yoneda.obj Y ⟶ G} (hf' : Presheaf.representable f')
  {X : C} (g : yoneda.obj X ⟶ G) (hg : Presheaf.representable g)

/-- Given a representable morphism `f' : yoneda.obj Y ⟶ G`, `hf'.fst' g` denotes the preimage of
`hf'.fst g` under yoneda. -/
noncomputable abbrev fst' : hf'.pullback g ⟶ Y :=
  Functor.relativelyRepresentable.fst' Yoneda.fullyFaithful hf' g

lemma map_fst' : yoneda.map (hf'.fst' g) = hf'.fst g :=
  Functor.relativelyRepresentable.map_fst' Yoneda.fullyFaithful hf' g

/-- Variant of the pullback square when the first projection lies in the image of yoneda. -/
lemma isPullback' : IsPullback (yoneda.map (hf'.fst' g)) (yoneda.map (hf'.snd g)) f' g :=
  Functor.relativelyRepresentable.isPullback' Yoneda.fullyFaithful hf' g


@[reassoc]
lemma w' {X Y Z : C} {f : X ⟶ Z} (hf : Presheaf.representable (yoneda.map f)) (g : Y ⟶ Z) :
      hf.fst' (yoneda.map g) ≫ f = hf.snd (yoneda.map g) ≫ g :=
  Functor.relativelyRepresentable.w' Yoneda.fullyFaithful hf g

lemma isPullback_of_map {X Y Z : C} {f : X ⟶ Z} (hf : Presheaf.representable (yoneda.map f))
    (g : Y ⟶ Z) : IsPullback (hf.fst' (yoneda.map g)) (hf.snd (yoneda.map g)) f g :=
  Functor.relativelyRepresentable.isPullback_of_map Yoneda.fullyFaithful hf g

variable {g}

/-- Two morphisms `a b : Z ⟶ hf.pullback g` are equal if
* Their compositions (in `C`) with `hf.snd g : hf.pullback  ⟶ X` are equal.
* The compositions of `yoneda.map a` and `yoneda.map b` with `hf.fst g` are equal. -/
@[ext 100]
lemma hom_ext {Z : C} {a b : Z ⟶ hf.pullback g}
    (h₁ : yoneda.map a ≫ hf.fst g = yoneda.map b ≫ hf.fst g)
    (h₂ : a ≫ hf.snd g = b ≫ hf.snd g) : a = b :=
  Functor.relativelyRepresentable.hom_ext Yoneda.fullyFaithful hf h₁ h₂

/-- In the case of a representable morphism `f' : yoneda.obj Y ⟶ G`, whose codomain lies
in the image of yoneda, we get that two morphism `a b : Z ⟶ hf.pullback g` are equal if
* Their compositions (in `C`) with `hf'.snd g : hf.pullback  ⟶ X` are equal.
* Their compositions (in `C`) with `hf'.fst' g : hf.pullback  ⟶ Y` are equal. -/
@[ext]
lemma hom_ext' {Z : C} {a b : Z ⟶ hf'.pullback g} (h₁ : a ≫ hf'.fst' g = b ≫ hf'.fst' g)
    (h₂ : a ≫ hf'.snd g = b ≫ hf'.snd g) : a = b :=
  Functor.relativelyRepresentable.hom_ext' Yoneda.fullyFaithful hf' h₁ h₂

section

variable {Z : C} (i : yoneda.obj Z ⟶ F) (h : Z ⟶ X) (hi : i ≫ f = yoneda.map h ≫ g)

/-- The lift (in `C`) obtained from the universal property of `yoneda.obj (hf.pullback g)`, in the
case when the cone point is in the image of `yoneda.obj`. -/
noncomputable abbrev lift : Z ⟶ hf.pullback g :=
  Functor.relativelyRepresentable.lift Yoneda.fullyFaithful hf i h hi

@[reassoc (attr := simp)]
lemma lift_fst : yoneda.map (hf.lift i h hi) ≫ hf.fst g = i := by
  apply Functor.relativelyRepresentable.lift_fst

@[reassoc (attr := simp)]
lemma lift_snd : hf.lift i h hi ≫ hf.snd g = h :=
  Functor.relativelyRepresentable.lift_snd Yoneda.fullyFaithful hf i h hi

end

section

variable {Z : C} (i : Z ⟶ Y) (h : Z ⟶ X) (hi : yoneda.map i ≫ f' = yoneda.map h ≫ g)

/-- Variant of `lift` in the case when the domain of `f` lies in the image of `yoneda.obj`. Thus,
in this case, one can obtain the lift directly by giving two morphisms in `C`. -/
noncomputable abbrev lift' : Z ⟶ hf'.pullback g :=
  Functor.relativelyRepresentable.lift' Yoneda.fullyFaithful hf' i h hi

@[reassoc (attr := simp)]
lemma lift'_fst : hf'.lift' i h hi ≫ hf'.fst' g = i :=
  Functor.relativelyRepresentable.lift'_fst Yoneda.fullyFaithful hf' i h hi

@[reassoc (attr := simp)]
lemma lift'_snd : hf'.lift' i h hi ≫ hf'.snd g = h :=
  Functor.relativelyRepresentable.lift'_snd Yoneda.fullyFaithful hf' i h hi

end

/-- Given two representable morphisms `f' : yoneda.obj Y ⟶ G` and `g : yoneda.obj X ⟶ G`, we
obtain an isomorphism `hf'.pullback g ⟶ hg.pullback f'`. -/
noncomputable abbrev symmetry : hf'.pullback g ⟶ hg.pullback f' :=
  Functor.relativelyRepresentable.symmetry Yoneda.fullyFaithful hf' hg

@[reassoc (attr := simp)]
lemma symmetry_fst : hf'.symmetry hg ≫ hg.fst' f' = hf'.snd g :=
  Functor.relativelyRepresentable.symmetry_fst Yoneda.fullyFaithful hf' hg

@[reassoc (attr := simp)]
lemma symmetry_snd : hf'.symmetry hg ≫ hg.snd f' = hf'.fst' g :=
  Functor.relativelyRepresentable.symmetry_snd Yoneda.fullyFaithful hf' hg

@[reassoc (attr := simp)]
lemma symmetry_symmetry : hf'.symmetry hg ≫ hg.symmetry hf' = 𝟙 _ :=
  Functor.relativelyRepresentable.symmetry_symmetry Yoneda.fullyFaithful hf' hg

/-- The isomorphism given by `Presheaf.representable.symmetry`. -/
@[simps!]
noncomputable abbrev symmetryIso : hf'.pullback g ≅ hg.pullback f' :=
  Functor.relativelyRepresentable.symmetryIso Yoneda.fullyFaithful hf' hg

end

end Presheaf.representable

end CategoryTheory
