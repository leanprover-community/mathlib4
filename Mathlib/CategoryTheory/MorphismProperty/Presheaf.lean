/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Joël Riou, Ravi Vakil
-/

import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!

# Representable morphisms of presheaves

In this file we define and develop basic results on the representability of morphisms of presheaves.

## Main definitions

* `Presheaf.representable` is a `MorphismProperty` expressing the fact that a morphism of presheaves
  is representable.
* `MorphismProperty.presheaf`: given a `P : MorphismProperty C`, we say that a morphism of
  presheaves `f : F ⟶ G` satisfies `P.presheaf` if it is representable, and the property `P`
  holds for the preimage under yoneda of pullbacks of `f` by morphisms `g : yoneda.obj X ⟶ G`.

## API

## Main results

* `representable_isMultiplicative`: The class of representable morphisms is multiplicative.
* `representable_stableUnderBaseChange`: Being representable is stable under base change.
* `representable_of_isIso`: Isomorphisms are representable

* `presheaf_yoneda_map`: If `f : X ⟶ Y` satisfies `P`, and `P` is stable under compostions,
  then `yoneda.map f` satisfies `P.presheaf`.

* `presheaf_stableUnderBaseChange`: `P.presheaf` is stable under base change
* `presheaf_respectsIso`: `P.presheaf` respects isomorphisms
* `presheaf_isStableUnderComposition`: If `P` is stable under composition, then so is `P.presheaf`
* `presheaf_isMultiplicative`: If `P` is multiplicative and respects isos, so is `P.presheaf`

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
def Presheaf.representable : MorphismProperty (Cᵒᵖ ⥤ Type v) :=
  fun F G f ↦ ∀ ⦃X : C⦄ (g : yoneda.obj X ⟶ G), ∃ (Y : C) (snd : Y ⟶ X)
    (fst : yoneda.obj Y ⟶ F), IsPullback fst (yoneda.map snd) f g

namespace Presheaf.representable

section

variable {F G : Cᵒᵖ ⥤ Type v} {f : F ⟶ G} (hf : Presheaf.representable f)
  {Y : C} {f' : yoneda.obj Y ⟶ G} (hf' : Presheaf.representable f')
  {X : C} (g : yoneda.obj X ⟶ G) (hg : Presheaf.representable g)

/-- Let `f : F ⟶ G` be a representable morphism in the category of presheaves of types on
a category `C`. Then, for any `g : yoneda.obj X ⟶ G`, `hf.pullback g` denotes the (choice of) a
corresponding object in `C` such that `yoneda.obj (hf.pullback g)` forms a categorical pullback
of `f` and `g` in the category of presheaves. -/
noncomputable def pullback : C :=
  (hf g).choose

/-- Given a representable morphism `f : F ⟶ G`, then for any `g : yoneda.obj X ⟶ G`, `hf.snd g`
denotes the morphism in `C` whose image under `yoneda` is the second projection in the choice of a
pullback square given by the defining property of `f` being representable. -/
noncomputable abbrev snd : hf.pullback g ⟶ X :=
  (hf g).choose_spec.choose

/-- Given a representable morphism `f : F ⟶ G`, then for any `g : yoneda.obj X ⟶ G`, `hf.fst g`
denotes the first projection in the choice of a pullback square given by the defining property of
`f` being representable. -/
noncomputable abbrev fst : yoneda.obj (hf.pullback g) ⟶ F :=
  (hf g).choose_spec.choose_spec.choose

/-- Given a representable morphism `f' : yoneda.obj Y ⟶ G`, `hf'.fst' g` denotes the preimage of
`hf'.fst g` under yoneda. -/
noncomputable abbrev fst' : hf'.pullback g ⟶ Y :=
  Yoneda.fullyFaithful.preimage (hf'.fst g)

lemma yoneda_map_fst' : yoneda.map (hf'.fst' g) = hf'.fst g :=
  Functor.FullyFaithful.map_preimage _ _

lemma isPullback : IsPullback (hf.fst g) (yoneda.map (hf.snd g)) f g :=
  (hf g).choose_spec.choose_spec.choose_spec

@[reassoc]
lemma w : hf.fst g ≫ f = yoneda.map (hf.snd g) ≫ g := (hf.isPullback g).w

/-- Variant of the pullback square when the first projection lies in the image of yoneda. -/
lemma isPullback' : IsPullback (yoneda.map (hf'.fst' g)) (yoneda.map (hf'.snd g)) f' g :=
  (hf'.yoneda_map_fst' _) ▸ (hf' g).choose_spec.choose_spec.choose_spec

@[reassoc]
lemma w' {X Y Z : C} {f : X ⟶ Z}
    (hf : Presheaf.representable (yoneda.map f)) (g : Y ⟶ Z) :
      hf.fst' (yoneda.map g) ≫ f = hf.snd (yoneda.map g) ≫ g :=
  yoneda.map_injective <| by simp [(hf.w (yoneda.map g))]

lemma isPullback_of_yoneda_map {X Y Z : C} {f : X ⟶ Z}
    (hf : Presheaf.representable (yoneda.map f)) (g : Y ⟶ Z) :
    IsPullback (hf.fst' (yoneda.map g)) (hf.snd (yoneda.map g)) f g :=
  IsPullback.of_map yoneda (hf.w' g) (hf.isPullback' (yoneda.map g))

variable {g}

/-- Two morphisms `a b : Z ⟶ hf.pullback g` are equal if
* Their compositions (in `C`) with `hf.snd g : hf.pullback  ⟶ X` are equal.
* The compositions of `yoneda.map a` and `yoneda.map b` with `hf.fst g` are equal. -/
@[ext 100]
lemma hom_ext {Z : C} {a b : Z ⟶ hf.pullback g}
    (h₁ : yoneda.map a ≫ hf.fst g = yoneda.map b ≫ hf.fst g)
    (h₂ : a ≫ hf.snd g = b ≫ hf.snd g) : a = b :=
  yoneda.map_injective <|
    PullbackCone.IsLimit.hom_ext (hf.isPullback g).isLimit h₁ (by simpa using yoneda.congr_map h₂)

/-- In the case of a representable morphism `f' : yoneda.obj Y ⟶ G`, whose codomain lies
in the image of yoneda, we get that two morphism `a b : Z ⟶ hf.pullback g` are equal if
* Their compositions (in `C`) with `hf'.snd g : hf.pullback  ⟶ X` are equal.
* Their compositions (in `C`) with `hf'.fst' g : hf.pullback  ⟶ Y` are equal. -/
@[ext]
lemma hom_ext' {Z : C} {a b : Z ⟶ hf'.pullback g} (h₁ : a ≫ hf'.fst' g = b ≫ hf'.fst' g)
    (h₂ : a ≫ hf'.snd g = b ≫ hf'.snd g) : a = b :=
  hf'.hom_ext (by simpa [yoneda_map_fst'] using yoneda.congr_map h₁) h₂

section

variable {Z : C} (i : yoneda.obj Z ⟶ F) (h : Z ⟶ X) (hi : i ≫ f = yoneda.map h ≫ g)

/-- The lift (in `C`) obtained from the universal property of `yoneda.obj (hf.pullback g)`, in the
case when the cone point is in the image of `yoneda.obj`. -/
noncomputable def lift : Z ⟶ hf.pullback g :=
  Yoneda.fullyFaithful.preimage <| PullbackCone.IsLimit.lift (hf.isPullback g).isLimit _ _ hi

@[reassoc (attr := simp)]
lemma lift_fst : yoneda.map (hf.lift i h hi) ≫ hf.fst g = i := by
  simpa [lift] using PullbackCone.IsLimit.lift_fst _ _ _ _


@[reassoc (attr := simp)]
lemma lift_snd : hf.lift i h hi ≫ hf.snd g = h :=
  yoneda.map_injective <| by simpa [lift] using PullbackCone.IsLimit.lift_snd _ _ _ _

end

section

variable {Z : C} (i : Z ⟶ Y) (h : Z ⟶ X) (hi : (yoneda.map i) ≫ f' = yoneda.map h ≫ g)

/-- Variant of `lift` in the case when the domain of `f` lies in the image of `yoneda.obj`. Thus,
in this case, one can obtain the lift directly by giving two morphisms in `C`. -/
noncomputable def lift' : Z ⟶ hf'.pullback g := hf'.lift _ _ hi

@[reassoc (attr := simp)]
lemma lift'_fst : hf'.lift' i h hi ≫ hf'.fst' g = i :=
  yoneda.map_injective (by simp [yoneda_map_fst', lift'])

@[reassoc (attr := simp)]
lemma lift'_snd : hf'.lift' i h hi ≫ hf'.snd g = h := by
  simp [lift']

end

/-- Given two representable morphisms `f' : yoneda.obj Y ⟶ G` and `g : yoneda.obj X ⟶ G`, we
obtain an isomorphism `hf'.pullback g ⟶ hg.pullback f'`. -/
noncomputable def symmetry : hf'.pullback g ⟶ hg.pullback f' :=
  hg.lift' (hf'.snd g) (hf'.fst' g) (hf'.isPullback' _).w.symm

@[reassoc (attr := simp)]
lemma symmetry_fst : hf'.symmetry hg ≫ hg.fst' f' = hf'.snd g := by simp [symmetry]

@[reassoc (attr := simp)]
lemma symmetry_snd : hf'.symmetry hg ≫ hg.snd f' = hf'.fst' g := by simp [symmetry]

@[reassoc (attr := simp)]
lemma symmetry_symmetry : hf'.symmetry hg ≫ hg.symmetry hf' = 𝟙 _ := by aesop_cat

/-- The isomorphism given by `Presheaf.representable.symmetry`. -/
@[simps]
noncomputable def symmetryIso : hf'.pullback g ≅ hg.pullback f' where
  hom := hf'.symmetry hg
  inv := hg.symmetry hf'

instance : IsIso (hf'.symmetry hg) :=
  (hf'.symmetryIso hg).isIso_hom

end

end Presheaf.representable

end CategoryTheory
