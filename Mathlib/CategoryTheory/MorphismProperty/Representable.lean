/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Joël Riou, Ravi Vakil
-/

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

/-!

# Representable morphisms of presheaves

In this file we define and develop basic results on the representability of morphisms of presheaves.

## Main definitions

* `relativelyRepresentable` is a `MorphismProperty` expressing the fact that a morphism `f : F ⟶ G`
  of presheaves is representable, i.e. for any `g : F.obj X ⟶ G`, there exists a pullback
  square of the following form
```
  F.obj Y --F.map snd--> F.obj X
      |                                |
     fst                               g
      |                                |
      v                                v
      F ------------ f --------------> G
```

## API

Given `hf : relativelyRepresentable f`, with `f : F ⟶ G` and `g : F.obj X ⟶ G`, we provide:
* `hf.pullback g` which is the object in `C` such that `F.obj (hf.pullback g)` forms a
  pullback square of `f` and `g`.
* `hf.snd g` is the morphism `hf.pullback g ⟶ X`
* `hf.fst g` is the morphism `F.obj (hf.pullback g) ⟶ F`
*  Whenever `f` is of type `F.obj Y ⟶ G`, we also have `hf.fst' g : hf.pullback g ⟶ Y`
which is the preimage under `yoneda` of `hf.fst g`.
* `hom_ext`, `hom_ext'`, `lift`, `lift'` are variants of the universal property of
  `F.obj (hf.pullback g)`, where as much as possible has been formulated internally to `C`.
* `symmetry` and `symmetryIso` are variants of the fact that pullbacks are symmetric for
  representable morphisms, formulated internally to `C`.

-/

namespace CategoryTheory

open Category Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

def Functor.relativelyRepresentable : MorphismProperty D :=
  fun X Y f ↦ ∀ ⦃a : C⦄ (g : F.obj a ⟶ Y), ∃ (b : C) (snd : b ⟶ a)
    (fst : F.obj b ⟶ X), IsPullback fst (F.map snd) f g

namespace Functor.relativelyRepresentable

section

variable {F}
variable (hF : FullyFaithful F) {X Y : D} {f : X ⟶ Y} (hf : F.relativelyRepresentable f)
  {b : C} {f' : F.obj b ⟶ Y} (hf' : F.relativelyRepresentable f')
  {a : C} (g : F.obj a ⟶ Y) (hg : F.relativelyRepresentable g)

/-- Let `f : F ⟶ G` be a representable morphism in the category of presheaves of types on
a category `C`. Then, for any `g : F.obj X ⟶ G`, `hf.pullback g` denotes the (choice of) a
corresponding object in `C` such that `F.obj (hf.pullback g)` forms a categorical pullback
of `f` and `g` in the category of presheaves. -/
noncomputable def pullback : C :=
  (hf g).choose

/-- Given a representable morphism `f : F ⟶ G`, then for any `g : F.obj X ⟶ G`, `hf.snd g`
denotes the morphism in `C` whose image under `yoneda` is the second projection in the choice of a
pullback square given by the defining property of `f` being representable. -/
noncomputable abbrev snd : hf.pullback g ⟶ a :=
  (hf g).choose_spec.choose

/-- Given a representable morphism `f : F ⟶ G`, then for any `g : F.obj X ⟶ G`, `hf.fst g`
denotes the first projection in the choice of a pullback square given by the defining property of
`f` being representable. -/
noncomputable abbrev fst : F.obj (hf.pullback g) ⟶ X :=
  (hf g).choose_spec.choose_spec.choose

/-- Given a representable morphism `f' : F.obj Y ⟶ G`, `hf'.fst' g` denotes the preimage of
`hf'.fst g` under yoneda. -/
noncomputable abbrev fst' : hf'.pullback g ⟶ b :=
  hF.preimage (hf'.fst g)

lemma map_fst' : F.map (hf'.fst' hF g) = hf'.fst g :=
  hF.map_preimage _

lemma isPullback : IsPullback (hf.fst g) (F.map (hf.snd g)) f g :=
  (hf g).choose_spec.choose_spec.choose_spec

@[reassoc]
lemma w : hf.fst g ≫ f = F.map (hf.snd g) ≫ g := (hf.isPullback g).w

/-- Variant of the pullback square when the first projection lies in the image of yoneda. -/
lemma isPullback' : IsPullback (F.map (hf'.fst' hF g)) (F.map (hf'.snd g)) f' g :=
  (hf'.map_fst' hF _) ▸ hf'.isPullback g

@[reassoc]
lemma w' {X Y Z : C} {f : X ⟶ Z} (hf : F.relativelyRepresentable (F.map f)) (g : Y ⟶ Z) :
      hf.fst' hF (F.map g) ≫ f = hf.snd (F.map g) ≫ g :=
  hF.map_injective <| by simp [(hf.w (F.map g))]

lemma isPullback_of_map {X Y Z : C} {f : X ⟶ Z} (hf : F.relativelyRepresentable (F.map f))
    (g : Y ⟶ Z) [ReflectsLimit (cospan f g) F] :
    IsPullback (hf.fst' hF (F.map g)) (hf.snd (F.map g)) f g :=
  IsPullback.of_map F (hf.w' hF g) (hf.isPullback' hF (F.map g))

variable {g}

include hF in
/-- Two morphisms `a b : Z ⟶ hf.pullback g` are equal if
* Their compositions (in `C`) with `hf.snd g : hf.pullback  ⟶ X` are equal.
* The compositions of `F.map a` and `F.map b` with `hf.fst g` are equal. -/
@[ext 100]
lemma hom_ext {Z : C} {a b : Z ⟶ hf.pullback g} (h₁ : F.map a ≫ hf.fst g = F.map b ≫ hf.fst g)
    (h₂ : a ≫ hf.snd g = b ≫ hf.snd g) : a = b :=
  hF.map_injective <|
    PullbackCone.IsLimit.hom_ext (hf.isPullback g).isLimit h₁ (by simpa using F.congr_map h₂)

/-- In the case of a representable morphism `f' : F.obj Y ⟶ G`, whose codomain lies
in the image of yoneda, we get that two morphism `a b : Z ⟶ hf.pullback g` are equal if
* Their compositions (in `C`) with `hf'.snd g : hf.pullback  ⟶ X` are equal.
* Their compositions (in `C`) with `hf'.fst' g : hf.pullback  ⟶ Y` are equal. -/
@[ext]
lemma hom_ext' {Z : C} {a b : Z ⟶ hf'.pullback g} (h₁ : a ≫ hf'.fst' hF g = b ≫ hf'.fst' hF g)
    (h₂ : a ≫ hf'.snd g = b ≫ hf'.snd g) : a = b :=
  hf'.hom_ext hF (by simpa [map_fst'] using F.congr_map h₁) h₂

section

variable {c : C} (i : F.obj c ⟶ X) (h : c ⟶ a) (hi : i ≫ f = F.map h ≫ g)

/-- The lift (in `C`) obtained from the universal property of `yoneda.obj (hf.pullback g)`, in the
case when the cone point is in the image of `yoneda.obj`. -/
noncomputable def lift : c ⟶ hf.pullback g :=
  hF.preimage <| PullbackCone.IsLimit.lift (hf.isPullback g).isLimit _ _ hi

@[reassoc (attr := simp)]
lemma lift_fst : F.map (hf.lift hF i h hi) ≫ hf.fst g = i := by
  simpa [lift] using PullbackCone.IsLimit.lift_fst _ _ _ _

@[reassoc (attr := simp)]
lemma lift_snd : hf.lift hF i h hi ≫ hf.snd g = h :=
  hF.map_injective <| by simpa [lift] using PullbackCone.IsLimit.lift_snd _ _ _ _

end

section

variable {c : C} (i : c ⟶ b) (h : c ⟶ a) (hi : F.map i ≫ f' = F.map h ≫ g)

/-- Variant of `lift` in the case when the domain of `f` lies in the image of `yoneda.obj`. Thus,
in this case, one can obtain the lift directly by giving two morphisms in `C`. -/
noncomputable def lift' : c ⟶ hf'.pullback g := hf'.lift hF _ _ hi

@[reassoc (attr := simp)]
lemma lift'_fst : hf'.lift' hF i h hi ≫ hf'.fst' hF g = i :=
  hF.map_injective (by simp [map_fst' hF, lift'])

@[reassoc (attr := simp)]
lemma lift'_snd : hf'.lift' hF i h hi ≫ hf'.snd g = h := by
  simp [lift']

end

/-- Given two representable morphisms `f' : yoneda.obj Y ⟶ G` and `g : yoneda.obj X ⟶ G`, we
obtain an isomorphism `hf'.pullback g ⟶ hg.pullback f'`. -/
noncomputable def symmetry : hf'.pullback g ⟶ hg.pullback f' :=
  hg.lift' hF (hf'.snd g) (hf'.fst' hF g) (hf'.isPullback' hF _).w.symm

@[reassoc (attr := simp)]
lemma symmetry_fst : hf'.symmetry hF hg ≫ hg.fst' hF f' = hf'.snd g := by simp [symmetry]

@[reassoc (attr := simp)]
lemma symmetry_snd : hf'.symmetry hF hg ≫ hg.snd f' = hf'.fst' hF g := by simp [symmetry]

@[reassoc (attr := simp)]
lemma symmetry_symmetry : hf'.symmetry hF hg ≫ hg.symmetry hF hf' = 𝟙 _ :=
  hom_ext' hF hf' (by simp) (by simp)

/-- The isomorphism given by `Presheaf.representable.symmetry`. -/
@[simps]
noncomputable def symmetryIso : hf'.pullback g ≅ hg.pullback f' where
  hom := hf'.symmetry hF hg
  inv := hg.symmetry hF hf'

instance : IsIso (hf'.symmetry hF hg) :=
  (hf'.symmetryIso hF hg).isIso_hom

end

end Functor.relativelyRepresentable

end CategoryTheory
