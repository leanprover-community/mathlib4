/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Joël Riou, Ravi Vakil
-/

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

/-!

# Relatively representable morphisms

In this file we define and develop basic results about relatively representable morphisms.

Classically, a morphism `f : X ⟶ Y` of presheaves is said to be representable if for any morphism
`g : yoneda.obj X ⟶ G`, there exists a pullback square of the following form
```
  yoneda.obj Y --yoneda.map snd--> yoneda.obj X
      |                                |
     fst                               g
      |                                |
      v                                v
      F ------------ f --------------> G
```

In this file, we define a notion of relative representability which works with respect to any
functor, and not just `yoneda`. The fact that a morphism `f : F ⟶ G` between presheaves is
representable in the classical case will then be given by `yoneda.relativelyRepresentable f`.



## Main definitions
Throughout this file, `F : C ⥤ D` is a functor between categories `C` and `D`.

* We define `relativelyRepresentable` as a `MorphsimProperty`. A morphism `f : X ⟶ Y` in `D` is
  said to be relatively representable if for any `g : F.obj a ⟶ Y`, there exists a pullback square
  of the following form
```
  F.obj b --F.map snd--> F.obj a
      |                     |
     fst                    g
      |                     |
      v                     v
      X ------- f --------> Y
```

## API

Given `hf : relativelyRepresentable f`, with `f : X ⟶ Y` and `g : F.obj a ⟶ Y`, we provide:
* `hf.pullback g` which is the object in `C` such that `F.obj (hf.pullback g)` is a
  pullback of `f` and `g`.
* `hf.snd g` is the morphism `hf.pullback g ⟶ F.obj a`
* `hf.fst g` is the morphism `F.obj (hf.pullback g) ⟶ X`
*  If `F` is full, and `f` is of type `F.obj c ⟶ G`, we also have `hf.fst' g : hf.pullback g ⟶ X`
which is the preimage under `F` of `hf.fst g`.
* `hom_ext`, `hom_ext'`, `lift`, `lift'` are variants of the universal property of
  `F.obj (hf.pullback g)`, where as much as possible has been formulated internally to `C`.
  For these theorems we also need that `F` is full and/or faithful.
* `symmetry` and `symmetryIso` are variants of the fact that pullbacks are symmetric for
  representable morphisms, formulated internally to `C`. We assume that `F` is fully faithful here.

-/

namespace CategoryTheory

open Category Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

/-- A morphism `f : X ⟶ Y` in `D` is said to be relatively representable if for any
`g : F.obj a ⟶ Y`, there exists a pullback square of the following form
```
F.obj b --F.map snd--> F.obj a
    |                     |
   fst                    g
    |                     |
    v                     v
    X ------- f --------> Y
```
-/
def Functor.relativelyRepresentable : MorphismProperty D :=
  fun X Y f ↦ ∀ ⦃a : C⦄ (g : F.obj a ⟶ Y), ∃ (b : C) (snd : b ⟶ a)
    (fst : F.obj b ⟶ X), IsPullback fst (F.map snd) f g

namespace Functor.relativelyRepresentable

section

variable {F}
variable {X Y : D} {f : X ⟶ Y} (hf : F.relativelyRepresentable f)
  {b : C} {f' : F.obj b ⟶ Y} (hf' : F.relativelyRepresentable f')
  {a : C} (g : F.obj a ⟶ Y) (hg : F.relativelyRepresentable g)

/-- Let `f : X ⟶ Y` be a relatively representable morphism in `D`. Then, for any
`g : F.obj a ⟶ Y`, `hf.pullback g` denotes the (choice of) a corresponding object in `C` such that
there is a pullback square of the following form
```
hf.pullback g --F.map snd--> F.obj a
    |                          |
   fst                         g
    |                          |
    v                          v
    X ---------- f ----------> Y
``` -/
noncomputable def pullback : C :=
  (hf g).choose

/-- Given a representable morphism `f : X ⟶ Y`, then for any `g : F.obj a ⟶ Y`, `hf.snd g`
denotes the morphism in `C` giving rise to the following diagram
```
hf.pullback g --F.map (hf.snd g)--> F.obj a
    |                                 |
   fst                                g
    |                                 |
    v                                 v
    X -------------- f -------------> Y
``` -/
noncomputable abbrev snd : hf.pullback g ⟶ a :=
  (hf g).choose_spec.choose

/-- Given a relatively representable morphism `f : X ⟶ Y`, then for any `g : F.obj a ⟶ Y`,
`hf.fst g` denotes the first projection in the following diagram, given by the defining property
of `f` being relatively representable
```
hf.pullback g --F.map (hf.snd g)--> F.obj a
    |                                 |
hf.fst g                              g
    |                                 |
    v                                 v
    X -------------- f -------------> Y
``` -/
noncomputable abbrev fst : F.obj (hf.pullback g) ⟶ X :=
  (hf g).choose_spec.choose_spec.choose

/-- When `F` is full, given a representable morphism `f' : F.obj b ⟶ Y`, then `hf'.fst' g` denotes
the preimage of `hf'.fst g` under `F`. -/
noncomputable abbrev fst' [Full F] : hf'.pullback g ⟶ b :=
  F.preimage (hf'.fst g)

lemma map_fst' [Full F] : F.map (hf'.fst' g) = hf'.fst g :=
  F.map_preimage _

lemma isPullback : IsPullback (hf.fst g) (F.map (hf.snd g)) f g :=
  (hf g).choose_spec.choose_spec.choose_spec

@[reassoc]
lemma w : hf.fst g ≫ f = F.map (hf.snd g) ≫ g := (hf.isPullback g).w

/-- Variant of the pullback square when `F` is full, and given `f' : F.obj b ⟶ Y`. -/
lemma isPullback' [Full F] : IsPullback (F.map (hf'.fst' g)) (F.map (hf'.snd g)) f' g :=
  (hf'.map_fst' _) ▸ hf'.isPullback g

@[reassoc]
lemma w' {X Y Z : C} {f : X ⟶ Z} (hf : F.relativelyRepresentable (F.map f)) (g : Y ⟶ Z)
    [Full F] [Faithful F] : hf.fst' (F.map g) ≫ f = hf.snd (F.map g) ≫ g :=
  F.map_injective <| by simp [(hf.w (F.map g))]

lemma isPullback_of_map {X Y Z : C} {f : X ⟶ Z} (hf : F.relativelyRepresentable (F.map f))
    (g : Y ⟶ Z) [Full F] [Faithful F] :
    IsPullback (hf.fst' (F.map g)) (hf.snd (F.map g)) f g :=
  IsPullback.of_map F (hf.w' g) (hf.isPullback' (F.map g))

variable {g}

/-- Two morphisms `a b : c ⟶ hf.pullback g` are equal if
* Their compositions (in `C`) with `hf.snd g : hf.pullback  ⟶ X` are equal.
* The compositions of `F.map a` and `F.map b` with `hf.fst g` are equal. -/
@[ext 100]
lemma hom_ext [Faithful F] {c : C} {a b : c ⟶ hf.pullback g}
    (h₁ : F.map a ≫ hf.fst g = F.map b ≫ hf.fst g)
    (h₂ : a ≫ hf.snd g = b ≫ hf.snd g) : a = b :=
  F.map_injective <|
    PullbackCone.IsLimit.hom_ext (hf.isPullback g).isLimit h₁ (by simpa using F.congr_map h₂)

/-- In the case of a representable morphism `f' : F.obj Y ⟶ G`, whose codomain lies
in the image of `F`, we get that two morphism `a b : Z ⟶ hf.pullback g` are equal if
* Their compositions (in `C`) with `hf'.snd g : hf.pullback  ⟶ X` are equal.
* Their compositions (in `C`) with `hf'.fst' g : hf.pullback  ⟶ Y` are equal. -/
@[ext]
lemma hom_ext' [Full F] [Faithful F] {c : C} {a b : c ⟶ hf'.pullback g}
    (h₁ : a ≫ hf'.fst' g = b ≫ hf'.fst' g)
    (h₂ : a ≫ hf'.snd g = b ≫ hf'.snd g) : a = b :=
  hf'.hom_ext (by simpa [map_fst'] using F.congr_map h₁) h₂

section

variable {c : C} (i : F.obj c ⟶ X) (h : c ⟶ a) (hi : i ≫ f = F.map h ≫ g)

/-- The lift (in `C`) obtained from the universal property of `F.obj (hf.pullback g)`, in the
case when the cone point is in the image of `F.obj`. -/
noncomputable def lift [Full F] : c ⟶ hf.pullback g :=
  F.preimage <| PullbackCone.IsLimit.lift (hf.isPullback g).isLimit _ _ hi

@[reassoc (attr := simp)]
lemma lift_fst [Full F] : F.map (hf.lift i h hi) ≫ hf.fst g = i := by
  simpa [lift] using PullbackCone.IsLimit.lift_fst _ _ _ _

@[reassoc (attr := simp)]
lemma lift_snd [Full F] [Faithful F] : hf.lift i h hi ≫ hf.snd g = h :=
  F.map_injective <| by simpa [lift] using PullbackCone.IsLimit.lift_snd _ _ _ _

end

section

variable {c : C} (i : c ⟶ b) (h : c ⟶ a) (hi : F.map i ≫ f' = F.map h ≫ g)

/-- Variant of `lift` in the case when the domain of `f` lies in the image of `F.obj`. Thus,
in this case, one can obtain the lift directly by giving two morphisms in `C`. -/
noncomputable def lift' [Full F] : c ⟶ hf'.pullback g := hf'.lift _ _ hi

@[reassoc (attr := simp)]
lemma lift'_fst [Full F] [Faithful F] : hf'.lift' i h hi ≫ hf'.fst' g = i :=
  F.map_injective (by simp [map_fst', lift'])

@[reassoc (attr := simp)]
lemma lift'_snd [Full F] [Faithful F] : hf'.lift' i h hi ≫ hf'.snd g = h := by
  simp [lift']

end

/-- Given two representable morphisms `f' : F.obj b ⟶ Y` and `g : F.obj a ⟶ Y`, we
obtain an isomorphism `hf'.pullback g ⟶ hg.pullback f'`. -/
noncomputable def symmetry [Full F] : hf'.pullback g ⟶ hg.pullback f' :=
  hg.lift' (hf'.snd g) (hf'.fst' g) (hf'.isPullback' _).w.symm

@[reassoc (attr := simp)]
lemma symmetry_fst [Full F] [Faithful F] : hf'.symmetry hg ≫ hg.fst' f' = hf'.snd g := by
  simp [symmetry]

@[reassoc (attr := simp)]
lemma symmetry_snd [Full F] [Faithful F] : hf'.symmetry hg ≫ hg.snd f' = hf'.fst' g := by
  simp [symmetry]

@[reassoc (attr := simp)]
lemma symmetry_symmetry [Full F] [Faithful F] : hf'.symmetry hg ≫ hg.symmetry hf' = 𝟙 _ :=
  hom_ext' hf' (by simp) (by simp)

/-- The isomorphism given by `Presheaf.representable.symmetry`. -/
@[simps]
noncomputable def symmetryIso [Full F] [Faithful F] : hf'.pullback g ≅ hg.pullback f' where
  hom := hf'.symmetry hg
  inv := hg.symmetry hf'

instance [Full F] [Faithful F] : IsIso (hf'.symmetry hg) :=
  (hf'.symmetryIso hg).isIso_hom

end

end Functor.relativelyRepresentable

end CategoryTheory
