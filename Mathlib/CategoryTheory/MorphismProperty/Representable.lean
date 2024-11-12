/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Joël Riou, Ravi Vakil
-/

import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!

# Relatively representable morphisms

In this file we define and develop basic results about relatively representable morphisms.

Classically, a morphism `f : F ⟶ G` of presheaves is said to be representable if for any morphism
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

* `Functor.relativelyRepresentable`: A morphism `f : X ⟶ Y` in `D` is said to be relatively
  representable with respect to `F`, if for any `g : F.obj a ⟶ Y`, there exists a pullback square
  of the following form
```
  F.obj b --F.map snd--> F.obj a
      |                     |
     fst                    g
      |                     |
      v                     v
      X ------- f --------> Y
```

* `MorphismProperty.relative`: Given a morphism property `P` in `C`, a morphism `f : X ⟶ Y` in `D`
  satisfies `P.relative F` if it is relatively representable and for any `g : F.obj a ⟶ Y`, the
  property `P` holds for any represented pullback of `f` by `g`.

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

## Main results

* `relativelyRepresentable.isMultiplicative`: The class of relatively representable morphisms is
  multiplicative.
* `relativelyRepresentable.isStableUnderBaseChange`: Being relatively representable is stable under
  base change.
* `relativelyRepresentable.of_isIso`: Isomorphisms are relatively representable.

-/

namespace CategoryTheory

open Category Limits MorphismProperty

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

/-- When `C` has pullbacks, then `F.map f` is representable with respect to `F` for any
`f : a ⟶ b` in `C`. -/
lemma map [Full F] [HasPullbacks C] {a b : C} (f : a ⟶ b)
    [∀ c (g : c ⟶ b), PreservesLimit (cospan f g) F] :
    F.relativelyRepresentable (F.map f) := fun c g ↦ by
  obtain ⟨g, rfl⟩ := F.map_surjective g
  refine ⟨Limits.pullback f g, Limits.pullback.snd f g, F.map (Limits.pullback.fst f g), ?_⟩
  apply F.map_isPullback <| IsPullback.of_hasPullback f g

lemma of_isIso {X Y : D} (f : X ⟶ Y) [IsIso f] : F.relativelyRepresentable f :=
  fun a g ↦ ⟨a, 𝟙 a, g ≫ CategoryTheory.inv f, IsPullback.of_vert_isIso ⟨by simp⟩⟩

lemma isomorphisms_le : MorphismProperty.isomorphisms D ≤ F.relativelyRepresentable :=
  fun _ _ f hf ↦ letI : IsIso f := hf; of_isIso F f

instance isMultiplicative : IsMultiplicative F.relativelyRepresentable where
  id_mem _ := of_isIso F _
  comp_mem {F G H} f g hf hg := fun X h ↦
    ⟨hf.pullback (hg.fst h), hf.snd (hg.fst h) ≫ hg.snd h, hf.fst (hg.fst h),
      by simpa using IsPullback.paste_vert (hf.isPullback (hg.fst h)) (hg.isPullback h)⟩

instance isStableUnderBaseChange : IsStableUnderBaseChange F.relativelyRepresentable where
  of_isPullback {X Y Y' X' f g f' g'} P₁ hg a h := by
    refine ⟨hg.pullback (h ≫ f), hg.snd (h ≫ f), ?_, ?_⟩
    · apply P₁.lift (hg.fst (h ≫ f)) (F.map (hg.snd (h ≫ f)) ≫ h) (by simpa using hg.w (h ≫ f))
    · apply IsPullback.of_right' (hg.isPullback (h ≫ f)) P₁

instance respectsIso : RespectsIso F.relativelyRepresentable :=
  (isStableUnderBaseChange F).respectsIso

end Functor.relativelyRepresentable

namespace MorphismProperty

open Functor.relativelyRepresentable

variable {X Y : D} (P : MorphismProperty C)

/-- Given a morphism property `P` in a category `C`, a functor `F : C ⥤ D` and a morphism
`f : X ⟶ Y` in `D`. Then `f` satisfies the morphism property `P.relative` with respect to `F` iff:
* The morphism is representable with respect to `F`
* For any morphism `g : F.obj a ⟶ Y`, the property `P` holds for any represented pullback of
  `f` by `g`. -/
def relative : MorphismProperty D :=
  fun X Y f ↦ F.relativelyRepresentable f ∧
    ∀ ⦃a b : C⦄ (g : F.obj a ⟶ Y) (fst : F.obj b ⟶ X) (snd : b ⟶ a)
      (_ : IsPullback fst (F.map snd) f g), P snd

/-- Given a morphism property `P` in a category `C`, a morphism `f : F ⟶ G` of presheaves in the
category `Cᵒᵖ ⥤ Type v` satisfies the morphism property `P.presheaf` iff:
* The morphism is representable.
* For any morphism `g : F.obj a ⟶ G`, the property `P` holds for any represented pullback of
  `f` by `g`.
This is implemented as a special case of the more general notion of `P.relative`, to the case when
the functor `F` is `yoneda`. -/
abbrev presheaf : MorphismProperty (Cᵒᵖ ⥤ Type v₁) := P.relative yoneda

variable {P} {F}

/-- A morphism satisfying `P.relative` is representable. -/
lemma relative.rep {f : X ⟶ Y} (hf : P.relative F f) : F.relativelyRepresentable f :=
  hf.1

lemma relative.property {f : X ⟶ Y} (hf : P.relative F f) :
    ∀ ⦃a b : C⦄ (g : F.obj a ⟶ Y) (fst : F.obj b ⟶ X) (snd : b ⟶ a)
    (_ : IsPullback fst (F.map snd) f g), P snd :=
  hf.2

lemma relative.property_snd {f : X ⟶ Y} (hf : P.relative F f) {a : C} (g : F.obj a ⟶ Y) :
    P (hf.rep.snd g) :=
  hf.property g _ _ (hf.rep.isPullback g)

/-- Given a morphism property `P` which respects isomorphisms, then to show that a morphism
`f : X ⟶ Y` satisfies `P.relative` it suffices to show that:
* The morphism is representable.
* For any morphism `g : F.obj a ⟶ G`, the property `P` holds for *some* represented pullback
of `f` by `g`. -/
lemma relative.of_exists [F.Faithful] [F.Full] [P.RespectsIso] {f : X ⟶ Y}
    (h₀ : ∀ ⦃a : C⦄ (g : F.obj a ⟶ Y), ∃ (b : C) (fst : F.obj b ⟶ X) (snd : b ⟶ a)
      (_ : IsPullback fst (F.map snd) f g), P snd) : P.relative F f := by
  refine ⟨fun a g ↦ ?_, fun a b g fst snd h ↦ ?_⟩
  all_goals obtain ⟨c, g_fst, g_snd, BC, H⟩ := h₀ g
  · refine ⟨c, g_snd, g_fst, BC⟩
  · refine (P.arrow_mk_iso_iff ?_).2 H
    exact Arrow.isoMk (F.preimageIso (h.isoIsPullback X (F.obj a) BC)) (Iso.refl _)
      (F.map_injective (by simp))

lemma relative_of_snd [F.Faithful] [F.Full] [P.RespectsIso] {f : X ⟶ Y}
    (hf : F.relativelyRepresentable f) (h : ∀ ⦃a : C⦄ (g : F.obj a ⟶ Y), P (hf.snd g)) :
    P.relative F f :=
  relative.of_exists (fun _ g ↦ ⟨hf.pullback g, hf.fst g, hf.snd g, hf.isPullback g, h g⟩)

/-- If `P : MorphismProperty C` is stable under base change, `F` is fully faithful and preserves
pullbacks, and `C` has all pullbacks, then for any `f : a ⟶ b` in `C`, `F.map f` satisfies
`P.relative` if `f` satisfies `P`. -/
lemma relative_map [F.Faithful] [F.Full] [HasPullbacks C] [IsStableUnderBaseChange P]
    {a b : C} {f : a ⟶ b} [∀ c (g : c ⟶ b), PreservesLimit (cospan f g) F]
    (hf : P f) : P.relative F (F.map f) := by
  apply relative.of_exists
  intro Y' g
  obtain ⟨g, rfl⟩ := F.map_surjective g
  exact ⟨_, _, _, (IsPullback.of_hasPullback f g).map F, P.pullback_snd _ _ hf⟩

lemma of_relative_map {a b : C} {f : a ⟶ b} (hf : P.relative F (F.map f)) : P f :=
  hf.property (𝟙 _) (𝟙 _) f (IsPullback.id_horiz (F.map f))

lemma relative_map_iff [F.Faithful] [F.Full] [PreservesLimitsOfShape WalkingCospan F]
    [HasPullbacks C] [IsStableUnderBaseChange P] {X Y : C} {f : X ⟶ Y} :
    P.relative F (F.map f) ↔ P f :=
  ⟨fun hf ↦ of_relative_map hf, fun hf ↦ relative_map hf⟩

/-- If `P' : MorphismProperty C` is satisfied whenever `P` is, then also `P'.relative` is
satisfied whenever `P.relative` is. -/
lemma relative_monotone {P' : MorphismProperty C} (h : P ≤ P') :
    P.relative F ≤ P'.relative F := fun _ _ _ hf ↦
  ⟨hf.rep, fun _ _ g fst snd BC ↦ h _ (hf.property g fst snd BC)⟩

section

variable (P)

lemma relative_isStableUnderBaseChange : IsStableUnderBaseChange (P.relative F) where
  of_isPullback hfBC hg :=
    ⟨of_isPullback hfBC hg.rep,
      fun _ _ _ _ _ BC ↦ hg.property _ _ _ (IsPullback.paste_horiz BC hfBC)⟩

instance relative_isStableUnderComposition [F.Faithful] [F.Full] [P.IsStableUnderComposition] :
    IsStableUnderComposition (P.relative F) where
  comp_mem {F G H} f g hf hg := by
    refine ⟨comp_mem _ _ _ hf.1 hg.1, fun Z X p fst snd h ↦ ?_⟩
    rw [← hg.1.lift_snd (fst ≫ f) snd (by simpa using h.w)]
    refine comp_mem _ _ _ (hf.property (hg.1.fst p) fst _
      (IsPullback.of_bot ?_ ?_ (hg.1.isPullback p))) (hg.property_snd p)
    · rw [← Functor.map_comp, lift_snd]
      exact h
    · symm
      apply hg.1.lift_fst

instance relative_respectsIso : RespectsIso (P.relative F) :=
  (relative_isStableUnderBaseChange P).respectsIso

instance relative_isMultiplicative [F.Faithful] [F.Full] [P.IsMultiplicative] [P.RespectsIso] :
    IsMultiplicative (P.relative F) where
  id_mem X := relative.of_exists
    (fun Y g ↦ ⟨Y, g, 𝟙 Y, by simpa using IsPullback.of_id_snd, id_mem _ _⟩)

end

/-- Morphisms satisfying `(monomorphism C).presheaf` are in particular monomorphisms. -/
lemma presheaf_monomorphisms_le_monomorphisms :
    (monomorphisms C).presheaf ≤ monomorphisms _ := fun F G f hf ↦ by
  suffices ∀ {X : C} {a b : yoneda.obj X ⟶ F}, a ≫ f = b ≫ f → a = b from
    ⟨fun _ _ h ↦ hom_ext_yoneda (fun _ _ ↦ this (by simp only [assoc, h]))⟩
  intro X a b h
  /- It suffices to show that the lifts of `a` and `b` to morphisms
  `X ⟶ hf.rep.pullback g` are equal, where `g = a ≫ f = a ≫ f`. -/
  suffices hf.rep.lift (g := a ≫ f) a (𝟙 X) (by simp) =
      hf.rep.lift b (𝟙 X) (by simp [← h]) by
    simpa using yoneda.congr_map this =≫ (hf.rep.fst (a ≫ f))
  -- This follows from the fact that the induced maps `hf.rep.pullback g ⟶ X` are mono.
  have : Mono (hf.rep.snd (a ≫ f)) := hf.property_snd (a ≫ f)
  simp only [← cancel_mono (hf.rep.snd (a ≫ f)), lift_snd]

end MorphismProperty

end CategoryTheory
