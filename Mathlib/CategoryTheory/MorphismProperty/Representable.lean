/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Joël Riou, Ravi Vakil
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

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
* If `F` is full, and `f` is of type `F.obj c ⟶ G`, we also have `hf.fst' g : hf.pullback g ⟶ X`
  which is the preimage under `F` of `hf.fst g`.
* `hom_ext`, `hom_ext'`, `lift`, `lift'` are variants of the universal property of
  `F.obj (hf.pullback g)`, where as much as possible has been formulated internally to `C`.
  For these theorems we also need that `F` is full and/or faithful.
* `symmetry` and `symmetryIso` are variants of the fact that pullbacks are symmetric for
  representable morphisms, formulated internally to `C`. We assume that `F` is fully faithful here.

We also provide some basic API for dealing with triple pullbacks, i.e. given
`hf₁ : relativelyRepresentable f₁`, `f₂ : F.obj A₂ ⟶ X` and `f₃ : F.obj A₃ ⟶ X`, we define
`hf₁.pullback₃ f₂ f₃` to be the pullback of `(A₁ ×_X A₂) ×_{A₁} (A₁ ×_X A₃)`. We then develop
some API for working with this object, mirroring the usual API for pullbacks, but where as much
as possible is phrased internally to `C`.

## Main results

* `relativelyRepresentable.isMultiplicative`: The class of relatively representable morphisms is
  multiplicative.
* `relativelyRepresentable.isStableUnderBaseChange`: Being relatively representable is stable under
  base change.
* `relativelyRepresentable.of_isIso`: Isomorphisms are relatively representable.

-/

@[expose] public section

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
  F.map_injective (by simp [lift'])

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

section

-- TODO(Calle): This could be generalized to functors whose image forms a separating family.
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

variable {G : Cᵒᵖ ⥤ Type v₁}

lemma presheaf_mono_of_le (hP : P ≤ MorphismProperty.monomorphisms C)
    {X : C} {f : yoneda.obj X ⟶ G} (hf : P.presheaf f) : Mono f :=
  MorphismProperty.presheaf_monomorphisms_le_monomorphisms _
    (MorphismProperty.relative_monotone hP _ hf)

lemma fst'_self_eq_snd (hP : P ≤ MorphismProperty.monomorphisms C)
    {X : C} {f : yoneda.obj X ⟶ G} (hf : P.presheaf f) : hf.rep.fst' f = hf.rep.snd f := by
  have := P.presheaf_mono_of_le hP hf
  apply yoneda.map_injective
  rw [← cancel_mono f, (hf.rep.isPullback' f).w]

lemma isIso_fst'_self (hP : P ≤ MorphismProperty.monomorphisms C)
    {X : C} {f : yoneda.obj X ⟶ G} (hf : P.presheaf f) : IsIso (hf.rep.fst' f) :=
  have := P.presheaf_mono_of_le hP hf
  have := (hf.rep.isPullback' f).isIso_fst_of_mono
  Yoneda.fullyFaithful.isIso_of_isIso_map _

end

end MorphismProperty

namespace Functor.relativelyRepresentable

section Pullbacks₃
/-
In this section we develop some basic API that help deal with certain triple pullbacks obtained
from morphism `f₁ : F.obj A₁ ⟶ X` which is relatively representable with respect to some functor
`F : C ⥤ D`.

More precisely, given two objects `A₂` and `A₃` in `C`, and two morphisms `f₂ : A₂ ⟶ X` and
`f₃ : A₃ ⟶ X`, we can consider the pullbacks (in `D`) `(A₁ ×_X A₂)` and `(A₁ ×_X A₃)`
(which makes sense as objects in `C` due to `F` being relatively representable).

We can then consider the pullback, in `C`, of these two pullbacks. This is the object
`(A₁ ×_X A₂) ×_{A₁} (A₁ ×_X A₃)`. In this section we develop some basic API for dealing with this
pullback. This is used in `Mathlib/AlgebraicGeometry/Sites/Representability.lean` to show that
representability is Zariski-local.
-/
variable {F : C ⥤ D} [Full F] {A₁ A₂ A₃ : C} {X : D}
  {f₁ : F.obj A₁ ⟶ X} (hf₁ : F.relativelyRepresentable f₁)
  (f₂ : F.obj A₂ ⟶ X) (f₃ : F.obj A₃ ⟶ X)
  [HasPullback (hf₁.fst' f₂) (hf₁.fst' f₃)]

/-- The pullback `(A₁ ×_X A₂) ×_{A₁} (A₁ ×_X A₃)`. -/
noncomputable def pullback₃ := Limits.pullback (hf₁.fst' f₂) (hf₁.fst' f₃)
/-- The morphism `(A₁ ×_X A₂) ×_{A₁} (A₁ ×_X A₃) ⟶ A₁`. -/
noncomputable def pullback₃.p₁ : hf₁.pullback₃ f₂ f₃ ⟶ A₁ := pullback.fst _ _ ≫ hf₁.fst' f₂
/-- The morphism `(A₁ ×_X A₂) ×_{A₁} (A₁ ×_X A₃) ⟶ A₂`. -/
noncomputable def pullback₃.p₂ : hf₁.pullback₃ f₂ f₃ ⟶ A₂ := pullback.fst _ _ ≫ hf₁.snd f₂
/-- The morphism `(A₁ ×_X A₂) ×_{A₁} (A₁ ×_X A₃) ⟶ A₃`. -/
noncomputable def pullback₃.p₃ : hf₁.pullback₃ f₂ f₃ ⟶ A₃ := pullback.snd _ _ ≫ hf₁.snd f₃

/-- The morphism `F.obj (A₁ ×_X A₂) ×_{A₁} (A₁ ×_X A₃) ⟶ X`. -/
noncomputable def pullback₃.π : F.obj (pullback₃ hf₁ f₂ f₃) ⟶ X :=
  F.map (p₁ hf₁ f₂ f₃) ≫ f₁

@[reassoc (attr := simp)]
lemma pullback₃.map_p₁_comp : F.map (p₁ hf₁ f₂ f₃) ≫ f₁ = π _ _ _ :=
  rfl

@[reassoc (attr := simp)]
lemma pullback₃.map_p₂_comp : F.map (p₂ hf₁ f₂ f₃) ≫ f₂ = π _ _ _ := by
  simp [π, p₁, p₂, ← hf₁.w f₂]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma pullback₃.map_p₃_comp : F.map (p₃ hf₁ f₂ f₃) ≫ f₃ = π _ _ _ := by
  simp [π, p₁, p₃, ← hf₁.w f₃, pullback.condition]

section

variable [Faithful F] {Z : C} (x₁ : Z ⟶ A₁) (x₂ : Z ⟶ A₂) (x₃ : Z ⟶ A₃)
  (h₁₂ : F.map x₁ ≫ f₁ = F.map x₂ ≫ f₂)
  (h₁₃ : F.map x₁ ≫ f₁ = F.map x₃ ≫ f₃)

/-- The lift obtained from the universal property of `(A₁ ×_X A₂) ×_{A₁} (A₁ ×_X A₃)`. -/
noncomputable def lift₃ : Z ⟶ pullback₃ hf₁ f₂ f₃ :=
  pullback.lift (hf₁.lift' x₁ x₂ h₁₂)
    (hf₁.lift' x₁ x₃ h₁₃) (by simp)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma lift₃_p₁ : hf₁.lift₃ f₂ f₃ x₁ x₂ x₃ h₁₂ h₁₃ ≫ pullback₃.p₁ hf₁ f₂ f₃ = x₁ := by
  simp [lift₃, pullback₃.p₁]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma lift₃_p₂ : hf₁.lift₃ f₂ f₃ x₁ x₂ x₃ h₁₂ h₁₃ ≫ pullback₃.p₂ hf₁ f₂ f₃ = x₂ := by
  simp [lift₃, pullback₃.p₂]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma lift₃_p₃ : hf₁.lift₃ f₂ f₃ x₁ x₂ x₃ h₁₂ h₁₃ ≫ pullback₃.p₃ hf₁ f₂ f₃ = x₃ := by
  simp [lift₃, pullback₃.p₃]

end

@[reassoc (attr := simp)]
lemma pullback₃.fst_fst'_eq_p₁ : pullback.fst _ _ ≫ hf₁.fst' f₂ = pullback₃.p₁ hf₁ f₂ f₃ := rfl

@[reassoc (attr := simp)]
lemma pullback₃.fst_snd_eq_p₂ : pullback.fst _ _ ≫ hf₁.snd f₂ = pullback₃.p₂ hf₁ f₂ f₃ := rfl

@[reassoc (attr := simp)]
lemma pullback₃.snd_snd_eq_p₃ : pullback.snd _ _ ≫ hf₁.snd f₃ = pullback₃.p₃ hf₁ f₂ f₃ := rfl

@[reassoc (attr := simp)]
lemma pullback₃.snd_fst'_eq_p₁ :
    pullback.snd (hf₁.fst' f₂) (hf₁.fst' f₃) ≫ hf₁.fst' f₃ = pullback₃.p₁ hf₁ f₂ f₃ :=
  pullback.condition.symm

variable {hf₁ f₂ f₃} in
@[ext]
lemma pullback₃.hom_ext [Faithful F] {Z : C} {φ φ' : Z ⟶ pullback₃ hf₁ f₂ f₃}
    (h₁ : φ ≫ pullback₃.p₁ hf₁ f₂ f₃ = φ' ≫ pullback₃.p₁ hf₁ f₂ f₃)
    (h₂ : φ ≫ pullback₃.p₂ hf₁ f₂ f₃ = φ' ≫ pullback₃.p₂ hf₁ f₂ f₃)
    (h₃ : φ ≫ pullback₃.p₃ hf₁ f₂ f₃ = φ' ≫ pullback₃.p₃ hf₁ f₂ f₃) : φ = φ' := by
  apply pullback.hom_ext <;> ext <;> simpa

end Pullbacks₃

section Diagonal
/-
In this section, we prove a criterion for the diagonal morphisms to be relatively representable.
-/

variable {F : C ⥤ D}
variable [HasBinaryProducts C]
variable [HasPullbacks D] [HasBinaryProducts D] [HasTerminal D]
variable [Full F]
variable [PreservesLimitsOfShape (Discrete WalkingPair) F]

set_option backward.isDefEq.respectTransparency false in
/-- Assume that
1. `C` has binary products,
2. `D` has pullbacks, binary products and a terminal object, and
3. `F : C ⥤ D` is full and preserves binary products.

For an object `X` in a category `D`, if the diagonal morphism `X ⟶ X × X` is relatively
representable, then every morphism of the form `F.obj a ⟶ X` is relatively representable with
respect to `F`.
-/
lemma of_diag {X : D} (h : F.relativelyRepresentable (Limits.diag X))
    ⦃a : C⦄ (g : F.obj a ⟶ X) : F.relativelyRepresentable g := by
  rw [(by cat_disch : Limits.diag X = pullback.lift (𝟙 X) (𝟙 X) ≫ (prodIsoPullback X X).inv)] at h
  intro a' g'
  obtain ⟨_, ⟨left⟩⟩ := pullback_map_diagonal_isPullback g g' (terminal.from X)
  let prodMap : F.obj (a ⨯ a') ⟶ X ⨯ X :=
    (preservesLimitIso _ (pair _ _) ≪≫ HasLimit.isoOfNatIso (pairComp _ _ _)).hom ≫ prod.map g g'
  let pbRepr :=
    (h prodMap).choose_spec.choose_spec.choose_spec.isLimit'.some.conePointUniqueUpToIso <|
    pasteHorizIsPullback rfl (IsPullback.of_vert_isIso_mono (snd := pullback.congrHom
      (terminal.comp_from g) (terminal.comp_from g') ≪≫ (prodIsoPullback _ _).symm ≪≫
      (HasLimit.isoOfNatIso (pairComp _ _ _)).symm ≪≫ (preservesLimitIso _ (pair _ _)).symm |>.hom)
    ⟨by cat_disch⟩).isLimit'.some left
  exact ⟨_, ⟨_, ⟨_, IsPullback.of_iso_pullback (fst := pbRepr.hom ≫ pullback.fst g g')
    (snd := F.map (Functor.preimage F (pbRepr.hom ≫ pullback.snd g g')))
    ⟨by simp [pullback.condition]⟩ pbRepr (by cat_disch) (by cat_disch)⟩⟩⟩

/-- Assume that
1. `C` has binary products and pullbacks,
2. `D` has pullbacks, binary products and a terminal object, and
3. `F : C ⥤ D` is full and preserves binary products and pullbacks.

For a morphism `g : F.obj a ⟶ pullback (terminal.from X) (terminal.from X)`,
the canonical morphism from `F.obj a` to
`pullback ((g ≫ pullback.fst _ _) ≫ terminal.from X) ((g ≫ pullback.snd _ _) ≫ terminal.from X)`
is relatively representable with respect to `F`.
-/
lemma toPullbackTerminal {X : D} {a : C}
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
    (g : F.obj a ⟶ Limits.pullback (terminal.from X) (terminal.from X)) :
    F.relativelyRepresentable (pullback.lift (f := (g ≫ pullback.fst _ _) ≫ terminal.from X)
        (g := (g ≫ pullback.snd _ _) ≫ terminal.from X) (𝟙 _) (𝟙 _) (by cat_disch)) := by
  let pbIso := pullback.congrHom
    (terminal.comp_from _ : (g ≫ pullback.fst _ _) ≫ terminal.from X = terminal.from _)
    (terminal.comp_from _ : (g ≫ pullback.snd _ _) ≫ terminal.from X = terminal.from _) ≪≫
    (prodIsoPullback _ _).symm ≪≫ (HasLimit.isoOfNatIso (pairComp _ _ _)).symm ≪≫
    (preservesLimitIso _ (pair _ _)).symm
  rw [← comp_id (pullback.lift _ _), ← pbIso.hom_inv_id, ← Category.assoc]
  apply (respectsIso F).toRespectsRight.postcomp _ (inferInstance : IsIso _) _
  exact map_preimage F (_ ≫ pbIso.hom) ▸ map F (F.preimage _)

set_option backward.isDefEq.respectTransparency false in
/-- Assume that
1. `C` has binary products and pullbacks,
2. `D` has pullbacks, binary products and a terminal object, and
3. `F : C ⥤ D` is full and preserves binary products and pullbacks.

For an object `X` in a category `D`, if every morphism of the form `F.obj a ⟶ X` is relatively
representable with respect to `F`, so is the diagonal morphism `X ⟶ X × X`.
-/
lemma diag_of_map_from_obj [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
    {X : D} (h : ∀ ⦃a : C⦄ (g : F.obj a ⟶ X), F.relativelyRepresentable g) :
    F.relativelyRepresentable (Limits.diag X) := by
  rw [(by cat_disch : Limits.diag X = pullback.lift (𝟙 X) (𝟙 X) ≫ (prodIsoPullback X X).inv)]
  suffices F.relativelyRepresentable (pullback.lift (𝟙 _) (𝟙 _)) from
    (respectsIso F).toRespectsRight.postcomp _ (inferInstance : IsIso _) _ this
  intro a g
  obtain ⟨_, ⟨_, ⟨_, pbRepr⟩⟩⟩ := h (g ≫ pullback.fst _ _) (g ≫ pullback.snd _ _)
  obtain ⟨_, ⟨bot⟩⟩ := IsPullback.of_iso_pullback ⟨by rw [assoc]; simp [pullback.condition]⟩
    (pbRepr.isoPullback ≪≫ (pullbackDiagonalMapIdIso (g ≫ pullback.fst _ _) (g ≫ pullback.snd _ _)
      (terminal.from X)).symm) rfl rfl
  obtain ⟨_, ⟨_, ⟨topMap, top⟩⟩⟩ := (toPullbackTerminal g) <|
    (pbRepr.isoPullback ≪≫ (pullbackDiagonalMapIdIso (g ≫ pullback.fst _ _) (g ≫ pullback.snd _ _)
      (terminal.from X)).symm).hom ≫ pullback.snd
        (pullback.diagonal (terminal.from X))
        (pullback.map _ _ _ _ _ _ (𝟙 _) (by cat_disch) (by cat_disch))
  have hg : g = pullback.lift (𝟙 _) (𝟙 _) (by cat_disch) ≫ pullback.map
    ((g ≫ pullback.fst _ _) ≫ terminal.from X) ((g ≫ pullback.snd _ _) ≫ terminal.from X) _ _
      (g ≫ pullback.fst _ _) (g ≫ pullback.snd _ _) (𝟙 _) (by cat_disch) (by cat_disch) := by
    apply Limits.pullback.hom_ext <;> simp
  exact hg ▸ ⟨_, ⟨_, ⟨_, IsPullback.of_isLimit <| pasteVertIsPullback rfl bot
    (map_preimage F topMap ▸ top).flip.isLimit'.some⟩⟩⟩

/-- Assume that
1. `C` has binary products and pullbacks,
2. `D` has pullbacks, binary products and a terminal object, and
3. `F : C ⥤ D` is full and preserves binary products and pullbacks.

For an object `X` in a category `D`, the diagonal morphism `X ⟶ X × X` is relatively representable
with respect to `F` if and only if so is every morphism of the form `F.obj a ⟶ X`.
-/
lemma diag_iff {X : D} [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F] :
    F.relativelyRepresentable (Limits.diag X) ↔
      ∀ ⦃a : C⦄ (g : F.obj a ⟶ X), F.relativelyRepresentable g :=
  ⟨fun h _ g => of_diag h g, fun h => diag_of_map_from_obj h⟩

end Diagonal

end Functor.relativelyRepresentable

end CategoryTheory
