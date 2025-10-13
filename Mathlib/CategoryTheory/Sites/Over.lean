/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.CoverPreserving

/-! Localization

In this file, given a Grothendieck topology `J` on a category `C` and `X : C`, we construct
a Grothendieck topology `J.over X` on the category `Over X`. In order to do this,
we first construct a bijection `Sieve.overEquiv Y : Sieve Y ≃ Sieve Y.left`
for all `Y : Over X`. Then, as it is stated in SGA 4 III 5.2.1, a sieve of `Y : Over X`
is covering for `J.over X` if and only if the corresponding sieve of `Y.left`
is covering for `J`. As a result, the forgetful functor
`Over.forget X : Over X ⥤ X` is both cover-preserving and cover-lifting.

-/

universe v' v u' u

namespace CategoryTheory

open Category

variable {C : Type u} [Category.{v} C]

namespace Sieve

/-- The equivalence `Sieve Y ≃ Sieve Y.left` for all `Y : Over X`. -/
def overEquiv {X : C} (Y : Over X) :
    Sieve Y ≃ Sieve Y.left where
  toFun S := Sieve.functorPushforward (Over.forget X) S
  invFun S' := Sieve.functorPullback (Over.forget X) S'
  left_inv S := by
    ext Z g
    dsimp [Presieve.functorPullback, Presieve.functorPushforward]
    constructor
    · rintro ⟨W, a, b, h, w⟩
      let c : Z ⟶ W := Over.homMk b
        (by rw [← Over.w g, w, assoc, Over.w a])
      rw [show g = c ≫ a by ext; exact w]
      exact S.downward_closed h _
    · intro h
      exact ⟨Z, g, 𝟙 _, h, by simp⟩
  right_inv S := by
    ext Z g
    dsimp [Presieve.functorPullback, Presieve.functorPushforward]
    constructor
    · rintro ⟨W, a, b, h, rfl⟩
      exact S.downward_closed h _
    · intro h
      exact ⟨Over.mk ((g ≫ Y.hom)), Over.homMk g, 𝟙 _, h, by simp⟩

@[simp]
lemma overEquiv_top {X : C} (Y : Over X) :
    overEquiv Y ⊤ = ⊤ := by
  ext Z g
  simp only [top_apply, iff_true]
  dsimp [overEquiv, Presieve.functorPushforward]
  exact ⟨Y, 𝟙 Y, g, by simp, by simp⟩

@[simp]
lemma overEquiv_symm_top {X : C} (Y : Over X) :
    (overEquiv Y).symm ⊤ = ⊤ :=
  (overEquiv Y).injective (by simp)

lemma overEquiv_le_overEquiv_iff {X : C} {Y : Over X} (R₁ R₂ : Sieve Y) :
    R₁.overEquiv Y ≤ R₂.overEquiv Y ↔ R₁ ≤ R₂ := by
  refine ⟨fun h ↦ ?_, fun h ↦ Sieve.functorPushforward_monotone _ _ h⟩
  replace h : (overEquiv Y).symm (R₁.overEquiv Y) ≤ (overEquiv Y).symm (R₂.overEquiv Y) :=
    Sieve.functorPullback_monotone _ _ h
  simpa using h

lemma overEquiv_pullback {X : C} {Y₁ Y₂ : Over X} (f : Y₁ ⟶ Y₂) (S : Sieve Y₂) :
    overEquiv _ (S.pullback f) = (overEquiv _ S).pullback f.left := by
  ext Z g
  dsimp [overEquiv, Presieve.functorPushforward]
  constructor
  · rintro ⟨W, a, b, h, rfl⟩
    exact ⟨W, a ≫ f, b, h, by simp⟩
  · rintro ⟨W, a, b, h, w⟩
    let T := Over.mk (b ≫ W.hom)
    let c : T ⟶ Y₁ := Over.homMk g (by dsimp [T]; rw [← Over.w a, ← reassoc_of% w, Over.w f])
    let d : T ⟶ W := Over.homMk b
    refine ⟨T, c, 𝟙 Z, ?_, by simp [T, c]⟩
    rw [show c ≫ f = d ≫ a by ext; exact w]
    exact S.downward_closed h _

@[simp]
lemma overEquiv_symm_iff {X : C} {Y : Over X} (S : Sieve Y.left) {Z : Over X} (f : Z ⟶ Y) :
    (overEquiv Y).symm S f ↔ S f.left := by
  rfl

lemma overEquiv_iff {X : C} {Y : Over X} (S : Sieve Y) {Z : C} (f : Z ⟶ Y.left) :
    overEquiv Y S f ↔ S (Over.homMk f : Over.mk (f ≫ Y.hom) ⟶ Y) := by
  obtain ⟨S, rfl⟩ := (overEquiv Y).symm.surjective S
  simp

@[simp]
lemma functorPushforward_over_map {X Y : C} (f : X ⟶ Y) (Z : Over X) (S : Sieve Z.left) :
    Sieve.functorPushforward (Over.map f) ((Sieve.overEquiv Z).symm S) =
      (Sieve.overEquiv ((Over.map f).obj Z)).symm S := by
  ext W g
  constructor
  · rintro ⟨T, a, b, ha, rfl⟩
    exact S.downward_closed ha _
  · intro hg
    exact ⟨Over.mk (g.left ≫ Z.hom), Over.homMk g.left,
      Over.homMk (𝟙 _) (by simpa using Over.w g), hg, by cat_disch⟩

end Sieve

variable (J : GrothendieckTopology C)

namespace GrothendieckTopology

/-- The Grothendieck topology on the category `Over X` for any `X : C` that is
induced by a Grothendieck topology on `C`. -/
def over (X : C) : GrothendieckTopology (Over X) where
  sieves Y S := Sieve.overEquiv Y S ∈ J Y.left
  top_mem' Y := by
    change _ ∈ J Y.left
    simp
  pullback_stable' Y₁ Y₂ S₁ f h₁ := by
    change _ ∈ J _ at h₁ ⊢
    rw [Sieve.overEquiv_pullback]
    exact J.pullback_stable _ h₁
  transitive' Y S (hS : _ ∈ J _) R hR := J.transitive hS _ (fun Z f hf => by
    have hf' : _ ∈ J _ := hR ((Sieve.overEquiv_iff _ _).1 hf)
    rw [Sieve.overEquiv_pullback] at hf'
    exact hf')

lemma mem_over_iff {X : C} {Y : Over X} (S : Sieve Y) :
    S ∈ (J.over X) Y ↔ Sieve.overEquiv _ S ∈ J Y.left := by
  rfl

lemma overEquiv_symm_mem_over {X : C} (Y : Over X) (S : Sieve Y.left) (hS : S ∈ J Y.left) :
    (Sieve.overEquiv Y).symm S ∈ (J.over X) Y := by
  simpa only [mem_over_iff, Equiv.apply_symm_apply] using hS

lemma over_forget_coverPreserving (X : C) :
    CoverPreserving (J.over X) J (Over.forget X) where
  cover_preserve hS := hS

lemma over_forget_compatiblePreserving (X : C) :
    CompatiblePreserving J (Over.forget X) where
  compatible {_ Z _ _ hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ h} := by
    let W' : Over X := Over.mk (f₁ ≫ Y₁.hom)
    let g₁' : W' ⟶ Y₁ := Over.homMk f₁
    let g₂' : W' ⟶ Y₂ := Over.homMk f₂ (by simpa using h.symm =≫ Z.hom)
    exact hx g₁' g₂' hg₁ hg₂ (by ext; exact h)

instance (X : C) : (Over.forget X).IsCocontinuous (J.over X) J where
  cover_lift hS := J.overEquiv_symm_mem_over _ _ hS

instance (X : C) : (Over.forget X).IsContinuous (J.over X) J :=
  Functor.isContinuous_of_coverPreserving
    (over_forget_compatiblePreserving J X)
    (over_forget_coverPreserving J X)

/-- The pullback functor `Sheaf J A ⥤ Sheaf (J.over X) A` -/
abbrev overPullback (A : Type u') [Category.{v'} A] (X : C) :
    Sheaf J A ⥤ Sheaf (J.over X) A :=
  (Over.forget X).sheafPushforwardContinuous _ _ _

lemma over_map_coverPreserving {X Y : C} (f : X ⟶ Y) :
    CoverPreserving (J.over X) (J.over Y) (Over.map f) where
  cover_preserve {U S} hS := by
    obtain ⟨S, rfl⟩ := (Sieve.overEquiv U).symm.surjective S
    rw [Sieve.functorPushforward_over_map]
    apply overEquiv_symm_mem_over
    simpa [mem_over_iff] using hS

lemma over_map_compatiblePreserving {X Y : C} (f : X ⟶ Y) :
    CompatiblePreserving (J.over Y) (Over.map f) where
  compatible {F Z _ x hx Y₁ Y₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ h} := by
    let W' : Over X := Over.mk (f₁.left ≫ Y₁.hom)
    let g₁' : W' ⟶ Y₁ := Over.homMk f₁.left
    let g₂' : W' ⟶ Y₂ := Over.homMk f₂.left
      (by simpa using (Over.forget _).congr_map h.symm =≫ Z.hom)
    let e : (Over.map f).obj W' ≅ W := Over.isoMk (Iso.refl _)
      (by simpa [W'] using (Over.w f₁).symm)
    convert congr_arg (F.val.map e.inv.op)
      (hx g₁' g₂' hg₁ hg₂ (by ext; exact (Over.forget _).congr_map h)) using 1
    all_goals
      dsimp [e, W', g₁', g₂']
      rw [← FunctorToTypes.map_comp_apply]
      apply congr_fun
      congr 1
      rw [← op_comp]
      congr 1
      ext
      simp

instance {X Y : C} (f : X ⟶ Y) : (Over.map f).IsContinuous (J.over X) (J.over Y) :=
  Functor.isContinuous_of_coverPreserving
    (over_map_compatiblePreserving J f)
    (over_map_coverPreserving J f)

/-- The pullback functor `Sheaf (J.over Y) A ⥤ Sheaf (J.over X) A` induced
by a morphism `f : X ⟶ Y`. -/
abbrev overMapPullback (A : Type u') [Category.{v'} A] {X Y : C} (f : X ⟶ Y) :
    Sheaf (J.over Y) A ⥤ Sheaf (J.over X) A :=
  (Over.map f).sheafPushforwardContinuous _ _ _

end GrothendieckTopology

variable {J}

/-- Given `F : Sheaf J A` and `X : C`, this is the pullback of `F` on `J.over X`. -/
abbrev Sheaf.over {A : Type u'} [Category.{v'} A] (F : Sheaf J A) (X : C) :
    Sheaf (J.over X) A := (J.overPullback A X).obj F

end CategoryTheory
