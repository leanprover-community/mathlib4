/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.Grothendieck

/-! Localization

In this file, given a Grothendieck topology `J` on a category `C` and `X : C`, we construct
a Grothendieck topology `J.over X` on the category `Over X`. In order to do this,
we first construct a bijection `Sieve.overEquiv Y : Sieve Y ≃ Sieve Y.left`
for all `Y : Over X`. Then, as it is stated in SGA 4 III 5.2.1, a sieve of `Y : Over X`
is covering for `J.over X` if and only if the corresponding sieve of `Y.left`
is covering for `J`.

-/

universe v u

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

lemma overEquiv_pullback {X : C} {Y₁ Y₂ : Over X} (f : Y₁ ⟶ Y₂) (S : Sieve Y₂) :
    overEquiv _ (S.pullback f) = (overEquiv _ S).pullback f.left := by
  ext Z g
  dsimp [overEquiv, Presieve.functorPushforward]
  constructor
  · rintro ⟨W, a, b, h, rfl⟩
    exact ⟨W, a ≫ f, b, h, by simp⟩
  · rintro ⟨W, a, b, h, w⟩
    let T := Over.mk (b ≫ W.hom)
    let c : T ⟶ Y₁ := Over.homMk g (by dsimp; rw [← Over.w a, ← reassoc_of% w, Over.w f])
    let d : T ⟶ W := Over.homMk b
    refine' ⟨T, c, 𝟙 Z, _, by simp⟩
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

end GrothendieckTopology

end CategoryTheory
