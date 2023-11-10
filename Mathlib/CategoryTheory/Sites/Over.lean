import Mathlib.CategoryTheory.Sites.Grothendieck

universe v u

namespace CategoryTheory

open Category

variable {C : Type u} [Category.{v} C]

namespace Sieve

def overEquiv {X : C} (Y : Over X) :
    Sieve Y ≃ Sieve Y.left where
  toFun S := Sieve.functorPushforward (Over.forget X) S
  invFun S' := Sieve.functorPullback (Over.forget X) S'
  left_inv S := by
    ext Z g
    dsimp [Presieve.functorPullback, Presieve.functorPushforward]
    constructor
    · rintro ⟨W, a, b, h, w⟩
      let β : Z ⟶ W := Over.homMk b
        (by rw [← Over.w g, w, assoc, Over.w a])
      rw [show g = β ≫ a by ext; exact w]
      exact S.downward_closed h _
    · intro h
      exact ⟨Z, g, 𝟙 _, h, by simp⟩
  right_inv S' := by
    ext Z g
    dsimp [Presieve.functorPullback, Presieve.functorPushforward]
    constructor
    · rintro ⟨W, a, b, h, rfl⟩
      exact S'.downward_closed h _
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

lemma overEquiv_pullback {X : C} {Y₁ Y₂ : Over X} (f : Y₁ ⟶ Y₂)
    (S : Sieve Y₂) :
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
    have eq : c ≫ f = d ≫ a := by ext; exact w
    rw [eq]
    exact S.downward_closed h _

end Sieve

variable (J : GrothendieckTopology C)

namespace GrothendieckTopology

/-def over (X : C) : GrothendieckTopology (Over X) where
  sieves Y := fun S => Sieve.overEquiv _ S ∈ J _
  top_mem' Y := by
    change _ ∈ J Y.left
    simp
  pullback_stable' Y₁ Y₂ S₁ f h₁ := by
    change _ ∈ J _ at h₁ ⊢
    rw [Sieve.overEquiv_pullback]
    exact J.pullback_stable _ h₁
  transitive' Y S (hS : _ ∈ J _) R hR := by
    change _ ∈ J _
    sorry-/

end GrothendieckTopology


end CategoryTheory
