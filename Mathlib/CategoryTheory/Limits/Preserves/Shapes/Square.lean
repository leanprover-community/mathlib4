/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Preservations of pullback/pushout squares

If a functor `F : C ⥤ D` preserves suitable cospans (resp. spans),
and `sq : Square C` is a pullback square (resp. a pushout square)
then so is the square`sq.map F`.

The lemma `Square.isPullback_iff_map_coyoneda_isPullback` also
shows that a square is a pullback square iff it is so after the
application of the functor `coyoneda.obj X` for all `X : Cᵒᵖ`.
Similarly, a square is a pushout square iff the opposite
square becomes a pullback square after the application of the
functor `yoneda.obj X` for all `X : C`.

-/

universe v v' u u'

namespace CategoryTheory

open Opposite Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace Square

variable {sq : Square C}

lemma IsPullback.map (h : sq.IsPullback) (F : C ⥤ D) [PreservesLimit (cospan sq.f₂₄ sq.f₃₄) F] :
    (sq.map F).IsPullback :=
  Square.IsPullback.mk _ (isLimitPullbackConeMapOfIsLimit F sq.fac h.isLimit)

lemma IsPushout.map (h : sq.IsPushout) (F : C ⥤ D) [PreservesColimit (span sq.f₁₂ sq.f₁₃) F] :
    (sq.map F).IsPushout :=
  Square.IsPushout.mk _ (isColimitPushoutCoconeMapOfIsColimit F sq.fac h.isColimit)

variable (sq)

lemma isPullback_iff_map_coyoneda_isPullback :
    sq.IsPullback ↔ ∀ (X : Cᵒᵖ), (sq.map (coyoneda.obj X)).IsPullback := by
  constructor
  · intro h X
    apply h.map
  · intro h
    let e := fun {X} ↦ Equiv.ofBijective _
      ((PullbackCone.isLimitEquivBijective _).1 (h (op X)).isLimit)
    have he₁ : ∀ {X} (x), (@e X).symm x ≫ sq.f₁₂ = x.1.1 := fun {X} x ↦ by
      obtain ⟨x, rfl⟩ := e.surjective x
      simp only [Equiv.symm_apply_apply]
      rfl
    have he₂ : ∀ {X} (x), (@e X).symm x ≫ sq.f₁₃ = x.1.2 := fun {X} x ↦ by
      obtain ⟨x, rfl⟩ := e.surjective x
      simp only [Equiv.symm_apply_apply]
      rfl
    apply Square.IsPullback.mk
    refine PullbackCone.IsLimit.mk _
      (fun s ↦ e.symm ⟨⟨s.fst, s.snd⟩, s.condition⟩)
      (fun _ ↦ he₁ _) (fun s ↦ he₂ _) (fun s m hm₁ hm₂ ↦ ?_)
    apply e.injective
    rw [Equiv.apply_symm_apply]
    ext <;> assumption

lemma isPushout_iff_op_map_yoneda_isPullback :
    sq.IsPushout ↔ ∀ (X : C), (sq.op.map (yoneda.obj X)).IsPullback := by
  constructor
  · intro h X
    apply h.op.map
  · intro h
    let e := fun {X} ↦ Equiv.ofBijective _
      ((PullbackCone.isLimitEquivBijective _).1 (h X).isLimit)
    have he₁ : ∀ {X} (x), sq.f₂₄ ≫ (@e X).symm x = x.1.1 := fun {X} x ↦ by
      obtain ⟨x, rfl⟩ := e.surjective x
      simp only [Equiv.symm_apply_apply]
      rfl
    have he₂ : ∀ {X} (x), sq.f₃₄ ≫ (@e X).symm x = x.1.2 := fun {X} x ↦ by
      obtain ⟨x, rfl⟩ := e.surjective x
      simp only [Equiv.symm_apply_apply]
      rfl
    apply Square.IsPushout.mk
    refine PushoutCocone.IsColimit.mk _
      (fun s ↦ e.symm ⟨⟨s.inl, s.inr⟩, s.condition⟩)
      (fun _ ↦ he₁ _) (fun s ↦ he₂ _) (fun s m hm₁ hm₂ ↦ ?_)
    apply e.injective
    rw [Equiv.apply_symm_apply]
    ext <;> assumption

end Square

end CategoryTheory
