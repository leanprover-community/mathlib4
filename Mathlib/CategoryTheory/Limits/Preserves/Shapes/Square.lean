/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Ulift

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

lemma IsPullback.of_map (F : C ⥤ D) [ReflectsLimit (cospan sq.f₂₄ sq.f₃₄) F]
    (h : (sq.map F).IsPullback) : sq.IsPullback :=
  CategoryTheory.IsPullback.of_map F sq.fac h

variable (sq) in
lemma IsPullback.map_iff (F : C ⥤ D) [PreservesLimit (cospan sq.f₂₄ sq.f₃₄) F]
    [ReflectsLimit (cospan sq.f₂₄ sq.f₃₄) F] :
    (sq.map F).IsPullback ↔ sq.IsPullback :=
  ⟨fun h ↦ of_map F h, fun h ↦ h.map F⟩

lemma IsPushout.map (h : sq.IsPushout) (F : C ⥤ D) [PreservesColimit (span sq.f₁₂ sq.f₁₃) F] :
    (sq.map F).IsPushout :=
  Square.IsPushout.mk _ (isColimitPushoutCoconeMapOfIsColimit F sq.fac h.isColimit)

lemma IsPushout.of_map (F : C ⥤ D) [ReflectsColimit (span sq.f₁₂ sq.f₁₃) F]
    (h : (sq.map F).IsPushout) : sq.IsPushout :=
  CategoryTheory.IsPushout.of_map F sq.fac h

variable (sq) in
lemma IsPushout.map_iff (F : C ⥤ D) [PreservesColimit (span sq.f₁₂ sq.f₁₃) F]
    [ReflectsColimit (span sq.f₁₂ sq.f₁₃) F] :
    (sq.map F).IsPushout ↔ sq.IsPushout :=
  ⟨fun h ↦ of_map F h, fun h ↦ h.map F⟩

variable (sq)

lemma isPullback_iff_map_coyoneda_isPullback :
    sq.IsPullback ↔ ∀ (X : Cᵒᵖ), (sq.map (coyoneda.obj X)).IsPullback :=
  ⟨fun h _ ↦ h.map _, fun h ↦ IsPullback.mk _
    ((sq.pullbackCone.isLimitCoyonedaEquiv).symm (fun X ↦ (h X).isLimit))⟩

lemma isPushout_iff_op_map_yoneda_isPullback :
    sq.IsPushout ↔ ∀ (X : C), (sq.op.map (yoneda.obj X)).IsPullback :=
  ⟨fun h _ ↦ h.op.map _, fun h ↦ IsPushout.mk _
    ((sq.pushoutCocone.isColimitYonedaEquiv).symm
      (fun X ↦ IsLimit.ofIsoLimit (h X).isLimit (PullbackCone.ext (Iso.refl _))))⟩

section

variable {sq₁ : Square (Type v)} {sq₂ : Square (Type u)}
  (e₁ : sq₁.X₁ ≃ sq₂.X₁) (e₂ : sq₁.X₂ ≃ sq₂.X₂)
  (e₃ : sq₁.X₃ ≃ sq₂.X₃) (e₄ : sq₁.X₄ ≃ sq₂.X₄)
  (comm₁₂ : e₂ ∘ sq₁.f₁₂ = sq₂.f₁₂ ∘ e₁)
  (comm₁₃ : e₃ ∘ sq₁.f₁₃ = sq₂.f₁₃ ∘ e₁)
  (comm₂₄ : e₄ ∘ sq₁.f₂₄ = sq₂.f₂₄ ∘ e₂)
  (comm₃₄ : e₄ ∘ sq₁.f₃₄ = sq₂.f₃₄ ∘ e₃)
include comm₁₂ comm₁₃ comm₂₄ comm₃₄

variable (sq₁ sq₂) in
lemma IsPullback.iff_of_equiv : sq₁.IsPullback ↔ sq₂.IsPullback := by
  rw [← IsPullback.map_iff sq₁ uliftFunctor.{max u v},
      ← IsPullback.map_iff sq₂ uliftFunctor.{max u v}]
  refine iff_of_iso (Square.isoMk
    (((Equiv.trans Equiv.ulift e₁).trans Equiv.ulift.symm).toIso)
    (((Equiv.trans Equiv.ulift e₂).trans Equiv.ulift.symm).toIso)
    (((Equiv.trans Equiv.ulift e₃).trans Equiv.ulift.symm).toIso)
    (((Equiv.trans Equiv.ulift e₄).trans Equiv.ulift.symm).toIso)
    ?_ ?_ ?_ ?_)
  all_goals ext; apply ULift.down_injective
  · simpa [types_comp, uliftFunctor_map] using congrFun comm₁₂ _
  · simpa [types_comp, uliftFunctor_map] using congrFun comm₁₃ _
  · simpa [types_comp, uliftFunctor_map] using congrFun comm₂₄ _
  · simpa [types_comp, uliftFunctor_map] using congrFun comm₃₄ _

lemma IsPullback.of_equiv (h₁ : sq₁.IsPullback) : sq₂.IsPullback :=
  (iff_of_equiv sq₁ sq₂ e₁ e₂ e₃ e₄ comm₁₂ comm₁₃ comm₂₄ comm₃₄).1 h₁

end

end Square

end CategoryTheory
