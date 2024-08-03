/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Square
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-!
# Commutative squares that are pushout or pullback squares

In this file, we translate the `IsPushout` and `IsPullback`
API for the objects of the category `Square C` of commutative
squares in a category `C`.

-/

universe v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace Square

variable (sq : Square C)

/-- The pullback cone attached to a commutative square. -/
abbrev pullbackCone : PullbackCone sq.f₂₄ sq.f₃₄ :=
  PullbackCone.mk sq.f₁₂ sq.f₁₃ sq.fac

/-- The pushout cocone attached to a commutative square. -/
abbrev pushoutCocone : PushoutCocone sq.f₁₂ sq.f₁₃ :=
  PushoutCocone.mk sq.f₂₄ sq.f₃₄ sq.fac

/-- The condition that a commutative square is a pullback square. -/
protected def IsPullback : Prop :=
  IsPullback sq.f₁₂ sq.f₁₃ sq.f₂₄ sq.f₃₄

/-- The condition that a commutative square is a pushout square. -/
protected def IsPushout : Prop :=
  IsPushout sq.f₁₂ sq.f₁₃ sq.f₂₄ sq.f₃₄

lemma isPullback_iff :
    sq.IsPullback ↔ Nonempty (IsLimit sq.pullbackCone) :=
  ⟨fun h ↦ ⟨h.isLimit⟩, fun h ↦ { w := sq.fac, isLimit' := h }⟩

lemma isPushout_iff :
    sq.IsPushout ↔ Nonempty (IsColimit sq.pushoutCocone) :=
  ⟨fun h ↦ ⟨h.isColimit⟩, fun h ↦ { w := sq.fac, isColimit' := h }⟩

lemma IsPullback.mk (h : IsLimit sq.pullbackCone) : sq.IsPullback :=
  sq.isPullback_iff.2 ⟨h⟩

lemma IsPushout.mk (h : IsColimit sq.pushoutCocone) : sq.IsPushout :=
  sq.isPushout_iff.2 ⟨h⟩

variable {sq}

/-- If a commutative square `sq` is a pullback square,
then `sq.pullbackCone` is limit. -/
noncomputable def IsPullback.isLimit (h : sq.IsPullback) :
    IsLimit sq.pullbackCone :=
  CategoryTheory.IsPullback.isLimit h

/-- If a commutative square `sq` is a pushout square,
then `sq.pushoutCocone` is colimit. -/
noncomputable def IsPushout.isColimit (h : sq.IsPushout) :
    IsColimit sq.pushoutCocone :=
  CategoryTheory.IsPushout.isColimit h

lemma IsPullback.of_iso {sq₁ sq₂ : Square C} (h : sq₁.IsPullback)
    (e : sq₁ ≅ sq₂) : sq₂.IsPullback := by
  refine CategoryTheory.IsPullback.of_iso h
    (evaluation₁.mapIso e) (evaluation₂.mapIso e)
    (evaluation₃.mapIso e) (evaluation₄.mapIso e) ?_ ?_ ?_ ?_
  all_goals aesop_cat

lemma IsPullback.iff_of_iso {sq₁ sq₂ : Square C} (e : sq₁ ≅ sq₂) :
    sq₁.IsPullback ↔ sq₂.IsPullback :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

lemma IsPushout.of_iso {sq₁ sq₂ : Square C} (h : sq₁.IsPushout)
    (e : sq₁ ≅ sq₂) : sq₂.IsPushout := by
  refine CategoryTheory.IsPushout.of_iso h
    (evaluation₁.mapIso e) (evaluation₂.mapIso e)
    (evaluation₃.mapIso e) (evaluation₄.mapIso e) ?_ ?_ ?_ ?_
  all_goals aesop_cat

lemma IsPushout.iff_of_iso {sq₁ sq₂ : Square C} (e : sq₁ ≅ sq₂) :
    sq₁.IsPushout ↔ sq₂.IsPushout :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

lemma IsPushout.op {sq : Square C} (h : sq.IsPushout) : sq.op.IsPullback :=
  CategoryTheory.IsPushout.op h.flip

lemma IsPushout.unop {sq : Square Cᵒᵖ} (h : sq.IsPushout) : sq.unop.IsPullback :=
  CategoryTheory.IsPushout.unop h.flip

lemma IsPullback.op {sq : Square C} (h : sq.IsPullback) : sq.op.IsPushout :=
  CategoryTheory.IsPullback.op h.flip

lemma IsPullback.unop {sq : Square Cᵒᵖ} (h : sq.IsPullback) : sq.unop.IsPushout :=
  CategoryTheory.IsPullback.unop h.flip

variable {D : Type u'} [Category.{v'} D] (F : C ⥤ D)

lemma IsPullback.map {sq : Square C} [PreservesLimitsOfShape WalkingCospan F] (h : sq.IsPullback) :
    (sq.map F).IsPullback :=
  F.map_isPullback h

lemma IsPullback.of_map {sq : Square C} [ReflectsLimitsOfShape WalkingCospan F]
    (h : (sq.map F).IsPullback) : sq.IsPullback :=
  CategoryTheory.IsPullback.of_map F sq.fac h

lemma IsPullback.map_iff {sq : Square C} [PreservesLimitsOfShape WalkingCospan F]
    [ReflectsLimitsOfShape WalkingCospan F] : (sq.map F).IsPullback ↔ sq.IsPullback :=
  ⟨IsPullback.of_map _, IsPullback.map _⟩

section

variable
  {sq₁ : Square (Type v)}
  {sq₂ : Square (Type u)}
  (e₁ : sq₁.X₁ ≃ sq₂.X₁) (e₂ : sq₁.X₂ ≃ sq₂.X₂)
  (e₃ : sq₁.X₃ ≃ sq₂.X₃) (e₄ : sq₁.X₄ ≃ sq₂.X₄)
  (comm₁₂ : e₂ ∘ sq₁.f₁₂ = sq₂.f₁₂ ∘ e₁)
  (comm₁₃ : e₃ ∘ sq₁.f₁₃ = sq₂.f₁₃ ∘ e₁)
  (comm₂₄ : e₄ ∘ sq₁.f₂₄ = sq₂.f₂₄ ∘ e₂)
  (comm₃₄ : e₄ ∘ sq₁.f₃₄ = sq₂.f₃₄ ∘ e₃)

variable (sq₁ sq₂) in
lemma IsPullback.iff_of_equiv : sq₁.IsPullback ↔ sq₂.IsPullback := by
  rw [← IsPullback.map_iff (sq := sq₁) uliftFunctor.{max u v},
      ← IsPullback.map_iff (sq := sq₂) uliftFunctor.{max u v}]
  apply iff_of_iso
  refine Square.isoMk
    (((Equiv.trans Equiv.ulift e₁).trans Equiv.ulift.symm).toIso)
    (((Equiv.trans Equiv.ulift e₂).trans Equiv.ulift.symm).toIso)
    (((Equiv.trans Equiv.ulift e₃).trans Equiv.ulift.symm).toIso)
    (((Equiv.trans Equiv.ulift e₄).trans Equiv.ulift.symm).toIso)
    ?_ ?_ ?_ ?_
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
