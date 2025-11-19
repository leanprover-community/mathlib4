/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Subobject.NoetherianObject
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
import Mathlib.Order.OrderIsoNat

/-!
# Noetherian objects in an abelian category form a Serre class

-/

universe v u

open CategoryTheory ZeroObject

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {X Y : C}

namespace Abelian

variable [Abelian C]

lemma isNoetherianObject_of_epi (p : X ⟶ Y) [Epi p] [IsNoetherianObject X] :
    IsNoetherianObject Y := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro f
  obtain ⟨n, hn⟩ := monotone_chain_condition_of_isNoetherianObject
    ⟨_, (Subobject.pullback p).monotone.comp f.2⟩
  exact ⟨n, fun m hm ↦ Subobject.pullback_obj_injective p (hn m hm)⟩

instance : (isNoetherianObject (C := C)).IsClosedUnderQuotients where
  prop_of_epi f _ hX := by
    rw [← isNoetherianObject.is_iff] at hX ⊢
    exact isNoetherianObject_of_epi f

section

variable (S : ShortComplex C)

@[simps]
noncomputable def fromMonoOverOfShortComplex :
    MonoOver S.X₂ ⥤ ShortComplex C where
  obj A :=
    { X₁ := pullback A.arrow S.f
      X₂ := A.1.left
      X₃ := Limits.image (A.arrow ≫ S.g)
      f := pullback.fst _ _
      g := factorThruImage _
      zero := by simp [← cancel_mono (Limits.image.ι _), pullback.condition_assoc] }
  map {A B} φ :=
    { τ₁ := ((MonoOver.pullback S.f).map φ).left
      τ₂ := φ.left
      τ₃ := ((MonoOver.exists S.g).map φ).left
      comm₂₃ := by
        simp [← cancel_mono (Limits.image.ι _), MonoOver.w_assoc] }

variable {S}

lemma shortExact_fromMonoOverOfShortComplex_obj
    (hS : S.ShortExact) (A : MonoOver S.X₂) :
    ((fromMonoOverOfShortComplex S).obj A).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  dsimp [fromMonoOverOfShortComplex]
  exact
    { exact := by
        rw [ShortComplex.exact_iff_exact_up_to_refinements]
        intro Y x₂ hx₂
        dsimp at x₂ hx₂ ⊢
        rw [← cancel_mono (Limits.image.ι _), Category.assoc, zero_comp,
          Limits.image.fac] at hx₂
        obtain ⟨A', π, _, x₁, hx₁⟩  :=
          hS.exact.exact_up_to_refinements (x₂ ≫ A.obj.hom) (by simpa using hx₂)
        exact ⟨A', π, inferInstance, pullback.lift (π ≫ x₂) x₁ (by simpa),
          by simp⟩}

end

lemma isIso_monoOver_iff_of_shortExact
    {S : ShortComplex C} (hS : S.ShortExact)
    {A B : MonoOver S.X₂} (φ : A ⟶ B) :
    IsIso φ ↔ IsIso ((MonoOver.pullback S.f).map φ) ∧
        IsIso ((MonoOver.exists S.g).map φ) := by
  constructor
  · intro
    constructor <;> infer_instance
  · rintro ⟨h₁, h₃⟩
    rw [MonoOver.isIso_iff_isIso_left] at h₁ h₃ ⊢
    let ψ := ((fromMonoOverOfShortComplex S).map φ)
    have : IsIso ψ.τ₁ := h₁
    have : IsIso ψ.τ₃ := h₃
    exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ ψ
      (shortExact_fromMonoOverOfShortComplex_obj hS _)
      (shortExact_fromMonoOverOfShortComplex_obj hS _)

lemma isNoetherianObject_of_shortExact {S : ShortComplex C}
    (hS : S.ShortExact) (h₁ : IsNoetherianObject S.X₁)
    (h₃ : IsNoetherianObject S.X₃) :
    IsNoetherianObject S.X₂ := by
  rw [isNoetherianObject_iff_isEventuallyConstant]
  intro F₂
  obtain ⟨n₁, hn₁⟩ := isEventuallyConstant_of_isNoetherianObject
    (F₂ ⋙ MonoOver.pullback S.f)
  obtain ⟨n₃, hn₃⟩ := isEventuallyConstant_of_isNoetherianObject
    (F₂ ⋙ MonoOver.exists S.g)
  refine ⟨max n₁ n₃, fun m hm ↦ ?_⟩
  rw [isIso_monoOver_iff_of_shortExact hS]
  exact ⟨hn₁.isIso_map _ (homOfLE (le_max_left n₁ n₃)),
    hn₃.isIso_map _ (homOfLE (le_max_right n₁ n₃))⟩

instance : (isNoetherianObject (C := C)).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := by
    rw [← isNoetherianObject.is_iff] at h₁ h₃ ⊢
    exact isNoetherianObject_of_shortExact hS h₁ h₃

instance : (isNoetherianObject (C := C)).IsSerreClass where

end Abelian

end CategoryTheory
