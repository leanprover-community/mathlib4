/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.ClosedUnderIsomorphisms
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Serre classes

For any abelian category `C`, we introduce the type `SerreClass C` of Serre classes
(also known as "Serre subcategories"). A Serre class consists of a predicate
on objects of `C` which hold for the zero object and is such that if
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is a short exact sequence, then `X₂` belongs to the class
iff `X₁` and `X₃` do. This implies that the class is stable under subobjects,
quotients, extensions. As a result, if `X₁ ⟶ X₂ ⟶ X₃` is an exact sequence such
that `X₁` and `X₃` belong to the class, then so does `X₂` (see `SerreClass.prop_of_exact`).

## Future works

* Construct the localization of `C` with respect to a Serre class.

-/

universe v u

namespace CategoryTheory

open Limits ZeroObject

-- to be moved to `Algebra.Homology.ShortComplex.ShortExact`
lemma ShortComplex.Exact.shortExact {C : Type u} [Category.{v} C] [Preadditive C]
    {S : ShortComplex C} (hS : S.Exact) (h : S.HomologyData) :
    (ShortComplex.mk _ _ (h.exact_iff_i_p_zero.1 hS)).ShortExact where
  exact := by
    have := hS.epi_f' h.left
    have := hS.mono_g' h.right
    let S' := ShortComplex.mk h.left.i S.g (by simp)
    let S'' := ShortComplex.mk _ _ (h.exact_iff_i_p_zero.1 hS)
    let a : S ⟶ S' :=
      { τ₁ := h.left.f'
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _ }
    let b : S'' ⟶ S' :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := h.right.g' }
    rwa [ShortComplex.exact_iff_of_epi_of_isIso_of_mono b,
      ← ShortComplex.exact_iff_of_epi_of_isIso_of_mono a]

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- A Serre class in an abelian category consists of predicate which
is stable by subobject, quotient, extension and for the zero object. -/
structure SerreClass where
  /-- a predicate on objects -/
  prop : C → Prop
  prop_zero : prop 0
  iff_of_shortExact {S : ShortComplex C} (hS : S.ShortExact) :
    prop S.X₂ ↔ prop S.X₁ ∧ prop S.X₃

namespace SerreClass

variable {C} (c : SerreClass C)

section

variable {S : ShortComplex C} (hS : S.ShortExact)

include hS

lemma prop_X₂_of_shortExact (h₁ : c.prop S.X₁) (h₃ : c.prop S.X₃) : c.prop S.X₂ := by
  rw [c.iff_of_shortExact hS]
  constructor <;> assumption

lemma prop_X₁_of_shortExact (h₂ : c.prop S.X₂) : c.prop S.X₁ := by
  rw [c.iff_of_shortExact hS] at h₂
  exact h₂.1

lemma prop_X₃_of_shortExact (h₂ : c.prop S.X₂) : c.prop S.X₃ := by
  rw [c.iff_of_shortExact hS] at h₂
  exact h₂.2

end

lemma prop_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (hY : c.prop Y) : c.prop X := by
  have hS : (ShortComplex.mk _ _ (cokernel.condition f)).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f) }
  exact c.prop_X₁_of_shortExact hS hY

lemma prop_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (hX : c.prop X) : c.prop Y := by
  have hS : (ShortComplex.mk _ _ (kernel.condition f)).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel f) }
  exact c.prop_X₃_of_shortExact hS hX

lemma prop_iff_of_iso {X Y : C} (e : X ≅ Y) : c.prop X ↔ c.prop Y :=
  ⟨c.prop_of_epi e.hom, c.prop_of_mono e.hom⟩

instance : ClosedUnderIsomorphisms c.prop where
  of_iso e hX := by rwa [← c.prop_iff_of_iso e]

lemma prop_of_isZero {X : C} (hX : IsZero X) : c.prop X := by
  simpa only [c.prop_iff_of_iso (hX.iso (isZero_zero _))] using c.prop_zero

lemma prop_biprod {X₁ X₂ : C} (h₁ : c.prop X₁) (h₂ : c.prop X₂) :
    c.prop (X₁ ⊞ X₂) :=
  c.prop_X₂_of_shortExact
    (ShortComplex.Splitting.ofHasBinaryBiproduct X₁ X₂).shortExact h₁ h₂

lemma prop_of_exact {S : ShortComplex C} (hS : S.Exact)
    (h₁ : c.prop S.X₁) (h₃ : c.prop S.X₃) : c.prop S.X₂ := by
  let d := S.homologyData
  have := hS.epi_f' d.left
  have := hS.mono_g' d.right
  exact (c.prop_X₂_of_shortExact (hS.shortExact d)
    (c.prop_of_epi d.left.f' h₁) (c.prop_of_mono d.right.g' h₃) :)

end SerreClass

end CategoryTheory
