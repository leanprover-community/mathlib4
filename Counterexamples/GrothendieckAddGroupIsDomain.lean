/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.Localization.Additive

/-!
# The ring of differences of a commutative domain may not be a domain

The ring of differences is also known as the Grothendieck ring (`GrothendieckAddGroup` in Mathlib).
This example was constructed as a subsemiring of `ℤ[√1]` by Gemini 2.5 Pro.
-/

/-- The subsemiring of `ℤ[√1]` consisting of `0` and elements `a + b√1` with `0 ≤ b < a`. -/
def Subsemiring.zsqrtdOneNatGT : Subsemiring (ℤ√1) where
  carrier := {0} ∪ {z | 0 ≤ z.im ∧ z.im < z.re}
  mul_mem' := by
    rintro a b (rfl | ⟨h0a, ha⟩) (rfl | ⟨h0b, hb⟩)
    · exact .inl rfl
    · exact .inl (zero_mul _)
    · exact .inl (mul_zero _)
    rw [Set.mem_union, Set.mem_setOf, Zsqrtd.mul_im, Zsqrtd.mul_re, one_mul]
    have := h0a.trans_lt ha
    have := h0b.trans_lt hb
    exact .inr ⟨by positivity, mul_add_mul_lt_mul_add_mul' ha hb⟩
  one_mem' := .inr ⟨le_rfl, zero_lt_one⟩
  add_mem' := by
    rintro a b (rfl | ha) (rfl | hb)
    · exact .inl rfl
    · exact .inr (by rwa [zero_add])
    · exact .inr (by rwa [add_zero])
    · exact .inr ⟨add_nonneg ha.1 hb.1, add_lt_add ha.2 hb.2⟩
  zero_mem' := .inl rfl

namespace Subsemiring.zsqrtdOneNatGT

variable {z : ℤ√1}

lemma re_nonneg (hz : z ∈ zsqrtdOneNatGT) : 0 ≤ z.re := by
  obtain rfl | h := hz
  exacts [le_rfl, h.1.trans h.2.le]

lemma im_nonneg (hz : z ∈ zsqrtdOneNatGT) : 0 ≤ z.im := by
  obtain rfl | h := hz
  exacts [le_rfl, h.1]

lemma norm_eq_zero_iff_of_mem (hz : z ∈ zsqrtdOneNatGT) : z.re ^ 2 - z.im ^ 2 = 0 ↔ z = 0 where
  mp eq := hz.resolve_right fun h ↦ h.2.ne' <| by
    rwa [sub_eq_zero, sq_eq_sq₀ (re_nonneg hz) (im_nonneg hz)] at eq
  mpr h := by simp [h]

open Zsqrtd

instance : IsLeftCancelMulZero zsqrtdOneNatGT where
  mul_left_cancel_of_ne_zero := by
    rintro ⟨a, ha⟩ ha0 ⟨b, hb⟩ ⟨c, hc⟩ eq
    rw [← Subtype.coe_ne_coe] at ha0
    have hn := (norm_eq_zero_iff_of_mem ha).not.mpr ha0
    replace ha := ha.resolve_left ha0
    simp_rw [Subtype.ext_iff, Zsqrtd.ext_iff, coe_mul, mul_re, mul_im, one_mul] at eq ⊢
    suffices b.re = c.re by
      rw [this, add_right_cancel_iff] at eq
      exact ⟨this, mul_left_cancel₀ (ha.1.trans_lt ha.2).ne' eq.2⟩
    apply mul_left_cancel₀ hn
    convert congr(a.re * $(eq.1) - a.im * $(eq.2)) using 1 <;> ring

instance : IsDomain zsqrtdOneNatGT where
  __ := IsLeftCancelMulZero.to_isCancelMulZero

theorem not_noZeroDivisors_zsqrtd_one : ¬ NoZeroDivisors (ℤ√1) := fun _ ↦ by
  obtain h | h := eq_zero_or_eq_zero_of_mul_eq_zero (show (⟨1, 1⟩ * ⟨1, -1⟩ : ℤ√1) = 0 by rfl)
  all_goals cases h

theorem isLocalizationMap_subtype :
    (⊤ : AddSubmonoid zsqrtdOneNatGT).IsLocalizationMap zsqrtdOneNatGT.subtype :=
  AddSubmonoid.isLocalizationMap_of_addGroup Subtype.val_injective fun z ↦ by
    let yi := max 0 (-z.im)
    let yr := yi + 1 + max 0 (z.im - z.re)
    refine ⟨⟨⟨yr + z.re, yi + z.im⟩, .inr ?_⟩, ⟨⟨yr, yi⟩, .inr ?_⟩, ⟨⟩, by ext <;> simp⟩
    all_goals simp_rw [Set.mem_setOf, yi, yr]; omega

open Algebra (GrothendieckAddGroup)

/-- The canonical ring isomorphism between the Grothendieck ring of the subsemiring
`zsqrtdOneNatGT` and `ℤ[√1]`. -/
noncomputable def grothendieckAddGroupRingEquiv : GrothendieckAddGroup zsqrtdOneNatGT ≃+* ℤ√1 :=
  .symm <| isLocalizationMap_subtype.ringEquiv (g := GrothendieckAddGroup.ringHom _)
    (AddLocalization.addMonoidOf ⊤).isLocalizationMap

theorem not_noZeroDivisors_grothendieckAddGroup_zsqrtdOneNatGT :
    ¬ NoZeroDivisors (GrothendieckAddGroup zsqrtdOneNatGT) :=
  fun _ ↦ not_noZeroDivisors_zsqrtd_one grothendieckAddGroupRingEquiv.symm.noZeroDivisors

theorem not_isDomain_imp_isDomain_grothendieckAddGroup :
    ¬ ∀ (R : Type) [CommSemiring R] [IsCancelAdd R]
      [IsDomain R], IsDomain (GrothendieckAddGroup R) :=
  fun _ ↦ not_noZeroDivisors_grothendieckAddGroup_zsqrtdOneNatGT inferInstance

end Subsemiring.zsqrtdOneNatGT
