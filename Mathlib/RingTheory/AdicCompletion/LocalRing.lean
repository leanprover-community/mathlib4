/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/

import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.Defs

/-!
# Basic Properties of Complete Local Ring

In this file we proved that a ring that is adic complete with respect to a maximal ideal
ia a local ring (complete local ring).

-/

variable {R : Type*} [CommRing R] (m : Ideal R) [hmax : m.IsMaximal]

open Ideal Quotient

lemma isUnit_iff_nmem_of_isAdicComplete_maximal [IsAdicComplete m R] (r : R) :
    IsUnit r ↔ r ∉ m := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra mem
    rcases IsUnit.exists_left_inv h with ⟨s, hs⟩
    absurd m.ne_top_iff_one.mp (Ideal.IsMaximal.ne_top hmax)
    simp [← hs, Ideal.mul_mem_left m s mem]
  · have mapu {n : ℕ} (npos : n > 0) : IsUnit (Ideal.Quotient.mk (m ^ n) r) := by
      induction' n with n ih
      · absurd npos
        exact Nat.not_lt_zero 0
      · by_cases neq0 : n = 0
        · let max' : (m ^ (n + 1)).IsMaximal := by simpa only [neq0, zero_add, pow_one] using hmax
          let hField : Field (R ⧸ m ^ (n + 1)) := Ideal.Quotient.field (m ^ (n + 1))
          simpa [isUnit_iff_ne_zero, ne_eq, Ideal.Quotient.eq_zero_iff_mem.not, neq0] using h
        · apply factorPowSucc.isUnit_of_IsUnit_image (Nat.zero_lt_of_ne_zero neq0)
          simpa using (ih (Nat.zero_lt_of_ne_zero neq0))
    choose inv_series' inv_series_spec' using fun (n : {n : ℕ // n > 0}) ↦
      (IsUnit.exists_left_inv (mapu n.2))
    let inv_series : ℕ → R := fun n ↦ if h : n = 0 then 0 else Classical.choose <|
      (Ideal.Quotient.mk_surjective (I := m ^ n)) <| inv_series' ⟨n, (Nat.zero_lt_of_ne_zero h)⟩
    have inv_series_spec {n : ℕ} (npos : n > 0): (Ideal.Quotient.mk (m ^ n)) (inv_series n) =
      inv_series' ⟨n, npos⟩ := by
      simpa only [Nat.not_eq_zero_of_lt npos, inv_series]
      using Classical.choose_spec (Ideal.Quotient.mk_surjective (inv_series' ⟨n, npos⟩))
    have mod : ∀ {a b : ℕ}, a ≤ b → inv_series a ≡ inv_series b
      [SMOD m ^ a • (⊤ : Submodule R R)] := by
      intro a b le
      by_cases apos : a > 0
      · simp only [smul_eq_mul, Ideal.mul_top]
        rw [SModEq.sub_mem, ← eq_zero_iff_mem, map_sub, ← (mapu apos).mul_right_inj,
          mul_zero, mul_sub]
        nth_rw 3 [← factor_mk (pow_le_pow_right le), ← factor_mk (pow_le_pow_right le)]
        simp only [inv_series_spec apos, inv_series_spec (Nat.lt_of_lt_of_le apos le)]
        rw [← _root_.map_mul, mul_comm, inv_series_spec', mul_comm, inv_series_spec',
          map_one, sub_self]
      · simp [Nat.eq_zero_of_not_pos apos]
    rcases IsPrecomplete.prec IsAdicComplete.toIsPrecomplete mod with ⟨inv, hinv⟩
    have eq (n : ℕ): inv * r - 1 ≡ 0 [SMOD m ^ n • (⊤ : Submodule R R)] := by
      by_cases npos : n > 0
      · apply SModEq.sub_mem.mpr
        simp only [smul_eq_mul, Ideal.mul_top, sub_zero, ← eq_zero_iff_mem]
        rw [map_sub, map_one, _root_.map_mul, ← sub_add_cancel inv (inv_series n), map_add]
        have := SModEq.sub_mem.mp (hinv n).symm
        simp only [smul_eq_mul, Ideal.mul_top] at this
        simp [Ideal.Quotient.eq_zero_iff_mem.mpr this, inv_series_spec npos, inv_series_spec']
      · simp [Nat.eq_zero_of_not_pos npos]
    apply isUnit_iff_exists_inv'.mpr
    use inv
    exact sub_eq_zero.mp <| IsHausdorff.haus IsAdicComplete.toIsHausdorff (inv * r - 1) eq

theorem isLocalRing_of_isAdicComplete_maximal [IsAdicComplete m R] : IsLocalRing R where
  exists_pair_ne := ⟨0, 1, ne_of_mem_of_not_mem m.zero_mem
    (m.ne_top_iff_one.mp (Ideal.IsMaximal.ne_top hmax))⟩
  isUnit_or_isUnit_of_add_one {a b} hab := by
    simp only [isUnit_iff_nmem_of_isAdicComplete_maximal m]
    by_contra h
    push_neg at h
    absurd m.add_mem h.1 h.2
    simpa [hab] using m.ne_top_iff_one.mp (Ideal.IsMaximal.ne_top hmax)
