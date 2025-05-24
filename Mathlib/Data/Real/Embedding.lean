/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Algebra.Order.Module.OrderedSMul
import Mathlib.Tactic.Qify

/-!
# Embedding of archimedean groups into reals

This file provides embedding of any archimedean groups into reals.

## Main declarations
* `orderAddMonoidHom_real_of_pos` defines a `M →+o ℝ` for archimedean group `M`
  that maps a given positive element to the real number 1.
* `exists_orderAddMonoidHom_real_injective` states there exists an injective `M →+o ℝ`
  for any archimedean group `M`.
-/


namespace Archimedean

variable {M : Type*}
variable [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M] [Archimedean M]

/-- An auxiliary function that takes floor after multiplying by a power of two. -/
noncomputable
def kfloor {one : M} (hpos: 0 < one) (k : ℕ) (a : M) :=
  (existsUnique_zsmul_near_of_pos hpos ((2 ^ k) • a)).choose

theorem kfloor_smul_le {one : M} (hpos: 0 < one) (k : ℕ) (a : M):
    (kfloor hpos k a) • one ≤ ((2 ^ k) • a) :=
  (existsUnique_zsmul_near_of_pos hpos ((2 ^ k) • a)).choose_spec.1.1

theorem lt_kfloor_smul {one : M} (hpos: 0 < one) (k : ℕ) (a : M):
    ((2 ^ k) • a) < (kfloor hpos k a + 1) • one :=
  (existsUnique_zsmul_near_of_pos hpos ((2 ^ k) • a)).choose_spec.1.2

theorem kfloor_add_one_mem_Ico {one : M} (hpos: 0 < one) (k : ℕ) (a : M):
    kfloor hpos (k + 1) a ∈ Set.Ico (2 * (kfloor hpos k a)) (2 * (kfloor hpos k a + 1)) := by

  obtain hleft := (smul_le_smul_iff_of_pos_left (show (0 : ℤ) < 2 by simp)).mpr <|
    kfloor_smul_le hpos k a
  obtain hright := (smul_lt_smul_iff_of_pos_left (show (0 : ℤ) < 2 by simp)).mpr <|
    lt_kfloor_smul hpos k a
  rw [smul_smul, ← natCast_zsmul, smul_smul] at hleft hright
  norm_cast at hleft hright
  have : (2 * 2 ^ k : ℕ) = 2 ^ (k + 1) := by omega
  rw [this] at hleft hright

  obtain hleft' := kfloor_smul_le hpos (k + 1) a
  obtain hright' := lt_kfloor_smul hpos (k + 1) a

  constructor
  · obtain h := hleft.trans_lt hright'
    rw [smul_lt_smul_iff_of_pos_right hpos] at h
    exact Int.lt_add_one_iff.mp h
  · obtain h := hleft'.trans_lt hright
    rw [smul_lt_smul_iff_of_pos_right hpos] at h
    exact h

private theorem kfloor_add_mem_Ico {one : M} (hpos: 0 < one) (k : ℕ) (n : ℕ) (a : M):
    kfloor hpos (k + n) a ∈ Set.Ico (2 ^ n * (kfloor hpos k a)) (2 ^ n * (kfloor hpos k a + 1)) :=
    by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨ihleft, ihright⟩ := ih
    obtain ihleft := (mul_le_mul_iff_of_pos_left (show (0 : ℤ) < 2 by simp)).mpr ihleft
    obtain ihright := (mul_le_mul_iff_of_pos_left (show (0 : ℤ) < 2 by simp)).mpr
      (Int.add_one_le_iff.mpr ihright)
    rw [← mul_assoc] at ihleft ihright
    have : (2 * 2 ^ n : ℤ) = 2 ^ (n + 1) := by omega
    rw [this] at ihleft ihright
    rw [mul_add] at ihright
    rw [show (2 * 1 : ℤ) = 1 + 1 by simp] at ihright
    rw [← add_assoc] at ihright
    obtain ihright' := Int.add_one_le_iff.mp ihright

    rw [← add_assoc]
    obtain ⟨hleft, hright⟩ := kfloor_add_one_mem_Ico hpos (k + n) a
    refine ⟨ihleft.trans hleft, ?_⟩
    have hright' : kfloor hpos (k + n + 1) a ≤ 2 * (kfloor hpos (k + n) a) + 1 := by
      rw [mul_add, mul_one] at hright
      apply Int.lt_add_one_iff.mp
      rw [add_assoc _ 1 1]
      simpa using hright
    apply hright'.trans_lt ihright

private theorem aux_εbound {ε : ℚ} (h : 0 < ε) : 1 < ε * 2 ^ ⌊ε⁻¹⌋₊ := by
  suffices ε⁻¹ < 2 ^ (⌊ε⁻¹⌋₊) by
    apply (inv_mul_lt_iff₀ h).mp
    simpa using this
  apply lt_of_lt_of_le (Nat.lt_floor_add_one ε⁻¹)
  generalize ⌊ε⁻¹⌋₊ = n
  norm_cast
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.pow_add_one, mul_two]
    apply add_le_add ih
    exact Nat.one_le_two_pow

/-- An unbundled function that embeds archimedean`M` into `ℝ`.
The given element `one` is mapped to the real number 1. -/
noncomputable
abbrev embed_real {one : M} (hpos: 0 < one) (a : M) : ℝ :=
  Real.mk ⟨fun k ↦ (kfloor hpos k a / (2 ^ k) : ℚ), by
    intro ε hε
    use ⌊ε⁻¹⌋₊
    intro k hk
    simp only
    have : ((kfloor hpos ⌊ε⁻¹⌋₊ a) / 2 ^ ⌊ε⁻¹⌋₊ : ℚ) =
      2 ^ (k - ⌊ε⁻¹⌋₊) * (kfloor hpos ⌊ε⁻¹⌋₊ a) / 2 ^ k := by
      rw [div_eq_div_iff (by simp) (by simp)]
      rw [mul_comm (2 ^ (k - ⌊ε⁻¹⌋₊)), mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
    rw [this, ← sub_div, abs_div, div_lt_iff₀ (by simp)]
    apply lt_of_le_of_lt (b := 2 ^ (k - ⌊ε⁻¹⌋₊))
    · have : k = k - ⌊ε⁻¹⌋₊ + ⌊ε⁻¹⌋₊ := (Nat.sub_eq_iff_eq_add hk).mp rfl
      nth_rw 1 [this]
      obtain ⟨hleft, hright⟩ := kfloor_add_mem_Ico hpos ⌊ε⁻¹⌋₊ (k - ⌊ε⁻¹⌋₊) a
      rw [abs_le]
      constructor
      · simp only [neg_le_sub_iff_le_add]
        qify at hleft
        apply le_trans hleft
        rw [add_comm]
        simp
      · apply sub_left_le_of_le_add
        rw [add_comm]
        qify at hright
        rw [← mul_add_one]
        exact le_of_lt hright
    · rw [abs_eq_self.mpr (by simp), ← one_lt_div (by simp), mul_div_assoc, div_eq_mul_inv]
      rw [← pow_sub₀ _ (by simp) (by simp), Nat.sub_sub_self (hk)]
      exact aux_εbound hε
  ⟩

theorem embed_real_map_zero {one : M} (hpos: 0 < one) : embed_real hpos 0 = 0 := by
  convert Real.mk_zero
  rw [Subtype.eq_iff, CauSeq.coe_zero]
  ext k
  obtain hleft := kfloor_smul_le hpos k 0
  obtain hright := lt_kfloor_smul hpos k 0
  rw [smul_zero] at hleft hright
  rw [smul_nonpos_iff, or_iff_right (by simp [hpos])] at hleft
  rw [smul_pos_iff_of_pos_right hpos] at hright
  obtain hle := hleft.1
  obtain hge := Int.add_one_le_iff.mpr (Int.sub_lt_iff.mpr hright)
  simp only [zero_sub, Int.reduceNeg, neg_add_cancel] at hge
  simpa using le_antisymm hle hge

theorem embed_real_map_add {one : M} (hpos: 0 < one) (a b : M) :
    embed_real hpos (a + b) = embed_real hpos a + embed_real hpos b := by
  rw [← Real.mk_add, Real.mk_eq]
  intro ε hε
  use ⌊ε⁻¹⌋₊
  intro k hk
  simp only [CauSeq.sub_apply, CauSeq.add_apply]
  rw [← add_div, ← sub_div, abs_div, div_lt_iff₀ (by simp)]
  apply lt_of_le_of_lt (b := 1)
  · obtain hal := kfloor_smul_le hpos k a
    obtain har := lt_kfloor_smul hpos k a
    obtain hbl := kfloor_smul_le hpos k b
    obtain hbr := lt_kfloor_smul hpos k b
    obtain habl := kfloor_smul_le hpos k (a + b)
    obtain habr := lt_kfloor_smul hpos k (a + b)
    obtain habl' := add_le_add hal hbl
    obtain habr' := add_lt_add har hbr
    rw [← smul_add, ← add_smul] at habl' habr'

    obtain hab1 := (smul_lt_smul_iff_of_pos_right hpos).mp <| lt_of_le_of_lt habl' habr
    obtain hab2 := (smul_lt_smul_iff_of_pos_right hpos).mp <| lt_of_le_of_lt habl habr'
    rw [add_right_comm, Int.lt_add_one_iff, ← add_assoc] at hab2
    qify at hab1 hab2

    rw [abs_le]
    exact ⟨by simpa using hab1.le, sub_left_le_of_le_add hab2⟩
  · rw [abs_eq_self.mpr (by simp)]
    apply lt_of_lt_of_le (aux_εbound hε)
    rw [mul_le_mul_left hε]
    exact pow_le_pow_right₀ (by simp) hk

theorem embed_real_strictMono {one : M} (hpos: 0 < one) : StrictMono (embed_real hpos) := by
  intro a b hab
  have : b = a + (b - a) := by abel
  rw [this, embed_real_map_add, lt_add_iff_pos_right]
  set x := b - a
  have hx : 0 < x := sub_pos.mpr hab
  obtain ⟨s, hs⟩ := arch one hx

  rw [Real.mk_pos]

  have hpos : ∃ k, 0 < kfloor hpos k x := by
    by_contra! hkfloor
    have (k) : (kfloor hpos k x + 1) • one ≤ one := by
      nth_rw 3 [show one = (1: ℤ) • one by simp]
      rw [smul_le_smul_iff_of_pos_right hpos]
      simpa using hkfloor k
    have (k) : ((2 ^ k) • x) < one := lt_of_lt_of_le (lt_kfloor_smul _ _ _ ) (this k)
    obtain hxx : 2 ^ s < s := (nsmul_left_monotone hx.le).reflect_lt (lt_of_lt_of_le (this s) hs)
    contrapose! hxx
    generalize s = a
    induction a with
    | zero => simp
    | succ a ih =>
      rw [Nat.pow_add_one, mul_two]
      exact add_le_add ih Nat.one_le_two_pow

  obtain ⟨k, hk⟩ := hpos
  refine ⟨1 / 2 ^ k, ⟨by simp, ⟨k, ?_⟩⟩⟩
  intro j hj
  obtain hleft := (kfloor_add_mem_Ico hpos k (j - k) x).1
  have : k + (j - k) = j := Nat.add_sub_of_le hj
  rw [this] at hleft
  qify at hleft

  simp only
  rw [le_div_iff₀ (by simp), one_div_mul_eq_div, div_eq_mul_inv, ← pow_sub₀ _ (by simp) hj]
  refine le_trans ?_ hleft
  simpa using Int.cast_one_le_of_pos hk

/-- The bundled `M →+o ℝ` for archimedean `M`.
The given element `one` is mapped to the real number 1. -/
noncomputable
def orderAddMonoidHom_real_of_pos {one : M} (hpos: 0 < one) : M →+o ℝ where
  toFun := embed_real hpos
  map_zero' := embed_real_map_zero hpos
  map_add' := embed_real_map_add hpos
  monotone' := (embed_real_strictMono hpos).monotone

theorem orderAddMonoidHom_real_apply {one : M} (hpos: 0 < one) (a : M):
    (orderAddMonoidHom_real_of_pos hpos) a = embed_real hpos a := by rfl

theorem orderAddMonoidHom_real_of_pos_injective {one : M} (hpos: 0 < one) :
    Function.Injective (orderAddMonoidHom_real_of_pos hpos) :=
  (embed_real_strictMono hpos).injective

theorem orderAddMonoidHom_real_map_one {one : M} (hpos: 0 < one) :
    (orderAddMonoidHom_real_of_pos hpos) one = 1 := by
  rw [← Real.mk_one, orderAddMonoidHom_real_apply, Real.mk_eq]
  intro ε hε
  use ⌊ε⁻¹⌋₊
  intro k hk
  simp only [CauSeq.sub_apply, CauSeq.one_apply]
  rw [div_sub_one (by simp), abs_div, div_lt_iff₀ (by simp)]

  have hnonpos : kfloor hpos k one - (2 : ℚ) ^ k ≤ 0 := by
    apply sub_nonpos_of_le
    norm_cast
    apply (zsmul_left_strictMono hpos).le_iff_le.mp
    rw [natCast_zsmul]
    apply kfloor_smul_le

  rw [abs_eq_neg_self.mpr hnonpos, neg_sub]
  rw [abs_eq_self.mpr (by simp)]
  rw [sub_lt_comm]
  rw [← add_lt_add_iff_right 1]
  have : (2 : ℚ) ^ k < kfloor hpos k one + 1 := by
    norm_cast
    apply (zsmul_left_strictMono hpos).lt_iff_lt.mp
    rw [natCast_zsmul]
    apply lt_kfloor_smul

  refine lt_trans ?_ this
  rw [sub_add]
  suffices 1 < ε * 2 ^ k by simpa using this
  apply lt_of_lt_of_le (aux_εbound hε)
  rw [mul_le_mul_left hε]
  exact pow_le_pow_right₀ (by simp) hk

variable (M) in
theorem exists_orderAddMonoidHom_real_injective :
    ∃ f : M →+o ℝ, Function.Injective f := by
  by_cases h : Subsingleton M
  · let f : M →+o ℝ := {
      toFun := fun _ ↦ 0
      map_zero' := by simp
      map_add' := by simp
      monotone' := by
        intro a b h
        simp
    }
    exact ⟨f, Function.injective_of_subsingleton _⟩
  · have : Nontrivial M := not_subsingleton_iff_nontrivial.mp h
    obtain ⟨a, ha⟩ := exists_ne (0 : M)
    have ha : 0 < |a| := by simpa using ha
    exact ⟨orderAddMonoidHom_real_of_pos ha, orderAddMonoidHom_real_of_pos_injective ha⟩

end Archimedean
