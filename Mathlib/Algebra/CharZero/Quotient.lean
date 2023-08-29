/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.GroupTheory.QuotientGroup

#align_import algebra.char_zero.quotient from "leanprover-community/mathlib"@"d90e4e186f1d18e375dcd4e5b5f6364b01cb3e46"

/-!
# Lemmas about quotients in characteristic zero
-/


variable {R : Type*} [DivisionRing R] [CharZero R] {p : R}

namespace AddSubgroup

/-- `z • r` is a multiple of `p` iff `r` is `pk/z` above a multiple of `p`, where `0 ≤ k < |z|`. -/
theorem zsmul_mem_zmultiples_iff_exists_sub_div {r : R} {z : ℤ} (hz : z ≠ 0) :
    z • r ∈ AddSubgroup.zmultiples p ↔
      ∃ k : Fin z.natAbs, r - (k : ℕ) • (p / z : R) ∈ AddSubgroup.zmultiples p := by
  rw [AddSubgroup.mem_zmultiples_iff]
  -- ⊢ (∃ k, k • p = z • r) ↔ ∃ k, r - ↑k • (p / ↑z) ∈ zmultiples p
  simp_rw [AddSubgroup.mem_zmultiples_iff, div_eq_mul_inv, ← smul_mul_assoc, eq_sub_iff_add_eq]
  -- ⊢ (∃ k, k • p = z • r) ↔ ∃ k k_1, k_1 • p + ↑k • p * (↑z)⁻¹ = r
  have hz' : (z : R) ≠ 0 := Int.cast_ne_zero.mpr hz
  -- ⊢ (∃ k, k • p = z • r) ↔ ∃ k k_1, k_1 • p + ↑k • p * (↑z)⁻¹ = r
  conv_rhs => simp (config := { singlePass := true }) only [← (mul_right_injective₀ hz').eq_iff]
  -- ⊢ (∃ k, k • p = z • r) ↔ ∃ k k_1, (fun x x_1 => x * x_1) (↑z) (k_1 • p + ↑k •  …
  simp_rw [← zsmul_eq_mul, smul_add, ← mul_smul_comm, zsmul_eq_mul (z : R)⁻¹, mul_inv_cancel hz',
    mul_one, ← coe_nat_zsmul, smul_smul, ← add_smul]
  constructor
  -- ⊢ (∃ k, k • p = z • r) → ∃ k k_1, (z * k_1 + ↑↑k) • p = z • r
  · rintro ⟨k, h⟩
    -- ⊢ ∃ k k_1, (z * k_1 + ↑↑k) • p = z • r
    simp_rw [← h]
    -- ⊢ ∃ k_1 k_2, (z * k_2 + ↑↑k_1) • p = k • p
    refine' ⟨⟨(k % z).toNat, _⟩, k / z, _⟩
    -- ⊢ Int.toNat (k % z) < Int.natAbs z
    · rw [← Int.ofNat_lt, Int.toNat_of_nonneg (Int.emod_nonneg _ hz)]
      -- ⊢ k % z < ↑(Int.natAbs z)
      exact (Int.emod_lt _ hz).trans_eq (Int.abs_eq_natAbs _)
      -- 🎉 no goals
    rw [Fin.val_mk, Int.toNat_of_nonneg (Int.emod_nonneg _ hz)]
    -- ⊢ (z * (k / z) + k % z) • p = k • p
    nth_rewrite 3 [← Int.div_add_mod k z]
    -- ⊢ (z * (k / z) + k % z) • p = (z * Int.div k z + Int.mod k z) • p
    rw [Int.mod_def, ← Int.div_def', Int.emod_def]
    -- ⊢ (z * (k / z) + (k - z * (k / z))) • p = (z * (k / z) + (k - z * (k / z))) • p
    simp only [add_sub_cancel'_right, zsmul_eq_mul, Int.div_def']
    -- 🎉 no goals
  · rintro ⟨k, n, h⟩
    -- ⊢ ∃ k, k • p = z • r
    exact ⟨_, h⟩
    -- 🎉 no goals
#align add_subgroup.zsmul_mem_zmultiples_iff_exists_sub_div AddSubgroup.zsmul_mem_zmultiples_iff_exists_sub_div

theorem nsmul_mem_zmultiples_iff_exists_sub_div {r : R} {n : ℕ} (hn : n ≠ 0) :
    n • r ∈ AddSubgroup.zmultiples p ↔
      ∃ k : Fin n, r - (k : ℕ) • (p / n : R) ∈ AddSubgroup.zmultiples p := by
  rw [← coe_nat_zsmul r, zsmul_mem_zmultiples_iff_exists_sub_div (Int.coe_nat_ne_zero.mpr hn),
    Int.cast_ofNat]
  rfl
  -- 🎉 no goals
#align add_subgroup.nsmul_mem_zmultiples_iff_exists_sub_div AddSubgroup.nsmul_mem_zmultiples_iff_exists_sub_div

end AddSubgroup

namespace QuotientAddGroup

theorem zmultiples_zsmul_eq_zsmul_iff {ψ θ : R ⧸ AddSubgroup.zmultiples p} {z : ℤ} (hz : z ≠ 0) :
    z • ψ = z • θ ↔ ∃ k : Fin z.natAbs, ψ = θ + (k : ℕ) • (p / z : R) := by
  induction ψ using Quotient.inductionOn'
  -- ⊢ z • Quotient.mk'' a✝ = z • θ ↔ ∃ k, Quotient.mk'' a✝ = θ + ↑(↑k • (p / ↑z))
  induction θ using Quotient.inductionOn'
  -- ⊢ z • Quotient.mk'' a✝¹ = z • Quotient.mk'' a✝ ↔ ∃ k, Quotient.mk'' a✝¹ = Quot …
  -- Porting note: Introduced Zp notation to shorten lines
  let Zp := AddSubgroup.zmultiples p
  -- ⊢ z • Quotient.mk'' a✝¹ = z • Quotient.mk'' a✝ ↔ ∃ k, Quotient.mk'' a✝¹ = Quot …
  have : (Quotient.mk'' : R → R ⧸ Zp) = ((↑) : R → R ⧸ Zp) := rfl
  -- ⊢ z • Quotient.mk'' a✝¹ = z • Quotient.mk'' a✝ ↔ ∃ k, Quotient.mk'' a✝¹ = Quot …
  simp only [this]
  -- ⊢ z • ↑a✝¹ = z • ↑a✝ ↔ ∃ k, ↑a✝¹ = ↑a✝ + ↑(↑k • (p / ↑z))
  simp_rw [← QuotientAddGroup.mk_zsmul, ← QuotientAddGroup.mk_add,
    QuotientAddGroup.eq_iff_sub_mem, ← smul_sub, ← sub_sub]
  exact AddSubgroup.zsmul_mem_zmultiples_iff_exists_sub_div hz
  -- 🎉 no goals
#align quotient_add_group.zmultiples_zsmul_eq_zsmul_iff QuotientAddGroup.zmultiples_zsmul_eq_zsmul_iff

theorem zmultiples_nsmul_eq_nsmul_iff {ψ θ : R ⧸ AddSubgroup.zmultiples p} {n : ℕ} (hz : n ≠ 0) :
    n • ψ = n • θ ↔ ∃ k : Fin n, ψ = θ + (k : ℕ) • (p / n : R) := by
  rw [← coe_nat_zsmul ψ, ← coe_nat_zsmul θ,
    zmultiples_zsmul_eq_zsmul_iff (Int.coe_nat_ne_zero.mpr hz), Int.cast_ofNat]
  rfl
  -- 🎉 no goals
#align quotient_add_group.zmultiples_nsmul_eq_nsmul_iff QuotientAddGroup.zmultiples_nsmul_eq_nsmul_iff

end QuotientAddGroup
