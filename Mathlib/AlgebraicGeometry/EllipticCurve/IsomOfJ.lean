/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.FieldTheory.IsSepClosed

/-!

# Elliptic curves with same j-invariants are isomorphic

## Main results

- `WeierstrassCurve.exists_variableChange_of_j_eq`: if `E` and `E'` are elliptic curves with the
  same `j`-invariants defined over a separably closed field, then there exists a change of variables
  over that field which change `E` into `E'`.

-/

open Polynomial

variable {F : Type*} [Field F] [IsSepClosed F]

namespace WeierstrassCurve

variable (E E' : WeierstrassCurve F) [E.IsElliptic] [E'.IsElliptic]

section CharTwo

variable [CharP F 2]

omit [E.IsElliptic] [E'.IsElliptic] in
private lemma exists_variableChange_of_char_two_of_j_ne_zero
    [E.IsCharTwoJNeZeroNF] [E'.IsCharTwoJNeZeroNF] (heq : E.a₆ = E'.a₆) :
    ∃ C : VariableChange F, C • E = E' := by
  obtain ⟨s, hs⟩ := IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C' 2 2
    1 1 (E.a₂ + E'.a₂) (by norm_num) (by norm_num) one_ne_zero
  use ⟨1, 0, s, 0⟩
  ext
  · simp_rw [variableChange_a₁, inv_one, Units.val_one, a₁_of_isCharTwoJNeZeroNF]
    linear_combination s * CharP.cast_eq_zero F 2
  · simp_rw [variableChange_a₂, inv_one, Units.val_one, a₁_of_isCharTwoJNeZeroNF]
    linear_combination -hs + E.a₂ * CharP.cast_eq_zero F 2
  · simp_rw [variableChange_a₃, inv_one, Units.val_one, a₃_of_isCharTwoJNeZeroNF]
    ring1
  · simp_rw [variableChange_a₄, inv_one, Units.val_one, a₃_of_isCharTwoJNeZeroNF,
      a₄_of_isCharTwoJNeZeroNF]
    ring1
  · simp_rw [variableChange_a₆, inv_one, Units.val_one, heq]
    ring1

private lemma exists_variableChange_of_char_two_of_j_eq_zero
    [E.IsCharTwoJEqZeroNF] [E'.IsCharTwoJEqZeroNF] : ∃ C : VariableChange F, C • E = E' := by
  have ha₃ := E.Δ'.ne_zero
  rw [E.coe_Δ', Δ_of_isCharTwoJEqZeroNF_of_char_two, pow_ne_zero_iff (Nat.succ_ne_zero _)] at ha₃
  have ha₃' := E'.Δ'.ne_zero
  rw [E'.coe_Δ', Δ_of_isCharTwoJEqZeroNF_of_char_two, pow_ne_zero_iff (Nat.succ_ne_zero _)] at ha₃'
  haveI : NeZero (3 : F) := NeZero.mk <| by
    rw [show (3 : F) = 1 by linear_combination CharP.cast_eq_zero F 2]
    exact one_ne_zero
  obtain ⟨u, hu⟩ := IsSepClosed.exists_pow_nat_eq (E.a₃ / E'.a₃) 3
  obtain ⟨s, hs⟩ := IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C' 2 4
    1 _ (E.a₄ - u ^ 4 * E'.a₄) (by norm_num) (by norm_num) ha₃
  obtain ⟨t, ht⟩ := IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C' 2 2
    1 _ (s ^ 6 + E.a₄ * s ^ 2 + E.a₆ - u ^ 6 * E'.a₆) (by norm_num) (by norm_num) ha₃
  have hu0 : u ≠ 0 := by
    rw [← pow_ne_zero_iff three_ne_zero, hu, div_ne_zero_iff]
    exact ⟨ha₃, ha₃'⟩
  use ⟨Units.mk0 u hu0, s ^ 2, s, t⟩
  ext
  · simp_rw [variableChange_a₁, a₁_of_isCharTwoJEqZeroNF,
      show (2 : F) = 0 from CharP.cast_eq_zero F 2]
    ring1
  · simp_rw [variableChange_a₂, a₁_of_isCharTwoJEqZeroNF, a₂_of_isCharTwoJEqZeroNF,
      show (3 : F) = 1 by linear_combination CharP.cast_eq_zero F 2]
    ring1
  · simp_rw [variableChange_a₃, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, inv_mul_eq_div,
      hu, a₁_of_isCharTwoJEqZeroNF, show (2 : F) = 0 from CharP.cast_eq_zero F 2]
    field_simp
  · field_simp [variableChange_a₄, a₁_of_isCharTwoJEqZeroNF, a₂_of_isCharTwoJEqZeroNF]
    linear_combination hs + (s ^ 4 - s * t - E.a₃ * s) * CharP.cast_eq_zero F 2
  · field_simp [variableChange_a₆, a₁_of_isCharTwoJEqZeroNF, a₂_of_isCharTwoJEqZeroNF]
    linear_combination ht - (t ^ 2 + E.a₃ * t) * CharP.cast_eq_zero F 2

private lemma exists_variableChange_of_char_two (heq : E.j = E'.j) :
    ∃ C : VariableChange F, C • E = E' := by
  obtain ⟨C, _ | _⟩ := E.exists_variableChange_isCharTwoNF
  · obtain ⟨C', _ | _⟩ := E'.exists_variableChange_isCharTwoNF
    · simp_rw [← variableChange_j E C, ← variableChange_j E' C',
        j_of_isCharTwoJNeZeroNF_of_char_two, one_div, inv_inj] at heq
      obtain ⟨C'', hC⟩ := exists_variableChange_of_char_two_of_j_ne_zero _ _ heq
      use C'⁻¹ * C'' * C
      rw [mul_smul, mul_smul, hC, ← mul_smul, inv_mul_cancel, one_smul]
    · have h := (C • E).j_ne_zero_of_isCharTwoJNeZeroNF_of_char_two
      rw [variableChange_j, heq, ← variableChange_j E' C',
        j_of_isCharTwoJEqZeroNF_of_char_two] at h
      exact False.elim (h rfl)
  · obtain ⟨C', _ | _⟩ := E'.exists_variableChange_isCharTwoNF
    · have h := (C' • E').j_ne_zero_of_isCharTwoJNeZeroNF_of_char_two
      rw [variableChange_j, ← heq, ← variableChange_j E C,
        j_of_isCharTwoJEqZeroNF_of_char_two] at h
      exact False.elim (h rfl)
    · obtain ⟨C'', hC⟩ := exists_variableChange_of_char_two_of_j_eq_zero (C • E) (C' • E')
      use C'⁻¹ * C'' * C
      rw [mul_smul, mul_smul, hC, ← mul_smul, inv_mul_cancel, one_smul]

end CharTwo

section CharThree

variable [CharP F 3]

private lemma exists_variableChange_of_char_three_of_j_ne_zero
    [E.IsCharThreeJNeZeroNF] [E'.IsCharThreeJNeZeroNF] (heq : E.j = E'.j) :
    ∃ C : VariableChange F, C • E = E' := by
  have h := E.Δ'.ne_zero
  rw [E.coe_Δ', Δ_of_isCharThreeJNeZeroNF_of_char_three, mul_ne_zero_iff, neg_ne_zero,
    pow_ne_zero_iff three_ne_zero] at h
  obtain ⟨ha₂, ha₆⟩ := h
  have h := E'.Δ'.ne_zero
  rw [E'.coe_Δ', Δ_of_isCharThreeJNeZeroNF_of_char_three, mul_ne_zero_iff, neg_ne_zero,
    pow_ne_zero_iff three_ne_zero] at h
  obtain ⟨ha₂', ha₆'⟩ := h
  haveI : NeZero (2 : F) := NeZero.mk <| by
    rw [show (2 : F) = -1 by linear_combination CharP.cast_eq_zero F 3, neg_ne_zero]
    exact one_ne_zero
  obtain ⟨u, hu⟩ := IsSepClosed.exists_pow_nat_eq (E.a₂ / E'.a₂) 2
  have hu0 : u ≠ 0 := by
    rw [← pow_ne_zero_iff two_ne_zero, hu, div_ne_zero_iff]
    exact ⟨ha₂, ha₂'⟩
  use ⟨Units.mk0 u hu0, 0, 0, 0⟩
  ext
  · simp_rw [variableChange_a₁, a₁_of_isCharThreeJNeZeroNF]
    ring1
  · simp_rw [variableChange_a₂, a₁_of_isCharThreeJNeZeroNF, Units.val_inv_eq_inv_val,
      Units.val_mk0, inv_pow, inv_mul_eq_div, hu]
    field_simp
  · simp_rw [variableChange_a₃, a₁_of_isCharThreeJNeZeroNF, a₃_of_isCharThreeJNeZeroNF]
    ring1
  · simp_rw [variableChange_a₄, a₁_of_isCharThreeJNeZeroNF, a₃_of_isCharThreeJNeZeroNF,
      a₄_of_isCharThreeJNeZeroNF]
    ring1
  · simp_rw [j_of_isCharThreeJNeZeroNF_of_char_three, div_eq_div_iff ha₆ ha₆'] at heq
    simp_rw [variableChange_a₆, a₁_of_isCharThreeJNeZeroNF, a₃_of_isCharThreeJNeZeroNF,
      a₄_of_isCharThreeJNeZeroNF, Units.val_inv_eq_inv_val, Units.val_mk0,
      inv_pow, inv_mul_eq_div, pow_mul u 2 3, hu]
    field_simp
    linear_combination heq

private lemma exists_variableChange_of_char_three_of_j_eq_zero
    [E.IsShortNF] [E'.IsShortNF] : ∃ C : VariableChange F, C • E = E' := by
  have ha₄ := E.Δ'.ne_zero
  rw [E.coe_Δ', Δ_of_isShortNF_of_char_three, neg_ne_zero, pow_ne_zero_iff three_ne_zero] at ha₄
  have ha₄' := E'.Δ'.ne_zero
  rw [E'.coe_Δ', Δ_of_isShortNF_of_char_three, neg_ne_zero, pow_ne_zero_iff three_ne_zero] at ha₄'
  haveI : NeZero (4 : F) := NeZero.mk <| by
    rw [show (4 : F) = 1 by linear_combination CharP.cast_eq_zero F 3]
    exact one_ne_zero
  obtain ⟨u, hu⟩ := IsSepClosed.exists_pow_nat_eq (E.a₄ / E'.a₄) 4
  obtain ⟨r, hr⟩ := IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C' 3 3
    1 _ (E.a₆ - u ^ 6 * E'.a₆) (by norm_num) (by norm_num) ha₄
  have hu0 : u ≠ 0 := by
    rw [← pow_ne_zero_iff four_ne_zero, hu, div_ne_zero_iff]
    exact ⟨ha₄, ha₄'⟩
  use ⟨Units.mk0 u hu0, r, 0, 0⟩
  ext
  · simp_rw [variableChange_a₁, a₁_of_isShortNF]
    ring1
  · simp_rw [variableChange_a₂, a₁_of_isShortNF, a₂_of_isShortNF,
      show (3 : F) = 0 from CharP.cast_eq_zero F 3]
    ring1
  · simp_rw [variableChange_a₃, a₁_of_isShortNF, a₃_of_isShortNF]
    ring1
  · simp_rw [variableChange_a₄, a₁_of_isShortNF, a₂_of_isShortNF, a₃_of_isShortNF,
      Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, inv_mul_eq_div, hu,
      show (3 : F) = 0 from CharP.cast_eq_zero F 3]
    field_simp
  · simp_rw [variableChange_a₆, a₁_of_isShortNF, a₂_of_isShortNF, a₃_of_isShortNF,
      Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, inv_mul_eq_div]
    field_simp
    linear_combination hr

private lemma exists_variableChange_of_char_three (heq : E.j = E'.j) :
    ∃ C : VariableChange F, C • E = E' := by
  obtain ⟨C, _ | _⟩ := E.exists_variableChange_isCharThreeNF
  · obtain ⟨C', _ | _⟩ := E'.exists_variableChange_isCharThreeNF
    · rw [← variableChange_j E C, ← variableChange_j E' C'] at heq
      obtain ⟨C'', hC⟩ := exists_variableChange_of_char_three_of_j_ne_zero _ _ heq
      use C'⁻¹ * C'' * C
      rw [mul_smul, mul_smul, hC, ← mul_smul, inv_mul_cancel, one_smul]
    · have h := (C • E).j_ne_zero_of_isCharThreeJNeZeroNF_of_char_three
      rw [variableChange_j, heq, ← variableChange_j E' C', j_of_isShortNF_of_char_three] at h
      exact False.elim (h rfl)
  · obtain ⟨C', _ | _⟩ := E'.exists_variableChange_isCharThreeNF
    · have h := (C' • E').j_ne_zero_of_isCharThreeJNeZeroNF_of_char_three
      rw [variableChange_j, ← heq, ← variableChange_j E C, j_of_isShortNF_of_char_three] at h
      exact False.elim (h rfl)
    · obtain ⟨C'', hC⟩ := exists_variableChange_of_char_three_of_j_eq_zero (C • E) (C' • E')
      use C'⁻¹ * C'' * C
      rw [mul_smul, mul_smul, hC, ← mul_smul, inv_mul_cancel, one_smul]

end CharThree

section CharNeTwoOrThree

private lemma exists_variableChange_of_char_ne_two_or_three
    {p : ℕ} [CharP F p] (hchar2 : p ≠ 2) (hchar3 : p ≠ 3) (heq : E.j = E'.j) :
    ∃ C : VariableChange F, C • E = E' := by
  replace hchar2 : (2 : F) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_two hchar2
  replace hchar3 : (3 : F) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_three hchar3
  haveI := NeZero.mk hchar2
  haveI : NeZero (4 : F) := NeZero.mk <| by
    have := pow_ne_zero 2 hchar2
    norm_num1 at this
    exact this
  haveI : NeZero (6 : F) := NeZero.mk <| by
    have := mul_ne_zero hchar2 hchar3
    norm_num1 at this
    exact this
  letI : Invertible (2 : F) := invertibleOfNonzero hchar2
  letI : Invertible (3 : F) := invertibleOfNonzero hchar3
  wlog _ : E.IsShortNF generalizing E
  · obtain ⟨C, hE⟩ := E.exists_variableChange_isShortNF
    rw [← variableChange_j E C] at heq
    obtain ⟨C', hC⟩ := this _ heq hE
    exact ⟨C' * C, by rwa [mul_smul]⟩
  wlog _ : E'.IsShortNF generalizing E'
  · obtain ⟨C, hE'⟩ := E'.exists_variableChange_isShortNF
    rw [← variableChange_j E' C] at heq
    obtain ⟨C', hC⟩ := this _ heq hE'
    exact ⟨C⁻¹ * C', by rw [mul_smul, hC, ← mul_smul, inv_mul_cancel, one_smul]⟩
  simp_rw [j, Units.val_inv_eq_inv_val, inv_mul_eq_div,
    div_eq_div_iff E.Δ'.ne_zero E'.Δ'.ne_zero, coe_Δ', Δ_of_isShortNF, c₄_of_isShortNF] at heq
  replace heq : E.a₄ ^ 3 * E'.a₆ ^ 2 = E'.a₄ ^ 3 * E.a₆ ^ 2 := by
    letI : Invertible (47775744 : F) := invertibleOfNonzero <| by
      have := mul_ne_zero (pow_ne_zero 16 hchar2) (pow_ne_zero 6 hchar3)
      norm_num1 at this
      exact this
    rw [← mul_right_inj_of_invertible (47775744 : F)]
    linear_combination heq
  by_cases ha₄ : E.a₄ = 0
  · have ha₆ := E.Δ'.ne_zero
    rw [coe_Δ', Δ_of_isShortNF, ha₄, zero_pow three_ne_zero, mul_zero, zero_add, ← mul_assoc,
      mul_ne_zero_iff, pow_ne_zero_iff two_ne_zero] at ha₆
    replace ha₆ := ha₆.2
    have ha₄' : E'.a₄ = 0 := by
      rw [ha₄, zero_pow three_ne_zero, zero_mul, zero_eq_mul] at heq
      exact (pow_eq_zero_iff three_ne_zero).1 <| heq.resolve_right <| pow_ne_zero 2 ha₆
    have ha₆' := E'.Δ'.ne_zero
    rw [coe_Δ', Δ_of_isShortNF, ha₄', zero_pow three_ne_zero, mul_zero, zero_add, ← mul_assoc,
      mul_ne_zero_iff, pow_ne_zero_iff two_ne_zero] at ha₆'
    replace ha₆' := ha₆'.2
    obtain ⟨u, hu⟩ := IsSepClosed.exists_pow_nat_eq (E.a₆ / E'.a₆) 6
    have hu0 : u ≠ 0 := by
      rw [← pow_ne_zero_iff (Nat.succ_ne_zero 5), hu, div_ne_zero_iff]
      exact ⟨ha₆, ha₆'⟩
    use ⟨Units.mk0 u hu0, 0, 0, 0⟩
    ext
    · simp [variableChange_a₁]
    · simp [variableChange_a₂]
    · simp [variableChange_a₃]
    · simp [ha₄, ha₄', variableChange_a₄]
    · simp_rw [variableChange_a₆, a₁_of_isShortNF, a₂_of_isShortNF, a₃_of_isShortNF,
        ha₄, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, inv_mul_eq_div, hu]
      field_simp
  by_cases ha₆ : E.a₆ = 0
  · have ha₄ := E.Δ'.ne_zero
    rw [coe_Δ', Δ_of_isShortNF, ha₆, zero_pow two_ne_zero, mul_zero, add_zero, ← mul_assoc,
      mul_ne_zero_iff, pow_ne_zero_iff three_ne_zero] at ha₄
    replace ha₄ := ha₄.2
    have ha₆' : E'.a₆ = 0 := by
      rw [ha₆, zero_pow two_ne_zero, mul_zero, mul_eq_zero] at heq
      exact (pow_eq_zero_iff two_ne_zero).1 <| heq.resolve_left <| pow_ne_zero 3 ha₄
    have ha₄' := E'.Δ'.ne_zero
    rw [coe_Δ', Δ_of_isShortNF, ha₆', zero_pow two_ne_zero, mul_zero, add_zero, ← mul_assoc,
      mul_ne_zero_iff, pow_ne_zero_iff three_ne_zero] at ha₄'
    replace ha₄' := ha₄'.2
    obtain ⟨u, hu⟩ := IsSepClosed.exists_pow_nat_eq (E.a₄ / E'.a₄) 4
    have hu0 : u ≠ 0 := by
      rw [← pow_ne_zero_iff four_ne_zero, hu, div_ne_zero_iff]
      exact ⟨ha₄, ha₄'⟩
    use ⟨Units.mk0 u hu0, 0, 0, 0⟩
    ext
    · simp [variableChange_a₁]
    · simp [variableChange_a₂]
    · simp [variableChange_a₃]
    · simp_rw [variableChange_a₄, a₁_of_isShortNF, a₂_of_isShortNF, a₃_of_isShortNF,
        Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, inv_mul_eq_div, hu]
      field_simp
    · simp [ha₆, ha₆', variableChange_a₆]
  have ha₄' : E'.a₄ ≠ 0 := fun h ↦ by
    rw [h, zero_pow three_ne_zero, zero_mul, mul_eq_zero,
      pow_eq_zero_iff two_ne_zero, pow_eq_zero_iff three_ne_zero] at heq
    simpa [E'.coe_Δ', Δ_of_isShortNF, h, heq.resolve_left ha₄] using E'.Δ'.ne_zero
  have ha₆' : E'.a₆ ≠ 0 := fun h ↦ by
    rw [h, zero_pow two_ne_zero, mul_zero, zero_eq_mul,
      pow_eq_zero_iff two_ne_zero, pow_eq_zero_iff three_ne_zero] at heq
    tauto
  obtain ⟨u, hu⟩ := IsSepClosed.exists_pow_nat_eq (E.a₆ / E'.a₆ / (E.a₄ / E'.a₄)) 2
  have hu4 : u ^ 4 = E.a₄ / E'.a₄ := by
    rw [pow_mul u 2 2, hu]
    field_simp
    linear_combination -heq
  have hu6 : u ^ 6 = E.a₆ / E'.a₆ := by
    rw [pow_mul u 2 3, hu]
    field_simp
    linear_combination -E.a₆ * E'.a₆ * heq
  have hu0 : u ≠ 0 := by
    rw [← pow_ne_zero_iff four_ne_zero, hu4, div_ne_zero_iff]
    exact ⟨ha₄, ha₄'⟩
  use ⟨Units.mk0 u hu0, 0, 0, 0⟩
  ext
  · simp [variableChange_a₁]
  · simp [variableChange_a₂]
  · simp [variableChange_a₃]
  · simp_rw [variableChange_a₄, a₁_of_isShortNF, a₂_of_isShortNF, a₃_of_isShortNF,
      Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, inv_mul_eq_div, hu4]
    field_simp
  · simp_rw [variableChange_a₆, a₁_of_isShortNF, a₂_of_isShortNF, a₃_of_isShortNF,
      Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, inv_mul_eq_div, hu6]
    field_simp

end CharNeTwoOrThree

/-- If there are two elliptic curves with the same `j`-invariants defined over a
separably closed field, then there exists a change of variables over that field which change
one curve into another. -/
theorem exists_variableChange_of_j_eq (heq : E.j = E'.j) : ∃ C : VariableChange F, C • E = E' := by
  obtain ⟨p, _⟩ := CharP.exists F
  by_cases hchar2 : p = 2
  · subst hchar2
    exact exists_variableChange_of_char_two _ _ heq
  by_cases hchar3 : p = 3
  · subst hchar3
    exact exists_variableChange_of_char_three _ _ heq
  exact exists_variableChange_of_char_ne_two_or_three _ _ hchar2 hchar3 heq

end WeierstrassCurve
