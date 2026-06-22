/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Group.Embedding
public import Mathlib.Data.Matrix.Mul
public import Mathlib.GroupTheory.Perm.Sign

import Mathlib.Algebra.Module.End
import Mathlib.GroupTheory.Perm.Option

/-!
# Nonsingular inverses over semirings

This file proves `A * B = 1 ↔ B * A = 1` for square matrices over a commutative semiring.

-/

@[expose] public section

open Equiv Equiv.Perm Finset

variable {n m R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommSemiring R]

variable (s : ℤˣ) (A B : Matrix n n R) (i j : n)

namespace Matrix

/-- The determinant, but only the terms of a given sign.
`A.detp 1` is written `|A|⁺` in the literature and `A.detp (-1)` is written `|A|⁻`. -/
def detp : R := ∑ σ ∈ ofSign s, ∏ k, A k (σ k)

@[simp] lemma detp_transpose : A.transpose.detp s = A.detp s :=
  sum_equiv (.inv _) (by simp) fun σ _ ↦ prod_equiv σ (by simp) (by simp)

@[simp]
lemma detp_one_diagonal (d : n → R) : detp 1 (diagonal d) = ∏ i, d i := by
  rw [detp, sum_eq_single_of_mem 1]
  · simp
  · simp [ofSign]
  · rintro σ - hσ1
    obtain ⟨i, hi⟩ := not_forall.mp (mt Perm.ext_iff.mpr hσ1)
    exact prod_eq_zero (mem_univ i) (diagonal_apply_ne' _ hi)

@[simp]
lemma detp_one_one : detp 1 (1 : Matrix n n R) = 1 := by
  rw [← diagonal_one, detp_one_diagonal, prod_const_one]

@[simp]
lemma detp_neg_one_diagonal (d : n → R) : detp (-1) (diagonal d) = 0 := by
  rw [detp, sum_eq_zero]
  intro σ hσ
  have hσ1 : σ ≠ 1 := by
    contrapose hσ
    rw [hσ, mem_ofSign, sign_one]
    decide
  obtain ⟨i, hi⟩ := not_forall.mp (mt Perm.ext_iff.mpr hσ1)
  exact prod_eq_zero (mem_univ i) (diagonal_apply_ne' _ hi)

@[simp]
lemma detp_neg_one_one : detp (-1) (1 : Matrix n n R) = 0 := by
  rw [← diagonal_one, detp_neg_one_diagonal]

@[simp] lemma detp_one_of_isEmpty [IsEmpty n] : A.detp 1 = 1 := by
  rw [detp, sum_unique_nonempty _ _ ⟨1, _⟩] <;> simp

@[simp] lemma detp_neg_one_of_isEmpty [IsEmpty n] : A.detp (-1) = 0 := by
  rw [detp, ofSign, univ_unique]
  convert sum_empty
  simp +decide

@[simp] lemma detp_submatrix_equiv_equiv (f g : m ≃ n) :
    (A.submatrix f g).detp s = A.detp (s * sign (f.symm.trans g)) :=
  sum_equiv (equivCongr f g) (by simp) fun _ _ ↦ prod_equiv f (by simp) fun _ _ ↦ by simp

lemma detp_submatrix_equiv (e : m ≃ n) : (A.submatrix e e).detp s = A.detp s := by
  simp

variable {A}

lemma detp_eq_of_row_eq {p q : n} (hpq : p ≠ q) (hrow : A p = A q) : A.detp 1 = A.detp (-1) :=
  sum_equiv (.mulRight <| swap p q) (by simp [hpq]) fun _ _ ↦
    prod_equiv (swap p q) (by simp) (by aesop)

lemma detp_eq_of_col_eq {p q : n} (hpq : p ≠ q) (hcol : A.col p = A.col q) :
    A.detp 1 = A.detp (-1) := by
  simp_rw [← A.detp_transpose]; exact detp_eq_of_row_eq hpq hcol

lemma detp_eq_of_row_eq_zero {p : n} (hrow : A p = 0) : A.detp s = 0 :=
  sum_eq_zero fun _ _ ↦ prod_eq_zero (mem_univ p) congr($hrow _)

lemma detp_eq_of_col_eq_zero {p : n} (hcol : A.col p = 0) : A.detp s = 0 := by
  simpa only [detp_transpose] using detp_eq_of_row_eq_zero (A := Aᵀ) s hcol

variable (A)

/-- The adjugate matrix, but only the terms of a given sign. -/
def adjp : Matrix n n R :=
  of fun i j ↦ ∑ σ ∈ (ofSign s).filter (· j = i), ∏ k ∈ {j}ᶜ, A k (σ k)

lemma adjp_apply (i j : n) :
    adjp s A i j = ∑ σ ∈ (ofSign s).filter (· j = i), ∏ k ∈ {j}ᶜ, A k (σ k) :=
  rfl

lemma adjp_transpose : A.transpose.adjp s = (A.adjp s).transpose := by
  ext; exact sum_equiv (.inv _) (by aesop) fun σ hσ ↦
    prod_equiv σ (by simp [← (mem_filter.mp hσ).2]) (by simp)

private lemma adjp_none_right (A : Matrix (Option n) (Option n) R) (i : Option n) :
    A.adjp s i none = (A.submatrix some <| swap none i ∘ some).detp (sign (swap none i) * s) := by
  rw [adjp, of_apply, detp]
  convert sum_image (g := fun σ ↦ decomposeOption.symm (i, σ))
    ((Equiv.injective _).comp (Prod.mk_right_injective i)).injOn
  · ext σ; simp only [mem_filter, mem_ofSign, mem_image]
    refine ⟨fun h ↦ ⟨σ.removeNone, ?_⟩, ?_⟩
    · rw [← optionCongr_sign, map_equiv_removeNone, map_mul, h.1, h.2, mul_comm]
      use rfl; rw [← h.2]; exact decomposeOption.left_inv σ
    · rintro ⟨σ, h, rfl⟩
      rw [decomposeOption_symm_apply, map_mul, optionCongr_sign, h, ← mul_assoc, Int.units_mul_self]
      simp
  convert (prod_image (Option.some_injective n).injOn).symm
  · rfl
  · apply SetLike.coe_injective; simp [← Set.compl_range_some]

lemma adjp_none_none (A : Matrix (Option n) (Option n) R) :
    A.adjp s none none = (A.submatrix some some).detp s := by
  simp [adjp_none_right]

lemma adjp_some_none (A : Matrix (Option n) (Option n) R) :
    A.adjp s (some i) none = (A.submatrix some (Function.update some i none)).detp (-s) := by
  rw [adjp_none_right]; congr
  · simp
  · ext1; aesop

lemma adjp_none_some (A : Matrix (Option n) (Option n) R) :
    A.adjp s none (some i) = (A.submatrix (Function.update some i none) some).detp (-s) := by
  convert A.transpose.adjp_some_none s i using 1
  · rw [adjp_transpose, transpose_apply]
  · rw [← detp_transpose, transpose_submatrix]

theorem detp_mul :
    detp 1 (A * B) + (detp 1 A * detp (-1) B + detp (-1) A * detp 1 B) =
      detp (-1) (A * B) + (detp 1 A * detp 1 B + detp (-1) A * detp (-1) B) := by
  have hf {s t} {σ : Perm n} (hσ : σ ∈ ofSign s) :
      ofSign (t * s) = (ofSign t).map (mulRightEmbedding σ) := by
    ext τ
    simp_rw [mem_map, mulRightEmbedding_apply, ← eq_mul_inv_iff_mul_eq, exists_eq_right,
      mem_ofSign, map_mul, map_inv, mul_inv_eq_iff_eq_mul, mem_ofSign.mp hσ]
  have h {s t} : detp s A * detp t B =
      ∑ σ ∈ ofSign s, ∑ τ ∈ ofSign (t * s), ∏ k, A k (σ k) * B (σ k) (τ k) := by
    simp_rw [detp, sum_mul_sum, prod_mul_distrib]
    refine sum_congr rfl fun σ hσ ↦ ?_
    simp_rw [hf hσ, sum_map, mulRightEmbedding_apply, Perm.mul_apply]
    exact sum_congr rfl fun τ hτ ↦ (congr_arg (_ * ·) (Equiv.prod_comp σ _).symm)
  let ι : Perm n ↪ (n → n) := ⟨_, coe_fn_injective⟩
  have hι {σ x} : ι σ x = σ x := rfl
  let bij : Finset (n → n) := (disjUnion (ofSign 1) (ofSign (-1)) ofSign_disjoint).map ι
  replace h (s) : detp s (A * B) =
      ∑ σ ∈ bijᶜ, ∑ τ ∈ ofSign s, ∏ i : n, A i (σ i) * B (σ i) (τ i) +
        (detp 1 A * detp s B + detp (-1) A * detp (-s) B) := by
    simp_rw [h, neg_mul_neg, mul_one, detp, mul_apply, prod_univ_sum, Fintype.piFinset_univ]
    rw [sum_comm, ← sum_compl_add_sum bij, sum_map, sum_disjUnion]
    simp_rw [hι]
  rw [h, h, neg_neg, add_assoc]
  conv_rhs => rw [add_assoc]
  refine congr_arg₂ (· + ·) (sum_congr rfl fun σ hσ ↦ ?_) (add_comm _ _)
  replace hσ : ¬ Function.Injective σ := by
    contrapose hσ
    rw [notMem_compl, mem_map, ofSign_disjUnion]
    exact ⟨Equiv.ofBijective σ hσ.bijective_of_finite, mem_univ _, rfl⟩
  obtain ⟨i, j, hσ, hij⟩ := Function.not_injective_iff.mp hσ
  replace hσ k : σ (swap i j k) = σ k := by
    rw [swap_apply_def]
    split_ifs with h h <;> simp only [hσ, h]
  rw [← mul_neg_one, hf (mem_ofSign.mpr (sign_swap hij)), sum_map]
  simp_rw [prod_mul_distrib, mulRightEmbedding_apply, Perm.mul_apply]
  refine sum_congr rfl fun τ hτ ↦ congr_arg (_ * ·) ?_
  rw [← Equiv.prod_comp (swap i j)]
  simp only [hσ]

theorem mul_adjp_apply_eq : (A * adjp s A) i i = detp s A := by
  have key := sum_fiberwise_eq_sum_filter (ofSign s) univ (· i) fun σ ↦ ∏ k, A k (σ k)
  simp_rw [mem_univ, filter_true] at key
  simp_rw [mul_apply, adjp_apply, mul_sum, detp, ← key]
  refine sum_congr rfl fun x hx ↦ sum_congr rfl fun σ hσ ↦ ?_
  rw [← prod_mul_prod_compl ({i} : Finset n), prod_singleton, (mem_filter.mp hσ).2]

theorem mul_adjp_apply_ne (h : i ≠ j) : (A * adjp 1 A) i j = (A * adjp (-1) A) i j := by
  let A' : Matrix n n R := of <| Function.update A j (A i)
  have h' s : (A * adjp s A) i j = (A' * adjp s A') j j := sum_congr rfl fun _ _ ↦
    congr_arg₂ (· * ·) (by simp [A']) <| sum_congr rfl fun σ hσ ↦ prod_congr rfl fun k hk ↦ by
      rw [mem_compl, mem_singleton] at hk
      simp [A', hk]
  simp_rw [h', mul_adjp_apply_eq]
  apply detp_eq_of_row_eq h
  ext; simp [A', h]

theorem adjp_mul_apply_eq : (adjp s A * A) i i = detp s A := by
  rw [← detp_transpose, ← mul_adjp_apply_eq _ _ i, adjp_transpose, ← transpose_mul, transpose_apply]

theorem adjp_mul_apply_ne (h : i ≠ j) : (adjp 1 A * A) i j = (adjp (-1) A * A) i j := by
  simp_rw [← transpose_apply (_ * _) j i, transpose_mul,
    ← adjp_transpose, mul_adjp_apply_ne _ _ _ h.symm]

theorem mul_adjp_add_detp : A * adjp 1 A + detp (-1) A • 1 = A * adjp (-1) A + detp 1 A • 1 := by
  ext i j
  rcases eq_or_ne i j with rfl | h <;> simp_rw [add_apply, smul_apply, smul_eq_mul]
  · simp_rw [mul_adjp_apply_eq, one_apply_eq, mul_one, add_comm]
  · simp_rw [mul_adjp_apply_ne A i j h, one_apply_ne h, mul_zero]

/-- Laplace expansion of `detp` along the `none` row of an `Option`-indexed matrix. -/
lemma detp_option_expand_row_none (A : Matrix (Option n) (Option n) R) :
    A.detp s = A none none * (A.submatrix some some).detp s +
      ∑ k : n, A none (some k) * (A.submatrix some (Function.update some k none)).detp (-s) := by
  simp_rw [← A.mul_adjp_apply_eq s none, mul_apply,
    Fintype.sum_option, adjp_none_none, adjp_some_none]

variable {A B}

theorem isAddUnit_mul {d : n → R} (hAB : A * B = diagonal d) (i j k : n) (hij : i ≠ j) :
    IsAddUnit (A i k * B k j) := by
  revert k
  rw [← IsAddUnit.sum_univ_iff, ← mul_apply, hAB, diagonal_apply_ne _ hij]
  exact isAddUnit_zero

theorem isAddUnit_detp_mul_detp {d : n → R} (hAB : A * B = diagonal d) :
    IsAddUnit (detp 1 A * detp (-1) B + detp (-1) A * detp 1 B) := by
  suffices h : ∀ {s t}, s ≠ t → IsAddUnit (detp s A * detp t B) from
    (h (by decide)).add (h (by decide))
  intro s t h
  simp_rw [detp, sum_mul_sum, IsAddUnit.sum_iff]
  intro σ hσ τ hτ
  rw [mem_ofSign] at hσ hτ
  rw [← hσ, ← hτ, ← sign_inv] at h
  replace h := ne_of_apply_ne sign h
  rw [ne_eq, eq_comm, eq_inv_iff_mul_eq_one, eq_comm] at h
  simp_rw [Equiv.ext_iff, not_forall, Perm.mul_apply, Perm.one_apply] at h
  obtain ⟨k, hk⟩ := h
  rw [mul_comm, ← Equiv.prod_comp σ, mul_comm, ← prod_mul_distrib,
    ← mul_prod_erase univ _ (mem_univ k), ← smul_eq_mul]
  exact (isAddUnit_mul hAB k (τ (σ k)) (σ k) hk).smul_right _

theorem isAddUnit_detp_smul_mul_adjp {d : n → R} (hAB : A * B = diagonal d) :
    IsAddUnit (detp 1 A • (B * adjp (-1) B) + detp (-1) A • (B * adjp 1 B)) := by
  suffices h : ∀ {s t}, s ≠ t → IsAddUnit (detp s A • (B * adjp t B)) from
    (h (by decide)).add (h (by decide))
  intro s t h
  rw [isAddUnit_iff]
  intro i j
  simp_rw [smul_apply, smul_eq_mul, mul_apply, detp, adjp_apply, mul_sum, sum_mul,
    IsAddUnit.sum_iff]
  intro k hk σ hσ τ hτ
  rw [mem_filter] at hσ
  rw [mem_ofSign] at hσ hτ
  rw [← hσ.1, ← hτ, ← sign_inv] at h
  replace h := ne_of_apply_ne sign h
  rw [ne_eq, eq_comm, eq_inv_iff_mul_eq_one] at h
  obtain ⟨l, hl1, hl2⟩ := exists_mem_ne (one_lt_card_support_of_ne_one h) (τ⁻¹ j)
  rw [mem_support, ne_comm] at hl1
  rw [ne_eq, ← mem_singleton, ← mem_compl] at hl2
  rw [← prod_mul_prod_compl {τ⁻¹ j}, mul_mul_mul_comm, mul_comm, ← smul_eq_mul]
  apply IsAddUnit.smul_right
  have h0 : ∀ k, k ∈ ({τ⁻¹ j} : Finset n)ᶜ ↔ τ k ∈ ({j} : Finset n)ᶜ := by
    simp [inv_def, eq_symm_apply]
  rw [← prod_equiv τ h0 fun _ _ ↦ rfl, ← prod_mul_distrib, ← mul_prod_erase _ _ hl2, ← smul_eq_mul]
  exact (isAddUnit_mul hAB l (σ (τ l)) (τ l) hl1).smul_right _

theorem detp_smul_add_adjp (hAB : A * B = 1) :
    detp 1 B • A + adjp (-1) B = detp (-1) B • A + adjp 1 B := by
  have key := congr(A * $(mul_adjp_add_detp B))
  simp_rw [mul_add, ← mul_assoc, hAB, one_mul, Matrix.mul_smul, mul_one] at key
  rwa [add_comm, eq_comm, add_comm]

theorem detp_smul_adjp (hAB : A * B = 1) :
    A + (detp 1 A • adjp (-1) B + detp (-1) A • adjp 1 B) =
      detp 1 A • adjp 1 B + detp (-1) A • adjp (-1) B := by
  have h0 := detp_mul A B
  rw [hAB, detp_one_one, detp_neg_one_one, zero_add] at h0
  have h := detp_smul_add_adjp hAB
  replace h := congr(detp 1 A • $h + detp (-1) A • $h.symm)
  simp only [smul_add, smul_smul] at h
  rwa [add_add_add_comm, ← add_smul, add_add_add_comm, ← add_smul, ← h0, add_smul, one_smul,
    add_comm A, add_assoc, ((isAddUnit_detp_mul_detp hAB).smul_right _).add_right_inj] at h

instance (priority := low) instIsStablyFiniteRingOfCommSemiring : IsStablyFiniteRing R := by
  refine ⟨fun n ↦ ⟨fun {A B} hAB ↦ ?_⟩⟩
  have h0 := detp_mul A B
  rw [hAB, detp_one_one, detp_neg_one_one, zero_add] at h0
  replace h := congr(B * $(detp_smul_adjp hAB))
  simp only [mul_add, Matrix.mul_smul] at h
  replace h := congr($h + (detp 1 A * detp (-1) B + detp (-1) A * detp 1 B) • 1)
  simp_rw [add_smul, ← smul_smul] at h
  rwa [add_assoc, add_add_add_comm, ← smul_add, ← smul_add,
    add_add_add_comm, ← smul_add, ← smul_add, smul_add, smul_add,
    mul_adjp_add_detp, smul_add, ← mul_adjp_add_detp, smul_add, ← smul_add, ← smul_add,
    add_add_add_comm, smul_smul, smul_smul, ← add_smul, ← h0,
    add_smul, one_smul, ← add_assoc _ 1, add_comm _ 1, add_assoc,
    smul_add, smul_add, add_add_add_comm, smul_smul, smul_smul, ← add_smul,
    ((isAddUnit_detp_smul_mul_adjp hAB).add
      ((isAddUnit_detp_mul_detp hAB).smul_right _)).add_left_inj] at h

@[deprecated (since := "2025-11-29")] protected alias mul_eq_one_comm := mul_eq_one_comm

variable (A B)

/-- We can construct an instance of invertible A if A has a left inverse. -/
@[deprecated invertibleOfLeftInverse (since := "2025-12-06"), implicit_reducible]
protected def invertibleOfLeftInverse (h : B * A = 1) : Invertible A :=
  invertibleOfLeftInverse _ _ h

/-- We can construct an instance of invertible A if A has a right inverse. -/
@[deprecated invertibleOfRightInverse (since := "2025-12-06"), implicit_reducible]
protected def invertibleOfRightInverse (h : A * B = 1) : Invertible A :=
  invertibleOfRightInverse _ _ h

variable {A B}

@[deprecated IsUnit.of_mul_eq_one_right (since := "2025-12-06")]
theorem isUnit_of_left_inverse (h : B * A = 1) : IsUnit A :=
  .of_mul_eq_one_right _ h

@[deprecated isUnit_iff_exists_inv' (since := "2025-12-06")]
theorem exists_left_inverse_iff_isUnit : (∃ B, B * A = 1) ↔ IsUnit A :=
  isUnit_iff_exists_inv'.symm

@[deprecated IsUnit.of_mul_eq_one (since := "2025-12-06")]
theorem isUnit_of_right_inverse (h : A * B = 1) : IsUnit A :=
  .of_mul_eq_one _ h

@[deprecated isUnit_iff_exists_inv (since := "2025-12-06")]
theorem exists_right_inverse_iff_isUnit : (∃ B, A * B = 1) ↔ IsUnit A :=
  isUnit_iff_exists_inv.symm

end Matrix
