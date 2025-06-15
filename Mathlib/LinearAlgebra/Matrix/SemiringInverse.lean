/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.Group.Embedding
import Mathlib.Data.Matrix.Mul
import Mathlib.GroupTheory.Perm.Sign

/-!
# Nonsingular inverses over semirings

This files proves `A * B = 1 ↔ B * A = 1` for square matrices over a commutative semiring.

-/

open Equiv Equiv.Perm Finset

variable {n m R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommSemiring R]

variable (s : ℤˣ) (A B : Matrix n n R) (i j : n)

namespace Matrix

/-- The determinant, but only the terms of a given sign. -/
def detp : R := ∑ σ ∈ ofSign s, ∏ k, A k (σ k)

@[simp]
lemma detp_one_one : detp 1 (1 : Matrix n n R) = 1 := by
  rw [detp, sum_eq_single_of_mem 1]
  · simp [one_apply]
  · simp [ofSign]
  · rintro σ - hσ1
    obtain ⟨i, hi⟩ := not_forall.mp (mt Perm.ext_iff.mpr hσ1)
    exact prod_eq_zero (mem_univ i) (one_apply_ne' hi)

@[simp]
lemma detp_neg_one_one : detp (-1) (1 : Matrix n n R) = 0 := by
  rw [detp, sum_eq_zero]
  intro σ hσ
  have hσ1 : σ ≠ 1 := by
    contrapose! hσ
    rw [hσ, mem_ofSign, sign_one]
    decide
  obtain ⟨i, hi⟩ := not_forall.mp (mt Perm.ext_iff.mpr hσ1)
  exact prod_eq_zero (mem_univ i) (one_apply_ne' hi)

/-- The adjugate matrix, but only the terms of a given sign. -/
def adjp : Matrix n n R :=
  of fun i j ↦ ∑ σ ∈ (ofSign s).filter (· j = i), ∏ k ∈ {j}ᶜ, A k (σ k)

lemma adjp_apply (i j : n) :
    adjp s A i j = ∑ σ ∈ (ofSign s).filter (· j = i), ∏ k ∈ {j}ᶜ, A k (σ k) :=
  rfl

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
    contrapose! hσ
    rw [notMem_compl, mem_map, ofSign_disjUnion]
    exact ⟨Equiv.ofBijective σ hσ.bijective_of_finite, mem_univ _, rfl⟩
  obtain ⟨i, j, hσ, hij⟩ := Function.not_injective_iff.mp hσ
  replace hσ k : σ (swap i j k) = σ k := by
    rw [swap_apply_def]
    split_ifs with h h <;> simp only [hσ, h]
  rw [← mul_neg_one, hf (mem_ofSign.mpr (sign_swap hij)), sum_map]
  simp_rw [prod_mul_distrib, mulRightEmbedding_apply, Perm.mul_apply]
  refine sum_congr rfl fun τ hτ ↦ congr_arg (_ *  ·) ?_
  rw [← Equiv.prod_comp (swap i j)]
  simp only [hσ]

theorem mul_adjp_apply_eq : (A * adjp s A) i i = detp s A := by
  have key := sum_fiberwise_eq_sum_filter (ofSign s) univ (· i) fun σ ↦ ∏ k, A k (σ k)
  simp_rw [mem_univ, filter_True] at key
  simp_rw [mul_apply, adjp_apply, mul_sum, detp, ← key]
  refine sum_congr rfl fun x hx ↦ sum_congr rfl fun σ hσ ↦ ?_
  rw [← prod_mul_prod_compl ({i} : Finset n), prod_singleton, (mem_filter.mp hσ).2]

theorem mul_adjp_apply_ne (h : i ≠ j) : (A * adjp 1 A) i j = (A * adjp (-1) A) i j := by
  simp_rw [mul_apply, adjp_apply, mul_sum, sum_sigma']
  let f : (Σ x : n, Perm n) → (Σ x : n, Perm n) := fun ⟨x, σ⟩ ↦ ⟨σ i, σ * swap i j⟩
  let t s : Finset (Σ x : n, Perm n) := univ.sigma fun x ↦ (ofSign s).filter fun σ ↦ σ j = x
  have hf {s} : ∀ p ∈ t s, f (f p) = p := by
    intro ⟨x, σ⟩ hp
    rw [mem_sigma, mem_filter, mem_ofSign] at hp
    simp_rw [f, Perm.mul_apply, swap_apply_left, hp.2.2, mul_swap_mul_self]
  refine sum_bij' (fun p _ ↦ f p) (fun p _ ↦ f p) ?_ ?_ hf hf ?_
  · intro ⟨x, σ⟩ hp
    rw [mem_sigma, mem_filter, mem_ofSign] at hp ⊢
    rw [Perm.mul_apply, sign_mul, hp.2.1, sign_swap h, swap_apply_right]
    exact ⟨mem_univ (σ i), rfl, rfl⟩
  · intro ⟨x, σ⟩ hp
    rw [mem_sigma, mem_filter, mem_ofSign] at hp ⊢
    rw [Perm.mul_apply, sign_mul, hp.2.1, sign_swap h, swap_apply_right]
    exact ⟨mem_univ (σ i), rfl, rfl⟩
  · intro ⟨x, σ⟩ hp
    rw [mem_sigma, mem_filter, mem_ofSign] at hp
    have key : ({j}ᶜ : Finset n) = disjUnion ({i} : Finset n) ({i, j} : Finset n)ᶜ (by simp) := by
      rw [singleton_disjUnion, cons_eq_insert, compl_insert, insert_erase]
      rwa [mem_compl, mem_singleton]
    simp_rw [key, prod_disjUnion, prod_singleton, f, Perm.mul_apply, swap_apply_left, ← mul_assoc]
    rw [mul_comm (A i x) (A i (σ i)), hp.2.2]
    refine congr_arg _ (prod_congr rfl fun x hx ↦ ?_)
    rw [mem_compl, mem_insert, mem_singleton, not_or] at hx
    rw [swap_apply_of_ne_of_ne hx.1 hx.2]

theorem mul_adjp_add_detp : A * adjp 1 A + detp (-1) A • 1 = A * adjp (-1) A + detp 1 A • 1 := by
  ext i j
  rcases eq_or_ne i j with rfl | h <;> simp_rw [add_apply, smul_apply, smul_eq_mul]
  · simp_rw [mul_adjp_apply_eq, one_apply_eq, mul_one, add_comm]
  · simp_rw [mul_adjp_apply_ne A i j h, one_apply_ne h, mul_zero]

variable {A B}

theorem isAddUnit_mul (hAB : A * B = 1) (i j k : n) (hij : i ≠ j) : IsAddUnit (A i k * B k j) := by
  revert k
  rw [← IsAddUnit.sum_univ_iff, ← mul_apply, hAB, one_apply_ne hij]
  exact isAddUnit_zero

theorem isAddUnit_detp_mul_detp (hAB : A * B = 1) :
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

theorem isAddUnit_detp_smul_mul_adjp (hAB : A * B = 1) :
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
  obtain ⟨l, hl1, hl2⟩ := exists_ne_of_one_lt_card (one_lt_card_support_of_ne_one h) (τ⁻¹ j)
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
  simp_rw [mul_add, ← mul_assoc, hAB, one_mul, mul_smul, mul_one] at key
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

theorem mul_eq_one_comm : A * B = 1 ↔ B * A = 1 := by
  suffices h : ∀ A B : Matrix n n R, A * B = 1 → B * A = 1 from ⟨h A B, h B A⟩
  intro A B hAB
  have h0 := detp_mul A B
  rw [hAB, detp_one_one, detp_neg_one_one, zero_add] at h0
  replace h := congr(B * $(detp_smul_adjp hAB))
  simp only [mul_add, mul_smul, add_assoc] at h
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

variable (A B)

/-- We can construct an instance of invertible A if A has a left inverse. -/
def invertibleOfLeftInverse (h : B * A = 1) : Invertible A :=
  ⟨B, h, mul_eq_one_comm.mp h⟩

/-- We can construct an instance of invertible A if A has a right inverse. -/
def invertibleOfRightInverse (h : A * B = 1) : Invertible A :=
  ⟨B, mul_eq_one_comm.mp h, h⟩

variable {A B}

theorem isUnit_of_left_inverse (h : B * A = 1) : IsUnit A :=
  ⟨⟨A, B, mul_eq_one_comm.mp h, h⟩, rfl⟩

theorem exists_left_inverse_iff_isUnit : (∃ B, B * A = 1) ↔ IsUnit A :=
  ⟨fun ⟨_, h⟩ ↦ isUnit_of_left_inverse h, fun h ↦ have := h.invertible; ⟨⅟A, invOf_mul_self' A⟩⟩

theorem isUnit_of_right_inverse (h : A * B = 1) : IsUnit A :=
  ⟨⟨A, B, h, mul_eq_one_comm.mp h⟩, rfl⟩

theorem exists_right_inverse_iff_isUnit : (∃ B, A * B = 1) ↔ IsUnit A :=
  ⟨fun ⟨_, h⟩ ↦ isUnit_of_right_inverse h, fun h ↦ have := h.invertible; ⟨⅟A, mul_invOf_self' A⟩⟩

/-- A version of `mul_eq_one_comm` that works for square matrices with rectangular types. -/
theorem mul_eq_one_comm_of_equiv {A : Matrix m n R} {B : Matrix n m R} (e : m ≃ n) :
    A * B = 1 ↔ B * A = 1 := by
  refine (reindex e e).injective.eq_iff.symm.trans ?_
  rw [reindex_apply, reindex_apply, submatrix_one_equiv, ← submatrix_mul_equiv _ _ _ (.refl _),
    mul_eq_one_comm, submatrix_mul_equiv, coe_refl, submatrix_id_id]

end Matrix
