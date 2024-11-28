/-
Copyright (c) 2019 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Lu-Ming Zhang
-/
import Mathlib.Data.Matrix.Invertible
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Nonsingular inverses over semirings

This files proves `A * B = 1 ↔ B * A = 1` for square matrices over a commutative semiring.

-/


lemma IsAddUnit.smul
    {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {r : R} (hr : IsAddUnit r) (m : M) : IsAddUnit (r • m) := by
  obtain ⟨r, rfl⟩ := hr
  apply isAddUnit_of_add_eq_zero
  rw [← add_smul, r.add_neg, zero_smul]

namespace Matrix

open Equiv Finset

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommSemiring R]

variable (s : ℤˣ) (A B : Matrix n n R) (i j : n)

/-- Filter by parity -/
def filterp : Finset (Perm n) := univ.filter (fun σ ↦ σ.sign = s)

lemma mem_filterp {σ : Perm n} : σ ∈ filterp s ↔ σ.sign = s := by
  rw [filterp, mem_filter, and_iff_right (mem_univ σ)]

def fix : Finset (Perm n) := univ.filter (fun σ ↦ σ i = j)

/-- Filter determinant by parity. -/
def detp := ∑ σ ∈ filterp s, ∏ k, A k (σ k)

lemma detp_one_one : detp 1 (1 : Matrix n n R) = 1 := by
  rw [detp, sum_eq_single_of_mem 1]
  · simp [one_apply]
  · simp [filterp]
  · rintro σ - hσ1
    obtain ⟨i, hi⟩ := not_forall.mp (mt Perm.ext_iff.mpr hσ1)
    exact prod_eq_zero (mem_univ i) (one_apply_ne' hi)

lemma detp_neg_one_one : detp (-1) (1 : Matrix n n R) = 0 := by
  rw [detp, sum_eq_zero]
  intro σ hσ
  have hσ1 : σ ≠ 1 := by
    contrapose! hσ
    simp [filterp, hσ]
  obtain ⟨i, hi⟩ := not_forall.mp (mt Perm.ext_iff.mpr hσ1)
  exact prod_eq_zero (mem_univ i) (one_apply_ne' hi)

/-- Filter adjugate matrix by parity. -/
def adjp : Matrix n n R :=
  fun i j ↦ ∑ σ ∈ (filterp s).filter (fun σ ↦ σ j = i), ∏ k ∈ {j}ᶜ, A k (σ k)

lemma adjp_apply (i j : n) :
    adjp s A i j = ∑ σ ∈ (filterp s).filter (fun σ ↦ σ j = i), ∏ k ∈ {j}ᶜ, A k (σ k) :=
  rfl

-- actually needs an extra factor on each side...
theorem detp_mul₀ :
    detp s (A * B) = detp 1 A * detp s B + detp (-1) A * detp (-s) B := by
  -- simp_rw [detp, mul_apply, Finset.prod_univ_sum, Fintype.piFinset_univ]
  sorry

theorem detp_mul' :
    detp 1 (A * B) + (detp 1 A * detp (-1) B + detp (-1) A * detp 1 B) =
      detp (-1) (A * B) + (detp 1 A * detp 1 B + detp (-1) A * detp (-1) B) := by
  -- needs a proof that doesn't rely on detp_mul₀
  simp only [detp_mul₀, neg_neg]
  abel

theorem mul_adjp_add_detp_aux1 : (A * adjp s A) i i = detp s A := by
  have key := sum_fiberwise_eq_sum_filter (filterp s) univ (· i) fun σ ↦ ∏ k, A k (σ k)
  simp_rw [mem_univ, filter_True] at key
  simp_rw [mul_apply, adjp_apply, mul_sum, detp, ← key]
  refine sum_congr rfl fun x hx ↦ sum_congr rfl fun σ hσ ↦ ?_
  rw [← prod_mul_prod_compl ({i} : Finset n), prod_singleton, (mem_filter.mp hσ).2]

theorem mul_adjp_add_detp_aux2 (h : i ≠ j) : (A * adjp 1 A) i j = (A * adjp (-1) A) i j := by
  simp_rw [mul_apply, adjp_apply, mul_sum, sum_sigma']
  let f : (Σ x : n, Perm n) → (Σ x : n, Perm n) := fun ⟨x, σ⟩ ↦ ⟨σ i, σ * swap i j⟩
  let t s : Finset (Σ x : n, Perm n) := univ.sigma fun x ↦ (filterp s).filter (fun σ ↦ σ j = x)
  have hf {s} : ∀ p ∈ t s, f (f p) = p := by
    intro ⟨x, σ⟩ hp
    rw [mem_sigma, mem_filter, mem_filterp] at hp
    simp_rw [f, Perm.mul_apply, swap_apply_left, hp.2.2, mul_swap_mul_self]
  refine Finset.sum_bij' (fun p _ ↦ f p) (fun p _ ↦ f p) ?_ ?_ hf hf ?_
  · intro ⟨x, σ⟩ hp
    rw [mem_sigma, mem_filter, mem_filterp] at hp ⊢
    rw [Perm.mul_apply, Perm.sign_mul, hp.2.1, Perm.sign_swap h, swap_apply_right]
    exact ⟨mem_univ (σ i), rfl, rfl⟩
  · intro ⟨x, σ⟩ hp
    rw [mem_sigma, mem_filter, mem_filterp] at hp ⊢
    rw [Perm.mul_apply, Perm.sign_mul, hp.2.1, Perm.sign_swap h, swap_apply_right]
    exact ⟨mem_univ (σ i), rfl, rfl⟩
  · intro ⟨x, σ⟩ hp
    rw [mem_sigma, mem_filter, mem_filterp] at hp
    have key : ({j}ᶜ : Finset n) = disjUnion ({i} : Finset n) ({i, j} : Finset n)ᶜ (by simp) := by
      rw [singleton_disjUnion, cons_eq_insert, compl_insert, insert_erase]
      rwa [mem_compl, mem_singleton]
    simp_rw [key, prod_disjUnion, prod_singleton, Perm.mul_apply, swap_apply_left, ← mul_assoc]
    rw [mul_comm (A i x) (A i (σ i)), hp.2.2]
    refine congr_arg _ (Finset.prod_congr rfl fun x hx ↦ ?_)
    rw [mem_compl, mem_insert, mem_singleton, not_or] at hx
    rw [swap_apply_of_ne_of_ne hx.1 hx.2]

theorem mul_adjp_add_detp : A * adjp 1 A + detp (-1) A • 1 = A * adjp (-1) A + detp 1 A • 1 := by
  ext i j
  rcases eq_or_ne i j with rfl | h <;> simp_rw [add_apply, smul_apply, smul_eq_mul]
  · simp_rw [mul_adjp_add_detp_aux1, one_apply_eq, mul_one, add_comm]
  · simp_rw [mul_adjp_add_detp_aux2 A i j h, one_apply_ne h, mul_zero]

variable {A B}

theorem detp_smul_add_adjp (h : A * B = 1) :
    detp 1 B • A + adjp (-1) B = detp (-1) B • A + adjp 1 B := by
  have key := congr_arg (A * ·) (mul_adjp_add_detp B)
  simp_rw [mul_add, ← mul_assoc, h, one_mul, mul_smul, mul_one] at key
  rwa [add_comm, eq_comm, add_comm]

-- might also need an extra factor on each side unless we can prove cancellation (IsAddUnit)
theorem detp_smul_adjp (h : A * B = 1) :
    A + (detp 1 A • adjp (-1) B + detp (-1) A • adjp 1 B) =
      detp 1 A • adjp 1 B + detp (-1) A • adjp (-1) B := by
  have h0 := detp_mul' A B
  rw [h, detp_one_one, detp_neg_one_one, zero_add] at h0
  replace h := detp_smul_add_adjp h
  replace h := congr_arg₂ (· + ·) (congr_arg (detp 1 A • ·) h) (congr_arg (detp (-1) A • ·) h).symm
  simp only [smul_add, smul_smul] at h
  rwa [add_add_add_comm, ← add_smul, add_add_add_comm, ← add_smul, ← h0, add_smul, one_smul,
    add_comm A, add_assoc, IsAddUnit.add_right_inj] at h
  apply IsAddUnit.smul
  -- IsAddUnit (detp 1 A * detp (-1) B + detp (-1) A * detp 1 B)
  -- yup, this is good: ∑ ∑ A i (sigma(i)) * B j (tau (j)) invertible unless τ = σ⁻¹
  sorry

-- also need to prove cancelation here
theorem mul_eq_one_comm : A * B = 1 ↔ B * A = 1 := by
  revert A B
  suffices h : ∀ A B : Matrix n n R, A * B = 1 → B * A = 1 from fun A B ↦ ⟨h A B, h B A⟩
  intro A B h
  have h0 := detp_mul' A B
  rw [h, detp_one_one, detp_neg_one_one, zero_add] at h0
  replace h := detp_smul_adjp h
  replace h := congr_arg (B * ·) h
  simp only [mul_add, mul_smul, add_assoc] at h
  replace h := congr_arg (· + (detp 1 A * detp (-1) B + detp (-1) A * detp 1 B) • 1) h
  simp_rw [add_smul, ← smul_smul] at h
  rwa [add_assoc, add_add_add_comm, ← smul_add, ← smul_add,
    add_add_add_comm, ← smul_add, ← smul_add, smul_add, smul_add,
    mul_adjp_add_detp, smul_add, ← mul_adjp_add_detp, smul_add, ← smul_add, ← smul_add,
    add_add_add_comm, smul_smul, smul_smul, ← add_smul, ← h0,
    add_smul, one_smul, ← add_assoc _ 1, add_comm _ 1, add_assoc,
    smul_add, smul_add, add_add_add_comm, smul_smul, smul_smul, ← add_smul,
    IsAddUnit.add_left_inj] at h
  -- IsAddUnit (detp 1 A • (B * adjp (-1) B) + detp (-1) A • (B * adjp 1 B) +
  --  (detp 1 A * detp (-1) B + detp (-1) A * detp 1 B) • 1)
  apply IsAddUnit.add
  · -- IsAddUnit (detp 1 A • (B * adjp (-1) B) + detp (-1) A • (B * adjp 1 B))
    sorry
  · apply IsAddUnit.smul
    -- IsAddUnit (detp 1 A * detp (-1) B + detp (-1) A * detp 1 B)
    sorry

end Matrix
