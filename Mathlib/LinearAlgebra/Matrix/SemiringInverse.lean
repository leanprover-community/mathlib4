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


-/


namespace Matrix

open Equiv

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommSemiring R]

variable (s : ℤˣ) (A B : Matrix n n R) (i j : n)

/-- Filter by parity -/
def filterp : Finset (Perm n) := Finset.univ.filter (fun σ ↦ σ.sign = s)

def fix : Finset (Perm n) := Finset.univ.filter (fun σ ↦ σ i = j)

/-- Filter determinant by parity. -/
def detp := ∑ σ ∈ filterp s, ∏ k, A k (σ k)

lemma detp_one_one : detp 1 (1 : Matrix n n R) = 1 := by
  rw [detp, Finset.sum_eq_single_of_mem 1]
  · simp [one_apply]
  · simp [filterp]
  · rintro σ - hσ1
    obtain ⟨i, hi⟩ := not_forall.mp (mt Perm.ext_iff.mpr hσ1)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (one_apply_ne' hi)

lemma detp_neg_one_one : detp (-1) (1 : Matrix n n R) = 0 := by
  rw [detp, Finset.sum_eq_zero]
  intro σ hσ
  have hσ1 : σ ≠ 1 := by
    contrapose! hσ
    simp [filterp, hσ]
  obtain ⟨i, hi⟩ := not_forall.mp (mt Perm.ext_iff.mpr hσ1)
  exact Finset.prod_eq_zero (Finset.mem_univ i) (one_apply_ne' hi)

/-- Filter adjugate matrix by parity. -/
def adjp : Matrix n n R := fun i j ↦ ∑ σ ∈ filterp s ∩ fix j i, ∏ k ∈ {j}ᶜ, A k (σ k)

theorem detp_mul :
    detp s (A * B) = detp 1 A * detp s B + detp (-1) A * detp (-s) B := by
  simp only [detp, mul_apply]
  sorry

-- theorem detp_mul' :
--     detp 1 (A * B) + detp 1 A * detp (-1) B + detp (-1) A * detp 1 B =
--       detp (-1) (A * B) + detp 1 A * detp 1 B + detp (-1) A * detp (-1) B := by
--   simp only [detp_mul]
--   abel

variable {A B}

theorem detp_smul_eq_adjp_of_mul_eq_one (h : A * B = 1) :
    detp 1 B • A + adjp (-1) B = detp (-1) B • A + adjp 1 B := by
  sorry

theorem eq_detp_smul_adjp (h : A * B = 1) :
    A + detp 1 A • adjp (-1) B + detp (-1) A • adjp 1 B =
      detp 1 A • adjp 1 B + detp (-1) A • adjp (-1) B := by
  have h1 := detp_mul 1 A B
  have h2 := detp_mul (-1) A B
  rw [h] at h1 h2
  rw [detp_one_one] at h1
  rw [detp_neg_one_one, neg_neg] at h2
  have h3 := detp_smul_eq_adjp_of_mul_eq_one h
  have h4 := congr_arg (detp 1 A • ·) h3
  have h5 := congr_arg (detp (-1) A • ·) h3
  simp only [smul_add, smul_smul] at h4 h5
  have h6 := congr_arg₂ (· + ·) h4 h5.symm
  simp only at h6
  rwa [add_add_add_comm, ← add_smul, ← h1, one_smul, ← add_assoc,
    add_add_add_comm, ← add_smul, ← h2, zero_smul, ← add_assoc, zero_add] at h6

theorem mul_eq_one_comm : A * B = 1 ↔ B * A = 1 := by
  revert A B
  suffices h : ∀ A B : Matrix n n R, A * B = 1 → B * A = 1 from fun A B ↦ ⟨h A B, h B A⟩
  intro A B h
  have h1 i : ∑ k, A i k * B k i = 1 := (Matrix.ext_iff.mpr h i i).trans (Matrix.one_apply_eq i)
  have h2 i j (hij : i ≠ j) : ∑ k, A i k * B k j = 0 :=
    (Matrix.ext_iff.mpr h i j).trans (Matrix.one_apply_ne hij)
  have h3 (i j : n) : False := by
    let P1 := ∑ σ ∈ filterp 1 ∩ fix j i, ∏ k ∈ {j}ᶜ, B k (σ k)
    let P2 := ∑ σ ∈ filterp (-1) ∩ fix j i, ∏ k ∈ {j}ᶜ, B k (σ k)
    have h3 := congr_arg₂ (· + ·) (congr_arg (· * P1) (h1 i)) (congr_arg (· * P2) (h1 i)).symm
    simp_rw [one_mul, add_comm P1, P1, P2] at h3

    -- multiply both sides of h1 i by P1 and P2
    -- and go ham


  sorry

end Matrix
