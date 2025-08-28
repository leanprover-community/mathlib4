/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Nilpotent maps on finite modules

-/

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

theorem Module.End.isNilpotent_iff_of_finite [Module.Finite R M] {f : End R M} :
    IsNilpotent f ↔ ∀ m : M, ∃ n : ℕ, (f ^ n) m = 0 := by
  refine ⟨fun ⟨n, hn⟩ m ↦ ⟨n, by simp [hn]⟩, fun h ↦ ?_⟩
  rcases Module.Finite.fg_top (R := R) (M := M) with ⟨S, hS⟩
  choose g hg using h
  use Finset.sup S g
  ext m
  have hm : m ∈ Submodule.span R S := by simp [hS]
  induction hm using Submodule.span_induction with
  | mem x hx => exact pow_map_zero_of_le (Finset.le_sup hx) (hg x)
  | zero => simp
  | add => simp_all
  | smul => simp_all

namespace Matrix

open scoped Matrix

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {A : Matrix ι ι R}

@[simp]
theorem isNilpotent_transpose_iff :
    IsNilpotent Aᵀ ↔ IsNilpotent A := by
  simp_rw [IsNilpotent, ← transpose_pow, transpose_eq_zero]

theorem isNilpotent_iff :
    IsNilpotent A ↔ ∀ v, ∃ n : ℕ, A ^ n *ᵥ v = 0 := by
  simp_rw [← isNilpotent_toLin'_iff, Module.End.isNilpotent_iff_of_finite, ← toLin'_pow,
    toLin'_apply]

theorem isNilpotent_iff_forall_row :
    IsNilpotent A ↔ ∀ i, ∃ n : ℕ, (A ^ n).row i = 0 := by
  rw [← isNilpotent_transpose_iff, isNilpotent_iff]
  refine ⟨fun h i ↦ ?_, fun h v ↦ ?_⟩
  · obtain ⟨n, hn⟩ := h (Pi.single i 1)
    exact ⟨n, by simpa [← transpose_pow] using hn⟩
  · choose n hn using h
    suffices ∀ i, (A ^ ⨆ j, n j) i = 0 from ⟨⨆ j, n j, by simp [mulVec_eq_sum, this]⟩
    exact fun i ↦ pow_row_eq_zero_of_le (hn i) (Finite.le_ciSup n i)

theorem isNilpotent_iff_forall_col :
    IsNilpotent A ↔ ∀ i, ∃ n : ℕ, (A ^ n).col i = 0 := by
  rw [← isNilpotent_transpose_iff, isNilpotent_iff_forall_row]
  simp_rw [← transpose_pow, row_transpose]

end Matrix
