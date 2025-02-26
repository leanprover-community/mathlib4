/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Sym2.Order

/-!
# Lemmas on `Finset.sum` and `Finset.prod` involving `Finset.sym2` or `Finset.sym`.
-/

namespace Finset

open Multiset

theorem sum_sym2_filter_not_isDiag {ι α} [LinearOrder ι] [AddCommMonoid α]
    (s : Finset ι) (p : Sym2 ι → α) :
    ∑ i ∈ s.sym2 with ¬ i.IsDiag, p i = ∑ i ∈ s.offDiag with i.1 < i.2, p s(i.1, i.2) := by
  rw [Finset.offDiag_filter_lt_eq_filter_le]
  conv_rhs => rw [← Finset.sum_subtype_eq_sum_filter]
  refine (Finset.sum_equiv Sym2.sortEquiv.symm ?_ ?_).symm
  · rintro ⟨⟨i₁, j₁⟩, hij₁⟩
    simp [and_assoc]
  · rintro ⟨⟨i₁, j₁⟩, hij₁⟩
    simp

theorem range_sym_prop {m n : ℕ} {k : Sym ℕ m} (hk : k ∈ (Finset.range (n + 1)).sym m) :
    (Finset.sum (range (n + 1)) fun i => count i k) = m := by
  simp_rw [← k.prop, ← toFinset_sum_count_eq, eq_comm]
  apply sum_subset_zero_on_sdiff _ _ (fun _ _ ↦ rfl)
  · intro i hi
    simp only [Sym.val_eq_coe, mem_toFinset, Sym.mem_coe] at hi
    exact mem_sym_iff.mp hk i hi
  · intro _ hx
    simp only [Sym.val_eq_coe, mem_sdiff, Finset.mem_range, mem_toFinset, Sym.mem_coe] at hx
    simp only [count_eq_zero, Sym.mem_coe]
    exact hx.2

theorem sum_range_sym_mul_compl {m n : ℕ} {k : Sym ℕ m} (hk : k ∈ (Finset.range (n + 1)).sym m) :
    (Finset.sum (range (n + 1)) fun i => count i k * (n - i)) =
      m * n - Finset.sum (range (n + 1)) fun i => count i k * i := by
  suffices h : (((Finset.range (n + 1)).sum fun i => count i k * (n - i)) +
        (Finset.range (n + 1)).sum fun i => count i k * i) = m * n by
    rw [← h, Nat.add_sub_cancel]
  simp_rw [← sum_add_distrib, ← mul_add]
  have hn : ∀ x ∈ Finset.range (n + 1), count x ↑k * (n - x + x) = count x ↑k * n := fun _ hx ↦ by
    rw [Nat.sub_add_cancel (Nat.lt_succ_iff.mp (Finset.mem_range.mp hx))]
  rw [sum_congr rfl hn, ← sum_mul, range_sym_prop hk]

end Finset
