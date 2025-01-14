/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Sym2.Order

/-!
# Lemmas on `Finset.sum` and `Finset.prod` involving `Finset.sym2`
-/

theorem Finset.sum_sym2_filter_not_isDiag {ι α} [LinearOrder ι] [AddCommMonoid α]
    (s : Finset ι) (p : Sym2 ι → α) :
    ∑ i ∈ s.sym2 with ¬ i.IsDiag, p i = ∑ i ∈ s.offDiag with i.1 < i.2, p s(i.1, i.2) := by
  rw [Finset.offDiag_filter_lt_eq_filter_le]
  conv_rhs => rw [← Finset.sum_subtype_eq_sum_filter]
  refine (Finset.sum_equiv Sym2.sortEquiv.symm ?_ ?_).symm
  · rintro ⟨⟨i₁, j₁⟩, hij₁⟩
    simp [and_assoc]
  · rintro ⟨⟨i₁, j₁⟩, hij₁⟩
    simp
