/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Lemmas on `Finset.sum` and `Finset.prod` involving `Finset.sym2` or `Finset.sym`.
-/

namespace Finset

open Multiset

theorem sum_sym2_filter_not_isDiag {ι M} [LinearOrder ι] [AddCommMonoid M]
    (s : Finset ι) (p : Sym2 ι → M) :
    ∑ i ∈ s.sym2 with ¬ i.IsDiag, p i = ∑ i ∈ s.offDiag with i.1 < i.2, p s(i.1, i.2) := by
  rw [Finset.offDiag_filter_lt_eq_filter_le]
  conv_rhs => rw [← Finset.sum_subtype_eq_sum_filter]
  refine (Finset.sum_equiv Sym2.sortEquiv.symm ?_ ?_).symm
  all_goals aesop

theorem sum_count_of_mem_sym {α} [DecidableEq α] {m : ℕ} {k : Sym α m} {s : Finset α}
    (hk : k ∈ s.sym m) : (∑ i ∈ s, count i k) = m := by
  simp_all

end Finset

