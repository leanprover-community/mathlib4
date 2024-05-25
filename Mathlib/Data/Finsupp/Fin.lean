/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Sadofschi Costa
-/
import Mathlib.Data.Finsupp.Defs

#align_import data.finsupp.fin from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

/-!
# `cons` and `tail` for maps `Fin n →₀ M`

We interpret maps `Fin n →₀ M` as `n`-tuples of elements of `M`,
We define the following operations:
* `Finsupp.tail` : the tail of a map `Fin (n + 1) →₀ M`, i.e., its last `n` entries;
* `Finsupp.cons` : adding an element at the beginning of an `n`-tuple, to get an `n + 1`-tuple;

In this context, we prove some usual properties of `tail` and `cons`, analogous to those of
`Data.Fin.Tuple.Basic`.
-/


noncomputable section

namespace Finsupp

variable {n : ℕ} (i : Fin n) {M : Type*} [Zero M] (y : M) (t : Fin (n + 1) →₀ M) (s : Fin n →₀ M)

/-- `tail` for maps `Fin (n + 1) →₀ M`. See `Fin.tail` for more details. -/
def tail (s : Fin (n + 1) →₀ M) : Fin n →₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.tail s)
#align finsupp.tail Finsupp.tail

/-- `cons` for maps `Fin n →₀ M`. See `Fin.cons` for more details. -/
def cons (y : M) (s : Fin n →₀ M) : Fin (n + 1) →₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.cons y s : Fin (n + 1) → M)
#align finsupp.cons Finsupp.cons

theorem tail_apply : tail t i = t i.succ :=
  rfl
#align finsupp.tail_apply Finsupp.tail_apply

@[simp]
theorem cons_zero : cons y s 0 = y :=
  rfl
#align finsupp.cons_zero Finsupp.cons_zero

@[simp]
theorem cons_succ : cons y s i.succ = s i :=
  -- Porting note: was Fin.cons_succ _ _ _
  rfl
#align finsupp.cons_succ Finsupp.cons_succ

@[simp]
theorem tail_cons : tail (cons y s) = s :=
  ext fun k => by simp only [tail_apply, cons_succ]
#align finsupp.tail_cons Finsupp.tail_cons

@[simp]
theorem cons_tail : cons (t 0) (tail t) = t := by
  ext a
  by_cases c_a : a = 0
  · rw [c_a, cons_zero]
  · rw [← Fin.succ_pred a c_a, cons_succ, ← tail_apply]
#align finsupp.cons_tail Finsupp.cons_tail

@[simp]
theorem cons_zero_zero : cons 0 (0 : Fin n →₀ M) = 0 := by
  ext a
  by_cases c : a = 0
  · simp [c]
  · rw [← Fin.succ_pred a c, cons_succ]
    simp
#align finsupp.cons_zero_zero Finsupp.cons_zero_zero

variable {s} {y}

theorem cons_ne_zero_of_left (h : y ≠ 0) : cons y s ≠ 0 := by
  contrapose! h with c
  rw [← cons_zero y s, c, Finsupp.coe_zero, Pi.zero_apply]
#align finsupp.cons_ne_zero_of_left Finsupp.cons_ne_zero_of_left

theorem cons_ne_zero_of_right (h : s ≠ 0) : cons y s ≠ 0 := by
  contrapose! h with c
  ext a
  simp [← cons_succ a y s, c]
#align finsupp.cons_ne_zero_of_right Finsupp.cons_ne_zero_of_right

theorem cons_ne_zero_iff : cons y s ≠ 0 ↔ y ≠ 0 ∨ s ≠ 0 := by
  refine ⟨fun h => ?_, fun h => h.casesOn cons_ne_zero_of_left cons_ne_zero_of_right⟩
  refine imp_iff_not_or.1 fun h' c => h ?_
  rw [h', c, Finsupp.cons_zero_zero]
#align finsupp.cons_ne_zero_iff Finsupp.cons_ne_zero_iff

lemma cons_support : (s.cons y).support ⊆ insert 0 (s.support.map (Fin.succEmb n)) := by
  intro i hi
  suffices i = 0 ∨ ∃ a, ¬s a = 0 ∧ a.succ = i by simpa
  apply (Fin.eq_zero_or_eq_succ i).imp id (Exists.imp _)
  rintro i rfl
  simpa [Finsupp.mem_support_iff] using hi

end Finsupp
