/-
Copyright (c) 2024 Bolton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton
-/
import Mathlib.Data.Finsupp.Defs

/-!
# Finsupp version of Option.elim

Similar to how `Finsupp.cons` constructs a map `Fin (n + 1) →₀ M` from a map `Fin n →₀ M`,
we define `Finsupp.Option.cons` to construct a map `Option α →₀ M` from a map `α →₀ M`.
We can also define an analogue of `Finsupp.tail` for `Option α →₀ M`.

-/


noncomputable section

namespace Finsupp

namespace Option

-- variable {n : ℕ} (i : Fin n) {M : Type*} [Zero M] (y : M) (t : Fin (n + 1) →₀ M) (s : Fin n →₀ M)
variable {α : Type*} (i : α) {M : Type*} [Zero M] (y : M) (t : Option α →₀ M) (s : α →₀ M)

/-- `tail` for maps `Option α →₀ M`. See `Fin.tail` for more details. -/
def tail (s : Option α →₀ M) : α →₀ M where
  support := Finset.eraseNone s.support
  toFun i := s (some i)
  mem_support_toFun := by simp only [Finset.mem_eraseNone, mem_support_iff, ne_eq, implies_true]

/-- `cons` for maps `α →₀ M`. See `Fin.cons` for more details. -/
def cons (y : M) (s : α →₀ M) : Option α →₀ M where
  support := sorry --if M = 0 then Finset.insertNone s.support else (s.support.map Function.Embedding.some)
  toFun a := Option.elim a y s
  mem_support_toFun := _

theorem tail_apply : tail t i = t (some i) :=
  rfl

@[simp]
theorem cons_zero : cons y s none = y :=
  rfl

@[simp]
theorem cons_succ : cons y s (some i) = s i :=
  rfl

@[simp]
theorem tail_cons : tail (cons y s) = s :=
  ext fun k => by simp only [tail_apply, cons_succ]

@[simp]
theorem cons_tail : cons (t 0) (tail t) = t := by
  ext a
  by_cases c_a : a = 0
  · rw [c_a, cons_zero]
  · rw [← Fin.succ_pred a c_a, cons_succ, ← tail_apply]

@[simp]
theorem cons_zero_zero : cons 0 (0 : α →₀ M) = 0 := by
  ext a
  by_cases c : a = 0
  · simp [c]
  · rw [← Fin.succ_pred a c, cons_succ]
    simp

variable {s} {y}

theorem cons_ne_zero_of_left (h : y ≠ 0) : cons y s ≠ 0 := by
  contrapose! h with c
  rw [← cons_zero y s, c, Finsupp.coe_zero, Pi.zero_apply]

theorem cons_ne_zero_of_right (h : s ≠ 0) : cons y s ≠ 0 := by
  contrapose! h with c
  ext a
  simp [← cons_succ a y s, c]

theorem cons_ne_zero_iff : cons y s ≠ 0 ↔ y ≠ 0 ∨ s ≠ 0 := by
  refine' ⟨fun h => _, fun h => h.casesOn cons_ne_zero_of_left cons_ne_zero_of_right⟩
  refine' imp_iff_not_or.1 fun h' c => h _
  rw [h', c, Finsupp.cons_zero_zero]

lemma cons_support : (s.cons y).support ⊆ insert 0 (s.support.map (Fin.succEmb n).toEmbedding) := by
  intro i hi
  suffices i = 0 ∨ ∃ a, ¬s a = 0 ∧ a.succ = i by simpa
  apply (Fin.eq_zero_or_eq_succ i).imp id (Exists.imp _)
  rintro i rfl
  simpa [Finsupp.mem_support_iff] using hi

end Finsupp
