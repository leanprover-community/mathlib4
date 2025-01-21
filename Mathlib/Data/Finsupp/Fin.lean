/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Sadofschi Costa, Quang Dao
-/
import Mathlib.Data.Finsupp.Single

/-!
# Tuple operations on maps `Fin n →₀ M`

We interpret maps `Fin n →₀ M` as `n`-tuples of elements of `M`, and define the following
operations:
* `Finsupp.tail` : the tail of a map `Fin (n + 1) →₀ M`, i.e., its last `n` entries;
* `Finsupp.init` : the initial of a map `Fin n →₀ M`, i.e., its first `n - 1` entries;
* `Finsupp.removeNth` : removing an element at a given entry of a map `Fin (n + 1) →₀ M`;
* `Finsupp.cons` : adding an element at the beginning of an `n`-tuple, to get an `n + 1`-tuple;
* `Finsupp.snoc` : adding an element at the end of an `n`-tuple, to get an `n + 1`-tuple;
* `Finsupp.insertNth` : adding an element at a given entry of an `n`-tuple, to get an `n + 1`-tuple.

In this context, we prove some usual properties of these operations, analogous to those of
`Data.Fin.Tuple.Basic`.
-/

open Function

noncomputable section

namespace Finsupp

variable {n : ℕ} {M : Type*} [Zero M]

/-- `tail` for maps `Fin (n + 1) →₀ M`. See `Fin.tail` for more details. -/
def tail (s : Fin (n + 1) →₀ M) : Fin n →₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.tail s)

/-- `init` for maps `Fin n →₀ M`. See `Fin.init` for more details. -/
def init (s : Fin (n + 1) →₀ M) : Fin n →₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.init s)

/-- `removeNth` for maps `Fin n →₀ M`. See `Fin.removeNth` for more details. -/
def removeNth (p : Fin (n + 1)) (s : Fin (n + 1) →₀ M) : Fin n →₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.removeNth p s : Fin n → M)

/-- `cons` for maps `Fin n →₀ M`. See `Fin.cons` for more details. -/
def cons (y : M) (s : Fin n →₀ M) : Fin (n + 1) →₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.cons y s : Fin (n + 1) → M)

/-- `snoc` for maps `Fin n →₀ M`. See `Fin.snoc` for more details. -/
def snoc (s : Fin n →₀ M) (y : M) : Fin (n + 1) →₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.snoc s y : Fin (n + 1) → M)

/-- `insertNth` for maps `Fin n →₀ M`. See `Fin.insertNth` for more details. -/
def insertNth (p : Fin (n + 1)) (y : M) (s : Fin n →₀ M) : Fin (n + 1) →₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.insertNth p y s : Fin (n + 1) → M)

variable (p : Fin (n + 1)) (y : M) (t : Fin (n + 1) →₀ M) (s : Fin n →₀ M) (i : Fin n)

-- TODO: move these old theorems to the appropriate new sections
@[simp]
theorem tail_apply : tail t i = t i.succ := rfl

@[simp]
theorem cons_zero : cons y s 0 = y := rfl

@[simp]
theorem cons_succ : cons y s i.succ = s i := rfl

@[simp]
theorem tail_cons : tail (cons y s) = s :=
  ext fun k => by simp only [tail_apply, cons_succ]

section Remove

@[simp]
theorem removeNth_apply : removeNth p t i = t (p.succAbove i) := rfl

@[simp]
theorem removeNth_zero : removeNth 0 t = tail t := rfl

@[simp]
theorem removeNth_last : removeNth (Fin.last n) t = init t := by simp [removeNth, init]

/-- Updating the `i`-th entry does not affect removing the `i`-th entry. -/
@[simp]
theorem removeNth_update : removeNth p (update t p y) = removeNth p t := by simp [removeNth]

@[simp]
theorem tail_update_zero : tail (update t 0 y) = tail t := by simp [tail]

@[simp]
theorem tail_update_succ : tail (update t i.succ y) = update (tail t) i y := by ext; simp [tail]

@[simp]
theorem init_apply : init t i = t i.castSucc := rfl

@[simp]
theorem init_update_last : init (update t (Fin.last n) y) = init t := by simp [init]

@[simp]
theorem init_update_castSucc : init (update t i.castSucc y) = update (init t) i y := by
  ext; simp [init]

theorem tail_init_eq_init_tail (t : Fin (n + 2) →₀ M) : tail (init t) = init (tail t) := by
  simp only [tail, init, coe_equivFunOnFinite_symm, Fin.tail_init_eq_init_tail]

end Remove

section Add

@[simp]
theorem snoc_last : snoc s y (Fin.last n) = y := by simp [snoc]

@[simp]
theorem snoc_castSucc : snoc s y i.castSucc = s i := by simp [snoc]

@[simp]
theorem insertNth_zero : insertNth 0 y s = cons y s := by simp [insertNth, cons]

@[simp]
theorem insertNth_last : insertNth (Fin.last n) y s = snoc s y := by simp [insertNth, snoc]

@[simp]
theorem insertNth_apply_same : insertNth p y s p = y := by simp [insertNth]

@[simp]
theorem insertNth_apply_succAbove : insertNth p y s (p.succAbove i) = s i := by simp [insertNth]

@[simp]
theorem cons_tail : cons (t 0) (tail t) = t := by
  ext a
  by_cases c_a : a = 0
  · rw [c_a, cons_zero]
  · rw [← Fin.succ_pred a c_a, cons_succ, ← tail_apply]

@[simp]
theorem init_snoc : init (snoc s y) = s := by simp [init, snoc]

@[simp]
theorem snoc_init_self : snoc (init t) (t (Fin.last n)) = t := by simp [snoc, init]

@[simp]
theorem insertNth_removeNth : insertNth p y (removeNth p t) = update t p y := by
  simp [insertNth, removeNth, coe_equivFunOnFinite_symm, Fin.insertNth_removeNth, update]
  have : Function.update (⇑t) p y = ⇑(update t p y) := by simp only [coe_update]
  rw [this, equivFunOnFinite_symm_coe, update]

theorem insertNth_self_removeNth : insertNth p (t p) (removeNth p t) = t := by
  simp [insertNth, removeNth]

@[simp]
theorem cons_zero_zero : cons 0 (0 : Fin n →₀ M) = 0 := by
  ext a
  by_cases c : a = 0
  · simp only [c, cons_zero, coe_zero, Pi.zero_apply]
  · rw [← Fin.succ_pred a c, cons_succ]
    simp only [coe_zero, Pi.zero_apply, Fin.succ_pred]

@[simp]
theorem snoc_zero_zero : snoc (0 : Fin n →₀ M) 0 = 0 := by
  ext a
  simp only [snoc, coe_zero, equivFunOnFinite_symm_apply_toFun, Fin.snoc, Fin.castSucc_castLT,
    Pi.zero_apply, cast_eq, dite_eq_ite, ite_self]

@[simp]
theorem insertNth_zero_zero : insertNth p 0 (0 : Fin n →₀ M) = 0 := by
  ext a
  simp only [insertNth, coe_zero, equivFunOnFinite_symm_apply_toFun, Fin.insertNth,
    Fin.succAboveCases, eq_rec_constant, Pi.zero_apply, dite_eq_ite, ite_self]

variable {y} {s}

theorem cons_ne_zero_of_left (h : y ≠ 0) : cons y s ≠ 0 := by
  contrapose! h with c
  rw [← cons_zero y s, c, Finsupp.coe_zero, Pi.zero_apply]

theorem cons_ne_zero_of_right (h : s ≠ 0) : cons y s ≠ 0 := by
  contrapose! h with c
  ext a
  simp only [← cons_succ y s a, c, coe_zero, Pi.zero_apply]

theorem cons_ne_zero_iff : cons y s ≠ 0 ↔ y ≠ 0 ∨ s ≠ 0 := by
  refine ⟨fun h => ?_, fun h => h.casesOn cons_ne_zero_of_left cons_ne_zero_of_right⟩
  refine imp_iff_not_or.1 fun h' c => h ?_
  rw [h', c, Finsupp.cons_zero_zero]

theorem snoc_ne_zero_of_left (h : s ≠ 0) : snoc s y ≠ 0 := by
  contrapose! h with c
  ext a
  simp only [← snoc_castSucc y s a, c, coe_zero, Pi.zero_apply]

theorem snoc_ne_zero_of_right (h : y ≠ 0) : snoc s y ≠ 0 := by
  contrapose! h with c
  rw [← snoc_last y s, c, Finsupp.coe_zero, Pi.zero_apply]

theorem snoc_ne_zero_iff : snoc s y ≠ 0 ↔ s ≠ 0 ∨ y ≠ 0 := by
  refine ⟨fun h => ?_, fun h => h.casesOn snoc_ne_zero_of_left snoc_ne_zero_of_right⟩
  refine imp_iff_not_or.1 fun h' c => h ?_
  rw [h', c, Finsupp.snoc_zero_zero]

theorem insertNth_ne_zero_of_left (h : y ≠ 0) : insertNth p y s ≠ 0 := by
  contrapose! h with c
  rw [← insertNth_apply_same p y s, c, Finsupp.coe_zero, Pi.zero_apply]

theorem insertNth_ne_zero_of_right (h : s ≠ 0) : insertNth p y s ≠ 0 := by
  contrapose! h with c
  ext a
  simp only [← insertNth_apply_succAbove p y s a, c, coe_zero, Pi.zero_apply]

theorem insertNth_ne_zero_iff : insertNth p y s ≠ 0 ↔ y ≠ 0 ∨ s ≠ 0 := by
  refine ⟨fun h => ?_,
    fun h => h.casesOn (insertNth_ne_zero_of_left p) (insertNth_ne_zero_of_right p)⟩
  refine imp_iff_not_or.1 fun h' c => h ?_
  rw [h', c, Finsupp.insertNth_zero_zero]

theorem cons_support : (s.cons y).support ⊆ insert 0 (s.support.map (Fin.succEmb n)) := by
  intro i hi
  suffices i = 0 ∨ ∃ a, ¬s a = 0 ∧ a.succ = i by simpa
  apply (Fin.eq_zero_or_eq_succ i).imp id (Exists.imp _)
  rintro i rfl
  simpa [Finsupp.mem_support_iff] using hi

theorem cons_right_injective : Injective (Finsupp.cons y : (Fin n →₀ M) → Fin (n + 1) →₀ M) :=
  equivFunOnFinite.symm.injective.comp ((Fin.cons_right_injective _).comp DFunLike.coe_injective)

theorem snoc_support :
    (s.snoc y).support ⊆ insert (Fin.last n) (s.support.map Fin.castSuccEmb) := by
  intro i hi
  suffices i = Fin.last n ∨ ∃ a, ¬s a = 0 ∧ a.castSucc = i by simpa
  apply (Fin.eq_castSucc_or_eq_last i).symm.imp id (Exists.imp _)
  rintro i rfl
  simpa [Finsupp.mem_support_iff] using hi

theorem snoc_left_injective : Injective (Finsupp.snoc · y : (Fin n →₀ M) → Fin (n + 1) →₀ M) :=
  equivFunOnFinite.symm.injective.comp
    ((Fin.snoc_left_injective (α := fun _ => M) y).comp DFunLike.coe_injective)

theorem insertNth_support :
    (insertNth p y s).support ⊆ insert p (s.support.map (Fin.succAboveEmb p)) := by
  intro i hi
  suffices i = p ∨ ∃ a, ¬s a = 0 ∧ p.succAbove a = i by simpa
  apply (Fin.eq_self_or_eq_succAbove p i).imp id (Exists.imp _)
  rintro j rfl
  simpa [Finsupp.mem_support_iff] using hi

theorem insertNth_right_injective :
    Injective (Finsupp.insertNth p y : (Fin n →₀ M) → Fin (n + 1) →₀ M) :=
  equivFunOnFinite.symm.injective.comp
    ((Fin.insertNth_right_injective _).comp DFunLike.coe_injective)

end Add

end Finsupp
