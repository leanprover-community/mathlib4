/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Sadofschi Costa, Quang Dao
-/
import Mathlib.Data.Finsupp.Defs

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
def removeNth (i : Fin (n + 1)) (s : Fin (n + 1) →₀ M) : Fin n →₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.removeNth i s : Fin n → M)

/-- `cons` for maps `Fin n →₀ M`. See `Fin.cons` for more details. -/
def cons (y : M) (s : Fin n →₀ M) : Fin (n + 1) →₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.cons y s : Fin (n + 1) → M)

/-- `snoc` for maps `Fin n →₀ M`. See `Fin.snoc` for more details. -/
def snoc (s : Fin n →₀ M) (y : M) : Fin (n + 1) →₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.snoc s y : Fin (n + 1) → M)

/-- `insertNth` for maps `Fin n →₀ M`. See `Fin.insertNth` for more details. -/
def insertNth (i : Fin (n + 1)) (y : M) (s : Fin n →₀ M) : Fin (n + 1) →₀ M :=
  Finsupp.equivFunOnFinite.symm (Fin.insertNth i y s : Fin (n + 1) → M)

section Remove

variable (i : Fin (n + 1)) (s : Fin (n + 1) →₀ M) (j : Fin n) (y : M)

@[simp]
theorem removeNth_apply : removeNth i s j = s (i.succAbove j) := rfl

@[simp]
theorem removeNth_zero : removeNth 0 s = tail s := rfl

@[simp]
theorem removeNth_last : removeNth (Fin.last n) s = init s := by
  ext; simp [removeNth, init]

/-- Updating the `i`-th entry does not affect removing the `i`-th entry. -/
@[simp]
theorem removeNth_update : removeNth i (update s i y) = removeNth i s := by
  simp [removeNth, update]
  convert Fin.removeNth_update i y (⇑s)

@[simp]
theorem tail_apply : tail s j = s (j.succ) := rfl

@[simp]
theorem tail_update_zero : tail (update s 0 y) = tail s := by
  simp [tail, update]
  convert Fin.tail_update_zero (⇑s) y

@[simp]
theorem tail_update_succ : tail (update s 0 y) = tail s := by
  simp [tail, update]
  convert Fin.tail_update_zero (⇑s) y

@[simp]
theorem init_apply : init s j = s (j.castSucc) := rfl

@[simp]
theorem init_update_last : init (update s (Fin.last n) y) = init s := by
  simp [init, update]
  convert Fin.init_update_last (⇑s) y

@[simp]
theorem init_update_castSucc (i : Fin n) : init (update s i.castSucc y) = update (init s) i y := by
  ext a
  have : ⇑(equivFunOnFinite.symm (Fin.init ⇑s)) = Fin.init ⇑s := rfl
  simp [init, update, this]
  have : Fin.init (Function.update (⇑s) i.castSucc y) a = Function.update (Fin.init ⇑s) i y a := by
    simp only [Fin.init_update_castSucc]
  convert this

theorem tail_init_eq_init_tail (s : Fin (n + 2) →₀ M) : tail (init s) = init (tail s) := by
  simp only [tail, init, EmbeddingLike.apply_eq_iff_eq]
  have : (⇑(equivFunOnFinite.symm (Fin.init ⇑s)) : Fin (n + 1) → M) = Fin.init ⇑s := rfl
  rw [this]
  have : (⇑(equivFunOnFinite.symm (Fin.tail ⇑s)) : Fin (n + 1) → M) = Fin.tail ⇑s := rfl
  rw [this]
  convert Fin.tail_init_eq_init_tail (⇑s)

end Remove

section Add

variable (i : Fin n) (j : Fin (n + 1)) (y : M) (t : Fin (n + 1) →₀ M) (s : Fin n →₀ M)

@[simp]
theorem cons_zero : cons y s 0 = y := rfl

@[simp]
theorem cons_succ : cons y s i.succ = s i := rfl

@[simp]
theorem snoc_last : snoc s y (Fin.last n) = y := by simp [snoc]

@[simp]
theorem snoc_castSucc : snoc s y i.castSucc = s i := by simp [snoc]

@[simp]
theorem insertNth_zero : insertNth 0 y s = cons y s := by simp [insertNth, cons]

@[simp]
theorem insertNth_last : insertNth (Fin.last n) y s = snoc s y := by simp [insertNth, snoc]

@[simp]
theorem insertNth_apply_same : insertNth j y s j = y := by simp [insertNth]

@[simp]
theorem insertNth_apply_succAbove : insertNth j y s (j.succAbove i) = s i := by simp [insertNth]

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
theorem init_snoc : init (snoc s y) = s := by
  have : (⇑(equivFunOnFinite.symm (Fin.snoc (⇑s) y)) : Fin (n + 1) → M) = Fin.snoc ⇑s y := rfl
  simp [init, snoc, this]

@[simp]
theorem snoc_init_self : snoc (init t) (t (Fin.last n)) = t := by
  have : (⇑(equivFunOnFinite.symm (Fin.init (⇑t))) : Fin n → M) = Fin.init ⇑t := rfl
  simp [snoc, init, this]

@[simp]
theorem insertNth_removeNth (y : M) : insertNth j y (removeNth j t) = update t j y := by
  have : ⇑(equivFunOnFinite.symm (j.removeNth ⇑t)) = j.removeNth ⇑t := rfl
  simp [insertNth, removeNth, update, this]
  have : Function.update (⇑t) j y = ⇑(update t j y) := by
    simp only [update, coe_mk]
    convert rfl
  rw [this]
  simp only [equivFunOnFinite_symm_coe, update]

theorem insertNth_self_removeNth : insertNth j (t j) (removeNth j t) = t := by
  have : ⇑(equivFunOnFinite.symm (j.removeNth ⇑t)) = j.removeNth ⇑t := rfl
  simp [insertNth, removeNth, this]

@[simp]
theorem cons_zero_zero : cons 0 (0 : Fin n →₀ M) = 0 := by
  ext a
  by_cases c : a = 0
  · simp [c]
  · rw [← Fin.succ_pred a c, cons_succ]
    simp

@[simp]
theorem snoc_zero_zero : snoc (0 : Fin n →₀ M) 0 = 0 := by
  ext a
  simp [snoc, Fin.snoc]

@[simp]
theorem insertNth_zero_zero : insertNth j 0 (0 : Fin n →₀ M) = 0 := by
  ext a
  simp [insertNth, Fin.insertNth, Fin.succAboveCases]

variable {y} {s}

theorem cons_ne_zero_of_left (h : y ≠ 0) : cons y s ≠ 0 := by
  contrapose! h with c
  rw [← cons_zero y s, c, Finsupp.coe_zero, Pi.zero_apply]

theorem cons_ne_zero_of_right (h : s ≠ 0) : cons y s ≠ 0 := by
  contrapose! h with c
  ext a
  simp [← cons_succ a y s, c]

theorem cons_ne_zero_iff : cons y s ≠ 0 ↔ y ≠ 0 ∨ s ≠ 0 := by
  refine ⟨fun h => ?_, fun h => h.casesOn cons_ne_zero_of_left cons_ne_zero_of_right⟩
  refine imp_iff_not_or.1 fun h' c => h ?_
  rw [h', c, Finsupp.cons_zero_zero]

theorem snoc_ne_zero_of_left (h : s ≠ 0) : snoc s y ≠ 0 := by
  contrapose! h with c
  ext a
  simp [← snoc_castSucc a y s, c]

theorem snoc_ne_zero_of_right (h : y ≠ 0) : snoc s y ≠ 0 := by
  contrapose! h with c
  rw [← snoc_last y s, c, Finsupp.coe_zero, Pi.zero_apply]

theorem snoc_ne_zero_iff : snoc s y ≠ 0 ↔ s ≠ 0 ∨ y ≠ 0 := by
  refine ⟨fun h => ?_, fun h => h.casesOn snoc_ne_zero_of_left snoc_ne_zero_of_right⟩
  refine imp_iff_not_or.1 fun h' c => h ?_
  rw [h', c, Finsupp.snoc_zero_zero]

theorem insertNth_ne_zero_of_left (h : y ≠ 0) : insertNth j y s ≠ 0 := by
  contrapose! h with c
  rw [← insertNth_apply_same j y s, c, Finsupp.coe_zero, Pi.zero_apply]

theorem insertNth_ne_zero_of_right (h : s ≠ 0) : insertNth j y s ≠ 0 := by
  contrapose! h with c
  ext a
  simp [← insertNth_apply_succAbove a j y s, c]

theorem insertNth_ne_zero_iff : insertNth j y s ≠ 0 ↔ y ≠ 0 ∨ s ≠ 0 := by
  refine ⟨fun h => ?_,
    fun h => h.casesOn (insertNth_ne_zero_of_left j) (insertNth_ne_zero_of_right j)⟩
  refine imp_iff_not_or.1 fun h' c => h ?_
  rw [h', c, Finsupp.insertNth_zero_zero]

theorem cons_support : (s.cons y).support ⊆ insert 0 (s.support.map (Fin.succEmb n)) := by
  intro i hi
  suffices i = 0 ∨ ∃ a, ¬s a = 0 ∧ a.succ = i by simpa
  apply (Fin.eq_zero_or_eq_succ i).imp id (Exists.imp _)
  rintro i rfl
  simpa [Finsupp.mem_support_iff] using hi

theorem snoc_support :
    (s.snoc y).support ⊆ insert (Fin.last n) (s.support.map Fin.castSuccEmb) := by
  intro i hi
  suffices i = Fin.last n ∨ ∃ a, ¬s a = 0 ∧ a.castSucc = i by simpa
  apply (Fin.eq_castSucc_or_eq_last i).symm.imp id (Exists.imp _)
  rintro i rfl
  simpa [Finsupp.mem_support_iff] using hi

theorem insertNth_support :
    (insertNth j y s).support ⊆ insert j (s.support.map (Fin.succAboveEmb j)) := by
  intro i hi
  suffices i = j ∨ ∃ a, ¬s a = 0 ∧ j.succAbove a = i by simpa
  apply (Fin.eq_self_or_eq_succAbove i j).imp id (Exists.imp _)
  rintro i rfl
  simpa [Finsupp.mem_support_iff] using hi

end Add

end Finsupp
