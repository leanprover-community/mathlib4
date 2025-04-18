/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Fin.Basic

/-! # Constructions of embeddings of `Fin n` into a type

* `Fin.Embedding.cons` : from an embedding `x : Fin n ↪ α` and `a : α` such that
`a ∉ x.range`, construct an embedding `Fin (n + 1) ↪ α` by putting `a` at `0`

* `Fin.Embedding.tail`: the tail of an embedding `x : Fin (n + 1) ↪ α`

* `Fin.Embedding.snoc` : from an embedding `x : Fin n ↪ α` and `a : α`
such that `a ∉ x.range`, construct an embedding `Fin (n + 1) ↪ α`
by putting `a` at the end.

* `Fin.Embedding.init`: the init of an embedding `x : Fin (n + 1) ↪ α`

* `Fin.Embedding.append` : merges two embeddings `Fin m ↪ α` and `Fin n ↪ α`
into an embedding `Fin (m + n) ↪ α` if they have disjoint ranges

-/

open Function.Embedding Fin Set Nat

namespace Fin.Embedding

variable {α : Type*}

/-- Remove the first element from an injective (n + 1)-tuple -/
def tail {n : ℕ} (x : Fin (n + 1) ↪ α) : Fin n ↪ α :=
  ⟨Fin.tail x, fun i j h ↦ by rw [← succ_inj, x.inj' h]⟩

def coe_tail {n : ℕ} (x : Fin (n + 1) ↪ α) : ↑(tail x) = Fin.tail x := rfl

/-- Adding a new element at the beginning of an injective n-tuple, to get an injective n+1-tuple. -/
def cons {n : ℕ} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) : Fin (n + 1) ↪ α :=
  ⟨Fin.cons a x, cons_injective_iff.mpr ⟨ha, x.inj'⟩⟩

def coe_cons {n : ℕ} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) :
    ↑(cons x ha) = Fin.cons a x := rfl

theorem tail_cons {n : ℕ} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) :
    tail (cons x ha) = x := rfl

/-- Remove the last element from an injective (n + 1)-tuple -/
def init {n : ℕ} (x : Fin (n + 1) ↪ α) : Fin n ↪ α :=
  ⟨Fin.init x, fun i j h ↦ by rw [← castSucc_inj, x.inj' h]⟩

/-- Adding a new element at the end of an injective n-tuple, to get an injective n+1-tuple. -/
def snoc {n : ℕ} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) : Fin (n + 1) ↪ α :=
  ⟨Fin.snoc x a, snoc_injective_iff.mpr ⟨x.inj', ha⟩⟩

theorem coe_snoc {n : ℕ} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) :
    ↑(snoc x ha) = Fin.snoc x a := rfl

theorem init_snoc {n : ℕ} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) :
    init (snoc x ha) = x := by
  apply coe_injective
  simp [snoc, init, init_snoc]

theorem snoc_castSucc {n : ℕ} {x : Fin n ↪ α}
    {a : α} {ha : a ∉ range ⇑x} {i : Fin n} :
    snoc x ha i.castSucc  = x i := by
  rw [coe_snoc, Fin.snoc_castSucc]

theorem snoc_last {n : ℕ} {x : Fin n ↪ α}
    {a : α} {ha : a ∉ range ⇑x} :
    snoc x ha (last n) = a := by
  rw [coe_snoc, Fin.snoc_last]

-- Mathlib.Data.Fin.Basic
theorem _root_.Fin.exists_eq_castAdd_or_exists_eq_natAdd {m n : ℕ} (i : Fin (m + n)) :
    (∃ i' : Fin m, i = castAdd n i') ∨ ∃ i', i = natAdd m i' := by
  rcases Nat.lt_or_ge i.val m with hi | hi
  · exact Or.inl ⟨⟨i.val, hi⟩, by rw [castAdd_mk]⟩
  · exact Or.inr
      ⟨⟨i.val - m, by simp [Nat.sub_lt_iff_lt_add' hi, i.prop]⟩,
        by simp only [natAdd_mk, ← Fin.val_inj, Nat.add_sub_of_le hi]⟩

theorem _root_.Fin.append_injective_iff {m n : ℕ} {x : Fin m → α} {y : Fin n → α} :
  Function.Injective (Fin.append x y) ↔
    Function.Injective x ∧ Function.Injective y ∧ Disjoint (range x) (range y) := by
  constructor
  · intro H
    constructor
    · intro i j h
      rwa [← Fin.castAdd_inj, ← H.eq_iff, Fin.append_left, Fin.append_left]
    constructor
    · intro i j h
      rwa [← Fin.natAdd_inj, ← H.eq_iff, Fin.append_right, Fin.append_right]
    · rw [Set.disjoint_iff_forall_ne]
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      rw [← Fin.append_left x y i, ← Fin.append_right x y j, H.ne_iff]
      apply Fin.ne_of_lt
      simp only [lt_iff_val_lt_val, coe_castAdd, coe_natAdd]
      exact lt_of_lt_of_le i.prop (le_add_right m ↑j)
  · rintro ⟨Hx, Hy, H⟩
    intro i j h
    rcases Fin.exists_eq_castAdd_or_exists_eq_natAdd i with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rcases Fin.exists_eq_castAdd_or_exists_eq_natAdd j with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · simpa [append_left, Hx.eq_iff] using h
      · simp only [append_left, append_right] at h
        rw [Set.disjoint_iff_forall_ne] at H
        exact False.elim (H (mem_range_self i) (mem_range_self j) h)
    · rcases Fin.exists_eq_castAdd_or_exists_eq_natAdd j with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · simp only [append_left, append_right] at h
        rw [Set.disjoint_iff_forall_ne] at H
        exact False.elim (H (mem_range_self j) (mem_range_self i) h.symm)
      · simpa [append_right, Hy.eq_iff] using h

/-- Append a `Fin n ↪ α` at the end of a `Fin m ↪ α` if their ranges are disjoint -/
def append {m n : ℕ} {x : Fin m ↪ α} {y : Fin n ↪ α}
    (h : Disjoint (range ⇑x) (range ⇑y)) : Fin (m + n) ↪ α :=
  ⟨Fin.append x y, Fin.append_injective_iff.mpr ⟨x.inj', y.inj', h⟩⟩

theorem coe_append {m n : ℕ} {x : Fin m ↪ α} {y : Fin n ↪ α}
    (h : Disjoint (range ⇑x) (range ⇑y)) :
    append h = Fin.append x y := rfl

theorem append_left {m n : ℕ} {x : Fin m ↪ α} {y : Fin n ↪ α}
    (h : Disjoint (range ⇑x) (range ⇑y)) (i : Fin m) :
    append h (castAdd n i) = x i := by
  simp [coe_append, Fin.append_left]

theorem append_right {m n : ℕ} {x : Fin m ↪ α} {y : Fin n ↪ α}
    (h : Disjoint (range ⇑x) (range ⇑y)) (i : Fin n) :
    append h (natAdd m i) = y i := by
  simp [coe_append, Fin.append_right]

end Fin.Embedding

