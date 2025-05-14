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
  ⟨Fin.tail x, x.injective.comp <| Fin.succ_injective _⟩

@[simp, norm_cast]
theorem coe_tail {n : ℕ} (x : Fin (n + 1) ↪ α) : ↑(tail x) = Fin.tail x := rfl

/-- Adding a new element at the beginning of an injective n-tuple, to get an injective n+1-tuple. -/
def cons {n : ℕ} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) : Fin (n + 1) ↪ α :=
  ⟨Fin.cons a x, cons_injective_iff.mpr ⟨ha, x.inj'⟩⟩

@[simp, norm_cast]
theorem coe_cons {n : ℕ} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) :
    ↑(cons x ha) = Fin.cons a x := rfl

theorem tail_cons {n : ℕ} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) :
    tail (cons x ha) = x := rfl

/-- Remove the last element from an injective (n + 1)-tuple -/
def init {n : ℕ} (x : Fin (n + 1) ↪ α) : Fin n ↪ α :=
  ⟨Fin.init x, x.injective.comp <| castSucc_injective _⟩

/-- Adding a new element at the end of an injective n-tuple, to get an injective n+1-tuple. -/
def snoc {n : ℕ} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) : Fin (n + 1) ↪ α :=
  ⟨Fin.snoc x a, snoc_injective_iff.mpr ⟨x.inj', ha⟩⟩

@[simp, norm_cast]
theorem coe_snoc {n : ℕ} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) :
    ↑(snoc x ha) = Fin.snoc x a := rfl

theorem init_snoc {n : ℕ} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) :
    init (snoc x ha) = x := by
  apply coe_injective
  simp [snoc, init, init_snoc]

theorem snoc_castSucc {n : ℕ} {x : Fin n ↪ α} {a : α} {ha : a ∉ range ⇑x} {i : Fin n} :
    snoc x ha i.castSucc  = x i := by
  rw [coe_snoc, Fin.snoc_castSucc]

theorem snoc_last {n : ℕ} {x : Fin n ↪ α} {a : α} {ha : a ∉ range ⇑x} :
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

/-- Append a `Fin n ↪ α` at the end of a `Fin m ↪ α` if their ranges are disjoint -/
def append {m n : ℕ} {x : Fin m ↪ α} {y : Fin n ↪ α}
    (h : Disjoint (range ⇑x) (range ⇑y)) : Fin (m + n) ↪ α :=
  ⟨Fin.append x y, Fin.append_injective_iff.mpr ⟨x.inj', y.inj', h⟩⟩

@[simp, norm_cast]
theorem coe_append {m n : ℕ} {x : Fin m ↪ α} {y : Fin n ↪ α}
    (h : Disjoint (range ⇑x) (range ⇑y)) :
    append h = Fin.append x y := rfl

end Fin.Embedding

