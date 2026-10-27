/-
Copyright (c) 2026 Viviana del Barco, Gustavo Infanti, Exequiel Rivas, Paul Schwahn.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Viviana del Barco, Gustavo Infanti, Exequiel Rivas, Paul Schwahn
-/
module

import Mathlib

/-!
# Products in a magma

In this file we introduce three different notions of `n`-ary products in a magma and prove
results about their interactions.
- `Products`, the set of all products of a given tuple of elements,
  regardless of order and parenthesization.
- `LeftProducts`, the set of all "left-normal" products of a given tuple, i.e. those with all
  parentheses aligned to the left.
- `OrderedLeftProduct`, the left-normal product of a tuple in the given order.

## Main results

- `orderedLeftProduct_mem_leftProducts`: For a given tuple `a : Fin n → A`, `OrderedLeftProduct a`
  is contained in the set `LeftProducts a`.
- `leftProducts_exists_ordering`: Any element of `LeftProducts a` can be written as an
  `OrderedLeftProduct` up to a permutation of `a`.
-/

variable {A : Type*} [Mul A]

set_option linter.unusedVariables false in
/-- The set of all left-normal `n`-ary products of elements of `a : Fin n → A`. -/
def LeftProducts {n : ℕ} : (a : Fin n → A) → Set A :=
  Nat.rec
  (motive := fun n ↦ (Fin n → A) → Set A)
  (fun _ ↦ ∅) -- junk value
  (fun n M ↦ match n with
  | 0 => fun a ↦ {a 0}
  | m + 1 => fun a ↦
  Set.range fun (⟨i, x⟩ : (i : Fin (m + 1 + 1)) × M (a ∘ (Fin.succAbove i))) ↦ x * (a i))
  n

@[simp]
theorem leftProducts_zero (a : Fin 0 → A) : LeftProducts a = ∅ := by
  rfl

@[simp]
theorem leftProducts_one (a : Fin 1 → A) : LeftProducts a = {a 0} := by
  rfl

set_option linter.unusedVariables false in
theorem leftProducts_succ {n : ℕ} (hn : n ≠ 0) (a : Fin (n + 1) → A) :
    LeftProducts a = Set.range
      fun (⟨i, x⟩ : (i : Fin (n + 1)) × LeftProducts (a ∘ (Fin.succAbove i))) ↦ x * (a i) := by
  induction n
  · simp at hn
  · rfl

@[simp]
theorem leftProducts_two (a : Fin 2 → A) :
    LeftProducts a = {(a 0) * (a 1), (a 1) * (a 0)} := by
  rw [leftProducts_succ (by simp only [ne_eq, one_ne_zero, not_false_eq_true])]
  dsimp
  ext p
  simp only [Set.mem_range, Sigma.exists, Subtype.exists, leftProducts_one,
    Function.comp_apply, Set.mem_singleton_iff, exists_prop, exists_eq_left,
    Fin.exists_fin_two, Fin.zero_succAbove, Fin.succ_zero_eq_one, ne_eq, one_ne_zero,
    not_false_eq_true, Fin.succAbove_ne_zero_zero, Set.mem_insert_iff]
  aesop

/-- The ordered, left-normal product of the tuple `a : Fin n → A`. -/
def OrderedLeftProduct {n : ℕ} (a : Fin (n + 1) → A) : A := match n with
| 0 => a 0
| n + 1 => OrderedLeftProduct (Fin.init a) * a (Fin.last (n + 1))

@[simp]
theorem orderedLeftProduct_one (a : Fin 1 → A) :
  OrderedLeftProduct a = a 0 := rfl

theorem orderedLeftProduct_succ {n : ℕ} (a : Fin (n + 2) → A) :
  OrderedLeftProduct a = OrderedLeftProduct (Fin.init a) * a (Fin.last (n + 1)) := rfl

@[simp]
theorem orderedLeftProduct_two (a : Fin 2 → A) :
  OrderedLeftProduct a = a 0 * a 1 := rfl

@[simp]
theorem orderedLeftProducts_three (a : Fin 3 → A) :
  OrderedLeftProduct a = (a 0 * a 1) * a 2 := rfl

theorem orderedLeftProduct_mem_leftProducts {n : ℕ} (a : Fin (n + 1) → A) :
    OrderedLeftProduct a ∈ LeftProducts a := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [orderedLeftProduct_succ, leftProducts_succ (by simp)]
    dsimp
    use ⟨Fin.last (n + 1), OrderedLeftProduct (Fin.init a), ?soos⟩
    simp only [Fin.succAbove_last]
    apply hn

lemma leftProducts_exists_ordering {n : ℕ} {x : A} {a : Fin (n + 1) → A} (hx : x ∈ LeftProducts a) :
    ∃ e : Fin (n + 1) ≃ Fin (n + 1), x = OrderedLeftProduct (a ∘ e) := by
  induction n generalizing x with
  | zero =>
    simp only [orderedLeftProduct_one, Function.comp_apply]
    simp only [leftProducts_one, Set.mem_singleton_iff] at hx
    use Equiv.refl _
    simp only [Equiv.refl_apply]
    exact hx
  | succ n hn =>
    rw [leftProducts_succ (by simp)] at hx
    simp only [Set.mem_range, Sigma.exists, Subtype.exists, exists_prop] at hx
    rcases hx with ⟨i, q, hq, rfl⟩
    rcases hn hq with ⟨e, rfl⟩
    simp_rw [orderedLeftProduct_succ]
    let f : Fin (n + 2) → Fin (n + 2) := Fin.snoc (i.succAbove ∘ e) i
    let F := Equiv.ofBijective f (by
      rw [← Finite.injective_iff_bijective]
      apply Fin.snoc_injective_of_injective
      · apply Function.Injective.comp
        · exact Fin.succAbove_right_injective
        · exact Equiv.injective e
      · simp)
    use F
    simp only [Equiv.coe_ofBijective, Function.comp_apply, Fin.snoc_last, F, f]
    congr 2
    ext
    simp [Fin.init_def]

/-- The set of all `n`-ary products of elements of `a : Fin n → A`. -/
def Products {n : ℕ} : (a : Fin n → A) → Set A := match n with
| 0 => fun _ ↦ ∅
| 1 => fun a ↦ {a 0}
| n + 2 => fun a ↦ ⋃ (i : Fin (n + 2) × Fin (n + 1)), (Products <|
  Fin.cons (a i.1 * (a ∘ (Fin.succAbove i.1)) i.2) <| a ∘ (Fin.succAbove i.1) ∘ (Fin.succAbove i.2))

@[simp]
theorem products_zero (a : Fin 0 → A) : Products a = ∅ :=
  rfl

@[simp]
theorem products_one (a : Fin 1 → A) : Products a = {a 0} :=
  rfl

theorem products_succ {n : ℕ} (a : Fin (n + 2) → A) :
    Products a = ⋃ (i : Fin (n + 2) × Fin (n + 1)), (Products <|
    Fin.cons (a i.1 * (a ∘ (Fin.succAbove i.1)) i.2) <|
    a ∘ (Fin.succAbove i.1) ∘ (Fin.succAbove i.2)) :=
  rfl

@[simp]
theorem products_two (a : Fin 2 → A) :
    Products a = {a 0 * a 1, a 1 * a 0} := by
  rw [products_succ]
  aesop
