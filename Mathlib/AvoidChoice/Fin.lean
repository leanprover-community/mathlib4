/-
Copyright (c) 2025 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.FinRange
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.DepRewrite

/-!
# Let's avoid choice!

We gather results that are used to avoid the axiom of choice.

-/

@[expose] public section

namespace Constructive

namespace List

open List

theorem pairwise_lt_range' {s n} (step := 1) (pos : 0 < step := by simp) :
    List.Pairwise (· < ·) (List.range' s n step) :=
  match s, n, step, pos with
  | _, 0, _, _ => List.Pairwise.nil
  | s, n + 1, step, pos => by
    simp only [List.range'_succ, List.pairwise_cons]
    constructor
    · intro n m
      obtain ⟨a, -, rfl⟩ := List.mem_range'.1 m
      calc s < s + step := lt_add_of_pos_right _ pos
           _ ≤ s + step + step * a := Nat.le_add_right _ _
    · exact pairwise_lt_range' (s := s + step) step pos

theorem pairwise_le_range' {s n} (step := 1) :
    List.Pairwise (· ≤ ·) (List.range' s n step) :=
  match s, n, step with
  | _, 0, _ => List.Pairwise.nil
  | s, n + 1, step => by
    simp only [List.range'_succ, List.pairwise_cons]
    constructor
    · intro n m
      obtain ⟨a, -, rfl⟩ := List.mem_range'.1 m
      rw [add_assoc]
      exact Nat.le_add_right s (step + step * a)
    · exact pairwise_le_range' (s := s + step) step

theorem nodup_range' {s n : Nat} (step := 1) (h : 0 < step := by simp) :
    List.Nodup (List.range' s n step) :=
  (pairwise_lt_range' step h).imp Nat.ne_of_lt

theorem nodup_range {n : Nat} : List.Nodup (List.range n) := by
  simp +decide only [List.range_eq_range', nodup_range']

theorem nodup_finRange (n) : (List.finRange n).Nodup := by
  rw [List.finRange_eq_pmap_range]
  exact (List.Pairwise.pmap nodup_range _) fun _ _ _ _ => @Fin.ne_of_val_ne _ ⟨_, _⟩ ⟨_, _⟩

instance Fin.fintype (n : ℕ) : Fintype (Fin n) :=
  ⟨⟨List.finRange n, nodup_finRange n⟩, List.mem_finRange⟩

end List
section BigOperators

namespace Fin

open Finset

variable {n : ℕ} {M : Type*} [CommMonoid M] {A : Type*} [AddCommMonoid A]

theorem univ_def (n : ℕ) :
  (Finset.univ : Finset (Fin n)) = ⟨List.finRange n, List.nodup_finRange n⟩ := rfl

@[simp] theorem univ_val_map {α : Type*} {n : ℕ} (f : Fin n → α) :
    Finset.univ.val.map f = List.ofFn f := by
  simp [List.ofFn_eq_map, univ_def]

@[to_additive]
theorem prod_ofFn (f : Fin n → M) : (List.ofFn f).prod = ∏ i, f i := by
  simp only [prod_eq_multiset_prod, Fin.univ_val_map, Multiset.prod_coe]

@[to_additive]
theorem prod_univ_def (f : Fin n → M) : ∏ i, f i = ((List.finRange n).map f).prod := by
  rw [← List.ofFn_eq_map, prod_ofFn]

attribute [to_additive existing] Fin.prod
set_option linter.existingAttributeWarning false in
attribute [to_additive existing] Fin.prod_eq_prod_map_finRange
attribute [to_additive existing] Fin.prod_succ

@[to_additive]
theorem Fintype_prod_eq_prod (f : Fin n → M) : ∏ i, f i = Fin.prod f := by
  rw [Fin.prod_eq_prod_map_finRange, ← Fin.prod_univ_def]

@[to_additive]
theorem prod_univ_succ (f : Fin (n + 1) → M) : ∏ i, f i = f 0 * ∏ i : Fin n, f i.succ := by
  rw [Fintype_prod_eq_prod, Fintype_prod_eq_prod, Fin.prod_succ]

@[to_additive (attr := simp)]
theorem prod_univ_zero (f : Fin 0 → M) : ∏ i : Fin 0, f i = 1 := rfl

@[to_additive (attr := simp) sum_univ_one]
theorem prod_univ_one (f : Fin 1 → M) : ∏ i : Fin 1, f i = f 0 := by
  rw [prod_univ_succ]
  exact mul_one _

@[to_additive (attr := simp)]
theorem prod_univ_two (f : Fin 2 → M) : ∏ i : Fin 2, f i = f 0 * f 1 := by
  rw [prod_univ_succ, prod_univ_one]
  rfl

@[to_additive (attr := simp)]
theorem prod_cons (f : Fin n → M) (m : M) :
    (∏ i : Fin n.succ, (Fin.cons m f : Fin n.succ → M) i) = m * ∏ i : Fin n, f i := by
  rw [prod_univ_succ]
  simp

@[to_additive]
theorem prod_cons_one (f : Fin n → M) :
    (∏ i : Fin n.succ, (Fin.cons 1 f : Fin n.succ → M) i) = ∏ i : Fin n, f i := by
  simp

@[to_additive]
theorem prod_univ_succAbove_last (f : Fin (n + 1) → M) :
    ∏ i, f i = f (Fin.last n) * ∏ i : Fin n, f (((Fin.last n)).succAbove i) := by
  simp only [Fin.succAbove_last, Fintype_prod_eq_prod, Fin.prod_eq_prod_map_finRange,
    List.finRange_succ_last, List.map_append, List.map_map, List.map_cons, List.map_nil,
    List.prod_append, List.prod_cons, List.prod_nil, mul_one, mul_comm]
  rfl

@[to_additive (attr := simp)]
theorem prod_snoc (f : Fin n → M) (m : M) :
    (∏ i : Fin n.succ, (Fin.snoc f m : Fin n.succ → M) i) = m * ∏ i : Fin n, f i := by
  rw [Fin.prod_univ_succAbove_last]
  simp

@[to_additive]
theorem prod_snoc_one (f : Fin n → M) :
    (∏ i : Fin n.succ, (Fin.snoc f 1 : Fin n.succ → M) i) = ∏ i : Fin n, f i := by
  simp

@[to_additive]
theorem prod_natAdd_zero : ∀ a (f : Fin (0 + a) → M), ∏ i, f i = ∏ i, f (Fin.natAdd 0 i)
| 0 => by simp [-univ_eq_empty]
| (a + 1) => fun f ↦ by
  rw! (castMode := .all) [← add_assoc, prod_univ_succ, prod_univ_succ, prod_natAdd_zero]
  rfl

@[to_additive]
theorem prod_univ_add : ∀ a b (f : Fin (a + b) → M), (∏ i : Fin (a + b), f i) =
    (∏ i : Fin a, f (Fin.castAdd b i)) * ∏ i : Fin b, f (Fin.natAdd a i)
| 0, b => fun f ↦ by simp [-univ_eq_empty, prod_natAdd_zero]
| a, 0 => fun f ↦ by simp [-univ_eq_empty]
| a + 1, b + 1 => fun f ↦ by
  rw! (castMode := .all) [← add_assoc, prod_univ_succAbove_last (n := a + 1 + b),
    prod_univ_succAbove_last (n := b), ← mul_assoc, mul_comm (∏ i, f (Fin.castAdd (b + 1) i)),
    mul_assoc]
  congr 1
  rw [prod_univ_add (a + 1)]
  congr 1
  · simp; rfl
  · simp

@[to_additive]
theorem prod_trunc {a b : ℕ} (f : Fin (a + b) → M) (hf : ∀ j : Fin b, f (Fin.natAdd a j) = 1) :
    (∏ i : Fin (a + b), f i) = ∏ i : Fin a, f (Fin.castAdd b i) := by
  rw [prod_univ_add, Fintype.prod_eq_one _ hf, mul_one]

@[to_additive]
theorem prod_castLe_of_eq_one {a b : ℕ} (h : a ≤ b) (f : Fin b → M)
    (hf : ∀ i, a ≤ i.1 → f i = 1) : ∏ i, f i = ∏ i, f (Fin.castLE h i) := by
  rcases Nat.exists_eq_add_of_le h with ⟨k, rfl⟩
  rw [prod_univ_add]
  convert mul_one _
  exact Finset.prod_eq_one (fun i _ ↦ hf _ (Nat.le_add_right ..))

end Fin

end BigOperators

end Constructive
