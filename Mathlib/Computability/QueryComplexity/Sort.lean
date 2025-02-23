/-
Copyright (c) 2025 Tomaz Mascarenhas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving, Tomaz Mascarenhas
-/
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Computability.QueryComplexity.Defs
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.Interval.Finset.Fin

/-!
# Sorting has `O(n log n)` query complexity

We prove that merge sort is a sorting algorithm with `O(n log n)` query complexity.

## Main Definition
* Comp.mergeSort : List α → SComp α (List α)

## Main Results
* Comp.cost_mergeSort_le :
  ∀ (o : SOracle α) (s : List α) :
    (mergeSort s).cost o ≤ 3 * s.length * Nat.ceil_log2 s.length
-/

open Classical
open Set
noncomputable section

namespace QueryComplexity

namespace Comp

/-!
### The definition of a sorting algorithm
-/

variable {α β : Type}

/-- An oracle that answers queries over pairs of values. Used in the definition of `mergeSort` -/
def SOracle (α : Type) := α × α → Bool

/-- Sort computations are w.r.t. a `≤` comparison oracle -/
abbrev SComp (α β : Type) := Comp (α × α) (fun _ => Bool) β

/-- When one list is another, sorted -/
structure Sorted (o : SOracle α) (s t : List α) : Prop where
  perm : s.Perm t
  sorted : t.Sorted fun x y ↦ (o (x, y))

/-- Valid sorting oracles are deterministic, reflexive, and transitive -/
structure SOracle.Valid (o : SOracle α) : Prop where
  refl : ∀ x, (o (x, x))
  anti : ∀ x y, (o (x, y)) → (o (y, x)) → x = y
  total : ∀ x y, (o (x, y)) ∨ (o (y, x))
  trans : ∀ x y z, (o (x, y)) → (o (y, z)) → (o (x, z))

/-- A sorting algorithm reorders a set to be ordered w.r.t. the oracle -/
def Sorts (f : List α → SComp α (List α)) : Prop :=
  ∀ {o : SOracle α} {s t : List α}, o.Valid → ((f s).value o) = t → Sorted o s t

/-!
### Oracle and permutation machinery
-/

variable [Fintype α]

/-- Turn a permutation of `Fin.list n` into a valid oracle -/
def oracle (π : α ≃ Fin (Fintype.card α)) : SOracle α :=
  fun x ↦ (π x.1 ≤ π x.2)

/-- The set of valid oracles -/
def oracles (α : Type) [Fintype α] : Finset (SOracle α) :=
  (Finset.univ : Finset (α ≃ Fin (Fintype.card α))).image oracle

/-- `oracle π` is valid -/
lemma valid_oracle (π : α ≃ Fin (Fintype.card α)) : (oracle π).Valid where
  refl x := by simp [oracle]
  anti x y := by
    simp only [oracle, decide_eq_true_eq]
    intro u v
    rw [← π.injective.eq_iff]
    exact Fin.le_antisymm u v
  total x y := by
    simp only [oracle, decide_eq_true_eq, LinearOrder.le_total]
  trans x y z := by simp [oracle]; apply le_trans

/-- The inverse of `oracle`. The `x ≠ y` bit is superfluous if `o.Valid`, but lets us define
it without the validity assumption. -/
def unoracle (o : SOracle α) : α → Fin (Fintype.card α) :=
  fun x ↦ ⟨(Finset.univ.filter fun y ↦ x ≠ y ∧ (o (x,y)) = false).card, by
    simp only [Finset.card_lt_iff_ne_univ, ← Finset.compl_eq_empty_iff, ne_eq,
      ← Finset.nonempty_iff_ne_empty, Finset.compl_filter, Bool.not_eq_false,
      Finset.filter_nonempty_iff, Finset.mem_univ, true_and]
    use x
    simp only [not_true_eq_false, false_and, not_false_eq_true]⟩

/-- `unoracle ∘ oracle = id` -/
lemma unoracle_oracle (π : α ≃ Fin (Fintype.card α)) : unoracle (oracle π) = π := by
  ext x
  simp only [unoracle, oracle, decide_eq_false_iff_not, not_le]
  have s : ∀ x y : α, x ≠ y ∧ π y < π x ↔ π y < π x := by
    intro x y
    constructor
    · intro h; exact h.2
    · intro h; simp only [h, and_true]
      contrapose h; simp only [not_not] at h
      simp only [h, lt_self_iff_false, not_false_eq_true]
  simp only [← Finset.card_map π.toEmbedding, Finset.map_filter, Function.comp,
    Equiv.apply_symm_apply, Finset.map_univ_equiv, s]
  rw [← Fin.card_Iio]
  apply congr_arg
  ext k
  simp

/-- `oracle` is injective -/
lemma oracle_inj (α : Type) [Fintype α] : (oracle (α := α)).Injective := by
  intro e0 e1 e
  have h : unoracle (oracle e0) = unoracle (oracle e1) := by simp only [e]
  simpa only [unoracle_oracle, DFunLike.coe_fn_eq] using h

/-- There are `n!` valid oracles -/
@[simp]
lemma card_oracles (α : Type) [Fintype α] :
    (oracles α).card = (Fintype.card α).factorial := by
  simp only [oracles, Finset.card_image_of_injective _ (oracle_inj _), Finset.card_univ]
  exact Fintype.card_equiv (Fintype.equivFin α)

/-- `oracles` is nonempty -/
lemma oracles_nonempty (α : Type) [Fintype α] : (oracles α).Nonempty := by
  simp only [← Finset.card_ne_zero, card_oracles]
  apply Nat.factorial_ne_zero

/-!
### Merge sort is a sorting algorithm with `O(n log n)` query complexity

We define our `merge` to match `List.mergeSort`, so that we reuse the existing correctness proof.
-/

open List.MergeSort.Internal

/-- Redefinition of `List.merge` using the `Comp` abstraction -/
def merge (xs ys : List α) : SComp α (List α) := do
  match xs, ys with
  | [], ys => return ys
  | xs, [] => return xs
  | x :: xs, y :: ys =>
    if ← query (x,y) then
      return x :: (← merge xs (y :: ys))
    else
      return y :: (← merge (x :: xs) ys)

/-- Redefinition of `List.mergeSort` using the `Comp` abstraction -/
def mergeSort : List α → SComp α (List α)
  | [] => pure []
  | [a] => pure [a]
  | a :: b :: l => do
    let s := splitInTwo ⟨a :: b :: l, rfl⟩
    merge (← mergeSort s.1) (← mergeSort s.2)
  termination_by s => s.length

omit [Fintype α] in
/-- `merge` is `List.merge` -/
lemma merge_eq (o : SOracle α) : (s t : List α) →
    (merge s t).value o = (List.merge s t (fun x y ↦ (o (x,y))))
  | [], _ => by simp [merge, Idvalue, List.merge]
  | (_ :: _), [] => by simp only [merge, value_pure, List.merge]
  | (a :: l), (b :: r) => by
    simp only [merge, value_bind, value_allow_all, value_query, List.merge]
    cases o (a, b)
    · simp only [Bool.false_eq_true, ↓reduceIte, bind_pure_comp, value_map, List.cons.injEq,
        true_and]
      apply merge_eq o _ _
    · simp only [↓reduceIte, bind_pure_comp, value_map, List.cons.injEq, true_and]
      apply merge_eq o _ _

omit [Fintype α] in
/-- `mergeSort` is `List.mergeSort` -/
lemma mergeSort_eq (o : SOracle α) : (s : List α) →
    (mergeSort s).value o = (List.mergeSort s (fun x y ↦ (o (x,y))))
  | [] => by simp only [mergeSort, value_pure, List.mergeSort_nil]
  | [a] => by simp only [mergeSort, value_pure, List.mergeSort_singleton]
  | a :: b :: l => by
    simp only [mergeSort, List.length_cons, splitInTwo_fst, splitInTwo_snd,
      value_bind, List.mergeSort]
    set t := splitInTwo ⟨a :: b :: l, rfl⟩
    simp only [mergeSort_eq o ((List.take ((l.length + 1 + 1 + 1) / 2) (a :: b :: l))),
      mergeSort_eq o ((List.drop ((l.length + 1 + 1 + 1) / 2) (a :: b :: l))),
      pure_bind, merge_eq o]
  termination_by s => s.length

omit [Fintype α]
/-- `mergeSort` sorts -/
lemma sorts_mergeSort : Sorts (mergeSort (α := α)) := by
  intro o s t v pt
  simp only [mergeSort_eq _ ,  ne_eq, ite_eq_right_iff,
    one_ne_zero, imp_false, Decidable.not_not] at pt
  rw [<- pt]
  exact {
    perm := List.Perm.symm (List.mergeSort_perm _ _)
    sorted := by
      apply List.sorted_mergeSort
      · intro _ _ _; apply v.trans
      · intro _ _; simp only [Bool.or_eq_true]; apply v.total
  }

/-- `merge` is `O(n)` -/
lemma cost_merge_le (o : SOracle α) : (s t : List α) →
    (merge s t).cost o ≤ s.length + t.length
  | [], _ => by simp [merge, List.merge]
  | (_ :: _), [] => by simp [merge, List.merge]
  | (a :: l), (b :: r) => by
    simp only [cost', merge, cost_bind, cost_allow_all, cost_query, value_allow_all, value_query,
      List.length_cons, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, min_add_add_right,
      add_comm 1, add_le_add_iff_right, ← add_assoc]
    cases o (a, b)
    · simp only [Bool.false_eq_true, ↓reduceIte, bind_pure_comp, cost_map]
      apply cost_merge_le o _ _
    · simp only [↓reduceIte, bind_pure_comp, cost_map]
      have ih := cost_merge_le o l (b :: r)
      simp only [List.length_cons] at ih
      omega

/-- `merge` preserves `length` -/
lemma length_merge (o : SOracle α) : (s t x : List α) →
    (px : ((merge s t).value o) = x) → x.length = s.length + t.length
  | [], t, x, px => by
    simp only [merge] at px
    rw [<- px]
    simp only [value_pure, List.length_nil, zero_add]
  | (a :: l), [], x, px => by
    simp only [merge] at px
    rw [<- px]
    simp only [value_pure, List.length_cons, List.length_nil, add_zero]
  | (a :: s), (b :: t), x, px => by
    simp only [merge, value_bind, value_allow_all, value_query] at px
    by_cases ho : (o (a, b))
    · rw [ho] at px; simp at px; rw [<- px]; simp;
      have ih := length_merge o s (b :: t) ((merge s (b :: t)).value o) rfl
      simp only [List.length_cons] at ih
      omega
    · simp at ho; rw [ho] at px; simp at px; rw [<- px]; simp;
      have ih := length_merge o (a :: s) t ((merge (a :: s) t).value o) rfl
      simp only [List.length_cons] at ih
      omega

/-- `mergeSort` preserves `length` -/
lemma length_mergeSort (o : SOracle α) : (s x : List α) →
    (px : ((mergeSort s).value o) = x) →
    x.length = s.length := by
  intros s x p
  rw [mergeSort_eq o s] at p
  rw [<- p, List.length_mergeSort]

/-- `log2 n`, rounding up -/
def Nat.ceil_log2 (n : ℕ) : ℕ := Nat.log2 (2 * n - 1)

/-- `Nat.ceil_log2` is an upper bound -/
lemma Nat.le_ceil_log2 (n : ℕ) : n ≤ 2 ^ ceil_log2 n := by
  simp only [Nat.ceil_log2]
  by_cases n0 : n = 0
  · simp [n0]
  · have h := Nat.lt_log2_self (n := 2 * n - 1)
    omega

/-- `Nat.ceil_log2 n` is zero for `n ≤ 1` -/
@[simp]
lemma Nat.ceil_log2_eq_zero_iff (n : ℕ) : ceil_log2 n = 0 ↔ n ≤ 1 := by
  by_cases n0 : n = 0
  · simp only [ceil_log2, n0, mul_zero, _root_.zero_le, tsub_eq_zero_of_le, Nat.log2_zero]
  by_cases n1 : n = 1
  · simp only [ceil_log2, n1, mul_one, Nat.reduceSub, le_refl, iff_true]
    unfold Nat.log2
    decide
  have nle : ¬n ≤ 1 := by omega
  simp only [nle, iff_false, ne_eq]
  have h := Nat.le_ceil_log2 n
  contrapose h
  simp only [ne_eq, not_not] at h
  simp only [h, pow_zero, not_le]
  omega

/-- `Nat.log2` is monotonic -/
lemma Nat.log2_le_log2 {a b : ℕ} (ab : a ≤ b) : a.log2 ≤ b.log2 := by
  induction' b using Nat.strong_induction_on with b h generalizing a
  rw [Nat.log2]
  nth_rw 2 [Nat.log2]
  by_cases a2 : a < 2
  · by_cases a0 : a = 0
    · simp [a0]
    · have a1 : a = 1 := by omega
      simp [a1]
  · have b2 : 2 ≤ b := by omega
    simp only [not_lt.mp a2, ↓reduceIte, b2, add_le_add_iff_right]
    apply h
    all_goals omega

/-- `Nat.log2` is monotonic -/
lemma Nat.ceil_log2_le_ceil_log2 {a b : ℕ} (ab : a ≤ b) : ceil_log2 a ≤ ceil_log2 b := by
  apply Nat.log2_le_log2; omega

/-- `n/2` has one smaller `ceil_log2` -/
lemma Nat.ceil_log2_div2 (n : ℕ) (n2 : 2 ≤ n) : ceil_log2 (n / 2) ≤ ceil_log2 n - 1 := by
  simp only [ceil_log2]
  have e : (2 * n - 1).log2 = ((2 * n - 1) / 2).log2 + 1 := by
    rw [Nat.log2]; simp only [(by omega : 2 * n - 1 ≥ 2), if_true]
  rw [e, Nat.add_sub_cancel]
  apply Nat.log2_le_log2
  omega

/-- The cost of `mergeSort`. The factor of 3 is unnecessarily, but makes the proof easier. -/
def mergeSort_bound (n : ℕ) : ℕ := 3 * n * Nat.ceil_log2 n

/-- The inductive step inequality in `cost_mergeSort_le` -/
lemma mul_log_le (n : ℕ) (n2 : 2 ≤ n) :
    mergeSort_bound ((n+1)/2) + (mergeSort_bound (n/2) + n) ≤ mergeSort_bound n := by
  simp only [mergeSort_bound]
  have h0 := Nat.ceil_log2_div2 n n2
  generalize ha : Nat.ceil_log2 n = a at h0
  have h1 : (Nat.ceil_log2 ((n + 1) / 2)) ≤ a := by
    rw [← ha]
    apply Nat.ceil_log2_le_ceil_log2
    omega
  have a1 : 1 ≤ a := by
    contrapose n2
    simp only [not_le, Nat.lt_one_iff] at n2
    simp only [n2, Nat.ceil_log2_eq_zero_iff] at ha
    omega
  trans 3 * ((n + 1) / 2) * a + (3 * (n / 2) * (a - 1) + n)
  · gcongr
  generalize hu : n / 2 = u
  generalize hv : (n + 1) / 2 = v
  have uv : u + v = n := by omega
  simp only [Nat.mul_sub_left_distrib, mul_one]
  trans 3 * v * a + 3 * u * a + (n - 3 * u)
  · simp only [add_assoc, add_le_add_iff_left]
    have un : n ≤ 3 * u := by omega
    have uu : 3 * u ≤ 3 * u * a := Nat.le_mul_of_pos_right _ a1
    simp only [Nat.sub_eq_zero_of_le un, add_zero]
    omega
  · simp only [← Nat.add_mul, ← Nat.mul_add, add_comm _ u, uv]
    omega

/-- `mergeSort` is `O(n log n)` -/
lemma cost_mergeSort_le (o : SOracle α) (s : List α) :
    (mergeSort s).cost o ≤ mergeSort_bound s.length := by
  generalize hn : s.length = n
  induction' n using Nat.strong_induction_on with n h generalizing s
  induction' s with a s d
  · simp only [List.length_nil] at hn
    simp [mergeSort, ← hn]
  · clear d
    induction' s with b s d
    · simp only [List.length_singleton] at hn
      simp [mergeSort, ← hn]
    · simp only [List.length_cons, Nat.succ_eq_add_one] at hn
      simp only [cost', mergeSort, cost_bind, splitInTwo]
      let t := ((a :: b :: s).length + 1) / 2
      let l1 := (List.splitAt t (a :: b :: s)).1
      let l2 := (List.splitAt t (a :: b :: s)).2
      have l1_length : l1.length < n := by
        simp only [t, l1, List.length_cons, List.splitAt_eq, List.length_take, ← hn, inf_lt_right,
          not_le]
        omega
      have l2_length : l2.length < n := by
        simp only [t, l2, List.length_cons, List.splitAt_eq, List.length_drop]
        omega
      have ih :
          cost (merge ((mergeSort l1).value fun x ↦ o) ((mergeSort l2).value fun x ↦ o))
               (fun x ↦ o) () ≤ n := by
        refine le_trans (cost_merge_le _ _ _) ?_
        rw [length_mergeSort _ l1 _ rfl]
        rw [length_mergeSort _ l2 _ rfl]
        simp only [l1, l2, t, List.length_cons, List.splitAt_eq, List.length_take, Nat.cast_min,
          List.length_drop, ← Nat.cast_min, ← Nat.cast_add, Nat.cast_le]
        omega
      have h1 := h _ l1_length _ rfl
      have h2 := h _ l2_length _ rfl
      refine le_trans (add_le_add h1 (add_le_add h2 ih)) ?_
      convert mul_log_le n (by omega)
      · simp only [t, l1, List.length_cons, List.splitAt_eq, List.length_take]
        omega
      · simp only [t, l2, List.length_cons, List.splitAt_eq, List.length_drop]
        omega

end Comp

end QueryComplexity
