/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Embedding
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.List.GetD

/-!

# Lists as finsupp

## Main definitions

- `List.toFinsupp`: Interpret a list as a finitely supported function, where the indexing type is
  `ℕ`, and the values are either the elements of the list (accessing by indexing) or `0` outside of
  the list.

## Main theorems

- `List.toFinsupp_eq_sum_map_enum_single`: A `l : List M` over `M` an `AddMonoid`, when interpreted
  as a finitely supported function, is equal to the sum of `Finsupp.single` produced by mapping over
  `List.enum l`.

## Implementation details

The functions defined here rely on a decidability predicate that each element in the list
can be decidably determined to be not equal to zero or that one can decide one is out of the
bounds of a list. For concretely defined lists that are made up of elements of decidable terms,
this holds. More work will be needed to support lists over non-dec-eq types like `ℝ`, where the
elements are beyond the dec-eq terms of casted values from `ℕ, ℤ, ℚ`.
-/

namespace List

variable {M : Type*} [Zero M] (l : List M) [DecidablePred (getD l · 0 ≠ 0)] (n : ℕ)

/-- Indexing into a `l : List M`, as a finitely-supported function,
where the support are all the indices within the length of the list
that index to a non-zero value. Indices beyond the end of the list are sent to 0.

This is a computable version of the `Finsupp.onFinset` construction.
-/
def toFinsupp : ℕ →₀ M where
  toFun i := getD l i 0
  support := {i ∈ Finset.range l.length | getD l i 0 ≠ 0}
  mem_support_toFun n := by
    simp only [Ne, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
    contrapose!
    exact getD_eq_default _ _

@[norm_cast]
theorem coe_toFinsupp : (l.toFinsupp : ℕ → M) = (l.getD · 0) :=
  rfl

@[simp, norm_cast]
theorem toFinsupp_apply (i : ℕ) : (l.toFinsupp : ℕ → M) i = l.getD i 0 :=
  rfl

theorem toFinsupp_support :
    l.toFinsupp.support = {i ∈ Finset.range l.length | getD l i 0 ≠ 0} :=
  rfl

theorem toFinsupp_apply_lt (hn : n < l.length) : l.toFinsupp n = l[n] :=
  getD_eq_getElem _ _ hn

theorem toFinsupp_apply_fin (n : Fin l.length) : l.toFinsupp n = l[n] :=
  getD_eq_getElem _ _ n.isLt

theorem toFinsupp_apply_le (hn : l.length ≤ n) : l.toFinsupp n = 0 :=
  getD_eq_default _ _ hn

@[simp]
theorem toFinsupp_nil [DecidablePred fun i => getD ([] : List M) i 0 ≠ 0] :
    toFinsupp ([] : List M) = 0 := by
  ext
  simp

theorem toFinsupp_singleton (x : M) [DecidablePred (getD [x] · 0 ≠ 0)] :
    toFinsupp [x] = Finsupp.single 0 x := by
  ext ⟨_ | i⟩ <;> simp [Finsupp.single_apply, (Nat.zero_lt_succ _).ne]

theorem toFinsupp_append {R : Type*} [AddZeroClass R] (l₁ l₂ : List R)
    [DecidablePred (getD (l₁ ++ l₂) · 0 ≠ 0)] [DecidablePred (getD l₁ · 0 ≠ 0)]
    [DecidablePred (getD l₂ · 0 ≠ 0)] :
    toFinsupp (l₁ ++ l₂) =
      toFinsupp l₁ + (toFinsupp l₂).embDomain (addLeftEmbedding l₁.length) := by
  ext n
  simp only [toFinsupp_apply, Finsupp.add_apply]
  cases lt_or_ge n l₁.length with
  | inl h =>
    rw [getD_append _ _ _ _ h, Finsupp.embDomain_notin_range, add_zero]
    rintro ⟨k, rfl : length l₁ + k = n⟩
    omega
  | inr h =>
    rcases Nat.exists_eq_add_of_le h with ⟨k, rfl⟩
    rw [getD_append_right _ _ _ _ h, Nat.add_sub_cancel_left, getD_eq_default _ _ h, zero_add]
    exact Eq.symm (Finsupp.embDomain_apply _ _ _)

theorem toFinsupp_cons_eq_single_add_embDomain {R : Type*} [AddZeroClass R] (x : R) (xs : List R)
    [DecidablePred (getD (x::xs) · 0 ≠ 0)] [DecidablePred (getD xs · 0 ≠ 0)] :
    toFinsupp (x::xs) =
      Finsupp.single 0 x + (toFinsupp xs).embDomain ⟨Nat.succ, Nat.succ_injective⟩ := by
  classical
    convert toFinsupp_append [x] xs using 3
    · exact (toFinsupp_singleton x).symm
    · ext n
      exact add_comm n 1

theorem toFinsupp_concat_eq_toFinsupp_add_single {R : Type*} [AddZeroClass R] (x : R) (xs : List R)
    [DecidablePred fun i => getD (xs ++ [x]) i 0 ≠ 0] [DecidablePred fun i => getD xs i 0 ≠ 0] :
    toFinsupp (xs ++ [x]) = toFinsupp xs + Finsupp.single xs.length x := by
  classical rw [toFinsupp_append, toFinsupp_singleton, Finsupp.embDomain_single,
    addLeftEmbedding_apply, add_zero]


theorem toFinsupp_eq_sum_mapIdx_single {R : Type*} [AddMonoid R] (l : List R)
    [DecidablePred (getD l · 0 ≠ 0)] :
    toFinsupp l = (l.mapIdx fun n r => Finsupp.single n r).sum := by
  /- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: `induction` fails to substitute `l = []` in
  `[DecidablePred (getD l · 0 ≠ 0)]`, so we manually do some `revert`/`intro` as a workaround -/
  revert l; intro l
  induction l using List.reverseRecOn with
  | nil => exact toFinsupp_nil
  | append_singleton x xs ih =>
    classical simp [toFinsupp_concat_eq_toFinsupp_add_single, ih]

@[deprecated (since := "2025-01-28")]
alias toFinsupp_eq_sum_map_enum_single := toFinsupp_eq_sum_mapIdx_single

end List
