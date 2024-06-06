/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Data.Finsupp.Defs

#align_import data.list.to_finsupp from "leanprover-community/mathlib"@"06a655b5fcfbda03502f9158bbf6c0f1400886f9"

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
  support := (Finset.range l.length).filter fun i => getD l i 0 ≠ 0
  mem_support_toFun n := by
    simp only [Ne, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
    contrapose!
    exact getD_eq_default _ _
#align list.to_finsupp List.toFinsupp

@[norm_cast]
theorem coe_toFinsupp : (l.toFinsupp : ℕ → M) = (l.getD · 0) :=
  rfl
#align list.coe_to_finsupp List.coe_toFinsupp

@[simp, norm_cast]
theorem toFinsupp_apply (i : ℕ) : (l.toFinsupp : ℕ → M) i = l.getD i 0 :=
  rfl
#align list.to_finsupp_apply List.toFinsupp_apply

theorem toFinsupp_support :
    l.toFinsupp.support = (Finset.range l.length).filter (getD l · 0 ≠ 0) :=
  rfl
#align list.to_finsupp_support List.toFinsupp_support

theorem toFinsupp_apply_lt (hn : n < l.length) : l.toFinsupp n = l.get ⟨n, hn⟩ :=
  getD_eq_get _ _ _

theorem toFinsupp_apply_fin (n : Fin l.length) : l.toFinsupp n = l.get n :=
  getD_eq_get _ _ _

set_option linter.deprecated false in
@[deprecated] -- 2023-04-10
theorem toFinsupp_apply_lt' (hn : n < l.length) : l.toFinsupp n = l.nthLe n hn :=
  getD_eq_get _ _ _
#align list.to_finsupp_apply_lt List.toFinsupp_apply_lt'

theorem toFinsupp_apply_le (hn : l.length ≤ n) : l.toFinsupp n = 0 :=
  getD_eq_default _ _ hn
#align list.to_finsupp_apply_le List.toFinsupp_apply_le

@[simp]
theorem toFinsupp_nil [DecidablePred fun i => getD ([] : List M) i 0 ≠ 0] :
    toFinsupp ([] : List M) = 0 := by
  ext
  simp
#align list.to_finsupp_nil List.toFinsupp_nil

theorem toFinsupp_singleton (x : M) [DecidablePred (getD [x] · 0 ≠ 0)] :
    toFinsupp [x] = Finsupp.single 0 x := by
  ext ⟨_ | i⟩ <;> simp [Finsupp.single_apply, (Nat.zero_lt_succ _).ne]
#align list.to_finsupp_singleton List.toFinsupp_singleton

@[simp]
theorem toFinsupp_cons_apply_zero (x : M) (xs : List M)
    [DecidablePred (getD (x::xs) · 0 ≠ 0)] : (x::xs).toFinsupp 0 = x :=
  rfl
#align list.to_finsupp_cons_apply_zero List.toFinsupp_cons_apply_zero

@[simp]
theorem toFinsupp_cons_apply_succ (x : M) (xs : List M) (n : ℕ)
    [DecidablePred (getD (x::xs) · 0 ≠ 0)] [DecidablePred (getD xs · 0 ≠ 0)] :
    (x::xs).toFinsupp n.succ = xs.toFinsupp n :=
  rfl
#align list.to_finsupp_cons_apply_succ List.toFinsupp_cons_apply_succ

-- Porting note (#10756): new theorem
theorem toFinsupp_append {R : Type*} [AddZeroClass R] (l₁ l₂ : List R)
    [DecidablePred (getD (l₁ ++ l₂) · 0 ≠ 0)] [DecidablePred (getD l₁ · 0 ≠ 0)]
    [DecidablePred (getD l₂ · 0 ≠ 0)] :
    toFinsupp (l₁ ++ l₂) =
      toFinsupp l₁ + (toFinsupp l₂).embDomain (addLeftEmbedding l₁.length) := by
  ext n
  simp only [toFinsupp_apply, Finsupp.add_apply]
  cases lt_or_le n l₁.length with
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
#align list.to_finsupp_cons_eq_single_add_emb_domain List.toFinsupp_cons_eq_single_add_embDomain

theorem toFinsupp_concat_eq_toFinsupp_add_single {R : Type*} [AddZeroClass R] (x : R) (xs : List R)
    [DecidablePred fun i => getD (xs ++ [x]) i 0 ≠ 0] [DecidablePred fun i => getD xs i 0 ≠ 0] :
    toFinsupp (xs ++ [x]) = toFinsupp xs + Finsupp.single xs.length x := by
  classical rw [toFinsupp_append, toFinsupp_singleton, Finsupp.embDomain_single,
    addLeftEmbedding_apply, add_zero]
#align list.to_finsupp_concat_eq_to_finsupp_add_single List.toFinsupp_concat_eq_toFinsupp_add_single


theorem toFinsupp_eq_sum_map_enum_single {R : Type*} [AddMonoid R] (l : List R)
    [DecidablePred (getD l · 0 ≠ 0)] :
    toFinsupp l = (l.enum.map fun nr : ℕ × R => Finsupp.single nr.1 nr.2).sum := by
  /- Porting note (#11215): TODO: `induction` fails to substitute `l = []` in
  `[DecidablePred (getD l · 0 ≠ 0)]`, so we manually do some `revert`/`intro` as a workaround -/
  revert l; intro l
  induction l using List.reverseRecOn with
  | nil => exact toFinsupp_nil
  | append_singleton x xs ih =>
    classical simp [toFinsupp_concat_eq_toFinsupp_add_single, enum_append, ih]
#align list.to_finsupp_eq_sum_map_enum_single List.toFinsupp_eq_sum_map_enum_single

end List
