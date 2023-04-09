/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky

! This file was ported from Lean 3 source module data.list.to_finsupp
! leanprover-community/mathlib commit 06a655b5fcfbda03502f9158bbf6c0f1400886f9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finsupp.Basic

/-!

# Lists as finsupp

# Main definitions

- `list.to_finsupp`: Interpret a list as a finitely supported function, where the indexing type
is `ℕ`, and the values are either the elements of the list (accessing by indexing) or `0` outside
of the list.

# Main theorems

- `list.to_finsupp_eq_sum_map_enum_single`: A `l : list M` over `M` an `add_monoid`,
when interpreted as a finitely supported function, is equal to the sum of `finsupp.single`
produced by mapping over `list.enum l`.

## Implementation details

The functions defined here rely on a decidability predicate that each element in the list
can be decidably determined to be not equal to zero or that one can decide one is out of the
bounds of a list. For concretely defined lists that are made up of elements of decidable terms,
this holds. More work will be needed to support lists over non-dec-eq types like `ℝ`, where the
elements are beyond the dec-eq terms of casted values from `ℕ, ℤ, ℚ`.

-/


namespace List

variable {M : Type _} [Zero M] (l : List M) [DecidablePred fun i => getD l i 0 ≠ 0] (n : ℕ)

/-- Indexing into a `l : list M`, as a finitely-supported function,
where the support are all the indices within the length of the list
that index to a non-zero value. Indices beyond the end of the list are sent to 0.

This is a computable version of the `finsupp.on_finset` construction.
-/
def toFinsupp : ℕ →₀ M where
  toFun i := getD l i 0
  support := (Finset.range l.length).filterₓ fun i => getD l i 0 ≠ 0
  mem_support_toFun n :=
    by
    simp only [Ne.def, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
    contrapose!
    exact nthd_eq_default _ _
#align list.to_finsupp List.toFinsupp

@[norm_cast]
theorem coe_toFinsupp : (l.toFinsupp : ℕ → M) = fun i => l.getD i 0 :=
  rfl
#align list.coe_to_finsupp List.coe_toFinsupp

@[simp, norm_cast]
theorem toFinsupp_apply (i : ℕ) : (l.toFinsupp : ℕ → M) i = l.getD i 0 :=
  rfl
#align list.to_finsupp_apply List.toFinsupp_apply

theorem toFinsupp_support :
    l.toFinsupp.support = (Finset.range l.length).filterₓ fun i => getD l i 0 ≠ 0 :=
  rfl
#align list.to_finsupp_support List.toFinsupp_support

theorem toFinsupp_apply_lt (hn : n < l.length) : l.toFinsupp n = l.nthLe n hn :=
  getD_eq_nthLe _ _ _
#align list.to_finsupp_apply_lt List.toFinsupp_apply_lt

theorem toFinsupp_apply_le (hn : l.length ≤ n) : l.toFinsupp n = 0 :=
  getD_eq_default _ _ hn
#align list.to_finsupp_apply_le List.toFinsupp_apply_le

@[simp]
theorem toFinsupp_nil [DecidablePred fun i => getD ([] : List M) i 0 ≠ 0] :
    toFinsupp ([] : List M) = 0 := by
  ext
  simp
#align list.to_finsupp_nil List.toFinsupp_nil

theorem toFinsupp_singleton (x : M) [DecidablePred fun i => getD [x] i 0 ≠ 0] :
    toFinsupp [x] = Finsupp.single 0 x := by
  ext ⟨_ | i⟩ <;> simp [Finsupp.single_apply, (Nat.zero_lt_succ _).Ne]
#align list.to_finsupp_singleton List.toFinsupp_singleton

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem toFinsupp_cons_apply_zero (x : M) (xs : List M)
    [DecidablePred fun i => getD (x::xs) i 0 ≠ 0] : (x::xs).toFinsupp 0 = x :=
  rfl
#align list.to_finsupp_cons_apply_zero List.toFinsupp_cons_apply_zero

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem toFinsupp_cons_apply_succ (x : M) (xs : List M) (n : ℕ)
    [DecidablePred fun i => getD (x::xs) i 0 ≠ 0] [DecidablePred fun i => getD xs i 0 ≠ 0] :
    (x::xs).toFinsupp n.succ = xs.toFinsupp n :=
  rfl
#align list.to_finsupp_cons_apply_succ List.toFinsupp_cons_apply_succ

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem toFinsupp_cons_eq_single_add_embDomain {R : Type _} [AddZeroClass R] (x : R) (xs : List R)
    [DecidablePred fun i => getD (x::xs) i 0 ≠ 0] [DecidablePred fun i => getD xs i 0 ≠ 0] :
    toFinsupp (x::xs) =
      Finsupp.single 0 x + (toFinsupp xs).embDomain ⟨Nat.succ, Nat.succ_injective⟩ :=
  by
  ext (_ | i)
  · simp only [Nat.zero_eq, to_finsupp_cons_apply_zero, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_eq_same]
    rw [Finsupp.embDomain_notin_range]
    · exact (add_zero _).symm
    · simp
  · simp only [to_finsupp_cons_apply_succ, Finsupp.coe_add, Pi.add_apply]
    have hi : i.succ = (⟨Nat.succ, Nat.succ_injective⟩ : ℕ ↪ ℕ) i := rfl
    rw [finsupp.single_apply_eq_zero.mpr, zero_add, hi, Finsupp.embDomain_apply]
    simp
#align list.to_finsupp_cons_eq_single_add_emb_domain List.toFinsupp_cons_eq_single_add_embDomain

theorem toFinsupp_concat_eq_toFinsupp_add_single {R : Type _} [AddZeroClass R] (x : R) (xs : List R)
    [DecidablePred fun i => getD (xs ++ [x]) i 0 ≠ 0] [DecidablePred fun i => getD xs i 0 ≠ 0] :
    toFinsupp (xs ++ [x]) = toFinsupp xs + Finsupp.single xs.length x :=
  by
  ext i
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
  rcases lt_trichotomy xs.length i with (hi | rfl | hi)
  · rw [to_finsupp_apply_le _ _ hi.le, to_finsupp_apply_le, if_neg hi.ne, add_zero]
    simpa using Nat.succ_le_of_lt hi
  · rw [to_finsupp_apply_lt, to_finsupp_apply_le _ _ le_rfl, if_pos rfl, zero_add,
      nth_le_append_right le_rfl]
    · simp
    · simp
  · rw [to_finsupp_apply_lt _ _ hi, to_finsupp_apply_lt, if_neg hi.ne', add_zero, nth_le_append]
    simpa using Nat.lt_succ_of_lt hi
#align list.to_finsupp_concat_eq_to_finsupp_add_single List.toFinsupp_concat_eq_toFinsupp_add_single

theorem toFinsupp_eq_sum_map_enum_single {R : Type _} [AddMonoid R] (l : List R)
    [DecidablePred fun i => getD l i 0 ≠ 0] :
    toFinsupp l = (l.enum.map fun nr : ℕ × R => Finsupp.single nr.1 nr.2).Sum :=
  by
  induction' l using List.reverseRecOn with xs x IH
  · convert to_finsupp_nil
  · simp only [enum_append, map, enum_from_singleton, map_append, sum_append, sum_cons, sum_nil,
      add_zero]
    classical
      convert to_finsupp_concat_eq_to_finsupp_add_single _ _
      exact IH.symm
#align list.to_finsupp_eq_sum_map_enum_single List.toFinsupp_eq_sum_map_enum_single

end List

