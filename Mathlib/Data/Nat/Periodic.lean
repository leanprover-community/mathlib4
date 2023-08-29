/-
Copyright (c) 2021 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Mathlib.Algebra.Periodic
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Interval

#align_import data.nat.periodic from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# Periodic Functions on ℕ

This file identifies a few functions on `ℕ` which are periodic, and also proves a lemma about
periodic predicates which helps determine their cardinality when filtering intervals over them.
-/


namespace Nat

open Nat Function

theorem periodic_gcd (a : ℕ) : Periodic (gcd a) a := by
  simp only [forall_const, gcd_add_self_right, eq_self_iff_true, Periodic]
  -- 🎉 no goals
#align nat.periodic_gcd Nat.periodic_gcd

theorem periodic_coprime (a : ℕ) : Periodic (coprime a) a := by
  simp only [coprime_add_self_right, forall_const, iff_self_iff, eq_iff_iff, Periodic]
  -- 🎉 no goals
#align nat.periodic_coprime Nat.periodic_coprime

theorem periodic_mod (a : ℕ) : Periodic (fun n => n % a) a := by
  simp only [forall_const, eq_self_iff_true, add_mod_right, Periodic]
  -- 🎉 no goals
#align nat.periodic_mod Nat.periodic_mod

theorem _root_.Function.Periodic.map_mod_nat {α : Type*} {f : ℕ → α} {a : ℕ} (hf : Periodic f a) :
    ∀ n, f (n % a) = f n := fun n => by
  conv_rhs => rw [← Nat.mod_add_div n a, mul_comm, ← Nat.nsmul_eq_mul, hf.nsmul]
  -- 🎉 no goals
#align function.periodic.map_mod_nat Function.Periodic.map_mod_nat

section Multiset

open Multiset

/-- An interval of length `a` filtered over a periodic predicate of period `a` has cardinality
equal to the number naturals below `a` for which `p a` is true. -/
theorem filter_multiset_Ico_card_eq_of_periodic (n a : ℕ) (p : ℕ → Prop) [DecidablePred p]
    (pp : Periodic p a) : card (filter p (Ico n (n + a))) = a.count p := by
  rw [count_eq_card_filter_range, Finset.card, Finset.filter_val, Finset.range_val, ←
    multiset_Ico_map_mod n, ← map_count_True_eq_filter_card, ← map_count_True_eq_filter_card,
    map_map]
  congr; funext n
  -- ⊢ p = p ∘ fun x => x % a
         -- ⊢ p n = (p ∘ fun x => x % a) n
  exact (Function.Periodic.map_mod_nat pp n).symm
  -- 🎉 no goals
#align nat.filter_multiset_Ico_card_eq_of_periodic Nat.filter_multiset_Ico_card_eq_of_periodic

end Multiset

section Finset

open Finset

/-- An interval of length `a` filtered over a periodic predicate of period `a` has cardinality
equal to the number naturals below `a` for which `p a` is true. -/
theorem filter_Ico_card_eq_of_periodic (n a : ℕ) (p : ℕ → Prop) [DecidablePred p]
    (pp : Periodic p a) : ((Ico n (n + a)).filter p).card = a.count p :=
  filter_multiset_Ico_card_eq_of_periodic n a p pp
#align nat.filter_Ico_card_eq_of_periodic Nat.filter_Ico_card_eq_of_periodic

end Finset

end Nat
