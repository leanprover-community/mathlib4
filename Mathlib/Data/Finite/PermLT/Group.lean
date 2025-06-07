/-
Copyright (c) 2024-2025 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/

import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.Finite.PermLT.Defs

/-!
# Group instance for `PermLT`
-/

namespace PermLT

variable {n m i j : ℕ} {a b : PermLT n}

instance : Group (PermLT n) := Group.ofLeftAxioms
  (fun _ _ _ => ext <| fun i hi => by simp_rw [getElem_mul])
  (fun _ => ext <| fun i hi => by simp_rw [getElem_mul, getElem_one])
  (fun _ => ext <| fun i hi => by simp_rw [getElem_mul, getElem_one, getElem_inv_getElem])

section Group

theorem getElem_pow_eq_self_of_getElem_eq_self {k : ℕ} (hi : i < n := by get_elem_tactic)
  (hia : a[i] = i) : (a^k)[i] = i := by
  induction k with | zero => _ | succ k IH => _
  · simp_rw [pow_zero, getElem_one]
  · simp_rw [pow_succ, getElem_mul, hia, IH]

theorem getElem_inv_eq_self_of_getElem_eq_self (hi : i < n := by get_elem_tactic) :
  a[i] = i → (a⁻¹)[i] = i := by simp_rw [getElem_inv_eq_iff _ hi, eq_comm, imp_self]

theorem getElem_inv_ne_self_of_getElem_ne_self (hi : i < n := by get_elem_tactic):
  a[i] ≠ i → (a⁻¹)[i] ≠ i := by simp_rw [ne_eq, getElem_inv_eq_iff _ hi, eq_comm, imp_self]

theorem getElem_zpow_eq_self_of_getElem_eq_self {k : ℤ} (hi : i < n := by get_elem_tactic)
    (hia : a[i] = i) : (a^k)[i] = i := by
  cases k
  · exact getElem_pow_eq_self_of_getElem_eq_self _ hia
  · simp_rw [zpow_negSucc]
    exact (getElem_inv_eq_self_of_getElem_eq_self _ (getElem_pow_eq_self_of_getElem_eq_self _ hia))

@[simp]
theorem getElem_pow_add {i x y : ℕ} (hi : i < n) :
    (a^x)[(a^y)[i]] = (a^(x + y))[i] := by simp_rw [pow_add, getElem_mul]

@[simp]
theorem getElem_zpow_add {i : ℕ} {x y : ℤ} (hi : i < n) :
    (a^x)[(a^y)[i]] = (a^(x + y))[i] := by simp_rw [zpow_add, getElem_mul]

end Group

end PermLT
