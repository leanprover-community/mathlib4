/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Derivatives of `x ^ m`, `m : ℤ` within an open set

In this file we prove theorems about iterated derivatives of `x ^ m`, `m : ℤ` within an open set.

## Keywords

iterated, derivative, power, open set
-/

open scoped Nat

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {s : Set 𝕜}

theorem iteratedDerivWithin_zpow (m : ℤ) (k : ℕ) (hs : IsOpen s) :
    s.EqOn (iteratedDerivWithin k (fun y ↦ y ^ m) s)
    (fun y ↦ (∏ i ∈ Finset.range k, ((m : 𝕜) - i)) * y ^ (m - k)) := by
  apply Set.EqOn.trans (iteratedDerivWithin_of_isOpen_eq_iterate hs)
  intro t ht
  simp

theorem iteratedDerivWithin_one_div (k : ℕ) (hs : IsOpen s) :
    s.EqOn (iteratedDerivWithin k (fun y ↦ 1 / y) s)
    (fun y ↦ (-1) ^ k * (k !) * (y ^ (-1 - k : ℤ))) := by
  apply Set.EqOn.trans (iteratedDerivWithin_of_isOpen_eq_iterate hs)
  intro t ht
  simp
