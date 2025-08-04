/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Module.OrderedSMul
import Mathlib.Analysis.RCLike.Basic

open scoped ComplexOrder Pointwise

namespace StarOrderedRing

section RCLike

variable {𝕜 R : Type*} [RCLike 𝕜] [NonUnitalRing R] [PartialOrder R]
    [StarRing R] [StarOrderedRing R] [Module 𝕜 R] [StarModule 𝕜 R]
    [IsScalarTower 𝕜 R R] [SMulCommClass 𝕜 R R]

open AddSubmonoid in
lemma smul_nonneg (c : 𝕜) (a : R) (hc : 0 ≤ c) (ha : 0 ≤ a) : 0 ≤ c • a := by
  rw [nonneg_iff] at ha
  induction ha using closure_induction with
  | mem x hx =>
      rw [RCLike.nonneg_iff_exists_ofReal] at hc
      obtain ⟨rc, hrc₁, hrc₂⟩ := hc
      rw [Set.mem_range] at hx
      obtain ⟨z, hz⟩ := hx
      rw [← hz, ← hrc₂]
      let y := (Real.sqrt rc : 𝕜) • z
      have : (Real.sqrt rc : 𝕜) * Real.sqrt rc = rc := by exact_mod_cast Real.mul_self_sqrt hrc₁
      have hmain : (rc : 𝕜) • (star z * z) = star y * y := by
        simp [y, smul_mul_smul, this]
      rw [hmain]
      exact star_mul_self_nonneg y
  | one => simp
  | mul x y hx hy hx' hy' => simp [Left.add_nonneg hx' hy']

end RCLike

end StarOrderedRing
