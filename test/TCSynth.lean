/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison
-/
import Mathlib

/-!
# Test against slow typeclass synthesis

This file tests against regression in typeclass synthesis speed.
The tests below became fast by the fix in
https://github.com/leanprover/lean4/pull/4085
-/

section

-- Initial issue: https://github.com/leanprover-community/mathlib4/issues/12226

open Complex Filter Bornology

/--
error: failed to synthesize
  AddMonoidHomClass (AddGroupSeminorm ℂ) ℂ ℝ
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
set_option synthInstance.maxHeartbeats 3000 in
#synth AddMonoidHomClass (AddGroupSeminorm ℂ) ℂ ℝ

-- This then results in a near failure (or failure on nightly-testing) of the simpNF linter on
-- `Complex.comap_exp_cobounded` and `Complex.map_exp_comap_re_atTop`:

set_option synthInstance.maxHeartbeats 3000 in
example : comap exp (cobounded ℂ) = comap re atTop := by simp

end

section

-- Initial issue: https://github.com/leanprover-community/mathlib4/issues/12227

/-- info: NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring -/
#guard_msgs in
set_option synthInstance.maxHeartbeats 6000 in
variable {A : Type} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A]
  [CstarRing A] [StarModule ℂ A] (x : A) in
#synth NonUnitalNonAssocSemiring (elementalStarAlgebra ℂ x)

end

section

-- Initial issue: https://github.com/leanprover-community/mathlib4/issues/12229

open Real in
set_option synthInstance.maxHeartbeats 10000 in
example : expMapCircle (2 * π) = 1 := by simp

end

section

-- Initial issue: https://github.com/leanprover-community/mathlib4/issues/12230

open Complex in
set_option synthInstance.maxHeartbeats 3000 in
example (x : ℝ) : abs (cos x + sin x * I) = 1 := by simp

end

section

-- Initial issue: https://github.com/leanprover-community/mathlib4/issues/12231

variable {α m n : Type*}

open Matrix in
set_option synthInstance.maxHeartbeats 2000 in
example [AddCommGroup α] [StarAddMonoid α] [Module ℚ α] (c : ℚ)
    (M : Matrix m n α) : (c • M)ᴴ = c • Mᴴ := by simp

end

section

-- Initial issue: https://github.com/leanprover-community/mathlib4/issues/12232

open Equiv in
set_option synthInstance.maxHeartbeats 9000 in
example {n : ℕ} (p : Fin (n + 1)) (e : Perm (Fin n)) :
    Equiv.Perm.decomposeFin.symm (p, e) 0 = p := by simp

end
