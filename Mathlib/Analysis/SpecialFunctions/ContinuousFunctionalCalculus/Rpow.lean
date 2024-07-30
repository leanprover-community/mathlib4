/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.CstarAlgebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog
import Mathlib.Analysis.CstarAlgebra.ContinuousFunctionalCalculus.NonUnital

/-!
# Real powers defined via the continuous functional calculus

This file defines real powers via the continuous functional calculus (CFC) and builds its API.
This allows one to take real powers of matrices, operators, elements of a C⋆-algebra, etc.

## Main declarations

+ `CFC.rpow`: the real power function based on the CFC, i.e. `cfc Real.rpow`

## Implementation notes

FIXME

## TODO

FIXME
-/

open scoped NNReal

namespace CFC

section NonUnital

variable {A : Type*} [PartialOrder A] [NonUnitalNormedRing A] [StarRing A] [StarOrderedRing A]
  [TopologicalRing A] [Module ℝ≥0 A] [SMulCommClass ℝ≥0 A A] [IsScalarTower ℝ≥0 A A]
  [CompleteSpace A] [NonUnitalContinuousFunctionalCalculus ℝ≥0 (fun (a : A) => 0 ≤ a)]
  [UniqueNonUnitalContinuousFunctionalCalculus ℝ≥0 A]

noncomputable def rpowₙ (a : A) (y : ℝ) : A := cfcₙ (fun x => NNReal.rpow x y) a

-- This is set at a low priority to avoid overriding the regular `Pow`
-- instance on the reals
--noncomputable def instPowNonUnital : Pow A ℝ := ⟨rpowₙ⟩

end NonUnital

section Unital

variable {A : Type*} [PartialOrder A] [NormedRing A] [StarRing A] [StarOrderedRing A]
  [TopologicalRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
  [ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
  [UniqueContinuousFunctionalCalculus ℝ A]

noncomputable def rpow (a : A) (y : ℝ) : A := cfc (fun x => Real.rpow x y) a

lemma rpow_natCast {a : A} (n : ℕ) : rpow a n = a ^ n := by
  sorry

lemma exp_smul {a : A} {r : ℝ} : NormedSpace.exp ℂ (r • a) = rpow (NormedSpace.exp ℂ a) r := by
  sorry

lemma rpow_add {a : A} {x y : ℝ} : rpow a (x + y) = rpow a x * rpow a y := by sorry

lemma rpow_rpow {a : A} {x y : ℝ} : rpow (rpow a x) y = rpow a (x * y) := by sorry

lemma rpow_one {a : A} : rpow a 1 = a := by sorry

lemma one_rpow {x : ℝ} : rpow (1 : A) x = (1 : A) := by sorry

lemma rpow_zero {a : A} : rpow a 0 = 1 := by sorry

lemma zero_rpow {x : ℝ} (hx : x ≠ 0) : rpow (0 : A) x = 0 := by sorry




end Unital

end CFC
