/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.RingHomProperties
import Mathlib.RingTheory.IntegralClosure

#align_import ring_theory.ring_hom.integral from "leanprover-community/mathlib"@"a7c017d750512a352b623b1824d75da5998457d0"

/-!

# The meta properties of integral ring homomorphisms.

-/


namespace RingHom

open scoped TensorProduct

open TensorProduct Algebra.TensorProduct

theorem isIntegral_stableUnderComposition : StableUnderComposition fun f => f.IsIntegral := by
  introv R hf hg; exact RingHom.isIntegral_trans _ _ hf hg
#align ring_hom.is_integral_stable_under_composition RingHom.isIntegral_stableUnderComposition

theorem isIntegral_respectsIso : RespectsIso fun f => f.IsIntegral := by
  apply isIntegral_stableUnderComposition.respectsIso
  introv x
  rw [← e.apply_symm_apply x]
  apply RingHom.is_integral_map
#align ring_hom.is_integral_respects_iso RingHom.isIntegral_respectsIso

theorem isIntegral_stableUnderBaseChange : StableUnderBaseChange fun f => f.IsIntegral := by
  refine' StableUnderBaseChange.mk _ isIntegral_respectsIso _
  introv h x
  refine' TensorProduct.induction_on x _ _ _
  · apply isIntegral_zero
  · intro x y; exact IsIntegral.tmul x (h y)
  · intro x y hx hy; exact isIntegral_add hx hy
#align ring_hom.is_integral_stable_under_base_change RingHom.isIntegral_stableUnderBaseChange

end RingHom
