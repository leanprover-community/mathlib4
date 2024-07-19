/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.RingHomProperties
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!

# The meta properties of integral ring homomorphisms.

-/


namespace RingHom

open scoped TensorProduct

open TensorProduct Algebra.TensorProduct

theorem isIntegral_stableUnderComposition : StableUnderComposition fun f => f.IsIntegral := by
  introv R hf hg; exact hf.trans _ _ hg

theorem isIntegral_respectsIso : RespectsIso fun f => f.IsIntegral := by
  apply isIntegral_stableUnderComposition.respectsIso
  introv x
  rw [← e.apply_symm_apply x]
  apply RingHom.isIntegralElem_map

theorem isIntegral_stableUnderBaseChange : StableUnderBaseChange fun f => f.IsIntegral := by
  refine StableUnderBaseChange.mk _ isIntegral_respectsIso ?_
  introv h x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · apply isIntegral_zero
  · intro x y; exact IsIntegral.tmul x (h y)
  · intro x y hx hy; exact IsIntegral.add hx hy

end RingHom
