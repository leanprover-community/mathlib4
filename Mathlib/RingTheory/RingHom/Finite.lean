/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.RingHomProperties

#align_import ring_theory.ring_hom.finite from "leanprover-community/mathlib"@"b5aecf07a179c60b6b37c1ac9da952f3b565c785"

/-!

# The meta properties of finite ring homomorphisms.

-/


namespace RingHom

open scoped TensorProduct

open TensorProduct Algebra.TensorProduct

theorem finite_stableUnderComposition : StableUnderComposition @Finite := by
  introv R hf hg
  exact hg.comp hf
#align ring_hom.finite_stable_under_composition RingHom.finite_stableUnderComposition

theorem finite_respectsIso : RespectsIso @Finite := by
  apply finite_stableUnderComposition.respectsIso
  intros
  exact Finite.of_surjective _ (RingEquiv.toEquiv _).surjective
#align ring_hom.finite_respects_iso RingHom.finite_respectsIso

theorem finite_stableUnderBaseChange : StableUnderBaseChange @Finite := by
  refine StableUnderBaseChange.mk _ finite_respectsIso ?_
  classical
  introv h
  replace h : Module.Finite R T := by
    rw [RingHom.Finite] at h; convert h; ext; simp_rw [Algebra.smul_def]; rfl
  suffices Module.Finite S (S ⊗[R] T) by
    rw [RingHom.Finite]; convert this; congr; ext; simp_rw [Algebra.smul_def]; rfl
  exact inferInstance
#align ring_hom.finite_stable_under_base_change RingHom.finite_stableUnderBaseChange

end RingHom
