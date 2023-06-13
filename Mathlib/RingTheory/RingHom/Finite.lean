/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module ring_theory.ring_hom.finite
! leanprover-community/mathlib commit b5aecf07a179c60b6b37c1ac9da952f3b565c785
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.RingHomProperties

/-!

# The meta properties of finite ring homomorphisms.

-/


namespace RingHom

open scoped TensorProduct

open TensorProduct Algebra.TensorProduct

theorem finite_stableUnderComposition : StableUnderComposition @Finite := by introv R hf hg;
  exact hg.comp hf
#align ring_hom.finite_stable_under_composition RingHom.finite_stableUnderComposition

theorem finite_respectsIso : RespectsIso @Finite :=
  by
  apply finite_stable_under_composition.respects_iso
  intros
  exact Finite.of_surjective _ e.to_equiv.surjective
#align ring_hom.finite_respects_iso RingHom.finite_respectsIso

theorem finite_stableUnderBaseChange : StableUnderBaseChange @Finite :=
  by
  refine' stable_under_base_change.mk _ finite_respects_iso _
  classical
  introv h
  skip
  replace h : Module.Finite R T := by convert h; ext; rw [Algebra.smul_def]; rfl
  suffices Module.Finite S (S ⊗[R] T) by change Module.Finite _ _; convert this; ext;
    rw [Algebra.smul_def]; rfl
  exact inferInstance
#align ring_hom.finite_stable_under_base_change RingHom.finite_stableUnderBaseChange

end RingHom

