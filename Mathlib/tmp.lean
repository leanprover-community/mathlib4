/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import Mathlib.SetTheory.Cardinal.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-! # Stupid theorems -/

universe u v

theorem module_rank_ne_natCast_of_nontrivial {R : Type u} [Nontrivial R] (n : Nat) :
    Module.rank.{u,max u v} R ≠ n := by
  intro h
  simp_rw [funext_iff, Pi.natCast_apply] at h
  inhabit R
  obtain ⟨instR⟩ : Nonempty (CommRing R) := inferInstance
  have hn1 : 1 = (n : Cardinal) := by
    simpa using h (ULift.{v} R) inferInstance inferInstance inferInstance
  have := h (ULift.{v} R × ULift.{v} R) inferInstance inferInstance inferInstance
  rw [rank_prod', h, ←hn1] at this
  norm_num at this

theorem module_rank_eq_natCast_iff {R : Type u} (n : Nat) :
    Module.rank.{u,max u v} R = n ↔ IsEmpty R ∨ (Subsingleton R ∧ n = 1) := by
  obtain h | h := isEmpty_or_nonempty R
  · simp [h, funext_iff]
    intro M iR
    exact IsEmpty.elim ‹_› iR.zero
  obtain ⟨instR⟩ : Nonempty (CommRing R) := inferInstance
  obtain h | h := subsingleton_or_nontrivial R
  · simp [h, funext_iff, @eq_comm _ _ 1]
    constructor
    · intro h
      specialize h (ULift R) inferInstance inferInstance inferInstance
      exact_mod_cast h
    · rintro rfl _
      simp
  · rw [← not_nontrivial_iff_subsingleton]
    simp [h]
    exact module_rank_ne_natCast_of_nontrivial n
