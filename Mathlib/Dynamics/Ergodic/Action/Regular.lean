/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Dynamics.Ergodic.Action.Basic
public import Mathlib.MeasureTheory.Group.Prod

/-!
# Regular action of a group on itself is ergodic

In this file we prove that the left and right actions of a group on itself are ergodic.
-/

@[expose] public section

open MeasureTheory Measure Filter Set
open scoped Pointwise

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SFinite μ]

@[to_additive]
instance [μ.IsMulLeftInvariant] : ErgodicSMul G G μ := by
  refine ⟨fun {s} hsm hs ↦ ?_⟩
  suffices (∃ᵐ x ∂μ, x ∈ s) → ∀ᵐ x ∂μ, x ∈ s by
    simp only [eventuallyConst_set, ← not_frequently]
    exact or_not_of_imp this
  intro hμs
  obtain ⟨a, has, ha⟩ : ∃ a ∈ s, ∀ᵐ b ∂μ, (b * a ∈ s ↔ a ∈ s) := by
    refine (hμs.and_eventually ?_).exists
    rw [ae_ae_comm]
    · exact ae_of_all _ fun b ↦ (hs b).mem_iff
    · exact ((hsm.preimage <| measurable_snd.mul measurable_fst).mem.iff
        (hsm.preimage measurable_fst).mem).setOf
  simpa [has] using (MeasureTheory.quasiMeasurePreserving_mul_right μ a⁻¹).ae ha

@[to_additive]
instance [μ.IsMulRightInvariant] : ErgodicSMul Gᵐᵒᵖ G μ := by
  refine ⟨fun {s} hsm hs ↦ ?_⟩
  suffices (∃ᵐ x ∂μ, x ∈ s) → ∀ᵐ x ∂μ, x ∈ s by
    simp only [eventuallyConst_set, ← not_frequently]
    exact or_not_of_imp this
  intro hμs
  obtain ⟨a, has, ha⟩ : ∃ a ∈ s, ∀ᵐ b ∂μ, (a * b ∈ s ↔ a ∈ s) := by
    refine (hμs.and_eventually ?_).exists
    rw [ae_ae_comm]
    · exact ae_of_all _ fun b ↦ (hs ⟨b⟩).mem_iff
    · exact ((hsm.preimage <| measurable_fst.mul measurable_snd).mem.iff
        (hsm.preimage measurable_fst).mem).setOf
  simpa [has] using (quasiMeasurePreserving_mul_left μ a⁻¹).ae ha
