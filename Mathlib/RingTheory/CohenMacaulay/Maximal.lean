/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yongle Hu
-/
import Mathlib.RingTheory.CohenMacaulay.Basic
import Mathlib.RingTheory.RegularLocalRing.Basic

/-!

# Maximal Cohen Macaulay Module

The definition of maximal Cohen Macaulay module.

# Main definition and results

* `free_of_isMaximalCohenMacaulay_of_isRegularLocalRing` : maximal Cohen Macaulay module over
  regular local ring is free.

-/

universe v' v u' u

variable {R : Type u} [CommRing R]

open IsLocalRing

class ModuleCat.IsMaximalCohenMacaulay [IsLocalRing R] [Small.{v} R]
    (M : ModuleCat.{v} R) : Prop where
  depth_eq_dim : IsLocalRing.depth M = ringKrullDim R

lemma isMaximalCohenMacaulay_def [IsLocalRing R] [Small.{v} R]
    (M : ModuleCat.{v} R) : M.IsMaximalCohenMacaulay ↔ IsLocalRing.depth M = ringKrullDim R :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

/-
--need subsingleton imply depth eq top
instance [IsNoetherianRing R] [IsLocalRing R] [Small.{v} R]
    (M : ModuleCat.{v} R) [M.IsMaximalCohenMacaulay] : Nontrivial M := sorry
-/

lemma isCohenMacaulay_of_isMaximalCohenMacaulay [IsNoetherianRing R] [IsLocalRing R] [Small.{v} R]
    (M : ModuleCat.{v} R) [Module.Finite R M] [M.IsMaximalCohenMacaulay] : M.IsCohenMacaulay := by
  rw [M.isCohenMacaulay_iff]
  by_cases h : Subsingleton M
  · exact Or.inl h
  · have : Nontrivial M := not_subsingleton_iff_nontrivial.mp h
    right
    apply le_antisymm _ (depth_le_supportDim M)
    simpa [(isMaximalCohenMacaulay_def M).mp ‹_›] using Module.supportDim_le_ringKrullDim R M

lemma isCohenMacaulayLocalRing_of_isRegularLocalRing [IsRegularLocalRing R] :
    IsCohenMacaulayLocalRing R := by
  apply isCohenMacaulayLocalRing_of_ringKrullDim_le_depth
  rw [depth_eq_sSup_length_regular]
  let fg' : (maximalIdeal R).FG := (isNoetherianRing_iff_ideal_fg R).mp inferInstance _
  let _ : Fintype (maximalIdeal R).generators := (Submodule.FG.finite_generators fg').fintype
  have : ringKrullDim R = ((maximalIdeal R).generators.toFinset.card : ℕ∞) := by
    rw [← (isRegularLocalRing_def R).mp ‹_›, ← Set.ncard_eq_toFinset_card',
      Submodule.FG.generators_ncard fg']
    rfl
  simp only [this, WithBot.coe_le_coe]
  apply le_sSup
  use (maximalIdeal R).generators.toFinset.toList
  simp only [Finset.length_toList, Set.toFinset_card, Set.coe_fintypeCard, Finset.mem_toList,
    Set.mem_toFinset, exists_prop, and_true]
  refine ⟨?_, fun r hr ↦ Submodule.FG.generators_mem (maximalIdeal R) hr⟩
  apply isRegular_of_span_eq_maximalIdeal
  · simpa [Ideal.ofList] using (maximalIdeal R).span_generators
  · rw [Finset.length_toList, this]
    rfl

theorem free_of_isMaximalCohenMacaulay_of_isRegularLocalRing [IsRegularLocalRing R] [Small.{v} R]
    (M : ModuleCat.{v} R) [Module.Finite R M] [M.IsMaximalCohenMacaulay] : Module.Free R M := by
  rcases exist_nat_eq R with ⟨n, hn⟩
  induction' n with n ih generalizing R M
  · sorry
  · sorry
