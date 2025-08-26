/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yongle Hu
-/
import Mathlib.RingTheory.CohenMacaulay.Basic

/-!

# Maximal Cohen Macaulay Module

-/

universe v' v u' u

variable {R : Type u} [CommRing R]

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
