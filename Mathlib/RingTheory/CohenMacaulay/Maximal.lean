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

lemma isCohenMacaulay_of_isMaximalCohenMacaulay [IsLocalRing R] [Small.{v} R] (M : ModuleCat.{v} R)
    [M.IsMaximalCohenMacaulay] : M.IsCohenMacaulay := by
  sorry
