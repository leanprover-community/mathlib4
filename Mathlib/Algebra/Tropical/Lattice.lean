/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

#align_import algebra.tropical.lattice from "leanprover-community/mathlib"@"6d0adfa76594f304b4650d098273d4366edeb61b"

/-!

# Order on tropical algebraic structure

This file defines the orders induced on tropical algebraic structures by the underlying type.

## Main declarations

* `ConditionallyCompleteLattice (Tropical R)`
* `ConditionallyCompleteLinearOrder (Tropical R)`

## Implementation notes

The order induced is the definitionally equal underlying order, which makes the proofs and
constructions quicker to implement.

-/


variable {R S : Type*}

open Tropical

instance instSupTropical [Sup R] : Sup (Tropical R) where
  sup x y := trop (untrop x ⊔ untrop y)

instance instInfTropical [Inf R] : Inf (Tropical R) where
  inf x y := trop (untrop x ⊓ untrop y)

instance instSemilatticeInfTropical [SemilatticeInf R] : SemilatticeInf (Tropical R) :=
  { instInfTropical,
    Tropical.instPartialOrderTropical with
    le_inf := fun _ _ _ ↦ @SemilatticeInf.le_inf R _ _ _ _
    inf_le_left := fun _ _ ↦ inf_le_left
    inf_le_right := fun _ _ ↦ inf_le_right }

instance instSemilatticeSupTropical [SemilatticeSup R] : SemilatticeSup (Tropical R) :=
  { instSupTropical,
    Tropical.instPartialOrderTropical with
    sup_le := fun _ _ _ ↦ @SemilatticeSup.sup_le R _ _ _ _
    le_sup_left := fun _ _ ↦ le_sup_left
    le_sup_right := fun _ _ ↦ le_sup_right }

instance instLatticeTropical [Lattice R] : Lattice (Tropical R) :=
  { instSemilatticeInfTropical, instSemilatticeSupTropical with }

instance [SupSet R] : SupSet (Tropical R) where sSup s := trop (sSup (untrop '' s))

instance [InfSet R] : InfSet (Tropical R) where sInf s := trop (sInf (untrop '' s))

instance instConditionallyCompleteLatticeTropical [ConditionallyCompleteLattice R] :
    ConditionallyCompleteLattice (Tropical R) :=
  { @instInfTropical R _, @instSupTropical R _,
    instLatticeTropical with
    le_csSup  := fun _s _x hs hx ↦
      le_csSup (untrop_monotone.map_bddAbove hs) (Set.mem_image_of_mem untrop hx)
    csSup_le := fun _s _x hs hx ↦
      csSup_le (hs.image untrop) (untrop_monotone.mem_upperBounds_image hx)
    le_csInf := fun _s _x hs hx ↦
      le_csInf (hs.image untrop) (untrop_monotone.mem_lowerBounds_image hx)
    csInf_le := fun _s _x hs hx ↦
      csInf_le (untrop_monotone.map_bddBelow hs) (Set.mem_image_of_mem untrop hx) }

instance [ConditionallyCompleteLinearOrder R] : ConditionallyCompleteLinearOrder (Tropical R) :=
  { instConditionallyCompleteLatticeTropical, Tropical.instLinearOrderTropical with
    csSup_of_not_bddAbove := by
      intro s hs
      -- ⊢ sSup s = sSup Set.univ
      have : Set.range untrop = (Set.univ : Set R) := Equiv.range_eq_univ tropEquiv.symm
      -- ⊢ sSup s = sSup Set.univ
      simp [sSup, this]
      -- ⊢ sSup (untrop '' s) = sSup Set.univ
      apply csSup_of_not_bddAbove
      -- ⊢ ¬BddAbove (untrop '' s)
      contrapose! hs
      -- ⊢ BddAbove s
      change BddAbove (tropOrderIso.symm '' s) at hs
      -- ⊢ BddAbove s
      exact tropOrderIso.symm.bddAbove_image.1 hs
      -- 🎉 no goals
    csInf_of_not_bddBelow := by
      intro s hs
      -- ⊢ sInf s = sInf Set.univ
      have : Set.range untrop = (Set.univ : Set R) := Equiv.range_eq_univ tropEquiv.symm
      -- ⊢ sInf s = sInf Set.univ
      simp [sInf, this]
      -- ⊢ sInf (untrop '' s) = sInf Set.univ
      apply csInf_of_not_bddBelow
      -- ⊢ ¬BddBelow (untrop '' s)
      contrapose! hs
      -- ⊢ BddBelow s
      change BddBelow (tropOrderIso.symm '' s) at hs
      -- ⊢ BddBelow s
      exact tropOrderIso.symm.bddBelow_image.1 hs }
      -- 🎉 no goals
