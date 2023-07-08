/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky

! This file was ported from Lean 3 source module algebra.tropical.lattice
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

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


variable {R S : Type _}

open Tropical

instance [Sup R] : Sup (Tropical R) where
  sup x y := trop (untrop x ⊔ untrop y)

instance [Inf R] : Inf (Tropical R) where
  inf x y := trop (untrop x ⊓ untrop y)

instance [SemilatticeInf R] : SemilatticeInf (Tropical R) :=
  { instInfTropical,
    Tropical.instPartialOrderTropical with
    le_inf := fun _ _ _ ↦ @SemilatticeInf.le_inf R _ _ _ _
    inf_le_left := fun _ _ ↦ inf_le_left
    inf_le_right := fun _ _ ↦ inf_le_right }

instance [SemilatticeSup R] : SemilatticeSup (Tropical R) :=
  { instSupTropical,
    Tropical.instPartialOrderTropical with
    sup_le := fun _ _ _ ↦ @SemilatticeSup.sup_le R _ _ _ _
    le_sup_left := fun _ _ ↦ le_sup_left
    le_sup_right := fun _ _ ↦ le_sup_right }

instance [Lattice R] : Lattice (Tropical R) :=
  { instSemilatticeInfTropical, instSemilatticeSupTropical with }

instance [SupSet R] : SupSet (Tropical R) where sSup s := trop (sSup (untrop '' s))

instance [InfSet R] : InfSet (Tropical R) where sInf s := trop (sInf (untrop '' s))

instance [ConditionallyCompleteLattice R] : ConditionallyCompleteLattice (Tropical R) :=
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
  { instConditionallyCompleteLatticeTropical, Tropical.instLinearOrderTropical with }
