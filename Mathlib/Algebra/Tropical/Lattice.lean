/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Tropical.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

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
set_option backward.defeqAttrib.useBackward true

@[expose] public section


variable {R S : Type*}

open Tropical

instance instSemilatticeInfTropical [SemilatticeInf R] : SemilatticeInf (Tropical R) :=
  { Tropical.instPartialOrderTropical with
    inf := fun x y ↦ trop (untrop x ⊓ untrop y)
    le_inf := fun _ _ _ ↦ @SemilatticeInf.le_inf R _ _ _ _
    inf_le_left := fun _ _ ↦ inf_le_left
    inf_le_right := fun _ _ ↦ inf_le_right }

instance instSemilatticeSupTropical [SemilatticeSup R] : SemilatticeSup (Tropical R) :=
  { Tropical.instPartialOrderTropical with
    sup := fun x y ↦ trop (untrop x ⊔ untrop y)
    sup_le := fun _ _ _ ↦ @SemilatticeSup.sup_le R _ _ _ _
    le_sup_left := fun _ _ ↦ le_sup_left
    le_sup_right := fun _ _ ↦ le_sup_right }

instance instLatticeTropical [Lattice R] : Lattice (Tropical R) :=
  { instSemilatticeInfTropical, instSemilatticeSupTropical with }

instance [SupSet R] : SupSet (Tropical R) where sSup s := trop (sSup (untrop '' s))

instance [InfSet R] : InfSet (Tropical R) where sInf s := trop (sInf (untrop '' s))

instance instConditionallyCompleteLatticeTropical [ConditionallyCompleteLattice R] :
    ConditionallyCompleteLattice (Tropical R) where
  isLUB_csSup _ hn hb :=
    .of_image untrop_le_iff <| isLUB_csSup (hn.image _) (untrop_monotone.map_bddAbove hb)
  isGLB_csInf _ hn hb :=
    .of_image untrop_le_iff <| isGLB_csInf (hn.image _) (untrop_monotone.map_bddBelow hb)

instance [ConditionallyCompleteLinearOrder R] : ConditionallyCompleteLinearOrder (Tropical R) :=
  { instConditionallyCompleteLatticeTropical, Tropical.instLinearOrderTropical with
    csSup_of_not_bddAbove := by
      intro s hs
      have : Set.range untrop = (Set.univ : Set R) := Equiv.range_eq_univ tropEquiv.symm
      simp only [sSup, Set.image_empty, trop_inj_iff]
      apply csSup_of_not_bddAbove
      contrapose hs
      change BddAbove (tropOrderIso.symm '' s) at hs
      exact tropOrderIso.symm.bddAbove_image.1 hs
    csInf_of_not_bddBelow := by
      intro s hs
      have : Set.range untrop = (Set.univ : Set R) := Equiv.range_eq_univ tropEquiv.symm
      simp only [sInf, Set.image_empty, trop_inj_iff]
      apply csInf_of_not_bddBelow
      contrapose hs
      change BddBelow (tropOrderIso.symm '' s) at hs
      exact tropOrderIso.symm.bddBelow_image.1 hs }
