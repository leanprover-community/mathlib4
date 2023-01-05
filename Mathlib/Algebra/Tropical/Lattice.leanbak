/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky

! This file was ported from Lean 3 source module algebra.tropical.lattice
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Tropical.Basic
import Mathbin.Order.ConditionallyCompleteLattice.Basic

/-!

# Order on tropical algebraic structure

This file defines the orders induced on tropical algebraic structures by the underlying type.

## Main declarations

* `conditionally_complete_lattice (tropical R)`
* `conditionally_complete_linear_order (tropical R)`

## Implementation notes

The order induced is the definitionally equal underlying order, which makes the proofs and
constructions quicker to implement.

-/


variable {R S : Type _}

open Tropical

instance [HasSup R] : HasSup (Tropical R) where sup x y := trop (untrop x ⊔ untrop y)

instance [HasInf R] : HasInf (Tropical R) where inf x y := trop (untrop x ⊓ untrop y)

instance [SemilatticeInf R] : SemilatticeInf (Tropical R) :=
  { Tropical.hasInf,
    Tropical.partialOrder with
    le_inf := fun _ _ _ => le_inf
    inf_le_left := fun _ _ => inf_le_left
    inf_le_right := fun _ _ => inf_le_right }

instance [SemilatticeSup R] : SemilatticeSup (Tropical R) :=
  { Tropical.hasSup,
    Tropical.partialOrder with
    sup_le := fun _ _ _ => sup_le
    le_sup_left := fun _ _ => le_sup_left
    le_sup_right := fun _ _ => le_sup_right }

instance [Lattice R] : Lattice (Tropical R) :=
  { Tropical.semilatticeInf, Tropical.semilatticeSup with }

instance [SupSet R] : SupSet (Tropical R) where sup s := trop (supₛ (untrop '' s))

instance [InfSet R] : InfSet (Tropical R) where inf s := trop (infₛ (untrop '' s))

instance [ConditionallyCompleteLattice R] : ConditionallyCompleteLattice (Tropical R) :=
  { Tropical.hasSup, Tropical.hasInf,
    Tropical.lattice with
    le_cSup := fun s x hs hx =>
      le_csupₛ (untrop_monotone.map_bdd_above hs) (Set.mem_image_of_mem untrop hx)
    cSup_le := fun s x hs hx =>
      csupₛ_le (hs.image untrop) (untrop_monotone.mem_upper_bounds_image hx)
    le_cInf := fun s x hs hx =>
      le_cinfₛ (hs.image untrop) (untrop_monotone.mem_lower_bounds_image hx)
    cInf_le := fun s x hs hx =>
      cinfₛ_le (untrop_monotone.map_bdd_below hs) (Set.mem_image_of_mem untrop hx) }

instance [ConditionallyCompleteLinearOrder R] : ConditionallyCompleteLinearOrder (Tropical R) :=
  { Tropical.conditionallyCompleteLattice, Tropical.linearOrder with }

