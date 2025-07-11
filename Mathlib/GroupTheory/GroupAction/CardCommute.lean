/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning
-/
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# A consequence of Burnside's lemma

See `Mathlib/GroupTheory/GroupAction/Quotient.lean` for Burnside's lemma itself.
This lemma is separate because it requires `Nat.card`
and hence transitively the development of cardinals.
-/

variable {α : Type*}

instance instInfiniteProdSubtypeCommute [Mul α] [Infinite α] :
    Infinite { p : α × α // Commute p.1 p.2 } :=
  Infinite.of_injective (fun a => ⟨⟨a, a⟩, rfl⟩) (by intro; simp)

open Fintype

theorem card_comm_eq_card_conjClasses_mul_card (G : Type*) [Group G] :
    Nat.card { p : G × G // Commute p.1 p.2 } = Nat.card (ConjClasses G) * Nat.card G := by
  classical
  rcases fintypeOrInfinite G; swap
  · rw [mul_comm, Nat.card_eq_zero_of_infinite, Nat.card_eq_zero_of_infinite, zero_mul]
  simp only [Nat.card_eq_fintype_card]
  calc card { p : G × G // Commute p.1 p.2 }
      _ = card ((a : G) × { b // Commute a b }) :=
            card_congr (Equiv.subtypeProdEquivSigmaSubtype Commute)
      _ = ∑ i, card { b // Commute i b } := card_sigma
      _ = ∑ x, card (MulAction.fixedBy G x) :=
            sum_equiv ConjAct.toConjAct.toEquiv (fun a ↦ card { b // Commute a b })
              (fun g ↦ card (MulAction.fixedBy G g))
              fun g ↦ card_congr' <| congr_arg _ <| funext fun h ↦ mul_inv_eq_iff_eq_mul.symm.eq
      _ = card (Quotient (MulAction.orbitRel (ConjAct G) G)) * card (ConjAct G) :=
             MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group _ _
      _ = card (ConjClasses G) * card G := by
             congr 1; apply card_congr'; congr; ext
             exact (Setoid.comm' _).trans isConj_iff.symm
