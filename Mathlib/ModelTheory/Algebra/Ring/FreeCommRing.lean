/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.RingTheory.FreeCommRing
import Mathlib.RingTheory.Congruence.Basic

/-!
# Making a term in the language of rings from an element of the FreeCommRing

This file defines the function `FirstOrder.Ring.termOfFreeCommRing` which constructs a
`Language.ring.Term α` from an element of `FreeCommRing α`.

The theorem `FirstOrder.Ring.realize_termOfFreeCommRing` shows that the term constructed when
realized in a ring `R` is equal to the lift of the element of `FreeCommRing α` to `R`.
-/

namespace FirstOrder

namespace Ring

open Language

variable {α : Type*}

section

/-- The kernel of `Term.realize`, as a ring congruence. -/
def realizeKer {R} [Ring R] (f : α → R) : RingCon (ring.Term α) where
  toSetoid := letI := compatibleRingOfRing R; Setoid.ker (Term.realize f)
  add' (hx : _ = _) (hy : _ = _) := show _ = _ by
    simp [hx, hy]
  mul' (hx : _ = _) (hy : _ = _) := show _ = _ by
    simp [hx, hy]

instance {R} [Ring R] (f : α → R) : Zero (realizeKer f).Quotient where zero := ⟦0⟧
instance {R} [Ring R] (f : α → R) : One (realizeKer f).Quotient where one := ⟦1⟧
instance {R} [Ring R] (f : α → R) : Neg (realizeKer f).Quotient where
  neg := Quotient.map' Neg.neg fun a b (h : _ = _) => show _ = _ by
    simpa only [realize_neg, neg_inj]

instance {R} [Ring R] (f : α → R) : Ring (realizeKer f).Quotient where
  add_assoc := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; refine Quotient.sound' (add_assoc _ _ _)
  zero_add := by rintro ⟨a⟩; refine Quotient.sound' (zero_add _)
  add_zero := by rintro ⟨a⟩; refine Quotient.sound' (add_zero _)
  add_comm := by rintro ⟨a⟩ ⟨b⟩; refine Quotient.sound' (add_comm _ _)
  left_distrib := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; refine Quotient.sound' (left_distrib _ _ _)
  right_distrib := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; refine Quotient.sound' (right_distrib _ _ _)
  mul_one := by rintro ⟨a⟩; refine Quotient.sound' (mul_one _)
  one_mul := by rintro ⟨a⟩; refine Quotient.sound' (one_mul _)
  mul_zero := by rintro ⟨a⟩; refine Quotient.sound' (mul_zero _)
  zero_mul := by rintro ⟨a⟩; refine Quotient.sound' (zero_mul _)
  mul_assoc := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; refine Quotient.sound' (mul_assoc _ _ _)
  neg_add_cancel := by rintro ⟨a⟩; refine Quotient.sound' (neg_add_cancel _)
  nsmul := nsmulRec
  zsmul := zsmulRec

instance {R} [CommRing R] (f : α → R) : CommRing (realizeKer f).Quotient where
  mul_comm := by rintro ⟨a⟩ ⟨b⟩; refine Quotient.sound' (mul_comm _ _)

def quotTermOfFreeRing :
    FreeRing α →+ (realizeKer (FreeRing.of : α → _)).Quotient :=
  FreeRing.lift (α := α) (R := (realizeKer (FreeRing.of : α → _)).Quotient)
    fun a => ⟦Term.var a⟧
def quotTermOfFreeCommRing :
    FreeCommRing α →+ (realizeKer (FreeCommRing.of : α → _)).Quotient :=
  FreeCommRing.lift (α := α) (R := (realizeKer (FreeCommRing.of : α → _)).Quotient)
    fun a => ⟦Term.var a⟧

end

/-- Make a `Language.ring.Term α` from an element of `FreeCommRing α` -/
noncomputable def termOfFreeCommRing (p : FreeCommRing α) : Language.ring.Term α :=
  (quotTermOfFreeCommRing p).out'

variable {R : Type*} [CommRing R] [CompatibleRing R]

@[simp]
theorem realize_termOfFreeCommRing (p : FreeCommRing α) (v : α → R) :
    (termOfFreeCommRing p).realize v = FreeCommRing.lift v p := by
  let _ := compatibleRingOfRing (FreeCommRing α)
  rw [termOfFreeCommRing]
  conv_rhs => rw [← Classical.choose_spec (exists_term_realize_eq_freeCommRing p)]
  induction Classical.choose (exists_term_realize_eq_freeCommRing p) with
  | var _ => simp
  | func f a ih =>
    cases f <;>
    simp [ih]

end Ring

end FirstOrder
