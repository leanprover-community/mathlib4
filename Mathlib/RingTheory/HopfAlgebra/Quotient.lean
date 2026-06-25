/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.Quotient
public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# Hopf algebra structure on quotients by a ring congruence

If the antipode of an `R`-Hopf algebra `A` descends along a bialgebra congruence `c`, then
`c.Quotient` is again a Hopf algebra.

## Main definitions

* `RingCon.IsHopfCon R c` : `IsBialgebraCon R c` together with descent of the antipode.

## Main results

* `HopfAlgebra R c.Quotient` instance when `[c.IsHopfCon R]`.
-/

public section

open Coalgebra HopfAlgebra LinearMap MulOpposite

variable {R A : Type*} [CommRing R] [Ring A] [HopfAlgebra R A]

variable (R) in
/-- A ring congruence `c` on an `R`-Hopf algebra is a *Hopf congruence* if it is a bialgebra
congruence along which the antipode also descends. -/
@[mk_iff]
class RingCon.IsHopfCon (c : RingCon A) : Prop extends RingCon.IsBialgebraCon R c where
  antipode_rel : ∀ ⦃x y : A⦄, c x y → c (antipode R x) (antipode R y)

namespace HopfAlgebra.Quotient

variable (c : RingCon A) [c.IsHopfCon R]

/-- The antipode descends to `c.Quotient`: it is the linear map underlying the algebra anti-hom
`(c.mkₐ R).op.comp (antipodeAlgHomOp R A)`, namely `a ↦ op (mkₐ (antipode a))`. -/
noncomputable instance : HopfAlgebraStruct R c.Quotient where
  antipode := (opLinearEquiv R).symm.toLinearMap ∘ₗ
    (c.liftₐ ((c.mkₐ R).op.comp (antipodeAlgHomOp R A)) fun _ _ h ↦
      congrArg op (by simpa using ‹c.IsHopfCon R›.antipode_rel h)).toLinearMap

@[simp]
lemma antipode_mkₐ (a : A) : antipode R (c.mkₐ R a) = c.mkₐ R (antipode R a) := rfl

lemma antipode_comp_mkₐ :
    (antipode R).comp (c.mkₐ R).toLinearMap = (c.mkₐ R).toLinearMap ∘ₗ antipode R := by
  ext a; exact antipode_mkₐ c a

noncomputable instance : HopfAlgebra R c.Quotient :=
  .ofSurjective (Bialgebra.Quotient.mkBialgHom c) (c.mkₐ_surjective (α := R)) (antipode_comp_mkₐ c)

end HopfAlgebra.Quotient
