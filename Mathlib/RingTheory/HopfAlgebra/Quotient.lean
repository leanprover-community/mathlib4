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
`c.Quotient` is again a Hopf algebra. A *Hopf ideal* of a Hopf algebra over a ring is a biideal
stable under the antipode; it induces such a congruence, so the quotient by a Hopf ideal is a
Hopf algebra.

## Main definitions

* `RingCon.IsHopfAlgebraCon R c` : `IsBialgebraCon R c` together with descent of the antipode.
* `Ideal.IsHopfIdeal R I` : `I` is a coideal (as an `R`-submodule) stable under the antipode.

## Main results

* `HopfAlgebra R c.Quotient` instance when `[c.IsHopfAlgebraCon R]`.
* `HopfAlgebra R (A ⧸ I)` instance when `[I.IsTwoSided]` and `[I.IsHopfIdeal R]`.
-/

public section

open HopfAlgebra MulOpposite

section RingCon

variable {R A : Type*} [CommSemiring R] [Semiring A] [HopfAlgebra R A]

variable (R) in
/-- A ring congruence `c` on an `R`-Hopf algebra is a *Hopf congruence* if it is a bialgebra
congruence along which the antipode also descends. -/
@[mk_iff]
class RingCon.IsHopfAlgebraCon (c : RingCon A) : Prop extends RingCon.IsBialgebraCon R c where
  antipode_rel : ∀ ⦃x y : A⦄, c x y → c (antipode R x) (antipode R y)

namespace HopfAlgebra.Quotient

variable (c : RingCon A) [hc : c.IsHopfAlgebraCon R]

/-- The antipode descends to `c.Quotient`: it is the linear map underlying the algebra anti-hom
`(c.mkₐ R).op.comp (antipodeAlgHomOp R A)`, namely `a ↦ op (mkₐ (antipode a))`. -/
noncomputable instance : HopfAlgebraStruct R c.Quotient where
  antipode := (opLinearEquiv R).symm.toLinearMap ∘ₗ
    (c.liftₐ ((c.mkₐ R).op.comp (antipodeAlgHomOp R A)) fun _ _ h ↦
      congrArg op (by simpa using hc.antipode_rel h)).toLinearMap

@[simp]
lemma antipode_mkₐ (a : A) : antipode R (c.mkₐ R a) = c.mkₐ R (antipode R a) := rfl

noncomputable instance : HopfAlgebra R c.Quotient :=
  .ofSurjective (Bialgebra.Quotient.mkBialgHom c) (c.mkₐ_surjective (α := R)) fun _ ↦ rfl

end HopfAlgebra.Quotient

end RingCon

section Ideal

variable {R A : Type*} [CommRing R] [Ring A]

variable (R) in
/-- An ideal whose underlying `R`-submodule is a coideal and which is stable under the
antipode (`S(I) ⊆ I`). Together with `I.IsTwoSided`, this makes `I` a *Hopf ideal*. -/
@[mk_iff]
class Ideal.IsHopfIdeal [HopfAlgebraStruct R A] (I : Ideal A) : Prop
    extends (I.restrictScalars R).IsCoideal where
  antipode_mem : ∀ ⦃x : A⦄, x ∈ I → antipode R x ∈ I

variable [HopfAlgebra R A] (I : Ideal A) [I.IsTwoSided] [I.IsHopfIdeal R]

/-- The ring congruence of a Hopf ideal is a Hopf algebra congruence. -/
instance : (Ideal.Quotient.ringCon I).IsHopfAlgebraCon R where
  antipode_rel := fun ⦃_ _⦄ h ↦ Quotient.exact <| Ideal.Quotient.eq.mpr <| by
    rw [← map_sub]
    exact Ideal.IsHopfIdeal.antipode_mem (Ideal.Quotient.eq.mp (Quotient.sound h))

namespace HopfAlgebra.Quotient

/-- The Hopf algebra structure on `A ⧸ I` when `I` is a Hopf ideal. -/
noncomputable instance : HopfAlgebra R (A ⧸ I) :=
  { (inferInstance : Bialgebra R (A ⧸ I)),
    (inferInstance : HopfAlgebra R (Ideal.Quotient.ringCon I).Quotient) with }

@[simp]
lemma antipode_mk (a : A) :
    antipode R (Ideal.Quotient.mk I a) = Ideal.Quotient.mk I (antipode R a) := rfl

end HopfAlgebra.Quotient

end Ideal
