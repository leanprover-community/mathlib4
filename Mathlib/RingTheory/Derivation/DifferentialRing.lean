/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
import Mathlib.RingTheory.Derivation.Basic

/-!
# Differential Rings and Algebras

This file defines differential rings, which are rings with a bundled `Derivation ℤ R R`, and
differential algebras, which are algebras of differential rings where the algebra map commutes
with the derivative.

This file also defines the x′ notation for the derivative of x in a differential ring.
-/

/--
A `CommRing` with a bundled `Derivation` to itself.
-/
class CommDifferentialRing (R : Type*) extends CommRing R where
  /-- The `Derivation` assosiated with the ring. -/
  deriv : Derivation ℤ R R

@[inherit_doc]
postfix:max "′" => CommDifferentialRing.deriv

open Lean PrettyPrinter Delaborator SubExpr in
/--
A delaborator for the x′ notation. This is required because it's not direct function application,
so the default delaborator doesn't work.
-/
@[delab app.DFunLike.coe]
def delabDeriv : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity' ``DFunLike.coe 6
  guard <| (e.getArg!' 4).isAppOf' ``CommDifferentialRing.deriv
  let arg ← withAppArg delab
  `($arg′)

/--
A differential algebra is an `Algebra` where the derivation commutes with `algebraMap`.
-/
class DifferentialAlgebra (A : Type*) (B : Type*) [CommDifferentialRing A] [CommDifferentialRing B]
    extends Algebra A B where
  deriv_algebraMap : ∀ a : A, (algebraMap A B a)′ = algebraMap A B a′

export DifferentialAlgebra (deriv_algebraMap)

instance (A : Type*) [CommDifferentialRing A] : DifferentialAlgebra A A where
  deriv_algebraMap _ := rfl

/--
Transfer a `CommDifferentialRing` instance accross a `RingEquiv`.
-/
def CommDifferentialRing.equiv {R R2 : Type*} [CommRing R] [CommDifferentialRing R2] (h : R ≃+* R2):
    CommDifferentialRing R where
  deriv := Derivation.mk' (h.symm.toAddMonoidHom.toIntLinearMap ∘ₗ
    CommDifferentialRing.deriv.toLinearMap ∘ₗ h.toAddMonoidHom.toIntLinearMap) (by simp)

@[norm_cast]
lemma algebraMap.coe_deriv {A : Type*} {B : Type*} [CommDifferentialRing A] [CommDifferentialRing B]
    [DifferentialAlgebra A B] (a : A) :
    (a′ : A) = (a : B)′ :=
  (DifferentialAlgebra.deriv_algebraMap _).symm


/--
Transfer a `DifferentialAlgebra` instance accross a `AlgEquiv`.
-/
def DifferentialAlgebra.equiv {A : Type*} [CommDifferentialRing A]
    {R R2 : Type*} [CommRing R] [CommDifferentialRing R2] [Algebra A R] [DifferentialAlgebra A R2]
    (h : R ≃ₐ[A] R2) :
    letI := CommDifferentialRing.equiv h.toRingEquiv
    DifferentialAlgebra A R :=
  letI := CommDifferentialRing.equiv h.toRingEquiv
  DifferentialAlgebra.mk fun a ↦ by
    change (LinearMap.comp ..) _ = _
    simp only [AlgEquiv.toRingEquiv_eq_coe, RingHom.toAddMonoidHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, LinearMap.coe_comp,
      AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_coe, RingHom.coe_coe, Derivation.coeFn_coe,
      Function.comp_apply, AlgEquiv.commutes, deriv_algebraMap]
    apply h.symm.commutes
