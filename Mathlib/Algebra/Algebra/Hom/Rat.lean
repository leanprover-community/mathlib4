/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat

/-!
# Homomorphisms of `ℚ`-algebras

-/

@[expose] public section

variable {R S : Type*} [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S]

namespace RingHom

/-- Reinterpret a `RingHom` as a `ℚ`-algebra homomorphism. This actually yields an equivalence,
see `RingHom.equivRatAlgHom`. -/
def toRatAlgHom (f : R →+* S) : R →ₐ[ℚ] S :=
  { f with commutes' := f.map_rat_algebraMap }

@[simp]
theorem toRatAlgHom_toRingHom (f : R →+* S) :
    ↑f.toRatAlgHom = f :=
  RingHom.ext fun _x => rfl

@[simp]
theorem toRatAlgHom_apply (f : R →+* S) (x : R) :
    f.toRatAlgHom x = f x :=
  rfl

end RingHom

@[simp]
theorem AlgHom.toRingHom_toRatAlgHom (f : R →ₐ[ℚ] S) : (f : R →+* S).toRatAlgHom = f :=
  AlgHom.ext fun _x => rfl

/-- The equivalence between `RingHom` and `ℚ`-algebra homomorphisms. -/
@[simps]
def RingHom.equivRatAlgHom : (R →+* S) ≃ (R →ₐ[ℚ] S) where
  toFun := RingHom.toRatAlgHom
  invFun := AlgHom.toRingHom
  left_inv f := RingHom.toRatAlgHom_toRingHom f
  right_inv f := AlgHom.toRingHom_toRatAlgHom f

namespace RingEquiv

/-- Reinterpret a `RingEquiv` as a `ℚ`-algebra isomorphism. This actually yields an
equivalence, see `RingEquiv.equivRatAlgEquiv`. -/
@[simps! -isSimp apply]
def toRatAlgEquiv (f : R ≃+* S) : R ≃ₐ[ℚ] S where
  toEquiv := f
  __ := f.toRingHom.toRatAlgHom

@[simp]
theorem toRatAlgEquiv_coe (f : R ≃+* S) : ⇑f.toRatAlgEquiv = ⇑f := rfl

@[simp]
theorem toRingEquiv_toRatAlgEquiv (f : R ≃+* S) :
    f.toRatAlgEquiv = f :=
  rfl

@[simp]
theorem toAlgHom_toRatAlgEquiv (f : R ≃+* S) :
    f.toRatAlgEquiv.toAlgHom = (f : R →+* S).toRatAlgHom :=
  rfl

@[simp]
theorem symm_toRatAlgEquiv (f : R ≃+* S) :
    f.toRatAlgEquiv.symm = f.symm.toRatAlgEquiv :=
  rfl

end RingEquiv

@[simp]
theorem AlgEquiv.toRatAlgEquiv_toRingEquiv (f : R ≃ₐ[ℚ] S) : (f : R ≃+* S).toRatAlgEquiv = f :=
  rfl

/-- The equivalence between `RingEquiv` and `ℚ`-algebra isomorphisms. -/
@[simps apply]
def RingEquiv.equivRatAlgEquiv : (R ≃+* S) ≃ (R ≃ₐ[ℚ] S) where
  toFun := RingEquiv.toRatAlgEquiv
  invFun := AlgEquiv.toRingEquiv
