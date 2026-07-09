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


namespace RingHom

variable {R S : Type*}

/-- Reinterpret a `RingHom` as a `ℚ`-algebra homomorphism. This actually yields an equivalence,
see `RingHom.equivRatAlgHom`. -/
def toRatAlgHom [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S) : R →ₐ[ℚ] S :=
  { f with commutes' := f.map_rat_algebraMap }

@[simp]
theorem toRatAlgHom_toRingHom [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S) :
    ↑f.toRatAlgHom = f :=
  RingHom.ext fun _x => rfl

@[simp]
theorem toRatAlgHom_apply [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S) (x : R) :
    f.toRatAlgHom x = f x :=
  rfl

end RingHom

section

variable {R S : Type*}

@[simp]
theorem AlgHom.toRingHom_toRatAlgHom [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S]
    (f : R →ₐ[ℚ] S) : (f : R →+* S).toRatAlgHom = f :=
  AlgHom.ext fun _x => rfl

/-- The equivalence between `RingHom` and `ℚ`-algebra homomorphisms. -/
@[simps]
def RingHom.equivRatAlgHom [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] :
    (R →+* S) ≃ (R →ₐ[ℚ] S) where
  toFun := RingHom.toRatAlgHom
  invFun := AlgHom.toRingHom
  left_inv f := RingHom.toRatAlgHom_toRingHom f
  right_inv f := AlgHom.toRingHom_toRatAlgHom f

end

namespace RingEquiv

variable {R S : Type*}

/-- Reinterpret a `RingEquiv` as a `ℚ`-algebra isomorphism. This actually yields an
equivalence, see `RingEquiv.equivRatAlgEquiv`. -/
def toRatAlgEquiv [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] (f : R ≃+* S) : R ≃ₐ[ℚ] S :=
  { f with commutes' := f.toRingHom.map_rat_algebraMap }

@[simp]
theorem toRingEquiv_toRatAlgEquiv [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] (f : R ≃+* S) :
    f.toRatAlgEquiv = f :=
  rfl

@[simp]
theorem coe_toRatAlgEquiv [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] (f : R ≃+* S) :
    ⇑f.toRatAlgEquiv = ⇑f :=
  rfl

@[simp]
theorem toRatAlgEquiv_apply [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] (f : R ≃+* S) (x : R) :
    f.toRatAlgEquiv x = f x :=
  rfl

end RingEquiv

section

variable {R S : Type*}

@[simp]
theorem AlgEquiv.toRatAlgEquiv_toRingEquiv [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S]
    (f : R ≃ₐ[ℚ] S) : (f : R ≃+* S).toRatAlgEquiv = f :=
  rfl

/-- The equivalence between `RingEquiv` and `ℚ`-algebra isomorphisms. -/
def RingEquiv.equivRatAlgEquiv [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] :
    (R ≃+* S) ≃ (R ≃ₐ[ℚ] S) where
  toFun := RingEquiv.toRatAlgEquiv
  invFun := AlgEquiv.toRingEquiv
  left_inv f := RingEquiv.toRingEquiv_toRatAlgEquiv f
  right_inv f := AlgEquiv.toRatAlgEquiv_toRingEquiv f

end
