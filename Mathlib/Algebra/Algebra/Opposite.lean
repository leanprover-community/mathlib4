/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Module.Opposites
import Mathlib.Algebra.Ring.Opposite

/-!
# Algebra structures on the multiplicative opposite

## Main definitions

* `MulOpposite.instAlgebra`: the algebra on `Aᵐᵒᵖ`
* `AlgHom.op`/`AlgHom.unop`: simultaneously convert the domain and codomain of a morphism to the
  opposite algebra.
* `AlgHom.opComm`: swap which side of a morphism lies in the opposite algebra.
* `AlgEquiv.op`/`AlgEquiv.unop`: simultaneously convert the source and target of an isomorphism to
  the opposite algebra.
* `AlgEquiv.opOp`: any algebra is isomorphic to the opposite of its opposite.
* `AlgEquiv.toOpposite`: in a commutative algebra, the opposite algebra is isomorphic to the
  original algebra.
* `AlgEquiv.opComm`: swap which side of an isomorphism lies in the opposite algebra.
-/


variable {R S A B : Type*}

open MulOpposite

section Semiring

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S A] [SMulCommClass R S A]
variable [IsScalarTower R S A]

namespace MulOpposite

variable {R A : Type _} [CommSemiring R] [Semiring A] [Algebra R A]

instance MulOpposite.instAlgebra : Algebra R Aᵐᵒᵖ where
  toRingHom := (algebraMap R A).toOpposite fun x y => Algebra.commutes _ _
  smul_def' c x := unop_injective <| by
    simp only [unop_smul, RingHom.toOpposite_apply, Function.comp_apply, unop_mul, op_mul,
      Algebra.smul_def, Algebra.commutes, op_unop, unop_op]
  commutes' r := MulOpposite.rec' fun x => by
    simp only [RingHom.toOpposite_apply, Function.comp_apply, ← op_mul, Algebra.commutes]
    -- 🎉 no goals

@[simp]
theorem algebraMap_apply (c : R) : algebraMap R Aᵐᵒᵖ c = op (algebraMap R A c) :=
  rfl
#align mul_opposite.algebra_map_apply MulOpposite.algebraMap_apply

end MulOpposite

namespace AlgEquiv
variable (R A)

/-- An algebra is isomorphic to the opposite of its opposite. -/
@[simps!]
def opOp : A ≃ₐ[R] Aᵐᵒᵖᵐᵒᵖ where
  __ := RingEquiv.opOp A
  commutes' _ := rfl

@[simp] theorem toRingEquiv_opOp : (opOp R A : A ≃+* Aᵐᵒᵖᵐᵒᵖ) = RingEquiv.opOp A := rfl

end AlgEquiv

namespace AlgHom

/--
An algebra homomorphism `f : A →ₐ[R] B` such that `f x` commutes with `f y` for all `x, y` defines
an algebra homomorphism from `Aᵐᵒᵖ`. -/
@[simps (config := { fullyApplied := false })]
def fromOpposite (f : A →ₐ[R] B) (hf : ∀ x y, Commute (f x) (f y)) : Aᵐᵒᵖ →ₐ[R] B :=
  { f.toRingHom.fromOpposite hf with
    toFun := f ∘ unop
    commutes' := fun r => f.commutes r }

@[simp]
theorem toLinearMap_fromOpposite (f : A →ₐ[R] B) (hf : ∀ x y, Commute (f x) (f y)) :
    (f.fromOpposite hf : Aᵐᵒᵖ →ₗ[R] B) = f ∘ₗ (opLinearEquiv R).symm.toLinearMap :=
  rfl

@[simp]
theorem toRingHom_fromOpposite (f : A →ₐ[R] B) (hf : ∀ x y, Commute (f x) (f y)) :
    (f.fromOpposite hf : Aᵐᵒᵖ →+* B) = (f : A →+* B).fromOpposite hf :=
  rfl

/--
An algebra homomorphism `f : A →ₐ[R] B` such that `f x` commutes with `f y` for all `x, y` defines
an algebra homomorphism to `Bᵐᵒᵖ`. -/
@[simps (config := { fullyApplied := false })]
def toOpposite (f : A →ₐ[R] B) (hf : ∀ x y, Commute (f x) (f y)) : A →ₐ[R] Bᵐᵒᵖ :=
  { f.toRingHom.toOpposite hf with
    toFun := op ∘ f
    commutes' := fun r => unop_injective <| f.commutes r }

@[simp]
theorem toLinearMap_toOpposite (f : A →ₐ[R] B) (hf : ∀ x y, Commute (f x) (f y)) :
    (f.toOpposite hf : A →ₗ[R] Bᵐᵒᵖ) = (opLinearEquiv R : B ≃ₗ[R] Bᵐᵒᵖ) ∘ₗ f.toLinearMap :=
  rfl

@[simp]
theorem toRingHom_toOpposite (f : A →ₐ[R] B) (hf : ∀ x y, Commute (f x) (f y)) :
    (f.toOpposite hf : A →+* Bᵐᵒᵖ) = (f : A →+* B).toOpposite hf :=
  rfl

/-- An algebra hom `A →ₐ[R] B` can equivalently be viewed as an algebra hom `Aᵐᵒᵖ →ₐ[R] Bᵐᵒᵖ`.
This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps!]
protected def op : (A →ₐ[R] B) ≃ (Aᵐᵒᵖ →ₐ[R] Bᵐᵒᵖ) where
  toFun f := { RingHom.op f.toRingHom with commutes' := fun r => unop_injective <| f.commutes r }
  invFun f := { RingHom.unop f.toRingHom with commutes' := fun r => op_injective <| f.commutes r }
  left_inv _f := AlgHom.ext fun _a => rfl
  right_inv _f := AlgHom.ext fun _a => rfl

theorem toRingHom_op (f : A →ₐ[R] B) : f.op.toRingHom = RingHom.op f.toRingHom :=
  rfl

/-- The 'unopposite' of an algebra hom `Aᵐᵒᵖ →ₐ[R] Bᵐᵒᵖ`. Inverse to `ring_hom.op`. -/
abbrev unop : (Aᵐᵒᵖ →ₐ[R] Bᵐᵒᵖ) ≃ (A →ₐ[R] B) := AlgHom.op.symm

theorem toRingHom_unop (f : Aᵐᵒᵖ →ₐ[R] Bᵐᵒᵖ) : f.unop.toRingHom = RingHom.unop f.toRingHom :=
  rfl

/-- Swap the `ᵐᵒᵖ` on an algebra hom to the opposite side. -/
@[simps!]
def opComm : (A →ₐ[R] Bᵐᵒᵖ) ≃ (Aᵐᵒᵖ →ₐ[R] B) :=
  AlgHom.op.trans <| AlgEquiv.refl.arrowCongr (AlgEquiv.opOp R B).symm

end AlgHom

namespace AlgEquiv

/-- An algebra iso `A ≃ₐ[R] B` can equivalently be viewed as an algebra iso `Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ`.
This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps!]
def op : (A ≃ₐ[R] B) ≃ Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ where
  toFun f :=
    { RingEquiv.op f.toRingEquiv with
      commutes' := fun r => MulOpposite.unop_injective <| f.commutes r }
  invFun f :=
    { RingEquiv.unop f.toRingEquiv with
      commutes' := fun r => MulOpposite.op_injective <| f.commutes r }
  left_inv _f := AlgEquiv.ext fun _a => rfl
  right_inv _f := AlgEquiv.ext fun _a => rfl

theorem toAlgHom_op (f : A ≃ₐ[R] B) :
    (AlgEquiv.op f).toAlgHom = AlgHom.op f.toAlgHom :=
  rfl

theorem toRingEquiv_op (f : A ≃ₐ[R] B) :
    (AlgEquiv.op f).toRingEquiv = RingEquiv.op f.toRingEquiv :=
  rfl

/-- The 'unopposite' of an algebra iso  `Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ`. Inverse to `alg_equiv.op`. -/
abbrev unop : (Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ) ≃ A ≃ₐ[R] B := AlgEquiv.op.symm

theorem toAlgHom_unop (f : Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ) : f.unop.toAlgHom = AlgHom.unop f.toAlgHom :=
  rfl

theorem toRingEquiv_unop (f : Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ) :
    (AlgEquiv.unop f).toRingEquiv = RingEquiv.unop f.toRingEquiv :=
  rfl

/-- Swap the `ᵐᵒᵖ` on an algebra isomorphism to the opposite side. -/
@[simps!]
def opComm : (A ≃ₐ[R] Bᵐᵒᵖ) ≃ (Aᵐᵒᵖ ≃ₐ[R] B) :=
  AlgEquiv.op.trans <| AlgEquiv.refl.equivCongr (opOp R B).symm

end AlgEquiv

end Semiring

section CommSemiring
variable (R A) [CommSemiring R] [CommSemiring A] [Algebra R A]

namespace AlgEquiv

/-- A commutative algebra is isomorphic to its opposite. -/
@[simps!]
def toOpposite : A ≃ₐ[R] Aᵐᵒᵖ where
  __ := RingEquiv.toOpposite A
  commutes' _r := rfl

@[simp] lemma toRingEquiv_toOpposite : (toOpposite R A : A ≃+* Aᵐᵒᵖ) = RingEquiv.toOpposite A := rfl
@[simp] lemma toLinearEquiv_toOpposite : toLinearEquiv (toOpposite R A) = opLinearEquiv R := rfl

end AlgEquiv

end CommSemiring
