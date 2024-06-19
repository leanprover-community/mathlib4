/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin
-/
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.LinearAlgebra.DirectSum.Finsupp

#align_import ring_theory.tensor_product from "leanprover-community/mathlib"@"88fcdc3da43943f5b01925deddaa5bf0c0e85e4e"

/-!
# The tensor product of R-algebras

This file provides results about the multiplicative structure on `A ⊗[R] B` when `R` is a
commutative (semi)ring and `A` and `B` are both `R`-algebras. On these tensor products,
multiplication is characterized by `(a₁ ⊗ₜ b₁) * (a₂ ⊗ₜ b₂) = (a₁ * a₂) ⊗ₜ (b₁ * b₂)`.

## Main declarations

- `LinearMap.baseChange A f` is the `A`-linear map `A ⊗ f`, for an `R`-linear map `f`.
- `Algebra.TensorProduct.semiring`: the ring structure on `A ⊗[R] B` for two `R`-algebras `A`, `B`.
- `Algebra.TensorProduct.leftAlgebra`: the `S`-algebra structure on `A ⊗[R] B`, for when `A` is
  additionally an `S` algebra.
- the structure isomorphisms
  * `Algebra.TensorProduct.lid : R ⊗[R] A ≃ₐ[R] A`
  * `Algebra.TensorProduct.rid : A ⊗[R] R ≃ₐ[S] A` (usually used with `S = R` or `S = A`)
  * `Algebra.TensorProduct.comm : A ⊗[R] B ≃ₐ[R] B ⊗[R] A`
  * `Algebra.TensorProduct.assoc : ((A ⊗[R] B) ⊗[R] C) ≃ₐ[R] (A ⊗[R] (B ⊗[R] C))`
- `Algebra.TensorProduct.liftEquiv`: a universal property for the tensor product of algebras.

## References

* [C. Kassel, *Quantum Groups* (§II.4)][Kassel1995]

-/

suppress_compilation

open scoped TensorProduct

open TensorProduct


namespace LinearMap

open TensorProduct

/-!
### The base-change of a linear map of `R`-modules to a linear map of `A`-modules
-/


section Semiring

variable {R A B M N P : Type*} [CommSemiring R]
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [Module R M] [Module R N] [Module R P]
variable (r : R) (f g : M →ₗ[R] N)
variable (A)

/-- `baseChange A f` for `f : M →ₗ[R] N` is the `A`-linear map `A ⊗[R] M →ₗ[A] A ⊗[R] N`.

This "base change" operation is also known as "extension of scalars". -/
def baseChange (f : M →ₗ[R] N) : A ⊗[R] M →ₗ[A] A ⊗[R] N :=
  AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) f
#align linear_map.base_change LinearMap.baseChange

variable {A}

@[simp]
theorem baseChange_tmul (a : A) (x : M) : f.baseChange A (a ⊗ₜ x) = a ⊗ₜ f x :=
  rfl
#align linear_map.base_change_tmul LinearMap.baseChange_tmul

theorem baseChange_eq_ltensor : (f.baseChange A : A ⊗ M → A ⊗ N) = f.lTensor A :=
  rfl
#align linear_map.base_change_eq_ltensor LinearMap.baseChange_eq_ltensor

@[simp]
theorem baseChange_add : (f + g).baseChange A = f.baseChange A + g.baseChange A := by
  ext
  -- Porting note: added `-baseChange_tmul`
  simp [baseChange_eq_ltensor, -baseChange_tmul]
#align linear_map.base_change_add LinearMap.baseChange_add

@[simp]
theorem baseChange_zero : baseChange A (0 : M →ₗ[R] N) = 0 := by
  ext
  simp [baseChange_eq_ltensor]
#align linear_map.base_change_zero LinearMap.baseChange_zero

@[simp]
theorem baseChange_smul : (r • f).baseChange A = r • f.baseChange A := by
  ext
  simp [baseChange_tmul]
#align linear_map.base_change_smul LinearMap.baseChange_smul

@[simp]
lemma baseChange_id : (.id : M →ₗ[R] M).baseChange A = .id := by
  ext; simp

lemma baseChange_comp (g : N →ₗ[R] P) :
    (g ∘ₗ f).baseChange A = g.baseChange A ∘ₗ f.baseChange A := by
  ext; simp

variable (R M) in
@[simp]
lemma baseChange_one : (1 : Module.End R M).baseChange A = 1 := baseChange_id

lemma baseChange_mul (f g : Module.End R M) :
    (f * g).baseChange A = f.baseChange A * g.baseChange A := by
  ext; simp

variable (R A M N)

/-- `baseChange` as a linear map.

When `M = N`, this is true more strongly as `Module.End.baseChangeHom`. -/
@[simps]
def baseChangeHom : (M →ₗ[R] N) →ₗ[R] A ⊗[R] M →ₗ[A] A ⊗[R] N where
  toFun := baseChange A
  map_add' := baseChange_add
  map_smul' := baseChange_smul
#align linear_map.base_change_hom LinearMap.baseChangeHom

/-- `baseChange` as an `AlgHom`. -/
@[simps!]
def _root_.Module.End.baseChangeHom : Module.End R M →ₐ[R] Module.End A (A ⊗[R] M) :=
  .ofLinearMap (LinearMap.baseChangeHom _ _ _ _) (baseChange_one _ _) baseChange_mul

lemma baseChange_pow (f : Module.End R M) (n : ℕ) :
    (f ^ n).baseChange A = f.baseChange A ^ n :=
  map_pow (Module.End.baseChangeHom _ _ _) f n

end Semiring

section Ring

variable {R A B M N : Type*} [CommRing R]
variable [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (f g : M →ₗ[R] N)

@[simp]
theorem baseChange_sub : (f - g).baseChange A = f.baseChange A - g.baseChange A := by
  ext
  -- Porting note: `tmul_sub` wasn't needed in mathlib3
  simp [baseChange_eq_ltensor, tmul_sub]

#align linear_map.base_change_sub LinearMap.baseChange_sub

@[simp]
theorem baseChange_neg : (-f).baseChange A = -f.baseChange A := by
  ext
  -- Porting note: `tmul_neg` wasn't needed in mathlib3
  simp [baseChange_eq_ltensor, tmul_neg]
#align linear_map.base_change_neg LinearMap.baseChange_neg

end Ring

end LinearMap

namespace Algebra

namespace TensorProduct

universe uR uS uA uB uC uD uE uF
variable {R : Type uR} {S : Type uS}
variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} {E : Type uE} {F : Type uF}

/-!
### The `R`-algebra structure on `A ⊗[R] B`
-/

section AddCommMonoidWithOne

variable [CommSemiring R]
variable [AddCommMonoidWithOne A] [Module R A]
variable [AddCommMonoidWithOne B] [Module R B]

instance : One (A ⊗[R] B) where one := 1 ⊗ₜ 1

theorem one_def : (1 : A ⊗[R] B) = (1 : A) ⊗ₜ (1 : B) :=
  rfl
#align algebra.tensor_product.one_def Algebra.TensorProduct.one_def

instance instAddCommMonoidWithOne : AddCommMonoidWithOne (A ⊗[R] B) where
  natCast n := n ⊗ₜ 1
  natCast_zero := by simp
  natCast_succ n := by simp [add_tmul, one_def]
  add_comm := add_comm

theorem natCast_def (n : ℕ) : (n : A ⊗[R] B) = (n : A) ⊗ₜ (1 : B) := rfl

theorem natCast_def' (n : ℕ) : (n : A ⊗[R] B) = (1 : A) ⊗ₜ (n : B) := by
  rw [natCast_def, ← nsmul_one, smul_tmul, nsmul_one]

end AddCommMonoidWithOne

section NonUnitalNonAssocSemiring

variable [CommSemiring R]
variable [NonUnitalNonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

#noalign algebra.tensor_product.mul_aux
#noalign algebra.tensor_product.mul_aux_apply

/-- (Implementation detail)
The multiplication map on `A ⊗[R] B`,
as an `R`-bilinear map.
-/
def mul : A ⊗[R] B →ₗ[R] A ⊗[R] B →ₗ[R] A ⊗[R] B :=
  TensorProduct.map₂ (LinearMap.mul R A) (LinearMap.mul R B)
#align algebra.tensor_product.mul Algebra.TensorProduct.mul

@[simp]
theorem mul_apply (a₁ a₂ : A) (b₁ b₂ : B) :
    mul (a₁ ⊗ₜ[R] b₁) (a₂ ⊗ₜ[R] b₂) = (a₁ * a₂) ⊗ₜ[R] (b₁ * b₂) :=
  rfl
#align algebra.tensor_product.mul_apply Algebra.TensorProduct.mul_apply

-- providing this instance separately makes some downstream code substantially faster
instance instMul : Mul (A ⊗[R] B) where
  mul a b := mul a b

@[simp]
theorem tmul_mul_tmul (a₁ a₂ : A) (b₁ b₂ : B) :
    a₁ ⊗ₜ[R] b₁ * a₂ ⊗ₜ[R] b₂ = (a₁ * a₂) ⊗ₜ[R] (b₁ * b₂) :=
  rfl
#align algebra.tensor_product.tmul_mul_tmul Algebra.TensorProduct.tmul_mul_tmul

theorem _root_.SemiconjBy.tmul {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B}
    (ha : SemiconjBy a₁ a₂ a₃) (hb : SemiconjBy b₁ b₂ b₃) :
    SemiconjBy (a₁ ⊗ₜ[R] b₁) (a₂ ⊗ₜ[R] b₂) (a₃ ⊗ₜ[R] b₃) :=
  congr_arg₂ (· ⊗ₜ[R] ·) ha.eq hb.eq

nonrec theorem _root_.Commute.tmul {a₁ a₂ : A} {b₁ b₂ : B}
    (ha : Commute a₁ a₂) (hb : Commute b₁ b₂) :
    Commute (a₁ ⊗ₜ[R] b₁) (a₂ ⊗ₜ[R] b₂) :=
  ha.tmul hb

instance instNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (A ⊗[R] B) where
  left_distrib a b c := by simp [HMul.hMul, Mul.mul]
  right_distrib a b c := by simp [HMul.hMul, Mul.mul]
  zero_mul a := by simp [HMul.hMul, Mul.mul]
  mul_zero a := by simp [HMul.hMul, Mul.mul]

-- we want `isScalarTower_right` to take priority since it's better for unification elsewhere
instance (priority := 100) isScalarTower_right [Monoid S] [DistribMulAction S A]
    [IsScalarTower S A A] [SMulCommClass R S A] : IsScalarTower S (A ⊗[R] B) (A ⊗[R] B) where
  smul_assoc r x y := by
    change r • x * y = r • (x * y)
    induction y using TensorProduct.induction_on with
    | zero => simp [smul_zero]
    | tmul a b => induction x using TensorProduct.induction_on with
      | zero => simp [smul_zero]
      | tmul a' b' =>
        dsimp
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', tmul_mul_tmul, smul_mul_assoc]
      | add x y hx hy => simp [smul_add, add_mul _, *]
    | add x y hx hy => simp [smul_add, mul_add _, *]
#align algebra.tensor_product.is_scalar_tower_right Algebra.TensorProduct.isScalarTower_right

-- we want `Algebra.to_smulCommClass` to take priority since it's better for unification elsewhere
instance (priority := 100) sMulCommClass_right [Monoid S] [DistribMulAction S A]
    [SMulCommClass S A A] [SMulCommClass R S A] : SMulCommClass S (A ⊗[R] B) (A ⊗[R] B) where
  smul_comm r x y := by
    change r • (x * y) = x * r • y
    induction y using TensorProduct.induction_on with
    | zero => simp [smul_zero]
    | tmul a b => induction x using TensorProduct.induction_on with
      | zero => simp [smul_zero]
      | tmul a' b' =>
        dsimp
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', tmul_mul_tmul, mul_smul_comm]
      | add x y hx hy => simp [smul_add, add_mul _, *]
    | add x y hx hy => simp [smul_add, mul_add _, *]
#align algebra.tensor_product.smul_comm_class_right Algebra.TensorProduct.sMulCommClass_right

end NonUnitalNonAssocSemiring

section NonAssocSemiring

variable [CommSemiring R]
variable [NonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

protected theorem one_mul (x : A ⊗[R] B) : mul (1 ⊗ₜ 1) x = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_ <;> simp (config := { contextual := true })
#align algebra.tensor_product.one_mul Algebra.TensorProduct.one_mul

protected theorem mul_one (x : A ⊗[R] B) : mul x (1 ⊗ₜ 1) = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_ <;> simp (config := { contextual := true })
#align algebra.tensor_product.mul_one Algebra.TensorProduct.mul_one

instance instNonAssocSemiring : NonAssocSemiring (A ⊗[R] B) where
  one_mul := Algebra.TensorProduct.one_mul
  mul_one := Algebra.TensorProduct.mul_one
  toNonUnitalNonAssocSemiring := instNonUnitalNonAssocSemiring
  __ := instAddCommMonoidWithOne

end NonAssocSemiring

section NonUnitalSemiring
variable [CommSemiring R]
variable [NonUnitalSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonUnitalSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

protected theorem mul_assoc (x y z : A ⊗[R] B) : mul (mul x y) z = mul x (mul y z) := by
  -- restate as an equality of morphisms so that we can use `ext`
  suffices LinearMap.llcomp R _ _ _ mul ∘ₗ mul =
      (LinearMap.llcomp R _ _ _ LinearMap.lflip <| LinearMap.llcomp R _ _ _ mul.flip ∘ₗ mul).flip by
    exact DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun this x) y) z
  ext xa xb ya yb za zb
  exact congr_arg₂ (· ⊗ₜ ·) (mul_assoc xa ya za) (mul_assoc xb yb zb)
#align algebra.tensor_product.mul_assoc Algebra.TensorProduct.mul_assoc

instance instNonUnitalSemiring : NonUnitalSemiring (A ⊗[R] B) where
  mul_assoc := Algebra.TensorProduct.mul_assoc

end NonUnitalSemiring

section Semiring
variable [CommSemiring R]
variable [Semiring A] [Algebra R A]
variable [Semiring B] [Algebra R B]
variable [Semiring C] [Algebra R C]

instance instSemiring : Semiring (A ⊗[R] B) where
  left_distrib a b c := by simp [HMul.hMul, Mul.mul]
  right_distrib a b c := by simp [HMul.hMul, Mul.mul]
  zero_mul a := by simp [HMul.hMul, Mul.mul]
  mul_zero a := by simp [HMul.hMul, Mul.mul]
  mul_assoc := Algebra.TensorProduct.mul_assoc
  one_mul := Algebra.TensorProduct.one_mul
  mul_one := Algebra.TensorProduct.mul_one
  natCast_zero := AddMonoidWithOne.natCast_zero
  natCast_succ := AddMonoidWithOne.natCast_succ

@[simp]
theorem tmul_pow (a : A) (b : B) (k : ℕ) : a ⊗ₜ[R] b ^ k = (a ^ k) ⊗ₜ[R] (b ^ k) := by
  induction' k with k ih
  · simp [one_def]
  · simp [pow_succ, ih]
#align algebra.tensor_product.tmul_pow Algebra.TensorProduct.tmul_pow

/-- The ring morphism `A →+* A ⊗[R] B` sending `a` to `a ⊗ₜ 1`. -/
@[simps]
def includeLeftRingHom : A →+* A ⊗[R] B where
  toFun a := a ⊗ₜ 1
  map_zero' := by simp
  map_add' := by simp [add_tmul]
  map_one' := rfl
  map_mul' := by simp
#align algebra.tensor_product.include_left_ring_hom Algebra.TensorProduct.includeLeftRingHom

variable [CommSemiring S] [Algebra S A]

instance leftAlgebra [SMulCommClass R S A] : Algebra S (A ⊗[R] B) :=
  { commutes' := fun r x => by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply, includeLeftRingHom_apply]
      rw [algebraMap_eq_smul_one, ← smul_tmul', ← one_def, mul_smul_comm, smul_mul_assoc, mul_one,
        one_mul]
    smul_def' := fun r x => by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply, includeLeftRingHom_apply]
      rw [algebraMap_eq_smul_one, ← smul_tmul', smul_mul_assoc, ← one_def, one_mul]
    toRingHom := TensorProduct.includeLeftRingHom.comp (algebraMap S A) }
#align algebra.tensor_product.left_algebra Algebra.TensorProduct.leftAlgebra

example : (algebraNat : Algebra ℕ (ℕ ⊗[ℕ] B)) = leftAlgebra := rfl

-- This is for the `undergrad.yaml` list.
/-- The tensor product of two `R`-algebras is an `R`-algebra. -/
instance instAlgebra : Algebra R (A ⊗[R] B) :=
  inferInstance

@[simp]
theorem algebraMap_apply [SMulCommClass R S A] (r : S) :
    algebraMap S (A ⊗[R] B) r = (algebraMap S A) r ⊗ₜ 1 :=
  rfl
#align algebra.tensor_product.algebra_map_apply Algebra.TensorProduct.algebraMap_apply

theorem algebraMap_apply' (r : R) :
    algebraMap R (A ⊗[R] B) r = 1 ⊗ₜ algebraMap R B r := by
  rw [algebraMap_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_tmul]

/-- The `R`-algebra morphism `A →ₐ[R] A ⊗[R] B` sending `a` to `a ⊗ₜ 1`. -/
def includeLeft [SMulCommClass R S A] : A →ₐ[S] A ⊗[R] B :=
  { includeLeftRingHom with commutes' := by simp }
#align algebra.tensor_product.include_left Algebra.TensorProduct.includeLeft

@[simp]
theorem includeLeft_apply [SMulCommClass R S A] (a : A) :
    (includeLeft : A →ₐ[S] A ⊗[R] B) a = a ⊗ₜ 1 :=
  rfl
#align algebra.tensor_product.include_left_apply Algebra.TensorProduct.includeLeft_apply

/-- The algebra morphism `B →ₐ[R] A ⊗[R] B` sending `b` to `1 ⊗ₜ b`. -/
def includeRight : B →ₐ[R] A ⊗[R] B where
  toFun b := 1 ⊗ₜ b
  map_zero' := by simp
  map_add' := by simp [tmul_add]
  map_one' := rfl
  map_mul' := by simp
  commutes' r := by simp only [algebraMap_apply']
#align algebra.tensor_product.include_right Algebra.TensorProduct.includeRight

@[simp]
theorem includeRight_apply (b : B) : (includeRight : B →ₐ[R] A ⊗[R] B) b = 1 ⊗ₜ b :=
  rfl
#align algebra.tensor_product.include_right_apply Algebra.TensorProduct.includeRight_apply

theorem includeLeftRingHom_comp_algebraMap :
    (includeLeftRingHom.comp (algebraMap R A) : R →+* A ⊗[R] B) =
      includeRight.toRingHom.comp (algebraMap R B) := by
  ext
  simp
#align algebra.tensor_product.include_left_comp_algebra_map Algebra.TensorProduct.includeLeftRingHom_comp_algebraMapₓ

section ext
variable [Algebra R S] [Algebra S C] [IsScalarTower R S A] [IsScalarTower R S C]

/-- A version of `TensorProduct.ext` for `AlgHom`.

Using this as the `@[ext]` lemma instead of `Algebra.TensorProduct.ext'` allows `ext` to apply
lemmas specific to `A →ₐ[S] _` and `B →ₐ[R] _`; notably this allows recursion into nested tensor
products of algebras.

See note [partially-applied ext lemmas]. -/
@[ext high]
theorem ext ⦃f g : (A ⊗[R] B) →ₐ[S] C⦄
    (ha : f.comp includeLeft = g.comp includeLeft)
    (hb : (f.restrictScalars R).comp includeRight = (g.restrictScalars R).comp includeRight) :
    f = g := by
  apply AlgHom.toLinearMap_injective
  ext a b
  have := congr_arg₂ HMul.hMul (AlgHom.congr_fun ha a) (AlgHom.congr_fun hb b)
  dsimp at *
  rwa [← f.map_mul, ← g.map_mul, tmul_mul_tmul, _root_.one_mul, _root_.mul_one] at this

theorem ext' {g h : A ⊗[R] B →ₐ[S] C} (H : ∀ a b, g (a ⊗ₜ b) = h (a ⊗ₜ b)) : g = h :=
  ext (AlgHom.ext fun _ => H _ _) (AlgHom.ext fun _ => H _ _)
#align algebra.tensor_product.ext Algebra.TensorProduct.ext

end ext

end Semiring

section AddCommGroupWithOne
variable [CommSemiring R]
variable [AddCommGroupWithOne A] [Module R A]
variable [AddCommGroupWithOne B] [Module R B]

instance instAddCommGroupWithOne : AddCommGroupWithOne (A ⊗[R] B) where
  toAddCommGroup := TensorProduct.addCommGroup
  __ := instAddCommMonoidWithOne
  intCast z := z ⊗ₜ (1 : B)
  intCast_ofNat n := by simp [natCast_def]
  intCast_negSucc n := by simp [natCast_def, add_tmul, neg_tmul, one_def]

theorem intCast_def (z : ℤ) : (z : A ⊗[R] B) = (z : A) ⊗ₜ (1 : B) := rfl

end AddCommGroupWithOne

section NonUnitalNonAssocRing
variable [CommRing R]
variable [NonUnitalNonAssocRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonUnitalNonAssocRing B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

instance instNonUnitalNonAssocRing : NonUnitalNonAssocRing (A ⊗[R] B) where
  toAddCommGroup := TensorProduct.addCommGroup
  __ := instNonUnitalNonAssocSemiring

end NonUnitalNonAssocRing

section NonAssocRing
variable [CommRing R]
variable [NonAssocRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonAssocRing B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

instance instNonAssocRing : NonAssocRing (A ⊗[R] B) where
  toAddCommGroup := TensorProduct.addCommGroup
  __ := instNonAssocSemiring
  __ := instAddCommGroupWithOne

end NonAssocRing

section NonUnitalRing
variable [CommRing R]
variable [NonUnitalRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
variable [NonUnitalRing B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

instance instNonUnitalRing : NonUnitalRing (A ⊗[R] B) where
  toAddCommGroup := TensorProduct.addCommGroup
  __ := instNonUnitalSemiring

end NonUnitalRing

section CommSemiring
variable [CommSemiring R]
variable [CommSemiring A] [Algebra R A]
variable [CommSemiring B] [Algebra R B]

instance instCommSemiring : CommSemiring (A ⊗[R] B) where
  toSemiring := inferInstance
  mul_comm x y := by
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp
    · intro a₁ b₁
      refine TensorProduct.induction_on y ?_ ?_ ?_
      · simp
      · intro a₂ b₂
        simp [mul_comm]
      · intro a₂ b₂ ha hb
        simp [mul_add, add_mul, ha, hb]
    · intro x₁ x₂ h₁ h₂
      simp [mul_add, add_mul, h₁, h₂]

end CommSemiring

section Ring
variable [CommRing R]
variable [Ring A] [Algebra R A]
variable [Ring B] [Algebra R B]

instance instRing : Ring (A ⊗[R] B) where
  toSemiring := instSemiring
  __ := TensorProduct.addCommGroup
  __ := instNonAssocRing

theorem intCast_def' (z : ℤ) : (z : A ⊗[R] B) = (1 : A) ⊗ₜ (z : B) := by
  rw [intCast_def, ← zsmul_one, smul_tmul, zsmul_one]

-- verify there are no diamonds
example : (instRing : Ring (A ⊗[R] B)).toAddCommGroup = addCommGroup := by
  with_reducible_and_instances rfl
-- fails at `with_reducible_and_instances rfl` #10906
example : (algebraInt _ : Algebra ℤ (ℤ ⊗[ℤ] B)) = leftAlgebra := rfl

end Ring

section CommRing
variable [CommRing R]
variable [CommRing A] [Algebra R A]
variable [CommRing B] [Algebra R B]

instance instCommRing : CommRing (A ⊗[R] B) :=
  { toRing := inferInstance
    mul_comm := mul_comm }

section RightAlgebra

/-- `S ⊗[R] T` has a `T`-algebra structure. This is not a global instance or else the action of
`S` on `S ⊗[R] S` would be ambiguous. -/
abbrev rightAlgebra : Algebra B (A ⊗[R] B) :=
  (Algebra.TensorProduct.includeRight.toRingHom : B →+* A ⊗[R] B).toAlgebra
#align algebra.tensor_product.right_algebra Algebra.TensorProduct.rightAlgebra

attribute [local instance] TensorProduct.rightAlgebra

instance right_isScalarTower : IsScalarTower R B (A ⊗[R] B) :=
  IsScalarTower.of_algebraMap_eq fun r => (Algebra.TensorProduct.includeRight.commutes r).symm
#align algebra.tensor_product.right_is_scalar_tower Algebra.TensorProduct.right_isScalarTower

end RightAlgebra

end CommRing

/-- Verify that typeclass search finds the ring structure on `A ⊗[ℤ] B`
when `A` and `B` are merely rings, by treating both as `ℤ`-algebras.
-/
example [Ring A] [Ring B] : Ring (A ⊗[ℤ] B) := by infer_instance

/-- Verify that typeclass search finds the comm_ring structure on `A ⊗[ℤ] B`
when `A` and `B` are merely comm_rings, by treating both as `ℤ`-algebras.
-/
example [CommRing A] [CommRing B] : CommRing (A ⊗[ℤ] B) := by infer_instance

/-!
We now build the structure maps for the symmetric monoidal category of `R`-algebras.
-/

section Monoidal

section

variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [Semiring B] [Algebra R B]
variable [Semiring C] [Algebra R C] [Algebra S C]
variable [Semiring D] [Algebra R D]

/-- Build an algebra morphism from a linear map out of a tensor product, and evidence that on pure
tensors, it preserves multiplication and the identity.

Note that we state `h_one` using `1 ⊗ₜ[R] 1` instead of `1` so that lemmas about `f` applied to pure
tensors can be directly applied by the caller (without needing `TensorProduct.one_def`).
-/
def algHomOfLinearMapTensorProduct (f : A ⊗[R] B →ₗ[S] C)
    (h_mul : ∀ (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) ⊗ₜ (b₁ * b₂)) = f (a₁ ⊗ₜ b₁) * f (a₂ ⊗ₜ b₂))
    (h_one : f (1 ⊗ₜ[R] 1) = 1) : A ⊗[R] B →ₐ[S] C :=
  #adaptation_note
  /--
  After https://github.com/leanprover/lean4/pull/4119 we either need to specify
  the `(R := S) (A := A ⊗[R] B)` arguments, or use `set_option maxSynthPendingDepth 2 in`.
  -/
  AlgHom.ofLinearMap f h_one <| (f.map_mul_iff (R := S) (A := A ⊗[R] B)).2 <| by
    -- these instances are needed by the statement of `ext`, but not by the current definition.
    letI : Algebra R C := RestrictScalars.algebra R S C
    letI : IsScalarTower R S C := RestrictScalars.isScalarTower R S C
    ext
    exact h_mul _ _ _ _
#align algebra.tensor_product.alg_hom_of_linear_map_tensor_product Algebra.TensorProduct.algHomOfLinearMapTensorProduct

@[simp]
theorem algHomOfLinearMapTensorProduct_apply (f h_mul h_one x) :
    (algHomOfLinearMapTensorProduct f h_mul h_one : A ⊗[R] B →ₐ[S] C) x = f x :=
  rfl
#align algebra.tensor_product.alg_hom_of_linear_map_tensor_product_apply Algebra.TensorProduct.algHomOfLinearMapTensorProduct_apply

/-- Build an algebra equivalence from a linear equivalence out of a tensor product, and evidence
that on pure tensors, it preserves multiplication and the identity.

Note that we state `h_one` using `1 ⊗ₜ[R] 1` instead of `1` so that lemmas about `f` applied to pure
tensors can be directly applied by the caller (without needing `TensorProduct.one_def`).
-/
def algEquivOfLinearEquivTensorProduct (f : A ⊗[R] B ≃ₗ[S] C)
    (h_mul : ∀ (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) ⊗ₜ (b₁ * b₂)) = f (a₁ ⊗ₜ b₁) * f (a₂ ⊗ₜ b₂))
    (h_one : f (1 ⊗ₜ[R] 1) = 1) : A ⊗[R] B ≃ₐ[S] C :=
  { algHomOfLinearMapTensorProduct (f : A ⊗[R] B →ₗ[S] C) h_mul h_one, f with }
#align algebra.tensor_product.alg_equiv_of_linear_equiv_tensor_product Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct

@[simp]
theorem algEquivOfLinearEquivTensorProduct_apply (f h_mul h_one x) :
    (algEquivOfLinearEquivTensorProduct f h_mul h_one : A ⊗[R] B ≃ₐ[S] C) x = f x :=
  rfl
#align algebra.tensor_product.alg_equiv_of_linear_equiv_tensor_product_apply Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct_apply

/-- Build an algebra equivalence from a linear equivalence out of a triple tensor product,
and evidence of multiplicativity on pure tensors.
-/
def algEquivOfLinearEquivTripleTensorProduct (f : (A ⊗[R] B) ⊗[R] C ≃ₗ[R] D)
    (h_mul :
      ∀ (a₁ a₂ : A) (b₁ b₂ : B) (c₁ c₂ : C),
        f ((a₁ * a₂) ⊗ₜ (b₁ * b₂) ⊗ₜ (c₁ * c₂)) = f (a₁ ⊗ₜ b₁ ⊗ₜ c₁) * f (a₂ ⊗ₜ b₂ ⊗ₜ c₂))
    (h_one : f (((1 : A) ⊗ₜ[R] (1 : B)) ⊗ₜ[R] (1 : C)) = 1) :
    (A ⊗[R] B) ⊗[R] C ≃ₐ[R] D :=
  AlgEquiv.ofLinearEquiv f h_one <| f.map_mul_iff.2 <| by
    ext
    exact h_mul _ _ _ _ _ _
#align algebra.tensor_product.alg_equiv_of_linear_equiv_triple_tensor_product Algebra.TensorProduct.algEquivOfLinearEquivTripleTensorProduct

@[simp]
theorem algEquivOfLinearEquivTripleTensorProduct_apply (f h_mul h_one x) :
    (algEquivOfLinearEquivTripleTensorProduct f h_mul h_one : (A ⊗[R] B) ⊗[R] C ≃ₐ[R] D) x = f x :=
  rfl
#align algebra.tensor_product.alg_equiv_of_linear_equiv_triple_tensor_product_apply Algebra.TensorProduct.algEquivOfLinearEquivTripleTensorProduct_apply

section lift
variable [IsScalarTower R S C]

/-- The forward direction of the universal property of tensor products of algebras; any algebra
morphism from the tensor product can be factored as the product of two algebra morphisms that
commute.

See `Algebra.TensorProduct.liftEquiv` for the fact that every morphism factors this way. -/
def lift (f : A →ₐ[S] C) (g : B →ₐ[R] C) (hfg : ∀ x y, Commute (f x) (g y)) : (A ⊗[R] B) →ₐ[S] C :=
  algHomOfLinearMapTensorProduct
    (AlgebraTensorModule.lift <|
      letI restr : (C →ₗ[S] C) →ₗ[S] _ :=
        { toFun := (·.restrictScalars R)
          map_add' := fun f g => LinearMap.ext fun x => rfl
          map_smul' := fun c g => LinearMap.ext fun x => rfl }
      LinearMap.flip <| (restr ∘ₗ LinearMap.mul S C ∘ₗ f.toLinearMap).flip ∘ₗ g)
    (fun a₁ a₂ b₁ b₂ => show f (a₁ * a₂) * g (b₁ * b₂) = f a₁ * g b₁ * (f a₂ * g b₂) by
      rw [f.map_mul, g.map_mul, (hfg a₂ b₁).mul_mul_mul_comm])
    (show f 1 * g 1 = 1 by rw [f.map_one, g.map_one, one_mul])

@[simp]
theorem lift_tmul (f : A →ₐ[S] C) (g : B →ₐ[R] C) (hfg : ∀ x y, Commute (f x) (g y))
    (a : A) (b : B) :
    lift f g hfg (a ⊗ₜ b) = f a * g b :=
  rfl

@[simp]
theorem lift_includeLeft_includeRight :
    lift includeLeft includeRight (fun a b => (Commute.one_right _).tmul (Commute.one_left _)) =
      .id S (A ⊗[R] B) := by
  ext <;> simp

@[simp]
theorem lift_comp_includeLeft (f : A →ₐ[S] C) (g : B →ₐ[R] C) (hfg : ∀ x y, Commute (f x) (g y)) :
    (lift f g hfg).comp includeLeft = f :=
  AlgHom.ext <| by simp

@[simp]
theorem lift_comp_includeRight (f : A →ₐ[S] C) (g : B →ₐ[R] C) (hfg : ∀ x y, Commute (f x) (g y)) :
    ((lift f g hfg).restrictScalars R).comp includeRight = g :=
  AlgHom.ext <| by simp

/-- The universal property of the tensor product of algebras.

Pairs of algebra morphisms that commute are equivalent to algebra morphisms from the tensor product.

This is `Algebra.TensorProduct.lift` as an equivalence.

See also `GradedTensorProduct.liftEquiv` for an alternative commutativity requirement for graded
algebra. -/
@[simps]
def liftEquiv : {fg : (A →ₐ[S] C) × (B →ₐ[R] C) // ∀ x y, Commute (fg.1 x) (fg.2 y)}
    ≃ ((A ⊗[R] B) →ₐ[S] C) where
  toFun fg := lift fg.val.1 fg.val.2 fg.prop
  invFun f' := ⟨(f'.comp includeLeft, (f'.restrictScalars R).comp includeRight), fun x y =>
    ((Commute.one_right _).tmul (Commute.one_left _)).map f'⟩
  left_inv fg := by ext <;> simp
  right_inv f' := by ext <;> simp

end lift

end

variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [Semiring B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
variable [Semiring C] [Algebra R C] [Algebra S C] [IsScalarTower R S C]
variable [Semiring D] [Algebra R D]
variable [Semiring E] [Algebra R E]
variable [Semiring F] [Algebra R F]

section

variable (R A)

/-- The base ring is a left identity for the tensor product of algebra, up to algebra isomorphism.
-/
protected nonrec def lid : R ⊗[R] A ≃ₐ[R] A :=
  algEquivOfLinearEquivTensorProduct (TensorProduct.lid R A) (by
    simp only [mul_smul, lid_tmul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
    simp_rw [← mul_smul, mul_comm]
    simp)
    (by simp [Algebra.smul_def])
#align algebra.tensor_product.lid Algebra.TensorProduct.lid

@[simp] theorem lid_toLinearEquiv :
    (TensorProduct.lid R A).toLinearEquiv = _root_.TensorProduct.lid R A := rfl

variable {R} {A} in
@[simp]
theorem lid_tmul (r : R) (a : A) : TensorProduct.lid R A (r ⊗ₜ a) = r • a := rfl
#align algebra.tensor_product.lid_tmul Algebra.TensorProduct.lid_tmul

variable {A} in
@[simp]
theorem lid_symm_apply (a : A) : (TensorProduct.lid R A).symm a = 1 ⊗ₜ a := rfl

variable (S)

/-- The base ring is a right identity for the tensor product of algebra, up to algebra isomorphism.

Note that if `A` is commutative this can be instantiated with `S = A`.
-/
protected nonrec def rid : A ⊗[R] R ≃ₐ[S] A :=
  algEquivOfLinearEquivTensorProduct (AlgebraTensorModule.rid R S A)
    (fun a₁ a₂ r₁ r₂ => smul_mul_smul r₁ r₂ a₁ a₂ |>.symm)
    (one_smul R _)
#align algebra.tensor_product.rid Algebra.TensorProduct.rid

@[simp] theorem rid_toLinearEquiv :
    (TensorProduct.rid R S A).toLinearEquiv = AlgebraTensorModule.rid R S A := rfl

variable {R A} in
@[simp]
theorem rid_tmul (r : R) (a : A) : TensorProduct.rid R S A (a ⊗ₜ r) = r • a := rfl
#align algebra.tensor_product.rid_tmul Algebra.TensorProduct.rid_tmul

variable {A} in
@[simp]
theorem rid_symm_apply (a : A) : (TensorProduct.rid R S A).symm a = a ⊗ₜ 1 := rfl

section

variable (B)

/-- The tensor product of R-algebras is commutative, up to algebra isomorphism.
-/
protected def comm : A ⊗[R] B ≃ₐ[R] B ⊗[R] A :=
  algEquivOfLinearEquivTensorProduct (_root_.TensorProduct.comm R A B) (fun _ _ _ _ => rfl) rfl
#align algebra.tensor_product.comm Algebra.TensorProduct.comm

@[simp] theorem comm_toLinearEquiv :
    (Algebra.TensorProduct.comm R A B).toLinearEquiv = _root_.TensorProduct.comm R A B := rfl

variable {A B} in
@[simp]
theorem comm_tmul (a : A) (b : B) :
    TensorProduct.comm R A B (a ⊗ₜ b) = b ⊗ₜ a :=
  rfl
#align algebra.tensor_product.comm_tmul Algebra.TensorProduct.comm_tmul

variable {A B} in
@[simp]
theorem comm_symm_tmul (a : A) (b : B) :
    (TensorProduct.comm R A B).symm (b ⊗ₜ a) = a ⊗ₜ b :=
  rfl

theorem comm_symm :
    (TensorProduct.comm R A B).symm = TensorProduct.comm R B A := by
  ext; rfl

theorem adjoin_tmul_eq_top : adjoin R { t : A ⊗[R] B | ∃ a b, a ⊗ₜ[R] b = t } = ⊤ :=
  top_le_iff.mp <| (top_le_iff.mpr <| span_tmul_eq_top R A B).trans (span_le_adjoin R _)
#align algebra.tensor_product.adjoin_tmul_eq_top Algebra.TensorProduct.adjoin_tmul_eq_top

end

section

variable {R A}

theorem assoc_aux_1 (a₁ a₂ : A) (b₁ b₂ : B) (c₁ c₂ : C) :
    (TensorProduct.assoc R A B C) (((a₁ * a₂) ⊗ₜ[R] (b₁ * b₂)) ⊗ₜ[R] (c₁ * c₂)) =
      (TensorProduct.assoc R A B C) ((a₁ ⊗ₜ[R] b₁) ⊗ₜ[R] c₁) *
        (TensorProduct.assoc R A B C) ((a₂ ⊗ₜ[R] b₂) ⊗ₜ[R] c₂) :=
  rfl
#align algebra.tensor_product.assoc_aux_1 Algebra.TensorProduct.assoc_aux_1

theorem assoc_aux_2 : (TensorProduct.assoc R A B C) ((1 ⊗ₜ[R] 1) ⊗ₜ[R] 1) = 1 :=
  rfl
#align algebra.tensor_product.assoc_aux_2 Algebra.TensorProduct.assoc_aux_2ₓ

variable (R A B C)

-- Porting note: much nicer than Lean 3 proof
/-- The associator for tensor product of R-algebras, as an algebra isomorphism. -/
protected def assoc : (A ⊗[R] B) ⊗[R] C ≃ₐ[R] A ⊗[R] B ⊗[R] C :=
  algEquivOfLinearEquivTripleTensorProduct
    (_root_.TensorProduct.assoc R A B C)
    Algebra.TensorProduct.assoc_aux_1
    Algebra.TensorProduct.assoc_aux_2
#align algebra.tensor_product.assoc Algebra.TensorProduct.assoc

@[simp] theorem assoc_toLinearEquiv :
  (Algebra.TensorProduct.assoc R A B C).toLinearEquiv = _root_.TensorProduct.assoc R A B C := rfl

variable {A B C}

@[simp]
theorem assoc_tmul (a : A) (b : B) (c : C) :
    Algebra.TensorProduct.assoc R A B C ((a ⊗ₜ b) ⊗ₜ c) = a ⊗ₜ (b ⊗ₜ c) :=
  rfl
#align algebra.tensor_product.assoc_tmul Algebra.TensorProduct.assoc_tmul

@[simp]
theorem assoc_symm_tmul (a : A) (b : B) (c : C) :
    (Algebra.TensorProduct.assoc R A B C).symm (a ⊗ₜ (b ⊗ₜ c)) = (a ⊗ₜ b) ⊗ₜ c :=
  rfl

end

variable {R S A}

/-- The tensor product of a pair of algebra morphisms. -/
def map (f : A →ₐ[S] B) (g : C →ₐ[R] D) : A ⊗[R] C →ₐ[S] B ⊗[R] D :=
  algHomOfLinearMapTensorProduct (AlgebraTensorModule.map f.toLinearMap g.toLinearMap) (by simp)
    (by simp [one_def])
#align algebra.tensor_product.map Algebra.TensorProduct.map

@[simp]
theorem map_tmul (f : A →ₐ[S] B) (g : C →ₐ[R] D) (a : A) (c : C) : map f g (a ⊗ₜ c) = f a ⊗ₜ g c :=
  rfl
#align algebra.tensor_product.map_tmul Algebra.TensorProduct.map_tmul

@[simp]
theorem map_id : map (.id S A) (.id R C) = .id S _ :=
  ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)

theorem map_comp (f₂ : B →ₐ[S] C) (f₁ : A →ₐ[S] B) (g₂ : E →ₐ[R] F) (g₁ : D →ₐ[R] E) :
    map (f₂.comp f₁) (g₂.comp g₁) = (map f₂ g₂).comp (map f₁ g₁) :=
  ext (AlgHom.ext fun _ => rfl) (AlgHom.ext fun _ => rfl)

@[simp]
theorem map_comp_includeLeft (f : A →ₐ[S] B) (g : C →ₐ[R] D) :
    (map f g).comp includeLeft = includeLeft.comp f :=
  AlgHom.ext <| by simp
#align algebra.tensor_product.map_comp_include_left Algebra.TensorProduct.map_comp_includeLeft

@[simp]
theorem map_restrictScalars_comp_includeRight (f : A →ₐ[S] B) (g : C →ₐ[R] D) :
    ((map f g).restrictScalars R).comp includeRight = includeRight.comp g :=
  AlgHom.ext <| by simp

@[simp]
theorem map_comp_includeRight (f : A →ₐ[R] B) (g : C →ₐ[R] D) :
    (map f g).comp includeRight = includeRight.comp g :=
  map_restrictScalars_comp_includeRight f g

#align algebra.tensor_product.map_comp_include_right Algebra.TensorProduct.map_comp_includeRight

theorem map_range (f : A →ₐ[R] B) (g : C →ₐ[R] D) :
    (map f g).range = (includeLeft.comp f).range ⊔ (includeRight.comp g).range := by
  apply le_antisymm
  · rw [← map_top, ← adjoin_tmul_eq_top, ← adjoin_image, adjoin_le_iff]
    rintro _ ⟨_, ⟨a, b, rfl⟩, rfl⟩
    rw [map_tmul, ← _root_.mul_one (f a), ← _root_.one_mul (g b), ← tmul_mul_tmul]
    exact mul_mem_sup (AlgHom.mem_range_self _ a) (AlgHom.mem_range_self _ b)
  · rw [← map_comp_includeLeft f g, ← map_comp_includeRight f g]
    exact sup_le (AlgHom.range_comp_le_range _ _) (AlgHom.range_comp_le_range _ _)
#align algebra.tensor_product.map_range Algebra.TensorProduct.map_range

/-- Construct an isomorphism between tensor products of an S-algebra with an R-algebra
from S- and R- isomorphisms between the tensor factors.
-/
def congr (f : A ≃ₐ[S] B) (g : C ≃ₐ[R] D) : A ⊗[R] C ≃ₐ[S] B ⊗[R] D :=
  AlgEquiv.ofAlgHom (map f g) (map f.symm g.symm)
    (ext' fun b d => by simp) (ext' fun a c => by simp)
#align algebra.tensor_product.congr Algebra.TensorProduct.congr

@[simp] theorem congr_toLinearEquiv (f : A ≃ₐ[S] B) (g : C ≃ₐ[R] D) :
    (Algebra.TensorProduct.congr f g).toLinearEquiv =
      TensorProduct.AlgebraTensorModule.congr f.toLinearEquiv g.toLinearEquiv := rfl

@[simp]
theorem congr_apply (f : A ≃ₐ[S] B) (g : C ≃ₐ[R] D) (x) :
    congr f g x = (map (f : A →ₐ[S] B) (g : C →ₐ[R] D)) x :=
  rfl
#align algebra.tensor_product.congr_apply Algebra.TensorProduct.congr_apply

@[simp]
theorem congr_symm_apply (f : A ≃ₐ[S] B) (g : C ≃ₐ[R] D) (x) :
    (congr f g).symm x = (map (f.symm : B →ₐ[S] A) (g.symm : D →ₐ[R] C)) x :=
  rfl
#align algebra.tensor_product.congr_symm_apply Algebra.TensorProduct.congr_symm_apply

@[simp]
theorem congr_refl : congr (.refl : A ≃ₐ[S] A) (.refl : C ≃ₐ[R] C) = .refl :=
  AlgEquiv.coe_algHom_injective <| map_id

theorem congr_trans (f₁ : A ≃ₐ[S] B) (f₂ : B ≃ₐ[S] C) (g₁ : D ≃ₐ[R] E) (g₂ : E ≃ₐ[R] F) :
    congr (f₁.trans f₂) (g₁.trans g₂) = (congr f₁ g₁).trans (congr f₂ g₂) :=
  AlgEquiv.coe_algHom_injective <| map_comp f₂.toAlgHom f₁.toAlgHom g₂.toAlgHom g₁.toAlgHom

theorem congr_symm (f : A ≃ₐ[S] B) (g : C ≃ₐ[R] D) : congr f.symm g.symm = (congr f g).symm := rfl

end

end Monoidal

section

variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [Semiring B] [Algebra R B]
variable [CommSemiring C] [Algebra R C] [Algebra S C] [IsScalarTower R S C]

/-- If `A`, `B`, `C` are `R`-algebras, `A` and `C` are also `S`-algebras (forming a tower as
`·/S/R`), then the product map of `f : A →ₐ[S] C` and `g : B →ₐ[R] C` is an `S`-algebra
homomorphism.

This is just a special case of `Algebra.TensorProduct.lift` for when `C` is commutative. -/
abbrev productLeftAlgHom (f : A →ₐ[S] C) (g : B →ₐ[R] C) : A ⊗[R] B →ₐ[S] C :=
  lift f g (fun _ _ => Commute.all _ _)
#align algebra.tensor_product.product_left_alg_hom Algebra.TensorProduct.productLeftAlgHom

end

section

variable [CommSemiring R] [Semiring A] [Semiring B] [CommSemiring S]
variable [Algebra R A] [Algebra R B] [Algebra R S]
variable (f : A →ₐ[R] S) (g : B →ₐ[R] S)
variable (R)

/-- `LinearMap.mul'` is an `AlgHom` on commutative rings. -/
def lmul' : S ⊗[R] S →ₐ[R] S :=
  algHomOfLinearMapTensorProduct (LinearMap.mul' R S)
    (fun a₁ a₂ b₁ b₂ => by simp only [LinearMap.mul'_apply, mul_mul_mul_comm]) <| by
    simp only [LinearMap.mul'_apply, _root_.mul_one]
#align algebra.tensor_product.lmul' Algebra.TensorProduct.lmul'

variable {R}

theorem lmul'_toLinearMap : (lmul' R : _ →ₐ[R] S).toLinearMap = LinearMap.mul' R S :=
  rfl
#align algebra.tensor_product.lmul'_to_linear_map Algebra.TensorProduct.lmul'_toLinearMap

@[simp]
theorem lmul'_apply_tmul (a b : S) : lmul' (S := S) R (a ⊗ₜ[R] b) = a * b :=
  rfl
#align algebra.tensor_product.lmul'_apply_tmul Algebra.TensorProduct.lmul'_apply_tmul

@[simp]
theorem lmul'_comp_includeLeft : (lmul' R : _ →ₐ[R] S).comp includeLeft = AlgHom.id R S :=
  AlgHom.ext <| _root_.mul_one
#align algebra.tensor_product.lmul'_comp_include_left Algebra.TensorProduct.lmul'_comp_includeLeft

@[simp]
theorem lmul'_comp_includeRight : (lmul' R : _ →ₐ[R] S).comp includeRight = AlgHom.id R S :=
  AlgHom.ext <| _root_.one_mul
#align algebra.tensor_product.lmul'_comp_include_right Algebra.TensorProduct.lmul'_comp_includeRight

/-- If `S` is commutative, for a pair of morphisms `f : A →ₐ[R] S`, `g : B →ₐ[R] S`,
We obtain a map `A ⊗[R] B →ₐ[R] S` that commutes with `f`, `g` via `a ⊗ b ↦ f(a) * g(b)`.

This is a special case of `Algebra.TensorProduct.productLeftAlgHom` for when the two base rings are
the same.
-/
def productMap : A ⊗[R] B →ₐ[R] S := productLeftAlgHom f g
#align algebra.tensor_product.product_map Algebra.TensorProduct.productMap

theorem productMap_eq_comp_map : productMap f g = (lmul' R).comp (TensorProduct.map f g) := by
  ext <;> rfl

@[simp]
theorem productMap_apply_tmul (a : A) (b : B) : productMap f g (a ⊗ₜ b) = f a * g b := rfl

#align algebra.tensor_product.product_map_apply_tmul Algebra.TensorProduct.productMap_apply_tmul

theorem productMap_left_apply (a : A) : productMap f g (a ⊗ₜ 1) = f a := by
  simp
#align algebra.tensor_product.product_map_left_apply Algebra.TensorProduct.productMap_left_apply

@[simp]
theorem productMap_left : (productMap f g).comp includeLeft = f :=
  lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _)
#align algebra.tensor_product.product_map_left Algebra.TensorProduct.productMap_left

theorem productMap_right_apply (b : B) :
    productMap f g (1 ⊗ₜ b) = g b := by simp
#align algebra.tensor_product.product_map_right_apply Algebra.TensorProduct.productMap_right_apply

@[simp]
theorem productMap_right : (productMap f g).comp includeRight = g :=
  lift_comp_includeRight _ _ (fun _ _ => Commute.all _ _)
#align algebra.tensor_product.product_map_right Algebra.TensorProduct.productMap_right

theorem productMap_range : (productMap f g).range = f.range ⊔ g.range := by
  rw [productMap_eq_comp_map, AlgHom.range_comp, map_range, map_sup, ← AlgHom.range_comp,
    ← AlgHom.range_comp,
    ← AlgHom.comp_assoc, ← AlgHom.comp_assoc, lmul'_comp_includeLeft, lmul'_comp_includeRight,
    AlgHom.id_comp, AlgHom.id_comp]
#align algebra.tensor_product.product_map_range Algebra.TensorProduct.productMap_range

end

section Basis

universe uM uι
variable {M : Type uM} {ι : Type uι}
variable [CommSemiring R] [Semiring A] [Algebra R A]
variable [AddCommMonoid M] [Module R M] (b : Basis ι R M)
variable (A)

/-- Given an `R`-algebra `A` and an `R`-basis of `M`, this is an `R`-linear isomorphism
`A ⊗[R] M ≃ (ι →₀ A)` (which is in fact `A`-linear). -/
noncomputable def basisAux : A ⊗[R] M ≃ₗ[R] ι →₀ A :=
  _root_.TensorProduct.congr (Finsupp.LinearEquiv.finsuppUnique R A PUnit.{uι+1}).symm b.repr ≪≫ₗ
    (finsuppTensorFinsupp R R A R PUnit ι).trans
      (Finsupp.lcongr (Equiv.uniqueProd ι PUnit) (_root_.TensorProduct.rid R A))
#align algebra.tensor_product.basis_aux Algebra.TensorProduct.basisAux

variable {A}

theorem basisAux_tmul (a : A) (m : M) :
    basisAux A b (a ⊗ₜ m) = a • Finsupp.mapRange (algebraMap R A) (map_zero _) (b.repr m) := by
  ext
  simp [basisAux, ← Algebra.commutes, Algebra.smul_def]
#align algebra.tensor_product.basis_aux_tmul Algebra.TensorProduct.basisAux_tmul

theorem basisAux_map_smul (a : A) (x : A ⊗[R] M) : basisAux A b (a • x) = a • basisAux A b x :=
  TensorProduct.induction_on x (by simp)
    (fun x y => by simp only [TensorProduct.smul_tmul', basisAux_tmul, smul_assoc])
    fun x y hx hy => by simp [hx, hy]
#align algebra.tensor_product.basis_aux_map_smul Algebra.TensorProduct.basisAux_map_smul

variable (A)

/-- Given a `R`-algebra `A`, this is the `A`-basis of `A ⊗[R] M` induced by a `R`-basis of `M`. -/
noncomputable def basis : Basis ι A (A ⊗[R] M) where
  repr := { basisAux A b with map_smul' := basisAux_map_smul b }
#align algebra.tensor_product.basis Algebra.TensorProduct.basis

variable {A}

@[simp]
theorem basis_repr_tmul (a : A) (m : M) :
    (basis A b).repr (a ⊗ₜ m) = a • Finsupp.mapRange (algebraMap R A) (map_zero _) (b.repr m) :=
  basisAux_tmul b a m -- Porting note: Lean 3 had _ _ _
#align algebra.tensor_product.basis_repr_tmul Algebra.TensorProduct.basis_repr_tmul

theorem basis_repr_symm_apply (a : A) (i : ι) :
    (basis A b).repr.symm (Finsupp.single i a) = a ⊗ₜ b.repr.symm (Finsupp.single i 1) := by
  rw [basis, LinearEquiv.coe_symm_mk] -- Porting note: `coe_symm_mk` isn't firing in `simp`
  simp [Equiv.uniqueProd_symm_apply, basisAux]

@[simp]
theorem basis_apply (i : ι) : basis A b i = 1 ⊗ₜ b i := basis_repr_symm_apply b 1 i

theorem basis_repr_symm_apply' (a : A) (i : ι) : a • basis A b i = a ⊗ₜ b i := by
  simpa using basis_repr_symm_apply b a i

section baseChange

open LinearMap

variable [Fintype ι]
variable {ι' N : Type*} [Fintype ι'] [DecidableEq ι'] [AddCommMonoid N] [Module R N]
variable (A : Type*) [CommSemiring A] [Algebra R A]

lemma _root_.Basis.baseChange_linearMap (b : Basis ι R M) (b' : Basis ι' R N) (ij : ι × ι') :
    baseChange A (b'.linearMap b ij) = (basis A b').linearMap (basis A b) ij := by
  apply (basis A b').ext
  intro k
  conv_lhs => simp only [basis_apply, baseChange_tmul]
  simp_rw [Basis.linearMap_apply_apply, basis_apply]
  split <;> simp only [TensorProduct.tmul_zero]

variable [DecidableEq ι]

lemma _root_.Basis.baseChange_end (b : Basis ι R M) (ij : ι × ι) :
    baseChange A (b.end ij) = (basis A b).end ij :=
  b.baseChange_linearMap A b ij

end baseChange

end Basis

instance (R A M : Type*)
    [CommSemiring R] [AddCommMonoid M] [Module R M] [Module.Free R M]
    [CommSemiring A] [Algebra R A] :
    Module.Free A (A ⊗[R] M) :=
  Module.Free.of_basis <| Algebra.TensorProduct.basis A (Module.Free.chooseBasis R M)

end TensorProduct

end Algebra

namespace LinearMap

open Algebra.TensorProduct

variable {R M₁ M₂ ι ι₂ : Type*} (A : Type*)
  [Fintype ι] [Finite ι₂] [DecidableEq ι] [DecidableEq ι₂]
  [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]

@[simp]
lemma toMatrix_baseChange (f : M₁ →ₗ[R] M₂) (b₁ : Basis ι R M₁) (b₂ : Basis ι₂ R M₂) :
    toMatrix (basis A b₁) (basis A b₂) (f.baseChange A) =
    (toMatrix b₁ b₂ f).map (algebraMap R A) := by
  ext; simp [toMatrix_apply]

end LinearMap

namespace LinearMap

variable (R A M N : Type*) [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

open Module
open scoped TensorProduct

/-- The natural linear map $A ⊗ \text{Hom}_R(M, N) → \text{Hom}_A (M_A, N_A)$,
where $M_A$ and $N_A$ are the respective modules over $A$ obtained by extension of scalars.

See `LinearMap.tensorProductEnd` for this map specialized to endomorphisms,
and bundled as `A`-algebra homomorphism. -/
@[simps!]
noncomputable
def tensorProduct : A ⊗[R] (M →ₗ[R] N) →ₗ[A] (A ⊗[R] M) →ₗ[A] (A ⊗[R] N) :=
  TensorProduct.AlgebraTensorModule.lift <|
  { toFun := fun a ↦ a • baseChangeHom R A M N
    map_add' := by simp only [add_smul, forall_true_iff]
    map_smul' := by simp only [smul_assoc, RingHom.id_apply, forall_true_iff] }

/-- The natural `A`-algebra homomorphism $A ⊗ (\text{End}_R M) → \text{End}_A (A ⊗ M)$,
where `M` is an `R`-module, and `A` an `R`-algebra. -/
@[simps!]
noncomputable
def tensorProductEnd : A ⊗[R] (End R M) →ₐ[A] End A (A ⊗[R] M) :=
  Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (LinearMap.tensorProduct R A M M)
    (fun a b f g ↦ by
      apply LinearMap.ext
      intro x
      simp only [tensorProduct, mul_comm a b, mul_eq_comp,
        TensorProduct.AlgebraTensorModule.lift_apply, TensorProduct.lift.tmul, coe_restrictScalars,
        coe_mk, AddHom.coe_mk, mul_smul, smul_apply, baseChangeHom_apply, baseChange_comp,
        comp_apply, Algebra.mul_smul_comm, Algebra.smul_mul_assoc])
    (by
      apply LinearMap.ext
      intro x
      simp only [tensorProduct, TensorProduct.AlgebraTensorModule.lift_apply,
        TensorProduct.lift.tmul, coe_restrictScalars, coe_mk, AddHom.coe_mk, one_smul,
        baseChangeHom_apply, baseChange_eq_ltensor, one_apply, one_eq_id, lTensor_id,
        LinearMap.id_apply])

end LinearMap

namespace Module

variable {R S A M N : Type*} [CommSemiring R] [CommSemiring S] [Semiring A]
variable [AddCommMonoid M] [AddCommMonoid N]
variable [Algebra R S] [Algebra S A] [Algebra R A]
variable [Module R M] [Module S M] [Module A M] [Module R N]
variable [IsScalarTower R A M] [IsScalarTower S A M] [IsScalarTower R S M]

/-- The algebra homomorphism from `End M ⊗ End N` to `End (M ⊗ N)` sending `f ⊗ₜ g` to
the `TensorProduct.map f g`, the tensor product of the two maps.

This is an `AlgHom` version of `TensorProduct.AlgebraTensorModule.homTensorHomMap`. Like that
definition, this is generalized across many different rings; namely a tower of algebras `A/S/R`. -/
def endTensorEndAlgHom : End A M ⊗[R] End R N →ₐ[S] End A (M ⊗[R] N) :=
  Algebra.TensorProduct.algHomOfLinearMapTensorProduct
    (AlgebraTensorModule.homTensorHomMap R A S M N M N)
    (fun _f₁ _f₂ _g₁ _g₂ => AlgebraTensorModule.ext fun _m _n => rfl)
    (AlgebraTensorModule.ext fun _m _n => rfl)
#align module.End_tensor_End_alg_hom Module.endTensorEndAlgHom

theorem endTensorEndAlgHom_apply (f : End A M) (g : End R N) :
    endTensorEndAlgHom (R := R) (S := S) (A := A) (M := M) (N := N) (f ⊗ₜ[R] g)
      = AlgebraTensorModule.map f g :=
  rfl
#align module.End_tensor_End_alg_hom_apply Module.endTensorEndAlgHom_apply

end Module

theorem Subalgebra.finite_sup {K L : Type*} [CommSemiring K] [CommSemiring L] [Algebra K L]
    (E1 E2 : Subalgebra K L) [Module.Finite K E1] [Module.Finite K E2] :
    Module.Finite K ↥(E1 ⊔ E2) := by
  rw [← E1.range_val, ← E2.range_val, ← Algebra.TensorProduct.productMap_range]
  exact Module.Finite.range (Algebra.TensorProduct.productMap E1.val E2.val).toLinearMap

@[deprecated Subalgebra.finite_sup (since := "2024-04-11")]
theorem Subalgebra.finiteDimensional_sup {K L : Type*} [Field K] [CommRing L] [Algebra K L]
    (E1 E2 : Subalgebra K L) [FiniteDimensional K E1] [FiniteDimensional K E2] :
    FiniteDimensional K (E1 ⊔ E2 : Subalgebra K L) := Subalgebra.finite_sup E1 E2
#align subalgebra.finite_dimensional_sup Subalgebra.finiteDimensional_sup

namespace TensorProduct.Algebra

variable {R A B M : Type*}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [Semiring A] [Semiring B] [Module A M] [Module B M]
variable [Algebra R A] [Algebra R B]
variable [IsScalarTower R A M] [IsScalarTower R B M]

/-- An auxiliary definition, used for constructing the `Module (A ⊗[R] B) M` in
`TensorProduct.Algebra.module` below. -/
def moduleAux : A ⊗[R] B →ₗ[R] M →ₗ[R] M :=
  TensorProduct.lift
    { toFun := fun a => a • (Algebra.lsmul R R M : B →ₐ[R] Module.End R M).toLinearMap
      map_add' := fun r t => by
        ext
        simp only [add_smul, LinearMap.add_apply]
      map_smul' := fun n r => by
        ext
        simp only [RingHom.id_apply, LinearMap.smul_apply, smul_assoc] }
#align tensor_product.algebra.module_aux TensorProduct.Algebra.moduleAux

theorem moduleAux_apply (a : A) (b : B) (m : M) : moduleAux (a ⊗ₜ[R] b) m = a • b • m :=
  rfl
#align tensor_product.algebra.module_aux_apply TensorProduct.Algebra.moduleAux_apply

variable [SMulCommClass A B M]

/-- If `M` is a representation of two different `R`-algebras `A` and `B` whose actions commute,
then it is a representation the `R`-algebra `A ⊗[R] B`.

An important example arises from a semiring `S`; allowing `S` to act on itself via left and right
multiplication, the roles of `R`, `A`, `B`, `M` are played by `ℕ`, `S`, `Sᵐᵒᵖ`, `S`. This example
is important because a submodule of `S` as a `Module` over `S ⊗[ℕ] Sᵐᵒᵖ` is a two-sided ideal.

NB: This is not an instance because in the case `B = A` and `M = A ⊗[R] A` we would have a diamond
of `smul` actions. Furthermore, this would not be a mere definitional diamond but a true
mathematical diamond in which `A ⊗[R] A` had two distinct scalar actions on itself: one from its
multiplication, and one from this would-be instance. Arguably we could live with this but in any
case the real fix is to address the ambiguity in notation, probably along the lines outlined here:
https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.234773.20base.20change/near/240929258
-/
protected def module : Module (A ⊗[R] B) M where
  smul x m := moduleAux x m
  zero_smul m := by simp only [(· • ·), map_zero, LinearMap.zero_apply]
  smul_zero x := by simp only [(· • ·), map_zero]
  smul_add x m₁ m₂ := by simp only [(· • ·), map_add]
  add_smul x y m := by simp only [(· • ·), map_add, LinearMap.add_apply]
  one_smul m := by
    -- Porting note: was one `simp only`, not two
    simp only [(· • ·), Algebra.TensorProduct.one_def]
    simp only [moduleAux_apply, one_smul]
  mul_smul x y m := by
    refine TensorProduct.induction_on x ?_ ?_ ?_ <;> refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp only [(· • ·), mul_zero, map_zero, LinearMap.zero_apply]
    · intro a b
      simp only [(· • ·), zero_mul, map_zero, LinearMap.zero_apply]
    · intro z w _ _
      simp only [(· • ·), zero_mul, map_zero, LinearMap.zero_apply]
    · intro a b
      simp only [(· • ·), mul_zero, map_zero, LinearMap.zero_apply]
    · intro a₁ b₁ a₂ b₂
      -- Porting note: was one `simp only`, not two
      simp only [(· • ·), Algebra.TensorProduct.tmul_mul_tmul]
      simp only [moduleAux_apply, mul_smul, smul_comm a₁ b₂]
    · intro z w hz hw a b
      -- Porting note: was one `simp only`, but random stuff doesn't work
      simp only [(· • ·)] at hz hw ⊢
      simp only [moduleAux_apply, mul_add, LinearMap.map_add,
        LinearMap.add_apply, moduleAux_apply, hz, hw, smul_add]
    · intro z w _ _
      simp only [(· • ·), mul_zero, map_zero, LinearMap.zero_apply]
    · intro a b z w hz hw
      simp only [(· • ·)] at hz hw ⊢
      simp only [LinearMap.map_add, add_mul, LinearMap.add_apply, hz, hw]
    · intro u v _ _ z w hz hw
      simp only [(· • ·)] at hz hw ⊢
      simp only [add_mul, LinearMap.map_add, LinearMap.add_apply, hz, hw, add_add_add_comm]
#align tensor_product.algebra.module TensorProduct.Algebra.module

attribute [local instance] TensorProduct.Algebra.module

theorem smul_def (a : A) (b : B) (m : M) : a ⊗ₜ[R] b • m = a • b • m :=
  rfl
#align tensor_product.algebra.smul_def TensorProduct.Algebra.smul_def

end TensorProduct.Algebra
