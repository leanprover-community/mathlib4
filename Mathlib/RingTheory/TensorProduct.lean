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

-/


universe u uS v₁ v₂ v₃ v₄

open scoped TensorProduct

open TensorProduct


namespace LinearMap

open TensorProduct

/-!
### The base-change of a linear map of `R`-modules to a linear map of `A`-modules
-/


section Semiring

variable {R A B M N : Type*} [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

variable (r : R) (f g : M →ₗ[R] N)

variable (A)

/-- `base_change A f` for `f : M →ₗ[R] N` is the `A`-linear map `A ⊗[R] M →ₗ[A] A ⊗[R] N`. -/
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
  -- porting note: added `-baseChange_tmul`
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

variable (R A M N)

/-- `base_change` as a linear map. -/
@[simps]
def baseChangeHom : (M →ₗ[R] N) →ₗ[R] A ⊗[R] M →ₗ[A] A ⊗[R] N where
  toFun := baseChange A
  map_add' := baseChange_add
  map_smul' := baseChange_smul
#align linear_map.base_change_hom LinearMap.baseChangeHom

end Semiring

section Ring

variable {R A B M N : Type*} [CommRing R]

variable [Ring A] [Algebra R A] [Ring B] [Algebra R B]

variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

variable (f g : M →ₗ[R] N)

@[simp]
theorem baseChange_sub : (f - g).baseChange A = f.baseChange A - g.baseChange A := by
  ext
  -- porting note: `tmul_sub` wasn't needed in mathlib3
  simp [baseChange_eq_ltensor, tmul_sub]

#align linear_map.base_change_sub LinearMap.baseChange_sub

@[simp]
theorem baseChange_neg : (-f).baseChange A = -f.baseChange A := by
  ext
  -- porting note: `tmul_neg` wasn't needed in mathlib3
  simp [baseChange_eq_ltensor, tmul_neg]
#align linear_map.base_change_neg LinearMap.baseChange_neg

end Ring

end LinearMap

namespace Algebra

namespace TensorProduct

section Semiring

variable {R : Type u} [CommSemiring R]

variable {A : Type v₁} [Semiring A] [Algebra R A]

variable {B : Type v₂} [Semiring B] [Algebra R B]

/-!
### The `R`-algebra structure on `A ⊗[R] B`
-/


/-- (Implementation detail)
The multiplication map on `A ⊗[R] B`,
for a fixed pure tensor in the first argument,
as an `R`-linear map.
-/
def mulAux (a₁ : A) (b₁ : B) : A ⊗[R] B →ₗ[R] A ⊗[R] B :=
  TensorProduct.map (LinearMap.mulLeft R a₁) (LinearMap.mulLeft R b₁)
#align algebra.tensor_product.mul_aux Algebra.TensorProduct.mulAux

@[simp]
theorem mulAux_apply (a₁ a₂ : A) (b₁ b₂ : B) :
    (mulAux a₁ b₁) (a₂ ⊗ₜ[R] b₂) = (a₁ * a₂) ⊗ₜ[R] (b₁ * b₂) :=
  rfl
#align algebra.tensor_product.mul_aux_apply Algebra.TensorProduct.mulAux_apply

/-- (Implementation detail)
The multiplication map on `A ⊗[R] B`,
as an `R`-bilinear map.
-/
def mul : A ⊗[R] B →ₗ[R] A ⊗[R] B →ₗ[R] A ⊗[R] B :=
  TensorProduct.lift <|
    LinearMap.mk₂ R mulAux
      (fun x₁ x₂ y =>
        TensorProduct.ext' fun x' y' => by
          simp only [mulAux_apply, LinearMap.add_apply, add_mul, add_tmul])
      (fun c x y =>
        TensorProduct.ext' fun x' y' => by
          simp only [mulAux_apply, LinearMap.smul_apply, smul_tmul', smul_mul_assoc])
      (fun x y₁ y₂ =>
        TensorProduct.ext' fun x' y' => by
          simp only [mulAux_apply, LinearMap.add_apply, add_mul, tmul_add])
      fun c x y =>
      TensorProduct.ext' fun x' y' => by
        simp only [mulAux_apply, LinearMap.smul_apply, smul_tmul, smul_tmul', smul_mul_assoc]
#align algebra.tensor_product.mul Algebra.TensorProduct.mul

@[simp]
theorem mul_apply (a₁ a₂ : A) (b₁ b₂ : B) :
    mul (a₁ ⊗ₜ[R] b₁) (a₂ ⊗ₜ[R] b₂) = (a₁ * a₂) ⊗ₜ[R] (b₁ * b₂) :=
  rfl
#align algebra.tensor_product.mul_apply Algebra.TensorProduct.mul_apply

#noalign algebra.tensor_product.mul_assoc'

protected theorem mul_assoc (x y z : A ⊗[R] B) : mul (mul x y) z = mul x (mul y z) := by
  -- restate as an equality of morphisms so that we can use `ext`
  suffices LinearMap.llcomp R _ _ _ mul ∘ₗ mul =
      (LinearMap.llcomp R _ _ _ LinearMap.lflip <| LinearMap.llcomp R _ _ _ mul.flip ∘ₗ mul).flip by
    exact FunLike.congr_fun (FunLike.congr_fun (FunLike.congr_fun this x) y) z
  ext xa xb ya yb za zb
  exact congr_arg₂ (· ⊗ₜ ·) (mul_assoc xa ya za) (mul_assoc xb yb zb)
#align algebra.tensor_product.mul_assoc Algebra.TensorProduct.mul_assoc

protected theorem one_mul (x : A ⊗[R] B) : mul (1 ⊗ₜ 1) x = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_ <;> simp (config := { contextual := true })
#align algebra.tensor_product.one_mul Algebra.TensorProduct.one_mul

protected theorem mul_one (x : A ⊗[R] B) : mul x (1 ⊗ₜ 1) = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_ <;> simp (config := { contextual := true })
#align algebra.tensor_product.mul_one Algebra.TensorProduct.mul_one

instance : One (A ⊗[R] B) where one := 1 ⊗ₜ 1

theorem one_def : (1 : A ⊗[R] B) = (1 : A) ⊗ₜ (1 : B) :=
  rfl
#align algebra.tensor_product.one_def Algebra.TensorProduct.one_def

instance : AddMonoidWithOne (A ⊗[R] B) where
  natCast n := n ⊗ₜ 1
  natCast_zero := by simp
  natCast_succ n := by simp [add_tmul, one_def]

theorem natCast_def (n : ℕ) : (n : A ⊗[R] B) = (n : A) ⊗ₜ (1 : B) := rfl

instance : AddCommMonoid (A ⊗[R] B) := by infer_instance

-- providing this instance separately makes some downstream code substantially faster
instance instMul : Mul (A ⊗[R] B) where
  mul a b := mul a b

@[simp]
theorem tmul_mul_tmul (a₁ a₂ : A) (b₁ b₂ : B) :
    a₁ ⊗ₜ[R] b₁ * a₂ ⊗ₜ[R] b₂ = (a₁ * a₂) ⊗ₜ[R] (b₁ * b₂) :=
  rfl
#align algebra.tensor_product.tmul_mul_tmul Algebra.TensorProduct.tmul_mul_tmul

-- note: we deliberately do not provide any fields that overlap with `AddMonoidWithOne` as this
-- appears to help performance.
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

variable {S : Type*}

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
    (algebraMap S (A ⊗[R] B)) r = (algebraMap S A) r ⊗ₜ 1 :=
  rfl
#align algebra.tensor_product.algebra_map_apply Algebra.TensorProduct.algebraMap_apply

variable {C : Type v₃} [Semiring C] [Algebra R C]

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
  commutes' r := by
    simp only [algebraMap_apply]
    trans r • (1 : A) ⊗ₜ[R] (1 : B)
    · rw [← tmul_smul, Algebra.smul_def]
      simp
    · simp [Algebra.smul_def]
#align algebra.tensor_product.include_right Algebra.TensorProduct.includeRight

@[simp]
theorem includeRight_apply (b : B) : (includeRight : B →ₐ[R] A ⊗[R] B) b = 1 ⊗ₜ b :=
  rfl
#align algebra.tensor_product.include_right_apply Algebra.TensorProduct.includeRight_apply

theorem includeLeftRingHom_comp_algebraMap {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] :
    (includeLeftRingHom.comp (algebraMap R S) : R →+* S ⊗[R] T) =
      includeRight.toRingHom.comp (algebraMap R T) := by
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
  rwa [←f.map_mul, ←g.map_mul, tmul_mul_tmul, _root_.one_mul, _root_.mul_one] at this

theorem ext' {g h : A ⊗[R] B →ₐ[S] C} (H : ∀ a b, g (a ⊗ₜ b) = h (a ⊗ₜ b)) : g = h :=
  ext (AlgHom.ext <| fun _ => H _ _) (AlgHom.ext <| fun _ => H _ _)
#align algebra.tensor_product.ext Algebra.TensorProduct.ext

end ext

end Semiring

section Ring

variable {R : Type u} [CommRing R]

variable {A : Type v₁} [Ring A] [Algebra R A]

variable {B : Type v₂} [Ring B] [Algebra R B]

instance instRing : Ring (A ⊗[R] B) where
  zsmul := SubNegMonoid.zsmul
  zsmul_zero' := SubNegMonoid.zsmul_zero'
  zsmul_succ' := SubNegMonoid.zsmul_succ'
  zsmul_neg' := SubNegMonoid.zsmul_neg'
  intCast z := z ⊗ₜ (1 : B)
  intCast_ofNat n := by simp [natCast_def]
  intCast_negSucc n := by simp [natCast_def, add_tmul, neg_tmul, one_def]
  add_left_neg := add_left_neg

theorem intCast_def (z : ℤ) : (z : A ⊗[R] B) = (z : A) ⊗ₜ (1 : B) := rfl

-- verify there are no diamonds
example : (instRing : Ring (A ⊗[R] B)).toAddCommGroup = addCommGroup := rfl
example : (algebraInt _ : Algebra ℤ (ℤ ⊗[ℤ] B)) = leftAlgebra := rfl

end Ring

section CommRing

variable {R : Type u} [CommRing R]

variable {A : Type v₁} [CommRing A] [Algebra R A]

variable {B : Type v₂} [CommRing B] [Algebra R B]

instance instCommRing : CommRing (A ⊗[R] B) :=
  { toRing := inferInstance
    mul_comm := fun x y => by
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · simp
      · intro a₁ b₁
        refine TensorProduct.induction_on y ?_ ?_ ?_
        · simp
        · intro a₂ b₂
          simp [mul_comm]
        · intro a₂ b₂ ha hb
          -- porting note: was `simp` not `rw`
          rw [mul_add, add_mul, ha, hb]
      · intro x₁ x₂ h₁ h₂
        -- porting note: was `simp` not `rw`
        rw [mul_add, add_mul, h₁, h₂] }

section RightAlgebra

/-- `S ⊗[R] T` has a `T`-algebra structure. This is not a global instance or else the action of
`S` on `S ⊗[R] S` would be ambiguous. -/
@[reducible]
def rightAlgebra : Algebra B (A ⊗[R] B) :=
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
example {A : Type v₁} [Ring A] {B : Type v₂} [Ring B] : Ring (A ⊗[ℤ] B) := by infer_instance

/-- Verify that typeclass search finds the comm_ring structure on `A ⊗[ℤ] B`
when `A` and `B` are merely comm_rings, by treating both as `ℤ`-algebras.
-/
example {A : Type v₁} [CommRing A] {B : Type v₂} [CommRing B] : CommRing (A ⊗[ℤ] B) := by
  infer_instance

/-!
We now build the structure maps for the symmetric monoidal category of `R`-algebras.
-/


section Monoidal

section

variable {R : Type u} {S : Type uS} [CommSemiring R] [CommSemiring S] [Algebra R S]

variable {A : Type v₁} [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

variable {B : Type v₂} [Semiring B] [Algebra R B]

variable {C : Type v₃} [Semiring C] [Algebra R C] [Algebra S C]

variable {D : Type v₄} [Semiring D] [Algebra R D]

/-- Build an algebra morphism from a linear map out of a tensor product,
and evidence of multiplicativity on pure tensors.
-/
def algHomOfLinearMapTensorProduct (f : A ⊗[R] B →ₗ[S] C)
    (w₁ : ∀ (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) ⊗ₜ (b₁ * b₂)) = f (a₁ ⊗ₜ b₁) * f (a₂ ⊗ₜ b₂))
    (w₂ : ∀ r, f (algebraMap S A r ⊗ₜ[R] 1) = algebraMap S C r) : A ⊗[R] B →ₐ[S] C :=
  { f with
    map_one' := by rw [← (algebraMap S C).map_one, ← w₂, (algebraMap S A).map_one]; rfl
    map_zero' := by simp only; rw [LinearMap.toFun_eq_coe, map_zero]
    map_mul' := fun x y => by
      simp only
      rw [LinearMap.toFun_eq_coe]
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · rw [zero_mul, map_zero, zero_mul]
      · intro a₁ b₁
        refine TensorProduct.induction_on y ?_ ?_ ?_
        · rw [mul_zero, map_zero, mul_zero]
        · intro a₂ b₂
          rw [tmul_mul_tmul, w₁]
        · intro x₁ x₂ h₁ h₂
          rw [mul_add, map_add, map_add, mul_add, h₁, h₂]
      · intro x₁ x₂ h₁ h₂
        rw [add_mul, map_add, map_add, add_mul, h₁, h₂]
    commutes' := fun r => by simp only; rw [LinearMap.toFun_eq_coe, algebraMap_apply, w₂] }
#align algebra.tensor_product.alg_hom_of_linear_map_tensor_product Algebra.TensorProduct.algHomOfLinearMapTensorProduct

@[simp]
theorem algHomOfLinearMapTensorProduct_apply (f w₁ w₂ x) :
    (algHomOfLinearMapTensorProduct f w₁ w₂ : A ⊗[R] B →ₐ[S] C) x = f x :=
  rfl
#align algebra.tensor_product.alg_hom_of_linear_map_tensor_product_apply Algebra.TensorProduct.algHomOfLinearMapTensorProduct_apply

/-- Build an algebra equivalence from a linear equivalence out of a tensor product,
and evidence of multiplicativity on pure tensors.
-/
def algEquivOfLinearEquivTensorProduct (f : A ⊗[R] B ≃ₗ[S] C)
    (w₁ : ∀ (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) ⊗ₜ (b₁ * b₂)) = f (a₁ ⊗ₜ b₁) * f (a₂ ⊗ₜ b₂))
    (w₂ : ∀ r, f ((algebraMap S A) r ⊗ₜ[R] 1) = (algebraMap S C) r) : A ⊗[R] B ≃ₐ[S] C :=
  { algHomOfLinearMapTensorProduct (f : A ⊗[R] B →ₗ[S] C) w₁ w₂, f with }
#align algebra.tensor_product.alg_equiv_of_linear_equiv_tensor_product Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct

@[simp]
theorem algEquivOfLinearEquivTensorProduct_apply (f w₁ w₂ x) :
    (algEquivOfLinearEquivTensorProduct f w₁ w₂ : A ⊗[R] B ≃ₐ[S] C) x = f x :=
  rfl
#align algebra.tensor_product.alg_equiv_of_linear_equiv_tensor_product_apply Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct_apply

/-- Build an algebra equivalence from a linear equivalence out of a triple tensor product,
and evidence of multiplicativity on pure tensors.
-/
def algEquivOfLinearEquivTripleTensorProduct (f : (A ⊗[R] B) ⊗[R] C ≃ₗ[R] D)
    (w₁ :
      ∀ (a₁ a₂ : A) (b₁ b₂ : B) (c₁ c₂ : C),
        f ((a₁ * a₂) ⊗ₜ (b₁ * b₂) ⊗ₜ (c₁ * c₂)) = f (a₁ ⊗ₜ b₁ ⊗ₜ c₁) * f (a₂ ⊗ₜ b₂ ⊗ₜ c₂))
    (w₂ : ∀ r, f (((algebraMap R A) r ⊗ₜ[R] (1 : B)) ⊗ₜ[R] (1 : C)) = (algebraMap R D) r) :
    (A ⊗[R] B) ⊗[R] C ≃ₐ[R] D :=
-- porting note : build the whole algebra isomorphism times out, so I propose to define the version
-- of tensoring three rings in terms of the version tensoring with two rings
algEquivOfLinearEquivTensorProduct f (fun x₁ x₂ c₁ c₂ => by
  refine TensorProduct.induction_on x₁ ?_ ?_ ?_ <;>
  refine TensorProduct.induction_on x₂ ?_ ?_ ?_ <;>
  simp only [zero_tmul, tmul_zero, tmul_mul_tmul, map_zero, zero_mul, mul_zero, mul_add, add_mul,
    map_add, add_tmul, tmul_add, w₁] <;>
  try
    intros
    trivial
  · intros ab₁ ab₂ h₁ h₂ a b
    rw [h₁, h₂]
  · intros a b ab₁ ab₂ h₁ h₂
    rw [h₁, h₂]
  · intros ab₁ ab₂ _ _ x y hx hy
    rw [add_add_add_comm, hx, hy, add_add_add_comm])
  w₂
#align algebra.tensor_product.alg_equiv_of_linear_equiv_triple_tensor_product Algebra.TensorProduct.algEquivOfLinearEquivTripleTensorProduct

@[simp]
theorem algEquivOfLinearEquivTripleTensorProduct_apply (f w₁ w₂ x) :
    (algEquivOfLinearEquivTripleTensorProduct f w₁ w₂ : (A ⊗[R] B) ⊗[R] C ≃ₐ[R] D) x = f x :=
  rfl
#align algebra.tensor_product.alg_equiv_of_linear_equiv_triple_tensor_product_apply Algebra.TensorProduct.algEquivOfLinearEquivTripleTensorProduct_apply

end

variable {R : Type u} {S : Type uS} [CommSemiring R] [CommSemiring S] [Algebra R S]

variable {A : Type v₁} [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

variable {B : Type v₂} [Semiring B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]

variable {C : Type v₃} [Semiring C] [Algebra R C]

variable {D : Type v₄} [Semiring D] [Algebra R D]

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

@[simp]
theorem lid_tmul (r : R) (a : A) : (TensorProduct.lid R A : R ⊗ A → A) (r ⊗ₜ a) = r • a := by
  simp [TensorProduct.lid]
#align algebra.tensor_product.lid_tmul Algebra.TensorProduct.lid_tmul

variable (S)

/-- The base ring is a right identity for the tensor product of algebra, up to algebra isomorphism.

Note that if `A` is commutative this can be instantiated with `S = A`.
-/
protected nonrec def rid : A ⊗[R] R ≃ₐ[S] A :=
  algEquivOfLinearEquivTensorProduct (AlgebraTensorModule.rid R S A)
    (fun _a₁ _a₂ _r₁ _r₂ => smul_mul_smul _ _ _ _ |>.symm)
    (fun _s => one_smul _ _)
#align algebra.tensor_product.rid Algebra.TensorProduct.rid

variable {R A} in
@[simp]
theorem rid_tmul (r : R) (a : A) : TensorProduct.rid R S A (a ⊗ₜ r) = r • a := rfl
#align algebra.tensor_product.rid_tmul Algebra.TensorProduct.rid_tmul


section

variable (B)

/-- The tensor product of R-algebras is commutative, up to algebra isomorphism.
-/
protected def comm : A ⊗[R] B ≃ₐ[R] B ⊗[R] A :=
  algEquivOfLinearEquivTensorProduct (_root_.TensorProduct.comm R A B) (by simp)
  fun r => by
    trans r • (1 : B) ⊗ₜ[R] (1 : A)
    · rw [← tmul_smul, Algebra.smul_def]
      simp
    · simp [Algebra.smul_def]
#align algebra.tensor_product.comm Algebra.TensorProduct.comm

@[simp]
theorem comm_tmul (a : A) (b : B) :
    (TensorProduct.comm R A B : A ⊗[R] B → B ⊗[R] A) (a ⊗ₜ b) = b ⊗ₜ a := by
  simp [TensorProduct.comm]
#align algebra.tensor_product.comm_tmul Algebra.TensorProduct.comm_tmul

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

theorem assoc_aux_2 (r : R) :
    (TensorProduct.assoc R A B C) (((algebraMap R A) r ⊗ₜ[R] 1) ⊗ₜ[R] 1) =
      (algebraMap R (A ⊗ (B ⊗ C))) r :=
  rfl
#align algebra.tensor_product.assoc_aux_2 Algebra.TensorProduct.assoc_aux_2

variable (A B C)

-- porting note: much nicer than Lean 3 proof
/-- The associator for tensor product of R-algebras, as an algebra isomorphism. -/
protected def assoc : (A ⊗[R] B) ⊗[R] C ≃ₐ[R] A ⊗[R] B ⊗[R] C :=
  algEquivOfLinearEquivTripleTensorProduct
    (_root_.TensorProduct.assoc R A B C)
    Algebra.TensorProduct.assoc_aux_1
    Algebra.TensorProduct.assoc_aux_2
#align algebra.tensor_product.assoc Algebra.TensorProduct.assoc

variable {A B C}

@[simp]
theorem assoc_tmul (a : A) (b : B) (c : C) :
    (_root_.TensorProduct.assoc R A B C : (A ⊗[R] B) ⊗[R] C → A ⊗[R] B ⊗[R] C) (a ⊗ₜ b ⊗ₜ c) =
      a ⊗ₜ (b ⊗ₜ c) :=
  rfl
#align algebra.tensor_product.assoc_tmul Algebra.TensorProduct.assoc_tmul

end

variable {R S A}

/-- The tensor product of a pair of algebra morphisms. -/
def map (f : A →ₐ[S] B) (g : C →ₐ[R] D) : A ⊗[R] C →ₐ[S] B ⊗[R] D :=
  algHomOfLinearMapTensorProduct (AlgebraTensorModule.map f.toLinearMap g.toLinearMap) (by simp)
    (by simp [AlgHom.commutes])
#align algebra.tensor_product.map Algebra.TensorProduct.map

@[simp]
theorem map_tmul (f : A →ₐ[S] B) (g : C →ₐ[R] D) (a : A) (c : C) : map f g (a ⊗ₜ c) = f a ⊗ₜ g c :=
  rfl
#align algebra.tensor_product.map_tmul Algebra.TensorProduct.map_tmul

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

end

end Monoidal

section

variable {R A B S : Type*} [CommSemiring R] [Semiring A] [Semiring B] [CommSemiring S]

variable [Algebra R A] [Algebra R B] [Algebra R S]

variable (f : A →ₐ[R] S) (g : B →ₐ[R] S)

variable (R)

/-- `LinearMap.mul'` is an `AlgHom` on commutative rings. -/
def lmul' : S ⊗[R] S →ₐ[R] S :=
  algHomOfLinearMapTensorProduct (LinearMap.mul' R S)
    (fun a₁ a₂ b₁ b₂ => by simp only [LinearMap.mul'_apply, mul_mul_mul_comm]) fun r => by
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
-/
def productMap : A ⊗[R] B →ₐ[R] S :=
  (lmul' R).comp (TensorProduct.map f g)
#align algebra.tensor_product.product_map Algebra.TensorProduct.productMap

@[simp]
theorem productMap_apply_tmul (a : A) (b : B) : productMap f g (a ⊗ₜ b) = f a * g b := rfl

#align algebra.tensor_product.product_map_apply_tmul Algebra.TensorProduct.productMap_apply_tmul

theorem productMap_left_apply (a : A) : productMap f g (a ⊗ₜ 1) = f a := by
  simp
#align algebra.tensor_product.product_map_left_apply Algebra.TensorProduct.productMap_left_apply

@[simp]
theorem productMap_left : (productMap f g).comp includeLeft = f :=
  AlgHom.ext <| by simp
#align algebra.tensor_product.product_map_left Algebra.TensorProduct.productMap_left

theorem productMap_right_apply (b : B) :
    productMap f g (1 ⊗ₜ b) = g b := by simp
#align algebra.tensor_product.product_map_right_apply Algebra.TensorProduct.productMap_right_apply

@[simp]
theorem productMap_right : (productMap f g).comp includeRight = g :=
  AlgHom.ext <| by simp
#align algebra.tensor_product.product_map_right Algebra.TensorProduct.productMap_right

theorem productMap_range : (productMap f g).range = f.range ⊔ g.range := by
  rw [productMap, AlgHom.range_comp, map_range, map_sup, ← AlgHom.range_comp, ← AlgHom.range_comp,
    ← AlgHom.comp_assoc, ← AlgHom.comp_assoc, lmul'_comp_includeLeft, lmul'_comp_includeRight,
    AlgHom.id_comp, AlgHom.id_comp]
#align algebra.tensor_product.product_map_range Algebra.TensorProduct.productMap_range

end

section

variable {R A A' B S : Type*}

variable [CommSemiring R] [CommSemiring A] [Semiring A'] [Semiring B] [CommSemiring S]

variable [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A'] [Algebra R B]

variable [Algebra R S] [Algebra A S] [IsScalarTower R A S]

/-- If `A`, `B` are `R`-algebras, `A'` is an `A`-algebra, then the product map of `f : A' →ₐ[A] S`
and `g : B →ₐ[R] S` is an `A`-algebra homomorphism. -/
@[simps!]
def productLeftAlgHom (f : A' →ₐ[A] S) (g : B →ₐ[R] S) : A' ⊗[R] B →ₐ[A] S :=
  { (productMap (f.restrictScalars R) g).toRingHom with
    commutes' := fun r => by
      dsimp
      simp }
#align algebra.tensor_product.product_left_alg_hom Algebra.TensorProduct.productLeftAlgHom

end

section Basis

-- porting note: need to make a universe explicit for some reason in the next declaration
universe uk uR uM uι
variable {k : Type uk} [CommRing k] (R : Type uR) [Ring R] [Algebra k R] {M : Type uM}
  [AddCommMonoid M] [Module k M] {ι : Type uι} (b : Basis ι k M)


/-- Given a `k`-algebra `R` and a `k`-basis of `M,` this is a `k`-linear isomorphism
`R ⊗[k] M ≃ (ι →₀ R)` (which is in fact `R`-linear). -/
noncomputable def basisAux : R ⊗[k] M ≃ₗ[k] ι →₀ R :=
  _root_.TensorProduct.congr (Finsupp.LinearEquiv.finsuppUnique k R PUnit.{uι+1}).symm b.repr ≪≫ₗ
    (finsuppTensorFinsupp k R k PUnit ι).trans
      (Finsupp.lcongr (Equiv.uniqueProd ι PUnit) (_root_.TensorProduct.rid k R))
#align algebra.tensor_product.basis_aux Algebra.TensorProduct.basisAux

variable {R}

theorem basisAux_tmul (r : R) (m : M) :
    basisAux R b (r ⊗ₜ m) = r • Finsupp.mapRange (algebraMap k R) (map_zero _) (b.repr m) := by
  ext
  simp [basisAux, ← Algebra.commutes, Algebra.smul_def]
#align algebra.tensor_product.basis_aux_tmul Algebra.TensorProduct.basisAux_tmul

theorem basisAux_map_smul (r : R) (x : R ⊗[k] M) : basisAux R b (r • x) = r • basisAux R b x :=
  TensorProduct.induction_on x (by simp)
    (fun x y => by simp only [TensorProduct.smul_tmul', basisAux_tmul, smul_assoc])
    fun x y hx hy => by simp [hx, hy]
#align algebra.tensor_product.basis_aux_map_smul Algebra.TensorProduct.basisAux_map_smul

variable (R)

/-- Given a `k`-algebra `R`, this is the `R`-basis of `R ⊗[k] M` induced by a `k`-basis of `M`. -/
noncomputable def basis : Basis ι R (R ⊗[k] M) where
  repr := { basisAux R b with map_smul' := basisAux_map_smul b }
#align algebra.tensor_product.basis Algebra.TensorProduct.basis

variable {R}

@[simp]
theorem basis_repr_tmul (r : R) (m : M) :
    (basis R b).repr (r ⊗ₜ m) = r • Finsupp.mapRange (algebraMap k R) (map_zero _) (b.repr m) :=
  basisAux_tmul b r m -- porting note: Lean 3 had _ _ _
#align algebra.tensor_product.basis_repr_tmul Algebra.TensorProduct.basis_repr_tmul

theorem basis_repr_symm_apply (r : R) (i : ι) :
    (basis R b).repr.symm (Finsupp.single i r) = r ⊗ₜ b.repr.symm (Finsupp.single i 1) := by
  rw [basis, LinearEquiv.coe_symm_mk] -- porting note: `coe_symm_mk` isn't firing in `simp`
  simp [Equiv.uniqueProd_symm_apply, basisAux]

-- Porting note: simpNF linter failed on `basis_repr_symm_apply`
@[simp]
theorem basis_repr_symm_apply' (r : R) (i : ι) :
    r • Algebra.TensorProduct.basis R b i = r ⊗ₜ b i := by
  simpa using basis_repr_symm_apply b r i

end Basis

end TensorProduct

end Algebra

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
    (fun _r => AlgebraTensorModule.ext fun _m _n => rfl)
#align module.End_tensor_End_alg_hom Module.endTensorEndAlgHom

theorem endTensorEndAlgHom_apply (f : End A M) (g : End R N) :
    endTensorEndAlgHom (R := R) (S := S) (A := A) (M := M) (N := N) (f ⊗ₜ[R] g)
      = AlgebraTensorModule.map f g :=
  rfl
#align module.End_tensor_End_alg_hom_apply Module.endTensorEndAlgHom_apply

end Module

theorem Subalgebra.finiteDimensional_sup {K L : Type*} [Field K] [CommRing L] [Algebra K L]
    (E1 E2 : Subalgebra K L) [FiniteDimensional K E1] [FiniteDimensional K E2] :
    FiniteDimensional K (E1 ⊔ E2 : Subalgebra K L) := by
  rw [← E1.range_val, ← E2.range_val, ← Algebra.TensorProduct.productMap_range]
  exact (Algebra.TensorProduct.productMap E1.val E2.val).toLinearMap.finiteDimensional_range
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
    -- porting note: was one `simp only` not two in lean 3
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
      -- porting note; was one `simp only` not two and a `rw` in mathlib3
      simp only [(· • ·), Algebra.TensorProduct.tmul_mul_tmul]
      simp only [moduleAux_apply, mul_smul]
      rw [smul_comm a₁ b₂]
    · intro z w hz hw a b
      --porting note: was one `simp only` but random stuff doesn't work
      simp only [(· • ·)] at hz hw ⊢
      simp only [moduleAux_apply]
      rw [mul_add]  -- simp only doesn't work
      simp only [LinearMap.map_add, LinearMap.add_apply, moduleAux_apply, hz, hw, smul_add]
    · intro z w _ _
      simp only [(· • ·), mul_zero, map_zero, LinearMap.zero_apply]
    · intro a b z w hz hw
      simp only [(· • ·)] at hz hw
      simp only [(· • ·), LinearMap.map_add, add_mul, LinearMap.add_apply, hz, hw]
    · intro u v _ _ z w hz hw
      simp only [(· • ·)] at hz hw
      -- porting note: no idea why this is such a struggle
      simp only [(· • ·)]
      rw [add_mul, LinearMap.map_add, LinearMap.add_apply, hz, hw]
      simp only [LinearMap.map_add, LinearMap.add_apply]
      rw [add_add_add_comm]
#align tensor_product.algebra.module TensorProduct.Algebra.module

attribute [local instance] TensorProduct.Algebra.module

theorem smul_def (a : A) (b : B) (m : M) : a ⊗ₜ[R] b • m = a • b • m :=
  rfl
#align tensor_product.algebra.smul_def TensorProduct.Algebra.smul_def

end TensorProduct.Algebra
