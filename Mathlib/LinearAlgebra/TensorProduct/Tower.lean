/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin, Eric Wieser
-/
import Mathlib.LinearAlgebra.TensorProduct
import Mathlib.Algebra.Algebra.Tower

#align_import ring_theory.tensor_product from "leanprover-community/mathlib"@"88fcdc3da43943f5b01925deddaa5bf0c0e85e4e"

/-!
# The `A`-module structure on `M ⊗[R] N`

When `M` is both an `R`-module and an `A`-module, and `Algebra R A`, then many of the morphisms
preserve the actions by `A`.

The `Module` instance itself is provided elsewhere as `TensorProduct.leftModule`. This file provides
more general versions of the definitions already in `LinearAlgebra/TensorProduct`.

In this file, we use the convention that `M`, `N`, `P`, `Q` are all `R`-modules, but only `M` and
`P` are simultaneously `A`-modules.

## Main definitions

 * `TensorProduct.AlgebraTensorModule.curry`
 * `TensorProduct.AlgebraTensorModule.uncurry`
 * `TensorProduct.AlgebraTensorModule.lcurry`
 * `TensorProduct.AlgebraTensorModule.lift`
 * `TensorProduct.AlgebraTensorModule.lift.equiv`
 * `TensorProduct.AlgebraTensorModule.mk`
 * `TensorProduct.AlgebraTensorModule.map`
 * `TensorProduct.AlgebraTensorModule.mapBilinear`
 * `TensorProduct.AlgebraTensorModule.congr`
 * `TensorProduct.AlgebraTensorModule.rid`
 * `TensorProduct.AlgebraTensorModule.homTensorHomMap`
 * `TensorProduct.AlgebraTensorModule.assoc`
 * `TensorProduct.AlgebraTensorModule.leftComm`
 * `TensorProduct.AlgebraTensorModule.rightComm`
 * `TensorProduct.AlgebraTensorModule.tensorTensorTensorComm`

## Implementation notes

We could thus consider replacing the less general definitions with these ones. If we do this, we
probably should still implement the less general ones as abbreviations to the more general ones with
fewer type arguments.
-/

namespace TensorProduct

namespace AlgebraTensorModule

universe uR uA uB uM uN uP uQ
variable {R : Type uR} {A : Type uA} {B : Type uB}
variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}

open LinearMap
open Algebra (lsmul)

section Semiring

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

variable [AddCommMonoid M] [Module R M] [Module A M] [Module B M]
variable [IsScalarTower R A M] [IsScalarTower R B M] [SMulCommClass A B M]

variable [AddCommMonoid N] [Module R N]

variable [AddCommMonoid P] [Module R P] [Module A P] [Module B P]
variable [IsScalarTower R A P] [IsScalarTower R B P] [SMulCommClass A B P]

variable [AddCommMonoid Q] [Module R Q]

theorem smul_eq_lsmul_rTensor (a : A) (x : M ⊗[R] N) : a • x = (lsmul R R M a).rTensor N x :=
  rfl
#align tensor_product.algebra_tensor_module.smul_eq_lsmul_rtensor TensorProduct.AlgebraTensorModule.smul_eq_lsmul_rTensor

/-- Heterobasic version of `TensorProduct.curry`:

Given a linear map `M ⊗[R] N →[A] P`, compose it with the canonical
bilinear map `M →[A] N →[R] M ⊗[R] N` to form a bilinear map `M →[A] N →[R] P`. -/
@[simps]
nonrec def curry (f : M ⊗[R] N →ₗ[A] P) : M →ₗ[A] N →ₗ[R] P :=
  { curry (f.restrictScalars R) with
    toFun := curry (f.restrictScalars R)
    map_smul' := fun c x => LinearMap.ext fun y => f.map_smul c (x ⊗ₜ y) }
#align tensor_product.algebra_tensor_module.curry TensorProduct.AlgebraTensorModule.curry
#align tensor_product.algebra_tensor_module.curry_apply TensorProduct.AlgebraTensorModule.curry_apply

theorem restrictScalars_curry (f : M ⊗[R] N →ₗ[A] P) :
    restrictScalars R (curry f) = TensorProduct.curry (f.restrictScalars R) :=
  rfl
#align tensor_product.algebra_tensor_module.restrict_scalars_curry TensorProduct.AlgebraTensorModule.restrictScalars_curry

/-- Just as `TensorProduct.ext` is marked `ext` instead of `TensorProduct.ext'`, this is
a better `ext` lemma than `TensorProduct.AlgebraTensorModule.ext` below.

See note [partially-applied ext lemmas]. -/
@[ext high]
nonrec theorem curry_injective : Function.Injective (curry : (M ⊗ N →ₗ[A] P) → M →ₗ[A] N →ₗ[R] P) :=
  fun _ _ h =>
  LinearMap.restrictScalars_injective R <|
    curry_injective <| (congr_arg (LinearMap.restrictScalars R) h : _)
#align tensor_product.algebra_tensor_module.curry_injective TensorProduct.AlgebraTensorModule.curry_injective

theorem ext {g h : M ⊗[R] N →ₗ[A] P} (H : ∀ x y, g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h :=
  curry_injective <| LinearMap.ext₂ H
#align tensor_product.algebra_tensor_module.ext TensorProduct.AlgebraTensorModule.ext

/-- Heterobasic version of `TensorProduct.lift`:

Constructing a linear map `M ⊗[R] N →[A] P` given a bilinear map `M →[A] N →[R] P` with the
property that its composition with the canonical bilinear map `M →[A] N →[R] M ⊗[R] N` is
the given bilinear map `M →[A] N →[R] P`. -/
nonrec def lift (f : M →ₗ[A] N →ₗ[R] P) : M ⊗[R] N →ₗ[A] P :=
  { lift (f.restrictScalars R) with
    map_smul' := fun c =>
      show
        ∀ x : M ⊗[R] N,
          (lift (f.restrictScalars R)).comp (lsmul R R _ c) x =
            (lsmul R R _ c).comp (lift (f.restrictScalars R)) x
        from
        ext_iff.1 <|
          TensorProduct.ext' fun x y => by
            simp only [comp_apply, Algebra.lsmul_coe, smul_tmul', lift.tmul,
              coe_restrictScalars, f.map_smul, smul_apply] }
#align tensor_product.algebra_tensor_module.lift TensorProduct.AlgebraTensorModule.lift

-- Porting note: autogenerated lemma unfolded to `liftAux`
@[simp]
theorem lift_apply (f : M →ₗ[A] N →ₗ[R] P) (a : M ⊗[R] N) :
    AlgebraTensorModule.lift f a = TensorProduct.lift (LinearMap.restrictScalars R f) a :=
  rfl

@[simp]
theorem lift_tmul (f : M →ₗ[A] N →ₗ[R] P) (x : M) (y : N) : lift f (x ⊗ₜ y) = f x y :=
  rfl
#align tensor_product.algebra_tensor_module.lift_tmul TensorProduct.AlgebraTensorModule.lift_tmul

variable (R A B M N P Q)

/-- Heterobasic version of `TensorProduct.uncurry`:

Linearly constructing a linear map `M ⊗[R] N →[A] P` given a bilinear map `M →[A] N →[R] P`
with the property that its composition with the canonical bilinear map `M →[A] N →[R] M ⊗[R] N` is
the given bilinear map `M →[A] N →[R] P`. -/
@[simps]
def uncurry : (M →ₗ[A] N →ₗ[R] P) →ₗ[B] M ⊗[R] N →ₗ[A] P where
  toFun := lift
  map_add' _ _ := ext fun x y => by simp only [lift_tmul, add_apply]
  map_smul' _ _ := ext fun x y => by simp only [lift_tmul, smul_apply, RingHom.id_apply]
-- porting note: new `B` argument
#align tensor_product.algebra_tensor_module.uncurry TensorProduct.AlgebraTensorModule.uncurryₓ

/-- Heterobasic version of `TensorProduct.lcurry`:

Given a linear map `M ⊗[R] N →[A] P`, compose it with the canonical
bilinear map `M →[A] N →[R] M ⊗[R] N` to form a bilinear map `M →[A] N →[R] P`. -/
@[simps]
def lcurry : (M ⊗[R] N →ₗ[A] P) →ₗ[B] M →ₗ[A] N →ₗ[R] P where
  toFun := curry
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
-- porting note: new `B` argument
#align tensor_product.algebra_tensor_module.lcurry TensorProduct.AlgebraTensorModule.lcurryₓ

/-- Heterobasic version of `TensorProduct.lift.equiv`:

A linear equivalence constructing a linear map `M ⊗[R] N →[A] P` given a
bilinear map `M →[A] N →[R] P` with the property that its composition with the
canonical bilinear map `M →[A] N →[R] M ⊗[R] N` is the given bilinear map `M →[A] N →[R] P`. -/
def lift.equiv : (M →ₗ[A] N →ₗ[R] P) ≃ₗ[B] M ⊗[R] N →ₗ[A] P :=
  LinearEquiv.ofLinear (uncurry R A B M N P) (lcurry R A B M N P)
    (LinearMap.ext fun _ => ext fun x y => lift_tmul _ x y)
    (LinearMap.ext fun f => LinearMap.ext fun x => LinearMap.ext fun y => lift_tmul f x y)
-- porting note: new `B` argument
#align tensor_product.algebra_tensor_module.lift.equiv TensorProduct.AlgebraTensorModule.lift.equivₓ

/-- Heterobasic version of `TensorProduct.mk`:

The canonical bilinear map `M →[A] N →[R] M ⊗[R] N`. -/
@[simps! apply]
nonrec def mk : M →ₗ[A] N →ₗ[R] M ⊗[R] N :=
  { mk R M N with map_smul' := fun _ _ => rfl }
#align tensor_product.algebra_tensor_module.mk TensorProduct.AlgebraTensorModule.mk
#align tensor_product.algebra_tensor_module.mk_apply TensorProduct.AlgebraTensorModule.mk_apply

variable {R A B M N P Q}

/-- Heterobasic version of `TensorProduct.map` -/
def map (f : M →ₗ[A] P) (g : N →ₗ[R] Q) : M ⊗[R] N →ₗ[A] P ⊗[R] Q :=
  lift <|
    { toFun := fun h => h ∘ₗ g,
      map_add' := fun h₁ h₂ => LinearMap.add_comp g h₂ h₁,
      map_smul' := fun c h => LinearMap.smul_comp c h g } ∘ₗ mk R A P Q ∘ₗ f

@[simp] theorem map_tmul (f : M →ₗ[A] P) (g : N →ₗ[R] Q) (m : M) (n : N) :
    map f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
  rfl

theorem map_add_left (f₁ f₂ : M →ₗ[A] P) (g : N →ₗ[R] Q) :
    map (f₁ + f₂) g = map f₁ g + map f₂ g := by
  ext
  simp_rw [curry_apply, TensorProduct.curry_apply, restrictScalars_apply, add_apply, map_tmul,
    add_apply, add_tmul]

theorem map_add_right (f : M →ₗ[A] P) (g₁ g₂ : N →ₗ[R] Q) :
    map f (g₁ + g₂) = map f g₁ + map f g₂ := by
  ext
  simp_rw [curry_apply, TensorProduct.curry_apply, restrictScalars_apply, add_apply, map_tmul,
    add_apply, tmul_add]

theorem map_smul_right (r : R) (f : M →ₗ[A] P) (g : N →ₗ[R] Q) : map f (r • g) = r • map f g := by
  ext
  simp_rw [curry_apply, TensorProduct.curry_apply, restrictScalars_apply, smul_apply, map_tmul,
    smul_apply, tmul_smul]

theorem map_smul_left (b : B) (f : M →ₗ[A] P) (g : N →ₗ[R] Q) : map (b • f) g = b • map f g := by
  ext
  simp_rw [curry_apply, TensorProduct.curry_apply, restrictScalars_apply, smul_apply, map_tmul,
    smul_apply, smul_tmul']

variable (R A B M N P Q)

/-- Heterobasic version of `TensorProduct.map_bilinear` -/
def mapBilinear : (M →ₗ[A] P) →ₗ[B] (N →ₗ[R] Q) →ₗ[R] (M ⊗[R] N →ₗ[A] P ⊗[R] Q) :=
  LinearMap.mk₂' _ _ map map_add_left map_smul_left map_add_right map_smul_right

variable {R A B M N P Q}

@[simp]
theorem mapBilinear_apply (f : M →ₗ[A] P) (g : N →ₗ[R] Q) :
    mapBilinear R A B M N P Q f g = map f g :=
  rfl

variable (R A B M N P Q)

/-- Heterobasic version of `TensorProduct.homTensorHomMap` -/
def homTensorHomMap : ((M →ₗ[A] P) ⊗[R] (N →ₗ[R] Q)) →ₗ[B] (M ⊗[R] N →ₗ[A] P ⊗[R] Q) :=
  lift <| mapBilinear R A B M N P Q

variable {R A B M N P Q}

@[simp] theorem homTensorHomMap_apply (f : M →ₗ[A] P) (g : N →ₗ[R] Q) :
    homTensorHomMap R A B M N P Q (f ⊗ₜ g) = map f g :=
  rfl

/-- Heterobasic version of `TensorProduct.congr` -/
def congr (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) : (M ⊗[R] N) ≃ₗ[A] (P ⊗[R] Q) :=
  LinearEquiv.ofLinear (map f g) (map f.symm g.symm)
    (ext fun _m _n => congr_arg₂ (· ⊗ₜ ·) (f.apply_symm_apply _) (g.apply_symm_apply _))
    (ext fun _m _n => congr_arg₂ (· ⊗ₜ ·) (f.symm_apply_apply _) (g.symm_apply_apply _))

@[simp] theorem congr_tmul (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) (m : M) (n : N) :
    congr f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
  rfl

@[simp] theorem congr_symm_tmul (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) (p : P) (q : Q) :
    (congr f g).symm (p ⊗ₜ q) = f.symm p ⊗ₜ g.symm q :=
  rfl

variable (R A M)

/-- Heterobasic version of `TensorProduct.rid`. -/
protected def rid : M ⊗[R] R ≃ₗ[A] M :=
  LinearEquiv.ofLinear
    (lift <| Algebra.lsmul _ _ _ |>.toLinearMap |>.flip)
    (mk R A M R |>.flip 1)
    (LinearMap.ext <| one_smul _)
    (ext <| fun _ _ => smul_tmul _ _ _ |>.trans <| congr_arg _ <| mul_one _)

variable {R M}

@[simp]
theorem rid_tmul (r : R) (m : M) : AlgebraTensorModule.rid R A M (m ⊗ₜ r) = r • m := rfl

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [Semiring B] [Algebra R A] [Algebra R B]

variable [AddCommMonoid M] [Module R M] [Module A M] [Module B M]
variable [IsScalarTower R A M] [IsScalarTower R B M] [SMulCommClass A B M]

variable [AddCommMonoid N] [Module R N]

variable [AddCommMonoid P] [Module R P] [Module A P] [Module B P]
variable [IsScalarTower R A P] [IsScalarTower R B P] [SMulCommClass A B P]

variable [AddCommMonoid Q] [Module R Q]

variable (R A B M N P Q)

attribute [local ext high] TensorProduct.ext

section assoc
variable [Algebra A B] [IsScalarTower A B M]

/-- Heterobasic version of `TensorProduct.assoc`:

Linear equivalence between `(M ⊗[A] N) ⊗[R] P` and `M ⊗[A] (N ⊗[R] P)`.

Note this is especially useful with `A = R` (where it is a "more linear" version of
`TensorProduct.assoc`), or with `B = A`. -/
def assoc : (M ⊗[A] P) ⊗[R] Q ≃ₗ[B] M ⊗[A] (P ⊗[R] Q) :=
  LinearEquiv.ofLinear
    (lift <| lift <| lcurry R A B P Q _ ∘ₗ mk A B M (P ⊗[R] Q))
    (lift <| uncurry R A B P Q _ ∘ₗ curry (mk R B _ Q))
    (by ext; rfl)
    (by ext; rfl)
-- porting note: new `B` argument
#align tensor_product.algebra_tensor_module.assoc TensorProduct.AlgebraTensorModule.assocₓ

variable {M P N Q}

@[simp]
theorem assoc_tmul (m : M) (p : P) (q : Q) :
    assoc R A B M P Q ((m ⊗ₜ p) ⊗ₜ q) = m ⊗ₜ (p ⊗ₜ q) :=
  rfl

@[simp]
theorem assoc_symm_tmul (m : M) (p : P) (q : Q) :
    (assoc R A B M P Q).symm (m ⊗ₜ (p ⊗ₜ q)) = (m ⊗ₜ p) ⊗ₜ q :=
  rfl

end assoc

section leftComm

/-- Heterobasic version of `TensorProduct.leftComm` -/
def leftComm : M ⊗[A] (P ⊗[R] Q) ≃ₗ[A] P ⊗[A] (M ⊗[R] Q) :=
  let e₁ := (assoc R A A M P Q).symm
  let e₂ := congr (TensorProduct.comm A M P) (1 : Q ≃ₗ[R] Q)
  let e₃ := assoc R A A P M Q
  e₁ ≪≫ₗ e₂ ≪≫ₗ e₃

variable {M N P Q}

@[simp]
theorem leftComm_tmul (m : M) (p : P) (q : Q) :
    leftComm R A M P Q (m ⊗ₜ (p ⊗ₜ q)) = p ⊗ₜ (m ⊗ₜ q) :=
  rfl

@[simp]
theorem leftComm_symm_tmul (m : M) (p : P) (q : Q):
    (leftComm R A M P Q).symm (p ⊗ₜ (m ⊗ₜ q)) = m ⊗ₜ (p ⊗ₜ q) :=
  rfl

end leftComm

section rightComm

/-- A tensor product analogue of `mul_right_comm`. -/
def rightComm : (M ⊗[A] P) ⊗[R] Q ≃ₗ[A] (M ⊗[R] Q) ⊗[A] P :=
  LinearEquiv.ofLinear
    (lift <| TensorProduct.lift <| LinearMap.flip <|
      lcurry R A A M Q ((M ⊗[R] Q) ⊗[A] P) ∘ₗ (mk A A (M ⊗[R] Q) P).flip)
    (TensorProduct.lift <| lift <| LinearMap.flip <|
      (TensorProduct.lcurry A M P ((M ⊗[A] P) ⊗[R] Q)).restrictScalars R
        ∘ₗ (mk R A (M ⊗[A] P) Q).flip)
    -- explicit `Eq.refl`s here help with performance, but also make it clear that the `ext` are
    -- letting us prove the result as an equality of pure tensors.
    (TensorProduct.ext <| ext <| fun m q => LinearMap.ext <| fun p => Eq.refl <|
      (m ⊗ₜ[R] q) ⊗ₜ[A] p)
    (curry_injective <| TensorProduct.ext' <| fun m p => LinearMap.ext <| fun q => Eq.refl <|
      (m ⊗ₜ[A] p) ⊗ₜ[R] q)

variable {M N P Q}

@[simp]
theorem rightComm_tmul (m : M) (p : P) (q : Q) :
    rightComm R A M P Q ((m ⊗ₜ p) ⊗ₜ q) = (m ⊗ₜ q) ⊗ₜ p :=
  rfl

@[simp]
theorem rightComm_symm_tmul (m : M) (p : P) (q : Q):
    (rightComm R A M P Q).symm ((m ⊗ₜ q) ⊗ₜ p) = (m ⊗ₜ p) ⊗ₜ q :=
  rfl

end rightComm

section tensorTensorTensorComm

/-- Heterobasic version of `tensorTensorTensorComm`. -/
def tensorTensorTensorComm :
  (M ⊗[R] N) ⊗[A] (P ⊗[R] Q) ≃ₗ[A] (M ⊗[A] P) ⊗[R] (N ⊗[R] Q) :=
(assoc R A A (M ⊗[R] N) P Q).symm
  ≪≫ₗ congr (rightComm R A M P N).symm (1 : Q ≃ₗ[R] Q)
  ≪≫ₗ assoc R _ _ (M ⊗[A] P) N Q

variable {M N P Q}

@[simp]
theorem tensorTensorTensorComm_tmul (m : M) (n : N) (p : P) (q : Q) :
    tensorTensorTensorComm R A M N P Q ((m ⊗ₜ n) ⊗ₜ (p ⊗ₜ q)) = (m ⊗ₜ p) ⊗ₜ (n ⊗ₜ q) :=
  rfl

@[simp]
theorem tensorTensorTensorComm_symm_tmul (m : M) (n : N) (p : P) (q : Q) :
    (tensorTensorTensorComm R A M N P Q).symm ((m ⊗ₜ p) ⊗ₜ (n ⊗ₜ q)) = (m ⊗ₜ n) ⊗ₜ (p ⊗ₜ q) :=
  rfl

end tensorTensorTensorComm

end CommSemiring

end AlgebraTensorModule

end TensorProduct
