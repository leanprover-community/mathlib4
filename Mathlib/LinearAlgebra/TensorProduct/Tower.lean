/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin, Eric Wieser
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.TensorProduct.Associator

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
* `LinearMap.baseChange A f` is the `A`-linear map `A ⊗ f`, for an `R`-linear map `f`.

## Implementation notes

We could thus consider replacing the less general definitions with these ones. If we do this, we
probably should still implement the less general ones as abbreviations to the more general ones with
fewer type arguments.
-/

@[expose] public section

namespace TensorProduct

namespace AlgebraTensorModule

universe uR uS uA uB uM uN uP uQ uP' uQ'
variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}
variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ} {P' : Type uP'} {Q' : Type uQ'}

open LinearMap
open Algebra (lsmul)

section Semiring

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable [AddCommMonoid M] [Module R M] [Module A M]
variable [IsScalarTower R A M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P] [Module A P]
variable [IsScalarTower R A P]
variable [AddCommMonoid Q] [Module R Q]
variable [AddCommMonoid P'] [Module R P'] [Module A P'] [Module B P']
variable [IsScalarTower R A P'] [IsScalarTower R B P'] [SMulCommClass A B P']
variable [AddCommMonoid Q'] [Module R Q']

theorem smul_eq_lsmul_rTensor (a : A) (x : M ⊗[R] N) : a • x = (lsmul R R M a).rTensor N x :=
  rfl

/-- Heterobasic version of `TensorProduct.curry`:

Given a linear map `M ⊗[R] N →[A] P`, compose it with the canonical
bilinear map `M →[A] N →[R] M ⊗[R] N` to form a bilinear map `M →[A] N →[R] P`. -/
@[simps]
nonrec def curry (f : M ⊗[R] N →ₗ[A] P) : M →ₗ[A] N →ₗ[R] P :=
  { curry (f.restrictScalars R) with
    toFun := curry (f.restrictScalars R)
    map_smul' := fun c x => LinearMap.ext fun y => f.map_smul c (x ⊗ₜ y) }

theorem restrictScalars_curry (f : M ⊗[R] N →ₗ[A] P) :
    restrictScalars R (curry f) = TensorProduct.curry (f.restrictScalars R) :=
  rfl

/-- Just as `TensorProduct.ext` is marked `ext` instead of `TensorProduct.ext'`, this is
a better `ext` lemma than `TensorProduct.AlgebraTensorModule.ext` below.

See note [partially-applied ext lemmas]. -/
@[ext high]
nonrec theorem curry_injective : Function.Injective (curry : (M ⊗ N →ₗ[A] P) → M →ₗ[A] N →ₗ[R] P) :=
  fun _ _ h =>
  LinearMap.restrictScalars_injective R <|
    curry_injective <| (congr_arg (LinearMap.restrictScalars R) h :)

theorem ext {g h : M ⊗[R] N →ₗ[A] P} (H : ∀ x y, g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h :=
  curry_injective <| LinearMap.ext₂ H

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
        LinearMap.ext_iff.1 <|
          TensorProduct.ext' fun x y => by
            simp only [comp_apply, Algebra.lsmul_coe, smul_tmul', lift.tmul,
              coe_restrictScalars, f.map_smul, smul_apply] }

@[simp]
theorem lift_apply (f : M →ₗ[A] N →ₗ[R] P) (a : M ⊗[R] N) :
    AlgebraTensorModule.lift f a = TensorProduct.lift (LinearMap.restrictScalars R f) a :=
  rfl

@[simp]
theorem lift_tmul (f : M →ₗ[A] N →ₗ[R] P) (x : M) (y : N) : lift f (x ⊗ₜ y) = f x y :=
  rfl

variable (R A B M N P Q)

section
variable [Module B P] [IsScalarTower R B P] [SMulCommClass A B P]

/-- Heterobasic version of `TensorProduct.uncurry`:

Linearly constructing a linear map `M ⊗[R] N →[A] P` given a bilinear map `M →[A] N →[R] P`
with the property that its composition with the canonical bilinear map `M →[A] N →[R] M ⊗[R] N` is
the given bilinear map `M →[A] N →[R] P`. -/
@[simps]
def uncurry : (M →ₗ[A] N →ₗ[R] P) →ₗ[B] M ⊗[R] N →ₗ[A] P where
  toFun := lift
  map_add' _ _ := ext fun x y => by simp only [lift_tmul, add_apply]
  map_smul' _ _ := ext fun x y => by simp only [lift_tmul, smul_apply, RingHom.id_apply]

/-- Heterobasic version of `TensorProduct.lcurry`:

Given a linear map `M ⊗[R] N →[A] P`, compose it with the canonical
bilinear map `M →[A] N →[R] M ⊗[R] N` to form a bilinear map `M →[A] N →[R] P`. -/
@[simps]
def lcurry : (M ⊗[R] N →ₗ[A] P) →ₗ[B] M →ₗ[A] N →ₗ[R] P where
  toFun := curry
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Heterobasic version of `TensorProduct.lift.equiv`:

A linear equivalence constructing a linear map `M ⊗[R] N →[A] P` given a
bilinear map `M →[A] N →[R] P` with the property that its composition with the
canonical bilinear map `M →[A] N →[R] M ⊗[R] N` is the given bilinear map `M →[A] N →[R] P`. -/
def lift.equiv : (M →ₗ[A] N →ₗ[R] P) ≃ₗ[B] M ⊗[R] N →ₗ[A] P :=
  LinearEquiv.ofLinear (uncurry R A B M N P) (lcurry R A B M N P)
    (LinearMap.ext fun _ => ext fun x y => lift_tmul _ x y)
    (LinearMap.ext fun f => LinearMap.ext fun x => LinearMap.ext fun y => lift_tmul f x y)

/-- Heterobasic version of `TensorProduct.mk`:

The canonical bilinear map `M →[A] N →[R] M ⊗[R] N`. -/
@[simps! apply]
nonrec def mk (A M N : Type*) [Semiring A]
    [AddCommMonoid M] [Module R M] [Module A M] [SMulCommClass R A M]
    [AddCommMonoid N] [Module R N] : M →ₗ[A] N →ₗ[R] M ⊗[R] N :=
  { mk R M N with map_smul' := fun _ _ => rfl }

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

@[simp]
theorem map_id : map (id : M →ₗ[A] M) (id : N →ₗ[R] N) = .id :=
  ext fun _ _ => rfl

theorem map_comp (f₂ : P →ₗ[A] P') (f₁ : M →ₗ[A] P) (g₂ : Q →ₗ[R] Q') (g₁ : N →ₗ[R] Q) :
    map (f₂.comp f₁) (g₂.comp g₁) = (map f₂ g₂).comp (map f₁ g₁) :=
  ext fun _ _ => rfl

@[simp]
protected theorem map_one : map (1 : M →ₗ[A] M) (1 : N →ₗ[R] N) = 1 := map_id

protected theorem map_mul (f₁ f₂ : M →ₗ[A] M) (g₁ g₂ : N →ₗ[R] N) :
    map (f₁ * f₂) (g₁ * g₂) = map f₁ g₁ * map f₂ g₂ := map_comp _ _ _ _

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

/-- The heterobasic version of `map` coincides with the regular version. -/
theorem map_eq (f : M →ₗ[R] P) (g : N →ₗ[R] Q) : map f g = TensorProduct.map f g := rfl

variable (A M) in
/-- Heterobasic version of `LinearMap.lTensor` -/
def lTensor : (N →ₗ[R] Q) →ₗ[R] M ⊗[R] N →ₗ[A] M ⊗[R] Q where
  toFun f := map LinearMap.id f
  map_add' f₁ f₂ := map_add_right _ f₁ f₂
  map_smul' _ _ := map_smul_right _ _ _

@[simp]
lemma coe_lTensor (f : N →ₗ[R] Q) :
    (lTensor A M f : M ⊗[R] N → M ⊗[R] Q) = f.lTensor M := rfl

@[simp]
lemma restrictScalars_lTensor (f : N →ₗ[R] Q) :
    (lTensor A M f).restrictScalars R = f.lTensor M := rfl

@[simp] lemma lTensor_tmul (f : N →ₗ[R] Q) (m : M) (n : N) :
    lTensor A M f (m ⊗ₜ[R] n) = m ⊗ₜ f n :=
  rfl

@[simp] lemma lTensor_id : lTensor A M (id : N →ₗ[R] N) = .id :=
  ext fun _ _ => rfl

lemma lTensor_comp (f₂ : Q →ₗ[R] Q') (f₁ : N →ₗ[R] Q) :
    lTensor A M (f₂.comp f₁) = (lTensor A M f₂).comp (lTensor A M f₁) :=
  ext fun _ _ => rfl

@[simp]
lemma lTensor_one : lTensor A M (1 : N →ₗ[R] N) = 1 := map_id

lemma lTensor_mul (f₁ f₂ : N →ₗ[R] N) :
    lTensor A M (f₁ * f₂) = lTensor A M f₁ * lTensor A M f₂ := lTensor_comp _ _

variable (R N) in
/-- Heterobasic version of `LinearMap.rTensor` -/
def rTensor : (M →ₗ[A] P) →ₗ[R] M ⊗[R] N →ₗ[A] P ⊗[R] N where
  toFun f := map f LinearMap.id
  map_add' f₁ f₂ := map_add_left f₁ f₂ _
  map_smul' _ _ := map_smul_left _ _ _

@[simp]
lemma coe_rTensor (f : M →ₗ[A] P) :
    (rTensor R N f : M ⊗[R] N → P ⊗[R] N) = f.rTensor N := rfl

@[simp]
lemma restrictScalars_rTensor (f : M →ₗ[A] P) :
    (rTensor R N f).restrictScalars R = f.rTensor N := rfl

@[simp] lemma rTensor_tmul (f : M →ₗ[A] P) (m : M) (n : N) :
    rTensor R N f (m ⊗ₜ[R] n) = f m ⊗ₜ n :=
  rfl

@[simp] lemma rTensor_id : rTensor R N (id : M →ₗ[A] M) = .id :=
  ext fun _ _ => rfl

lemma rTensor_comp (f₂ : P →ₗ[A] P') (f₁ : M →ₗ[A] P) :
    rTensor R N (f₂.comp f₁) = (rTensor R N f₂).comp (rTensor R N f₁) :=
  ext fun _ _ => rfl

@[simp]
lemma rTensor_one : rTensor R N (1 : M →ₗ[A] M) = 1 := map_id

lemma rTensor_mul (f₁ f₂ : M →ₗ[A] M) :
    rTensor R M (f₁ * f₂) = rTensor R M f₁ * rTensor R M f₂ := rTensor_comp _ _

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

@[simp]
theorem congr_refl : congr (.refl A M) (.refl R N) = .refl A _ :=
  LinearEquiv.toLinearMap_injective <| map_id

theorem congr_trans (f₁ : M ≃ₗ[A] P) (f₂ : P ≃ₗ[A] P') (g₁ : N ≃ₗ[R] Q) (g₂ : Q ≃ₗ[R] Q') :
    congr (f₁.trans f₂) (g₁.trans g₂) = (congr f₁ g₁).trans (congr f₂ g₂) :=
  LinearEquiv.toLinearMap_injective <| map_comp _ _ _ _

theorem congr_symm (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) : congr f.symm g.symm = (congr f g).symm := rfl

@[simp]
theorem congr_one : congr (1 : M ≃ₗ[A] M) (1 : N ≃ₗ[R] N) = 1 := congr_refl

theorem congr_mul (f₁ f₂ : M ≃ₗ[A] M) (g₁ g₂ : N ≃ₗ[R] N) :
    congr (f₁ * f₂) (g₁ * g₂) = congr f₁ g₁ * congr f₂ g₂ := congr_trans _ _ _ _

@[simp] theorem congr_tmul (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) (m : M) (n : N) :
    congr f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
  rfl

@[simp] theorem congr_symm_tmul (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) (p : P) (q : Q) :
    (congr f g).symm (p ⊗ₜ q) = f.symm p ⊗ₜ g.symm q :=
  rfl

theorem congr_eq (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    congr f g = TensorProduct.congr f g := rfl

variable (R A M)

/-- Heterobasic version of `TensorProduct.rid`. -/
protected def rid : M ⊗[R] R ≃ₗ[A] M :=
  LinearEquiv.ofLinear
    (lift <| Algebra.lsmul _ _ _ |>.toLinearMap |>.flip)
    (mk R A M R |>.flip 1)
    (LinearMap.ext <| one_smul _)
    (ext fun _ _ => smul_tmul _ _ _ |>.trans <| congr_arg _ <| mul_one _)

/-- The heterobasic version of `rid` coincides with the regular version. -/
theorem rid_eq_rid : AlgebraTensorModule.rid R R M = TensorProduct.rid R M := rfl

variable {R M} in
@[simp]
theorem rid_tmul (r : R) (m : M) : AlgebraTensorModule.rid R A M (m ⊗ₜ r) = r • m := rfl

variable {M} in
@[simp]
theorem rid_symm_apply (m : M) : (AlgebraTensorModule.rid R A M).symm m = m ⊗ₜ 1 := rfl

end

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable [AddCommMonoid M] [Module R M] [Module A M] [Module B M]
variable [IsScalarTower R A M] [IsScalarTower R B M] [SMulCommClass A B M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module A P]
variable [AddCommMonoid P'] [Module A P']
variable [AddCommMonoid Q] [Module R Q]
variable (R A B M N P P' Q)

attribute [local ext high] TensorProduct.ext

section assoc
variable [Module R P] [IsScalarTower R A P]
variable [Algebra A B] [IsScalarTower A B M]

/-- Heterobasic version of `TensorProduct.assoc`:

`B`-linear equivalence between `(M ⊗[A] P) ⊗[R] Q` and `M ⊗[A] (P ⊗[R] Q)`.

Note this is especially useful with `A = R` (where it is a "more linear" version of
`TensorProduct.assoc`), or with `B = A`. -/
def assoc : (M ⊗[A] P) ⊗[R] Q ≃ₗ[B] M ⊗[A] (P ⊗[R] Q) :=
  LinearEquiv.ofLinear
    (lift <| lift <| lcurry R A B P Q _ ∘ₗ mk A B M (P ⊗[R] Q))
    (lift <| uncurry R A B P Q _ ∘ₗ curry (mk R B _ Q))
    (by ext; rfl)
    (by ext; rfl)

variable {M P N Q}

@[simp]
theorem assoc_tmul (m : M) (p : P) (q : Q) :
    assoc R A B M P Q ((m ⊗ₜ p) ⊗ₜ q) = m ⊗ₜ (p ⊗ₜ q) :=
  rfl

@[simp]
theorem assoc_symm_tmul (m : M) (p : P) (q : Q) :
    (assoc R A B M P Q).symm (m ⊗ₜ (p ⊗ₜ q)) = (m ⊗ₜ p) ⊗ₜ q :=
  rfl

/-- The heterobasic version of `assoc` coincides with the regular version. -/
theorem assoc_eq : assoc R R R M P Q = TensorProduct.assoc R M P Q := rfl

theorem rTensor_tensor [Module R P'] [IsScalarTower R A P'] (g : P →ₗ[A] P') :
    g.rTensor (M ⊗[R] N) =
      assoc R A A P' M N ∘ₗ map (g.rTensor M) id ∘ₗ (assoc R A A P M N).symm.toLinearMap :=
  TensorProduct.ext <| LinearMap.ext fun _ ↦ ext fun _ _ ↦ rfl

end assoc

section cancelBaseChange
variable [Algebra A B] [IsScalarTower A B M]

/-- `B`-linear equivalence between `M ⊗[A] (A ⊗[R] N)` and `M ⊗[R] N`.
In particular useful with `B = A`. -/
def cancelBaseChange : M ⊗[A] (A ⊗[R] N) ≃ₗ[B] M ⊗[R] N :=
  letI g : (M ⊗[A] A) ⊗[R] N ≃ₗ[B] M ⊗[R] N := congr (AlgebraTensorModule.rid A B M) (.refl R N)
  (assoc R A B M A N).symm ≪≫ₗ g

/-- Base change distributes over tensor product. -/
def distribBaseChange : A ⊗[R] (N ⊗[R] Q) ≃ₗ[A] (A ⊗[R] N) ⊗[A] (A ⊗[R] Q) :=
  (cancelBaseChange _ _ _ _ _ ≪≫ₗ assoc _ _ _ _ _ _).symm

variable {M P N Q}

@[simp]
theorem cancelBaseChange_tmul (m : M) (n : N) (a : A) :
    cancelBaseChange R A B M N (m ⊗ₜ (a ⊗ₜ n)) = (a • m) ⊗ₜ n :=
  rfl

@[simp]
theorem cancelBaseChange_symm_tmul (m : M) (n : N) :
    (cancelBaseChange R A B M N).symm (m ⊗ₜ n) = m ⊗ₜ (1 ⊗ₜ n) :=
  rfl

theorem lTensor_comp_cancelBaseChange (f : N →ₗ[R] Q) :
    lTensor _ _ f ∘ₗ cancelBaseChange R A B M N =
      (cancelBaseChange R A B M Q).toLinearMap ∘ₗ lTensor _ _ (lTensor _ _ f) := by
  ext; simp

@[simp]
theorem distribBaseChange_tmul (n : N) (q : Q) (a : A) :
    distribBaseChange R A N Q (a ⊗ₜ (n ⊗ₜ q)) = (a ⊗ₜ n) ⊗ₜ (1 ⊗ₜ q) :=
  rfl

@[simp]
theorem distribBaseChange_symm_tmul
    (n : N) (q : Q) (a b : A) :
    (distribBaseChange R A N Q).symm ((a ⊗ₜ n) ⊗ₜ (b ⊗ₜ q)) = (a * b) ⊗ₜ (n ⊗ₜ q) := by
  apply ((distribBaseChange R A N Q).apply_eq_iff_symm_apply.mp ?_).symm
  rw [tmul_eq_smul_one_tmul b, ← smul_tmul, smul_tmul', mul_comm]
  simp

lemma cancelBaseChange_self_eq_lid :
    cancelBaseChange R A A A N = TensorProduct.lid A (A ⊗[R] N) := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      simp only [cancelBaseChange_tmul, lid_tmul, smul_tmul', smul_eq_mul, mul_comm]
    | add x y hx hy =>
      simp only [tmul_add, map_add, lid_tmul, hx, hy]
  | add x y hx hy => simp [hx, hy]

end cancelBaseChange

section leftComm
variable [Module R P] [IsScalarTower R A P]

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
theorem leftComm_symm_tmul (m : M) (p : P) (q : Q) :
    (leftComm R A M P Q).symm (p ⊗ₜ (m ⊗ₜ q)) = m ⊗ₜ (p ⊗ₜ q) :=
  rfl

/-- The heterobasic version of `leftComm` coincides with the regular version. -/
theorem leftComm_eq : leftComm R R M P Q = TensorProduct.leftComm R M P Q := rfl

end leftComm

section rightComm

variable [CommSemiring S] [Module S M] [Module S P] [Algebra S B]
  [IsScalarTower S B M] [SMulCommClass R S M] [SMulCommClass S R M]

variable (S) in
/-- A tensor product analogue of `mul_right_comm`.

Suppose we have a diagram of algebras `R → B ← S`,
and a `B`-module `M`, `S`-module `P`, `R`-module `Q`, then
```
(M ⊗ˢ P)      ⎛ M ⎞ ⊗ˢ P
 ⊗ᴿ       ≅ᴮ  ⎜ ⊗ᴿ⎟
 Q            ⎝ Q ⎠
```
-/
def rightComm : (M ⊗[S] P) ⊗[R] Q ≃ₗ[B] (M ⊗[R] Q) ⊗[S] P :=
  LinearEquiv.ofLinear
    (lift (lift (LinearMap.lflip.toLinearMap ∘ₗ
      (AlgebraTensorModule.mk _ _ _ _).compr₂ (AlgebraTensorModule.mk _ _ _ _))))
    (lift (lift (LinearMap.lflip.toLinearMap ∘ₗ
      (AlgebraTensorModule.mk _ _ _ _).compr₂ (AlgebraTensorModule.mk _ _ _ _))))
    (by ext; simp) (by ext; simp)

variable {M N P Q}

@[simp]
theorem rightComm_tmul (m : M) (p : P) (q : Q) :
    rightComm R S B M P Q ((m ⊗ₜ p) ⊗ₜ q) = (m ⊗ₜ q) ⊗ₜ p :=
  rfl

@[simp]
theorem rightComm_symm :
    (rightComm R S B M P Q).symm = rightComm S R B M Q P :=
  rfl

theorem rightComm_symm_tmul (m : M) (p : P) (q : Q) :
    (rightComm R S B M P Q).symm ((m ⊗ₜ q) ⊗ₜ p) = (m ⊗ₜ p) ⊗ₜ q :=
  rfl

/-- The heterobasic version of `leftComm` coincides with the regular version. -/
theorem rightComm_eq [Module R P] : rightComm R R R M P Q = TensorProduct.rightComm R M P Q := rfl

end rightComm

section tensorTensorTensorComm
variable [Module R P] [IsScalarTower R A P]

variable [Algebra A B] [IsScalarTower A B M]
variable [CommSemiring S] [Algebra R S] [Algebra S B] [Module S M] [Module S N]
variable [IsScalarTower R S M] [SMulCommClass A S M] [SMulCommClass S A M]
  [IsScalarTower S B M] [IsScalarTower R S N]

variable (S)

/-- Heterobasic version of `tensorTensorTensorComm`.

Suppose we have towers of algebras `R → S → B` and `R → A → B`, and
a `B`-module `M`, `S`-module `N`, `A`-module `P`, `R`-module `Q`, then
```
(M ⊗ˢ N)      ⎛ M ⎞ ⊗ˢ ⎛ N ⎞
 ⊗ᴬ       ≅ᴮ  ⎜ ⊗ᴬ⎟    ⎜ ⊗ᴿ⎟
(P ⊗ᴿ Q)      ⎝ P ⎠    ⎝ Q ⎠
```
-/
def tensorTensorTensorComm :
    (M ⊗[S] N) ⊗[A] (P ⊗[R] Q) ≃ₗ[B] (M ⊗[A] P) ⊗[S] (N ⊗[R] Q) :=
  (assoc R A B (M ⊗[S] N) P Q).symm
    ≪≫ₗ congr (rightComm A S B M N P) (.refl R Q)
    ≪≫ₗ assoc R _ _ (M ⊗[A] P) N Q

variable {M N P Q}

@[simp]
theorem tensorTensorTensorComm_tmul (m : M) (n : N) (p : P) (q : Q) :
    tensorTensorTensorComm R S A B M N P Q ((m ⊗ₜ n) ⊗ₜ (p ⊗ₜ q)) = (m ⊗ₜ p) ⊗ₜ (n ⊗ₜ q) :=
  rfl

@[simp]
theorem tensorTensorTensorComm_symm :
    (tensorTensorTensorComm R S A B M N P Q).symm = tensorTensorTensorComm R A S B M P N Q := rfl

theorem tensorTensorTensorComm_symm_tmul (m : M) (n : N) (p : P) (q : Q) :
    (tensorTensorTensorComm R S A B M N P Q).symm ((m ⊗ₜ p) ⊗ₜ (n ⊗ₜ q)) = (m ⊗ₜ n) ⊗ₜ (p ⊗ₜ q) :=
  rfl

/-- The heterobasic version of `tensorTensorTensorComm` coincides with the regular version. -/
theorem tensorTensorTensorComm_eq :
    tensorTensorTensorComm R R R R M N P Q = TensorProduct.tensorTensorTensorComm R M N P Q := rfl

end tensorTensorTensorComm

end CommSemiring

end AlgebraTensorModule

end TensorProduct

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

variable (A) in
/-- `baseChange A f` for `f : M →ₗ[R] N` is the `A`-linear map `A ⊗[R] M →ₗ[A] A ⊗[R] N`.

This "base change" operation is also known as "extension of scalars". -/
def baseChange (f : M →ₗ[R] N) : A ⊗[R] M →ₗ[A] A ⊗[R] N :=
  AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) f

@[simp]
theorem baseChange_tmul (a : A) (x : M) : f.baseChange A (a ⊗ₜ x) = a ⊗ₜ f x :=
  rfl

theorem baseChange_eq_ltensor : (f.baseChange A : A ⊗ M → A ⊗ N) = f.lTensor A :=
  rfl

@[simp]
theorem baseChange_add : (f + g).baseChange A = f.baseChange A + g.baseChange A := by
  ext
  simp [baseChange_eq_ltensor, -baseChange_tmul]

@[simp]
theorem baseChange_zero : baseChange A (0 : M →ₗ[R] N) = 0 := by
  ext
  simp

@[simp]
theorem baseChange_smul : (r • f).baseChange A = r • f.baseChange A := by
  ext
  simp

@[simp]
lemma baseChange_id : (.id : M →ₗ[R] M).baseChange A = .id := by
  ext; simp

lemma baseChange_comp (g : N →ₗ[R] P) :
    (g ∘ₗ f).baseChange A = g.baseChange A ∘ₗ f.baseChange A := by
  ext; simp

open AlgebraTensorModule in
lemma baseChange_baseChange {A B : Type*} [CommSemiring A] [Algebra R A]
    [Semiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (f : M →ₗ[R] N) :
    ((f.baseChange A).baseChange B) =
    (cancelBaseChange R A B B N).symm ∘ₗ
      (f.baseChange B) ∘ₗ (cancelBaseChange R A B B M) := by
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

/-- `baseChange` as an `AlgHom`. -/
@[simps!]
def _root_.Module.End.baseChangeHom : Module.End R M →ₐ[R] Module.End A (A ⊗[R] M) :=
  .ofLinearMap (LinearMap.baseChangeHom _ _ _ _) (baseChange_one _ _) baseChange_mul

lemma baseChange_pow (f : Module.End R M) (n : ℕ) :
    (f ^ n).baseChange A = f.baseChange A ^ n :=
  map_pow (Module.End.baseChangeHom _ _ _) f n

/-- `baseChange A e` for `e : M ≃ₗ[R] N` is the `A`-linear map `A ⊗[R] M ≃ₗ[A] A ⊗[R] N`. -/
def _root_.LinearEquiv.baseChange (e : M ≃ₗ[R] N) : A ⊗[R] M ≃ₗ[A] A ⊗[R] N :=
  AlgebraTensorModule.congr (.refl _ _) e

@[simp]
theorem _root_.LinearEquiv.coe_baseChange (f : M ≃ₗ[R] N) :
    f.baseChange R A M N = f.toLinearMap.baseChange A :=
   rfl

@[simp] lemma _root_.LinearEquiv.baseChange_tmul {e : M ≃ₗ[R] N} (a : A) (m : M) :
    e.baseChange R A M N (a ⊗ₜ m) = a ⊗ₜ e m :=
  rfl

@[simp] lemma _root_.LinearEquiv.baseChange_symm_tmul {e : M ≃ₗ[R] N} (a : A) (n : N) :
    (e.baseChange R A).symm (a ⊗ₜ n) = a ⊗ₜ e.symm n :=
  rfl

@[simp]
theorem _root_.LinearEquiv.baseChange_one :
    (1 : M ≃ₗ[R] M).baseChange R A M M = 1 := by
  ext x
  simp [← LinearEquiv.coe_toLinearMap]

theorem _root_.LinearEquiv.baseChange_trans (e : M ≃ₗ[R] N) (f : N ≃ₗ[R] P) :
    (e.trans f).baseChange R A M P = (e.baseChange R A M N).trans (f.baseChange R A N P) := by
  ext x
  simp only [← LinearEquiv.coe_toLinearMap, LinearEquiv.coe_baseChange, LinearEquiv.trans_apply,
    LinearEquiv.coe_trans, baseChange_eq_ltensor, lTensor_comp_apply]

theorem _root_.LinearEquiv.baseChange_mul (e : M ≃ₗ[R] M) (f : M ≃ₗ[R] M) :
    (e * f).baseChange R A M M = (e.baseChange R A M M) * (f.baseChange R A M M) := by
  simp [LinearEquiv.mul_eq_trans, LinearEquiv.baseChange_trans]

theorem _root_.LinearEquiv.baseChange_symm (e : M ≃ₗ[R] N) :
    e.symm.baseChange R A N M = (e.baseChange R A M N).symm := by
  ext x
  rw [LinearEquiv.eq_symm_apply]
  simp [← LinearEquiv.coe_toLinearMap, LinearEquiv.coe_baseChange,
    baseChange_eq_ltensor, ← lTensor_comp_apply]

theorem _root_.LinearEquiv.baseChange_inv (e : M ≃ₗ[R] M) :
    (e⁻¹).baseChange R A M M = (e.baseChange R A M M)⁻¹ :=
  LinearEquiv.baseChange_symm R A M M e

lemma _root_.LinearEquiv.baseChange_pow (f : M ≃ₗ[R] M) (n : ℕ) :
    (f ^ n).baseChange R A M M = f.baseChange R A M M ^ n := by
  induction n with
  | zero => simp
  | succ n h =>
    simp [pow_succ, LinearEquiv.baseChange_mul, h]

lemma _root_.LinearEquiv.baseChange_zpow (f : M ≃ₗ[R] M) (n : ℤ) :
    (f ^ n).baseChange R A M M = f.baseChange R A M M ^ n := by
  induction n with
  | zero => simp
  | succ n h =>
    simp only [zpow_add_one, LinearEquiv.baseChange_mul, h]
  | pred n h =>
    simp only [zpow_sub_one, LinearEquiv.baseChange_mul, h, LinearEquiv.baseChange_inv]

variable {R A M N} in
theorem rTensor_baseChange (φ : A →ₐ[R] B) (t : A ⊗[R] M) (f : M →ₗ[R] N) :
    (φ.toLinearMap.rTensor N) (f.baseChange A t) =
      (f.baseChange B) (φ.toLinearMap.rTensor M t) := by
  simp [LinearMap.baseChange_eq_ltensor, ← LinearMap.comp_apply]

end Semiring

section Ring

variable {R A B M N : Type*} [CommRing R]
variable [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (f g : M →ₗ[R] N)

@[simp]
theorem baseChange_sub : (f - g).baseChange A = f.baseChange A - g.baseChange A := by
  ext
  simp [tmul_sub]

@[simp]
theorem baseChange_neg : (-f).baseChange A = -f.baseChange A := by
  ext
  simp [tmul_neg]

end Ring

end LinearMap

namespace Submodule

open TensorProduct

variable {R M : Type*} (A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] (p : Submodule R M)

/-- If `A` is an `R`-algebra, any `R`-submodule `p` of an `R`-module `M` may be pushed forward to
an `A`-submodule of `A ⊗ M`.

This "base change" operation is also known as "extension of scalars". -/
def baseChange : Submodule A (A ⊗[R] M) :=
  LinearMap.range (p.subtype.baseChange A)

variable {A p} in
lemma tmul_mem_baseChange_of_mem (a : A) {m : M} (hm : m ∈ p) :
    a ⊗ₜ[R] m ∈ p.baseChange A :=
  ⟨a ⊗ₜ[R] ⟨m, hm⟩, rfl⟩

lemma baseChange_eq_span : p.baseChange A = span A (p.map (TensorProduct.mk R A M 1)) := by
  refine le_antisymm ?_ ?_
  · rw [baseChange, LinearMap.range_le_iff_comap, eq_top_iff,
      ← span_eq_top_of_span_eq_top R A _ (span_tmul_eq_top R ..), span_le]
    refine fun _ ⟨a, m, h⟩ ↦ ?_
    rw [← h, SetLike.mem_coe, mem_comap, LinearMap.baseChange_tmul, ← mul_one a, ← smul_eq_mul,
      ← smul_tmul']
    exact smul_mem _ a (subset_span ⟨m, m.2, rfl⟩)
  · refine span_le.2 fun _ ⟨m, hm, h⟩ ↦ h ▸ ⟨1 ⊗ₜ[R] ⟨m, hm⟩, rfl⟩

@[simp]
lemma baseChange_bot : (⊥ : Submodule R M).baseChange A = ⊥ := by simp [baseChange_eq_span]

@[simp]
lemma baseChange_top : (⊤ : Submodule R M).baseChange A = ⊤ := by
  rw [eq_top_iff, ← span_eq_top_of_span_eq_top R A _ (span_tmul_eq_top R ..)]
  exact span_le.2 fun _ ⟨a, m, h⟩ ↦ h ▸ tmul_mem_baseChange_of_mem _ trivial

@[simp]
lemma baseChange_span (s : Set M) :
    (span R s).baseChange A = span A (TensorProduct.mk R A M 1 '' s) := by
  rw [baseChange_eq_span, map_span, span_span_of_tower]

/-- Given an `R`-submodule `p` of `M`, and `R`-algebra `A`, we obtain an `A`-submodule of
`A ⊗[R] M` by `p.baseChange A`. This is then the surjective `A`-linear map
`A ⊗[R] M → p.baseChange A`. -/
def toBaseChange : A ⊗[R] p →ₗ[A] p.baseChange A :=
  LinearMap.rangeRestrict _

@[simp] lemma coe_toBaseChange_tmul (a : A) (x : p) :
    (p.toBaseChange A (a ⊗ₜ x) : A ⊗[R] M) = a ⊗ₜ (x : M) := rfl

lemma toBaseChange_surjective : Function.Surjective (p.toBaseChange A) :=
  LinearMap.surjective_rangeRestrict _

/-- This version enables better pattern matching via the tactic `obtain`. -/
lemma toBaseChange_surjective' {y : A ⊗[R] M} (hy : y ∈ p.baseChange A) :
    ∃ x : A ⊗[R] p, p.toBaseChange A x = y := by
  obtain ⟨x, hx⟩ := toBaseChange_surjective A p ⟨y, hy⟩
  exact ⟨x, congr($hx)⟩

end Submodule
