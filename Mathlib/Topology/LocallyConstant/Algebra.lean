/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.Pi
import Mathlib.Topology.LocallyConstant.Basic

#align_import topology.locally_constant.algebra from "leanprover-community/mathlib"@"bcfa726826abd57587355b4b5b7e78ad6527b7e4"

/-!
# Algebraic structure on locally constant functions

This file puts algebraic structure (`Group`, `AddGroup`, etc)
on the type of locally constant functions.

-/

set_option autoImplicit true

namespace LocallyConstant

variable {X Y : Type*} [TopologicalSpace X]

@[to_additive]
instance [One Y] : One (LocallyConstant X Y) where one := const X 1

@[to_additive (attr := simp)]
theorem coe_one [One Y] : ⇑(1 : LocallyConstant X Y) = (1 : X → Y) :=
  rfl
#align locally_constant.coe_one LocallyConstant.coe_one
#align locally_constant.coe_zero LocallyConstant.coe_zero

@[to_additive]
theorem one_apply [One Y] (x : X) : (1 : LocallyConstant X Y) x = 1 :=
  rfl
#align locally_constant.one_apply LocallyConstant.one_apply
#align locally_constant.zero_apply LocallyConstant.zero_apply

@[to_additive]
instance [Inv Y] : Inv (LocallyConstant X Y) where inv f := ⟨f⁻¹, f.isLocallyConstant.inv⟩

@[to_additive (attr := simp)]
theorem coe_inv [Inv Y] (f : LocallyConstant X Y) : ⇑(f⁻¹ : LocallyConstant X Y) = (f : X → Y)⁻¹ :=
  rfl
#align locally_constant.coe_inv LocallyConstant.coe_inv
#align locally_constant.coe_neg LocallyConstant.coe_neg

@[to_additive]
theorem inv_apply [Inv Y] (f : LocallyConstant X Y) (x : X) : f⁻¹ x = (f x)⁻¹ :=
  rfl
#align locally_constant.inv_apply LocallyConstant.inv_apply
#align locally_constant.neg_apply LocallyConstant.neg_apply

@[to_additive]
instance [Mul Y] : Mul (LocallyConstant X Y) where
  mul f g := ⟨f * g, f.isLocallyConstant.mul g.isLocallyConstant⟩

@[to_additive (attr := simp)]
theorem coe_mul [Mul Y] (f g : LocallyConstant X Y) : ⇑(f * g) = f * g :=
  rfl
#align locally_constant.coe_mul LocallyConstant.coe_mul
#align locally_constant.coe_add LocallyConstant.coe_add

@[to_additive]
theorem mul_apply [Mul Y] (f g : LocallyConstant X Y) (x : X) : (f * g) x = f x * g x :=
  rfl
#align locally_constant.mul_apply LocallyConstant.mul_apply
#align locally_constant.add_apply LocallyConstant.add_apply

@[to_additive]
instance [MulOneClass Y] : MulOneClass (LocallyConstant X Y) :=
  Function.Injective.mulOneClass FunLike.coe FunLike.coe_injective' rfl fun _ _ => rfl

/-- `FunLike.coe` as a `MonoidHom`. -/
@[to_additive (attr := simps) "`FunLike.coe` as an `AddMonoidHom`."]
def coeFnMonoidHom [MulOneClass Y] : LocallyConstant X Y →* X → Y where
  toFun := FunLike.coe
  map_one' := rfl
  map_mul' _ _ := rfl
#align locally_constant.coe_fn_monoid_hom LocallyConstant.coeFnMonoidHom
#align locally_constant.coe_fn_add_monoid_hom LocallyConstant.coeFnAddMonoidHom

/-- The constant-function embedding, as a multiplicative monoid hom. -/
@[to_additive (attr := simps) "The constant-function embedding, as an additive monoid hom."]
def constMonoidHom [MulOneClass Y] : Y →* LocallyConstant X Y where
  toFun := const X
  map_one' := rfl
  map_mul' _ _ := rfl
#align locally_constant.const_monoid_hom LocallyConstant.constMonoidHom
#align locally_constant.const_add_monoid_hom LocallyConstant.constAddMonoidHom

instance [MulZeroClass Y] : MulZeroClass (LocallyConstant X Y) :=
  Function.Injective.mulZeroClass FunLike.coe FunLike.coe_injective' rfl fun _ _ => rfl

instance [MulZeroOneClass Y] : MulZeroOneClass (LocallyConstant X Y) :=
  Function.Injective.mulZeroOneClass FunLike.coe FunLike.coe_injective' rfl rfl fun _ _ => rfl

section CharFn

variable (Y) [MulZeroOneClass Y] {U V : Set X}

/-- Characteristic functions are locally constant functions taking `x : X` to `1` if `x ∈ U`,
  where `U` is a clopen set, and `0` otherwise. -/
noncomputable def charFn (hU : IsClopen U) : LocallyConstant X Y :=
  indicator 1 hU
#align locally_constant.char_fn LocallyConstant.charFn

theorem coe_charFn (hU : IsClopen U) : (charFn Y hU : X → Y) = Set.indicator U 1 :=
  rfl
#align locally_constant.coe_char_fn LocallyConstant.coe_charFn

theorem charFn_eq_one [Nontrivial Y] (x : X) (hU : IsClopen U) : charFn Y hU x = (1 : Y) ↔ x ∈ U :=
  Set.indicator_eq_one_iff_mem _
#align locally_constant.char_fn_eq_one LocallyConstant.charFn_eq_one

theorem charFn_eq_zero [Nontrivial Y] (x : X) (hU : IsClopen U) : charFn Y hU x = (0 : Y) ↔ x ∉ U :=
  Set.indicator_eq_zero_iff_not_mem _
#align locally_constant.char_fn_eq_zero LocallyConstant.charFn_eq_zero

theorem charFn_inj [Nontrivial Y] (hU : IsClopen U) (hV : IsClopen V)
    (h : charFn Y hU = charFn Y hV) : U = V :=
  Set.indicator_one_inj Y <| coe_inj.mpr h
#align locally_constant.char_fn_inj LocallyConstant.charFn_inj

end CharFn

@[to_additive]
instance [Div Y] : Div (LocallyConstant X Y) where
  div f g := ⟨f / g, f.isLocallyConstant.div g.isLocallyConstant⟩

@[to_additive]
theorem coe_div [Div Y] (f g : LocallyConstant X Y) : ⇑(f / g) = f / g :=
  rfl
#align locally_constant.coe_div LocallyConstant.coe_div
#align locally_constant.coe_sub LocallyConstant.coe_sub

@[to_additive]
theorem div_apply [Div Y] (f g : LocallyConstant X Y) (x : X) : (f / g) x = f x / g x :=
  rfl
#align locally_constant.div_apply LocallyConstant.div_apply
#align locally_constant.sub_apply LocallyConstant.sub_apply

@[to_additive]
instance [Semigroup Y] : Semigroup (LocallyConstant X Y) :=
  Function.Injective.semigroup FunLike.coe FunLike.coe_injective' fun _ _ => rfl

instance [SemigroupWithZero Y] : SemigroupWithZero (LocallyConstant X Y) :=
  Function.Injective.semigroupWithZero FunLike.coe FunLike.coe_injective' rfl fun _ _ => rfl

@[to_additive]
instance [CommSemigroup Y] : CommSemigroup (LocallyConstant X Y) :=
  Function.Injective.commSemigroup FunLike.coe FunLike.coe_injective' fun _ _ => rfl

@[to_additive]
instance smul [SMul α Y] : SMul α (LocallyConstant X Y) where
  smul n f := f.map (n • ·)

@[to_additive (attr := simp)]
theorem coe_smul [SMul R Y] (r : R) (f : LocallyConstant X Y) : ⇑(r • f) = r • (f : X → Y) :=
  rfl
#align locally_constant.coe_smul LocallyConstant.coe_smul

@[to_additive]
theorem smul_apply [SMul R Y] (r : R) (f : LocallyConstant X Y) (x : X) : (r • f) x = r • f x :=
  rfl
#align locally_constant.smul_apply LocallyConstant.smul_apply

@[to_additive existing LocallyConstant.smul]
instance [Pow Y α] : Pow (LocallyConstant X Y) α where
  pow f n := f.map (· ^ n)

@[to_additive]
instance [Monoid Y] : Monoid (LocallyConstant X Y) :=
  Function.Injective.monoid FunLike.coe FunLike.coe_injective' rfl (fun _ _ => rfl) fun _ _ => rfl

instance [NatCast Y] : NatCast (LocallyConstant X Y) where
  natCast n := const X n

instance [IntCast Y] : IntCast (LocallyConstant X Y) where
  intCast n := const X n

instance [AddMonoidWithOne Y] : AddMonoidWithOne (LocallyConstant X Y) :=
  Function.Injective.addMonoidWithOne FunLike.coe FunLike.coe_injective' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ => rfl

@[to_additive]
instance [CommMonoid Y] : CommMonoid (LocallyConstant X Y) :=
  Function.Injective.commMonoid FunLike.coe FunLike.coe_injective' rfl (fun _ _ => rfl)
    fun _ _ => rfl

@[to_additive]
instance [Group Y] : Group (LocallyConstant X Y) :=
  Function.Injective.group FunLike.coe FunLike.coe_injective' rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]
instance [CommGroup Y] : CommGroup (LocallyConstant X Y) :=
  Function.Injective.commGroup FunLike.coe FunLike.coe_injective' rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance [Distrib Y] : Distrib (LocallyConstant X Y) :=
  Function.Injective.distrib FunLike.coe FunLike.coe_injective' (fun _ _ => rfl) fun _ _ => rfl

instance [NonUnitalNonAssocSemiring Y] : NonUnitalNonAssocSemiring (LocallyConstant X Y) :=
  Function.Injective.nonUnitalNonAssocSemiring FunLike.coe FunLike.coe_injective' rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance [NonUnitalSemiring Y] : NonUnitalSemiring (LocallyConstant X Y) :=
  Function.Injective.nonUnitalSemiring FunLike.coe FunLike.coe_injective' rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance [NonAssocSemiring Y] : NonAssocSemiring (LocallyConstant X Y) :=
  Function.Injective.nonAssocSemiring FunLike.coe FunLike.coe_injective' rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

/-- The constant-function embedding, as a ring hom.  -/
@[simps]
def constRingHom [NonAssocSemiring Y] : Y →+* LocallyConstant X Y :=
  { constMonoidHom, constAddMonoidHom with toFun := const X }
#align locally_constant.const_ring_hom LocallyConstant.constRingHom

instance [Semiring Y] : Semiring (LocallyConstant X Y) :=
  Function.Injective.semiring FunLike.coe FunLike.coe_injective' rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

instance [NonUnitalCommSemiring Y] : NonUnitalCommSemiring (LocallyConstant X Y) :=
  Function.Injective.nonUnitalCommSemiring FunLike.coe FunLike.coe_injective' rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance [CommSemiring Y] : CommSemiring (LocallyConstant X Y) :=
  Function.Injective.commSemiring FunLike.coe FunLike.coe_injective' rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

instance [NonUnitalNonAssocRing Y] : NonUnitalNonAssocRing (LocallyConstant X Y) :=
  Function.Injective.nonUnitalNonAssocRing FunLike.coe FunLike.coe_injective' rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance [NonUnitalRing Y] : NonUnitalRing (LocallyConstant X Y) :=
  Function.Injective.nonUnitalRing FunLike.coe FunLike.coe_injective' rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance [NonAssocRing Y] : NonAssocRing (LocallyConstant X Y) :=
  Function.Injective.nonAssocRing FunLike.coe FunLike.coe_injective' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl)

instance [Ring Y] : Ring (LocallyConstant X Y) :=
  Function.Injective.ring FunLike.coe FunLike.coe_injective' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

instance [NonUnitalCommRing Y] : NonUnitalCommRing (LocallyConstant X Y) :=
  Function.Injective.nonUnitalCommRing FunLike.coe FunLike.coe_injective' rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance [CommRing Y] : CommRing (LocallyConstant X Y) :=
  Function.Injective.commRing FunLike.coe FunLike.coe_injective' rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

variable {R : Type*}

instance [Monoid R] [MulAction R Y] : MulAction R (LocallyConstant X Y) :=
  Function.Injective.mulAction _ coe_injective fun _ _ => rfl

instance [Monoid R] [AddMonoid Y] [DistribMulAction R Y] :
    DistribMulAction R (LocallyConstant X Y) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective fun _ _ => rfl

instance [Semiring R] [AddCommMonoid Y] [Module R Y] : Module R (LocallyConstant X Y) :=
  Function.Injective.module R coeFnAddMonoidHom coe_injective fun _ _ => rfl

section Algebra

variable [CommSemiring R] [Semiring Y] [Algebra R Y]

instance : Algebra R (LocallyConstant X Y) where
  toRingHom := constRingHom.comp <| algebraMap R Y
  commutes' := by
    intros
    -- ⊢ ↑(RingHom.comp constRingHom (algebraMap R Y)) r✝ * x✝ = x✝ * ↑(RingHom.comp  …
    ext
    -- ⊢ ↑(↑(RingHom.comp constRingHom (algebraMap R Y)) r✝ * x✝¹) x✝ = ↑(x✝¹ * ↑(Rin …
    exact Algebra.commutes' _ _
    -- 🎉 no goals
  smul_def' := by
    intros
    -- ⊢ r✝ • x✝ = ↑(RingHom.comp constRingHom (algebraMap R Y)) r✝ * x✝
    ext
    -- ⊢ ↑(r✝ • x✝¹) x✝ = ↑(↑(RingHom.comp constRingHom (algebraMap R Y)) r✝ * x✝¹) x✝
    exact Algebra.smul_def' _ _
    -- 🎉 no goals

@[simp]
theorem coe_algebraMap (r : R) : ⇑(algebraMap R (LocallyConstant X Y) r) = algebraMap R (X → Y) r :=
  rfl
#align locally_constant.coe_algebra_map LocallyConstant.coe_algebraMap

end Algebra

section coeFn

/-- `FunLike.coe` as a `RingHom`. -/
@[simps!] def coeFnRingHom [Semiring Y] : LocallyConstant X Y →+* X → Y where
  toMonoidHom := coeFnMonoidHom
  __ := coeFnAddMonoidHom

/-- `FunLike.coe` as a linear map. -/
@[simps!] def coeFnₗ (R : Type*) [Semiring R] [AddCommMonoid Y]
    [Module R Y] : LocallyConstant X Y →ₗ[R] X → Y where
  toAddHom := coeFnAddMonoidHom.toAddHom
  map_smul' _ _ := rfl

/-- `FunLike.coe` as an `AlgHom`. -/
@[simps!] def coeFnAlgHom (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y] :
    LocallyConstant X Y →ₐ[R] X → Y where
  toRingHom := coeFnRingHom
  commutes' _ := rfl

end coeFn

section Eval

/-- Evaluation as a `MonoidHom` -/
@[to_additive (attr := simps!) "Evaluation as an `AddMonoidHom`"]
def evalMonoidHom [MulOneClass Y] (x : X) : LocallyConstant X Y →* Y :=
  (Pi.evalMonoidHom _ x).comp coeFnMonoidHom

/-- Evaluation as a linear map -/
@[simps!] def evalₗ (R : Type*) [Semiring R] [AddCommMonoid Y]
    [Module R Y] (x : X) : LocallyConstant X Y →ₗ[R] Y :=
  (LinearMap.proj x).comp (coeFnₗ R)

/-- Evaluation as a `RingHom` -/
@[simps!] def evalRingHom [Semiring Y] (x : X) : LocallyConstant X Y →+* Y :=
  (Pi.evalRingHom _ x).comp coeFnRingHom

/-- Evaluation as an `AlgHom` -/
@[simps!]
def evalₐ (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y] (x : X) :
    LocallyConstant X Y →ₐ[R] Y :=
  (Pi.evalAlgHom _ _ x).comp (coeFnAlgHom R)

end Eval

section Comap

variable [TopologicalSpace Y]

/-- `LocallyConstant.comap` as a `MulHom`. -/
@[to_additive (attr := simps) "`LocallyConstant.comap` as an `AddHom`."]
noncomputable
def comapMulHom [Mul Z] (f : X → Y) (hf : Continuous f) :
    LocallyConstant Y Z →ₙ* LocallyConstant X Z where
  toFun := comap f
  map_mul' r s := by ext x; simp [hf]
                     -- ⊢ ↑(comap f (r * s)) x = ↑(comap f r * comap f s) x
                            -- 🎉 no goals

/-- `LocallyConstant.comap` as a `MonoidHom`. -/
@[to_additive (attr := simps) "`LocallyConstant.comap` as an `AddMonoidHom`."]
noncomputable
def comapMonoidHom [MulOneClass Z] (f : X → Y) (hf : Continuous f) :
    LocallyConstant Y Z →* LocallyConstant X Z where
  toFun := comap f
  map_one' := by ext x; simp [hf]
                 -- ⊢ ↑(comap f 1) x = ↑1 x
                        -- 🎉 no goals
  map_mul' := map_mul (comapMulHom f hf)

/-- `LocallyConstant.comap` as a linear map. -/
@[simps!]
noncomputable
def comapₗ (R : Type*) [Semiring R] [AddCommMonoid Z] [Module R Z] (f : X → Y)
    (hf : Continuous f) : LocallyConstant Y Z →ₗ[R] LocallyConstant X Z where
  toFun := comap f
  map_add' := map_add (comapAddMonoidHom f hf)
  map_smul' r s := by ext x; simp [hf]
                      -- ⊢ ↑(AddHom.toFun { toFun := comap f, map_add' := (_ : ∀ (x y : LocallyConstant …
                             -- 🎉 no goals

/-- `LocallyConstant.comap` as a `RingHom`. -/
@[simps!]
noncomputable
def comapRingHom [Semiring Z] (f : X → Y) (hf : Continuous f) :
    LocallyConstant Y Z →+* LocallyConstant X Z where
  toMonoidHom := comapMonoidHom f hf
  __ := (comapAddMonoidHom f hf)

/-- `LocallyConstant.comap` as an `AlgHom` -/
@[simps!]
noncomputable
def comapₐ (R: Type*) [CommSemiring R] [Semiring Z] [Algebra R Z]
    (f : X → Y) (hf : Continuous f) : LocallyConstant Y Z →ₐ[R] LocallyConstant X Z where
  toRingHom := comapRingHom f hf
  commutes' r := by ext x; simp [hf]
                    -- ⊢ ↑(OneHom.toFun (↑↑(comapRingHom f hf)) (↑(algebraMap R (LocallyConstant Y Z) …
                           -- 🎉 no goals

lemma ker_comapₗ [Semiring R] [AddCommMonoid Z] [Module R Z] (f : X → Y)
    (hf : Continuous f) (hfs : Function.Surjective f) :
    LinearMap.ker (comapₗ R f hf : LocallyConstant Y Z →ₗ[R] LocallyConstant X Z) = ⊥ :=
  LinearMap.ker_eq_bot_of_injective <| comap_injective _ hf hfs

/-- `LocallyConstant.congrLeft` as a `MulEquiv`. -/
@[to_additive (attr := simps!) "`LocallyConstant.congrLeft` as an `AddEquiv`."]
noncomputable
def congrLeftMulEquiv [Mul Z] (e : X ≃ₜ Y) :
    LocallyConstant X Z ≃* LocallyConstant Y Z where
  toEquiv := congrLeft e
  map_mul' := map_mul (comapMulHom _ e.symm.continuous)

/-- `LocallyConstant.congrLeft` as a linear equivalence. -/
@[simps!]
noncomputable
def congrLeftₗ (R: Type*) [Semiring R] [AddCommMonoid Z] [Module R Z] (e : X ≃ₜ Y) :
    LocallyConstant X Z ≃ₗ[R] LocallyConstant Y Z where
  toLinearMap := comapₗ R _ e.symm.continuous
  __ := congrLeft e

/-- `LocallyConstant.congrLeft` as a `RingEquiv`. -/
@[simps!]
noncomputable
def congrLeftRingEquiv [Semiring Z] (e : X ≃ₜ Y) :
    LocallyConstant X Z ≃+* LocallyConstant Y Z where
  toEquiv := congrLeft e
  __ := comapMonoidHom _ e.symm.continuous
  __ := comapAddMonoidHom _ e.symm.continuous

/-- `LocallyConstant.congrLeft` as an `AlgEquiv`. -/
@[simps!]
noncomputable
def congrLeftₐ (R: Type*) [CommSemiring R] [Semiring Z] [Algebra R Z] (e : X ≃ₜ Y) :
    LocallyConstant X Z ≃ₐ[R] LocallyConstant Y Z where
  toEquiv := congrLeft e
  __ := comapₐ R _ e.symm.continuous

end Comap

end LocallyConstant
