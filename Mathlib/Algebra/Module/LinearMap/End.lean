/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/

import Mathlib.Algebra.Module.LinearMap.Basic

/-!
# Endomorphisms of a module

In this file we define the type of linear endomorphisms of a module over a ring (`Module.End`).
We set up the basic theory,
including the action of `Module.End` on the module we are considering endomorphisms of.

## Main results

* `Module.End.semiring` and `Module.End.ring`: the (semi)ring of endomorphisms formed by taking the
  additive structure above with composition as multiplication.

-/

universe u v

/-- Linear endomorphisms of a module, with associated ring structure
`Module.End.semiring` and algebra structure `Module.End.algebra`. -/
abbrev Module.End (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] :=
  M →ₗ[R] M
#align module.End Module.End

variable {R R₁ R₂ S M M₁ M₂ M₃ N N₁ N₂ : Type*}

namespace LinearMap

open Function

/-!
## Monoid structure of endomorphisms
-/

section Endomorphisms

variable [Semiring R] [AddCommMonoid M] [AddCommGroup N₁] [Module R M] [Module R N₁]

instance : One (Module.End R M) := ⟨LinearMap.id⟩

instance : Mul (Module.End R M) := ⟨LinearMap.comp⟩

theorem one_eq_id : (1 : Module.End R M) = id := rfl
#align linear_map.one_eq_id LinearMap.one_eq_id

theorem mul_eq_comp (f g : Module.End R M) : f * g = f.comp g := rfl
#align linear_map.mul_eq_comp LinearMap.mul_eq_comp

@[simp]
theorem one_apply (x : M) : (1 : Module.End R M) x = x := rfl
#align linear_map.one_apply LinearMap.one_apply

@[simp]
theorem mul_apply (f g : Module.End R M) (x : M) : (f * g) x = f (g x) := rfl
#align linear_map.mul_apply LinearMap.mul_apply

theorem coe_one : ⇑(1 : Module.End R M) = _root_.id := rfl
#align linear_map.coe_one LinearMap.coe_one

theorem coe_mul (f g : Module.End R M) : ⇑(f * g) = f ∘ g := rfl
#align linear_map.coe_mul LinearMap.coe_mul

instance _root_.Module.End.instNontrivial [Nontrivial M] : Nontrivial (Module.End R M) := by
  obtain ⟨m, ne⟩ := exists_ne (0 : M)
  exact nontrivial_of_ne 1 0 fun p => ne (LinearMap.congr_fun p m)

instance _root_.Module.End.monoid : Monoid (Module.End R M) where
  mul := (· * ·)
  one := (1 : M →ₗ[R] M)
  mul_assoc f g h := LinearMap.ext fun x ↦ rfl
  mul_one := comp_id
  one_mul := id_comp
#align module.End.monoid Module.End.monoid

instance _root_.Module.End.semiring : Semiring (Module.End R M) :=
  { AddMonoidWithOne.unary, Module.End.monoid, LinearMap.addCommMonoid with
    mul_zero := comp_zero
    zero_mul := zero_comp
    left_distrib := fun _ _ _ ↦ comp_add _ _ _
    right_distrib := fun _ _ _ ↦ add_comp _ _ _
    natCast := fun n ↦ n • (1 : M →ₗ[R] M)
    natCast_zero := zero_smul ℕ (1 : M →ₗ[R] M)
    natCast_succ := fun n ↦ AddMonoid.nsmul_succ n (1 : M →ₗ[R] M) }
#align module.End.semiring Module.End.semiring

/-- See also `Module.End.natCast_def`. -/
@[simp]
theorem _root_.Module.End.natCast_apply (n : ℕ) (m : M) : (↑n : Module.End R M) m = n • m := rfl
#align module.End.nat_cast_apply Module.End.natCast_apply

@[simp]
theorem _root_.Module.End.ofNat_apply (n : ℕ) [n.AtLeastTwo] (m : M) :
    (no_index (OfNat.ofNat n) : Module.End R M) m = OfNat.ofNat n • m := rfl

instance _root_.Module.End.ring : Ring (Module.End R N₁) :=
  { Module.End.semiring, LinearMap.addCommGroup with
    intCast := fun z ↦ z • (1 : N₁ →ₗ[R] N₁)
    intCast_ofNat := natCast_zsmul _
    intCast_negSucc := negSucc_zsmul _ }
#align module.End.ring Module.End.ring

/-- See also `Module.End.intCast_def`. -/
@[simp]
theorem _root_.Module.End.intCast_apply (z : ℤ) (m : N₁) : (z : Module.End R N₁) m = z • m :=
  rfl
#align module.End.int_cast_apply Module.End.intCast_apply

section

variable [Monoid S] [DistribMulAction S M] [SMulCommClass R S M]

instance _root_.Module.End.isScalarTower :
    IsScalarTower S (Module.End R M) (Module.End R M) :=
  ⟨smul_comp⟩
#align module.End.is_scalar_tower Module.End.isScalarTower

instance _root_.Module.End.smulCommClass [SMul S R] [IsScalarTower S R M] :
    SMulCommClass S (Module.End R M) (Module.End R M) :=
  ⟨fun s _ _ ↦ (comp_smul _ s _).symm⟩
#align module.End.smul_comm_class Module.End.smulCommClass

instance _root_.Module.End.smulCommClass' [SMul S R] [IsScalarTower S R M] :
    SMulCommClass (Module.End R M) S (Module.End R M) :=
  SMulCommClass.symm _ _ _
#align module.End.smul_comm_class' Module.End.smulCommClass'

theorem _root_.Module.End_isUnit_apply_inv_apply_of_isUnit
    {f : Module.End R M} (h : IsUnit f) (x : M) :
    f (h.unit.inv x) = x :=
  show (f * h.unit.inv) x = x by simp
#align module.End_is_unit_apply_inv_apply_of_is_unit Module.End_isUnit_apply_inv_apply_of_isUnit

theorem _root_.Module.End_isUnit_inv_apply_apply_of_isUnit
    {f : Module.End R M} (h : IsUnit f) (x : M) :
    h.unit.inv (f x) = x :=
  (by simp : (h.unit.inv * f) x = x)
#align module.End_is_unit_inv_apply_apply_of_is_unit Module.End_isUnit_inv_apply_apply_of_isUnit

theorem coe_pow (f : M →ₗ[R] M) (n : ℕ) : ⇑(f ^ n) = f^[n] := hom_coe_pow _ rfl (fun _ _ ↦ rfl) _ _
#align linear_map.coe_pow LinearMap.coe_pow

theorem pow_apply (f : M →ₗ[R] M) (n : ℕ) (m : M) : (f ^ n) m = f^[n] m := congr_fun (coe_pow f n) m
#align linear_map.pow_apply LinearMap.pow_apply

theorem pow_map_zero_of_le {f : Module.End R M} {m : M} {k l : ℕ} (hk : k ≤ l)
    (hm : (f ^ k) m = 0) : (f ^ l) m = 0 := by
  rw [← tsub_add_cancel_of_le hk, pow_add, mul_apply, hm, map_zero]
#align linear_map.pow_map_zero_of_le LinearMap.pow_map_zero_of_le

theorem commute_pow_left_of_commute
    [Semiring R₂] [AddCommMonoid M₂] [Module R₂ M₂] {σ₁₂ : R →+* R₂}
    {f : M →ₛₗ[σ₁₂] M₂} {g : Module.End R M} {g₂ : Module.End R₂ M₂}
    (h : g₂.comp f = f.comp g) (k : ℕ) : (g₂ ^ k).comp f = f.comp (g ^ k) := by
  induction' k with k ih
  · simp only [Nat.zero_eq, pow_zero, one_eq_id, id_comp, comp_id]
  · rw [pow_succ', pow_succ', LinearMap.mul_eq_comp, LinearMap.comp_assoc, ih,
    ← LinearMap.comp_assoc, h, LinearMap.comp_assoc, LinearMap.mul_eq_comp]
#align linear_map.commute_pow_left_of_commute LinearMap.commute_pow_left_of_commute

@[simp]
theorem id_pow (n : ℕ) : (id : M →ₗ[R] M) ^ n = id :=
  one_pow n
#align linear_map.id_pow LinearMap.id_pow

variable {f' : M →ₗ[R] M}

theorem iterate_succ (n : ℕ) : f' ^ (n + 1) = comp (f' ^ n) f' := by rw [pow_succ, mul_eq_comp]
#align linear_map.iterate_succ LinearMap.iterate_succ

theorem iterate_surjective (h : Surjective f') : ∀ n : ℕ, Surjective (f' ^ n)
  | 0 => surjective_id
  | n + 1 => by
    rw [iterate_succ]
    exact (iterate_surjective h n).comp h
#align linear_map.iterate_surjective LinearMap.iterate_surjective

theorem iterate_injective (h : Injective f') : ∀ n : ℕ, Injective (f' ^ n)
  | 0 => injective_id
  | n + 1 => by
    rw [iterate_succ]
    exact (iterate_injective h n).comp h
#align linear_map.iterate_injective LinearMap.iterate_injective

theorem iterate_bijective (h : Bijective f') : ∀ n : ℕ, Bijective (f' ^ n)
  | 0 => bijective_id
  | n + 1 => by
    rw [iterate_succ]
    exact (iterate_bijective h n).comp h
#align linear_map.iterate_bijective LinearMap.iterate_bijective

theorem injective_of_iterate_injective {n : ℕ} (hn : n ≠ 0) (h : Injective (f' ^ n)) :
    Injective f' := by
  rw [← Nat.succ_pred_eq_of_pos (pos_iff_ne_zero.mpr hn), iterate_succ, coe_comp] at h
  exact h.of_comp
#align linear_map.injective_of_iterate_injective LinearMap.injective_of_iterate_injective

theorem surjective_of_iterate_surjective {n : ℕ} (hn : n ≠ 0) (h : Surjective (f' ^ n)) :
    Surjective f' := by
  rw [← Nat.succ_pred_eq_of_pos (pos_iff_ne_zero.mpr hn), pow_succ', coe_mul] at h
  exact Surjective.of_comp h
#align linear_map.surjective_of_iterate_surjective LinearMap.surjective_of_iterate_surjective

end

/-! ## Action by a module endomorphism. -/


/-- The tautological action by `Module.End R M` (aka `M →ₗ[R] M`) on `M`.

This generalizes `Function.End.applyMulAction`. -/
instance applyModule : Module (Module.End R M) M where
  smul := (· <| ·)
  smul_zero := LinearMap.map_zero
  smul_add := LinearMap.map_add
  add_smul := LinearMap.add_apply
  zero_smul := (LinearMap.zero_apply : ∀ m, (0 : M →ₗ[R] M) m = 0)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
#align linear_map.apply_module LinearMap.applyModule

@[simp]
protected theorem smul_def (f : Module.End R M) (a : M) : f • a = f a :=
  rfl
#align linear_map.smul_def LinearMap.smul_def

/-- `LinearMap.applyModule` is faithful. -/
instance apply_faithfulSMul : FaithfulSMul (Module.End R M) M :=
  ⟨LinearMap.ext⟩
#align linear_map.apply_has_faithful_smul LinearMap.apply_faithfulSMul

instance apply_smulCommClass : SMulCommClass R (Module.End R M) M where
  smul_comm r e m := (e.map_smul r m).symm
#align linear_map.apply_smul_comm_class LinearMap.apply_smulCommClass

instance apply_smulCommClass' : SMulCommClass (Module.End R M) R M where
  smul_comm := LinearMap.map_smul
#align linear_map.apply_smul_comm_class' LinearMap.apply_smulCommClass'

instance apply_isScalarTower {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] :
    IsScalarTower R (Module.End R M) M :=
  ⟨fun _ _ _ ↦ rfl⟩
#align linear_map.apply_is_scalar_tower LinearMap.apply_isScalarTower

end Endomorphisms

end LinearMap

/-! ## Actions as module endomorphisms -/


namespace DistribMulAction

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]
variable [Monoid S] [DistribMulAction S M] [SMulCommClass S R M]

/-- Each element of the monoid defines a linear map.

This is a stronger version of `DistribMulAction.toAddMonoidHom`. -/
@[simps]
def toLinearMap (s : S) : M →ₗ[R] M where
  toFun := HSMul.hSMul s
  map_add' := smul_add s
  map_smul' _ _ := smul_comm _ _ _
#align distrib_mul_action.to_linear_map DistribMulAction.toLinearMap
#align distrib_mul_action.to_linear_map_apply DistribMulAction.toLinearMap_apply

/-- Each element of the monoid defines a module endomorphism.

This is a stronger version of `DistribMulAction.toAddMonoidEnd`. -/
@[simps]
def toModuleEnd : S →* Module.End R M where
  toFun := toLinearMap R M
  map_one' := LinearMap.ext <| one_smul _
  map_mul' _ _ := LinearMap.ext <| mul_smul _ _
#align distrib_mul_action.to_module_End DistribMulAction.toModuleEnd
#align distrib_mul_action.to_module_End_apply DistribMulAction.toModuleEnd_apply

end DistribMulAction

namespace Module

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M]
variable [Semiring S] [Module S M] [SMulCommClass S R M]

/-- Each element of the semiring defines a module endomorphism.

This is a stronger version of `DistribMulAction.toModuleEnd`. -/
@[simps]
def toModuleEnd : S →+* Module.End R M :=
  { DistribMulAction.toModuleEnd R M with
    toFun := DistribMulAction.toLinearMap R M
    map_zero' := LinearMap.ext <| zero_smul S
    map_add' := fun _ _ ↦ LinearMap.ext <| add_smul _ _ }
#align module.to_module_End Module.toModuleEnd
#align module.to_module_End_apply Module.toModuleEnd_apply

/-- The canonical (semi)ring isomorphism from `Rᵐᵒᵖ` to `Module.End R R` induced by the right
multiplication. -/
@[simps]
def moduleEndSelf : Rᵐᵒᵖ ≃+* Module.End R R :=
  { Module.toModuleEnd R R with
    toFun := DistribMulAction.toLinearMap R R
    invFun := fun f ↦ MulOpposite.op (f 1)
    left_inv := mul_one
    right_inv := fun _ ↦ LinearMap.ext_ring <| one_mul _ }
#align module.module_End_self Module.moduleEndSelf
#align module.module_End_self_apply Module.moduleEndSelf_apply

/-- The canonical (semi)ring isomorphism from `R` to `Module.End Rᵐᵒᵖ R` induced by the left
multiplication. -/
@[simps]
def moduleEndSelfOp : R ≃+* Module.End Rᵐᵒᵖ R :=
  { Module.toModuleEnd _ _ with
    toFun := DistribMulAction.toLinearMap _ _
    invFun := fun f ↦ f 1
    left_inv := mul_one
    right_inv := fun _ ↦ LinearMap.ext_ring_op <| mul_one _ }
#align module.module_End_self_op Module.moduleEndSelfOp
#align module.module_End_self_op_symm_apply Module.moduleEndSelfOp_symm_apply
#align module.module_End_self_op_apply Module.moduleEndSelfOp_apply

theorem End.natCast_def (n : ℕ) [AddCommMonoid N₁] [Module R N₁] :
    (↑n : Module.End R N₁) = Module.toModuleEnd R N₁ n :=
  rfl
#align module.End.nat_cast_def Module.End.natCast_def

theorem End.intCast_def (z : ℤ) [AddCommGroup N₁] [Module R N₁] :
    (z : Module.End R N₁) = Module.toModuleEnd R N₁ z :=
  rfl
#align module.End.int_cast_def Module.End.intCast_def

end Module

namespace LinearMap

section AddCommMonoid

section SMulRight

variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₁] [Module R M] [Module R M₁]
variable [Semiring S] [Module R S] [Module S M] [IsScalarTower R S M]

/-- When `f` is an `R`-linear map taking values in `S`, then `fun b ↦ f b • x` is an `R`-linear
map. -/
def smulRight (f : M₁ →ₗ[R] S) (x : M) : M₁ →ₗ[R] M where
  toFun b := f b • x
  map_add' x y := by dsimp only; rw [f.map_add, add_smul]
  map_smul' b y := by dsimp; rw [map_smul, smul_assoc]
#align linear_map.smul_right LinearMap.smulRight

@[simp]
theorem coe_smulRight (f : M₁ →ₗ[R] S) (x : M) : (smulRight f x : M₁ → M) = fun c => f c • x :=
  rfl
#align linear_map.coe_smul_right LinearMap.coe_smulRight

theorem smulRight_apply (f : M₁ →ₗ[R] S) (x : M) (c : M₁) : smulRight f x c = f c • x :=
  rfl
#align linear_map.smul_right_apply LinearMap.smulRight_apply

@[simp]
lemma smulRight_zero (f : M₁ →ₗ[R] S) : f.smulRight (0 : M) = 0 := by ext; simp

@[simp]
lemma zero_smulRight (x : M) : (0 : M₁ →ₗ[R] S).smulRight x = 0 := by ext; simp

@[simp]
lemma smulRight_apply_eq_zero_iff {f : M₁ →ₗ[R] S} {x : M} [NoZeroSMulDivisors S M] :
    f.smulRight x = 0 ↔ f = 0 ∨ x = 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  refine ⟨fun h ↦ Or.inl ?_, fun h ↦ by simp [h.resolve_right hx]⟩
  ext v
  replace h : f v • x = 0 := by simpa only [LinearMap.zero_apply] using LinearMap.congr_fun h v
  rw [smul_eq_zero] at h
  tauto

end SMulRight

end AddCommMonoid

section Module

variable [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R M₂] [Module S M₂] [SMulCommClass R S M₂]
variable (S)

/-- Applying a linear map at `v : M`, seen as `S`-linear map from `M →ₗ[R] M₂` to `M₂`.

 See `LinearMap.applyₗ` for a version where `S = R`. -/
@[simps]
def applyₗ' : M →+ (M →ₗ[R] M₂) →ₗ[S] M₂ where
  toFun v :=
    { toFun := fun f => f v
      map_add' := fun f g => f.add_apply g v
      map_smul' := fun x f => f.smul_apply x v }
  map_zero' := LinearMap.ext fun f => f.map_zero
  map_add' _ _ := LinearMap.ext fun f => f.map_add _ _
#align linear_map.applyₗ' LinearMap.applyₗ'

end Module

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₂] [Module R M₃]
variable (f g : M →ₗ[R] M₂)

/-- Composition by `f : M₂ → M₃` is a linear map from the space of linear maps `M → M₂`
to the space of linear maps `M → M₃`. -/
def compRight (f : M₂ →ₗ[R] M₃) : (M →ₗ[R] M₂) →ₗ[R] M →ₗ[R] M₃ where
  toFun := f.comp
  map_add' _ _ := LinearMap.ext fun _ => map_add f _ _
  map_smul' _ _ := LinearMap.ext fun _ => map_smul f _ _
#align linear_map.comp_right LinearMap.compRight

@[simp]
theorem compRight_apply (f : M₂ →ₗ[R] M₃) (g : M →ₗ[R] M₂) : compRight f g = f.comp g :=
  rfl
#align linear_map.comp_right_apply LinearMap.compRight_apply

/-- Applying a linear map at `v : M`, seen as a linear map from `M →ₗ[R] M₂` to `M₂`.
See also `LinearMap.applyₗ'` for a version that works with two different semirings.

This is the `LinearMap` version of `toAddMonoidHom.eval`. -/
@[simps]
def applyₗ : M →ₗ[R] (M →ₗ[R] M₂) →ₗ[R] M₂ :=
  { applyₗ' R with
    toFun := fun v => { applyₗ' R v with toFun := fun f => f v }
    map_smul' := fun _ _ => LinearMap.ext fun f => map_smul f _ _ }
#align linear_map.applyₗ LinearMap.applyₗ

/--
The family of linear maps `M₂ → M` parameterised by `f ∈ M₂ → R`, `x ∈ M`, is linear in `f`, `x`.
-/
def smulRightₗ : (M₂ →ₗ[R] R) →ₗ[R] M →ₗ[R] M₂ →ₗ[R] M where
  toFun f :=
    { toFun := LinearMap.smulRight f
      map_add' := fun m m' => by
        ext
        apply smul_add
      map_smul' := fun c m => by
        ext
        apply smul_comm }
  map_add' f f' := by
    ext
    apply add_smul
  map_smul' c f := by
    ext
    apply mul_smul
#align linear_map.smul_rightₗ LinearMap.smulRightₗ

@[simp]
theorem smulRightₗ_apply (f : M₂ →ₗ[R] R) (x : M) (c : M₂) :
    (smulRightₗ : (M₂ →ₗ[R] R) →ₗ[R] M →ₗ[R] M₂ →ₗ[R] M) f x c = f c • x :=
  rfl
#align linear_map.smul_rightₗ_apply LinearMap.smulRightₗ_apply

end CommSemiring

end LinearMap
