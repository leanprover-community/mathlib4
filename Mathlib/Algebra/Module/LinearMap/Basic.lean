/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.GroupTheory.GroupAction.DomAct.Basic

#align_import algebra.module.linear_map from "leanprover-community/mathlib"@"cc8e88c7c8c7bc80f91f84d11adb584bf9bd658f"

/-!
# Further results on (semi)linear maps
-/


assert_not_exists Submonoid
assert_not_exists Finset
assert_not_exists Star

open Function

universe u u' v w x y z

variable {R R₁ R₂ R₃ k S S₃ T M M₁ M₂ M₃ N₁ N₂ N₃ ι : Type*}

/-- Reinterpret an additive homomorphism as a `ℚ`-linear map. -/
def AddMonoidHom.toRatLinearMap [AddCommGroup M] [Module ℚ M] [AddCommGroup M₂] [Module ℚ M₂]
    (f : M →+ M₂) : M →ₗ[ℚ] M₂ :=
  { f with map_smul' := map_rat_smul f }
#align add_monoid_hom.to_rat_linear_map AddMonoidHom.toRatLinearMap

theorem AddMonoidHom.toRatLinearMap_injective [AddCommGroup M] [Module ℚ M] [AddCommGroup M₂]
    [Module ℚ M₂] : Function.Injective (@AddMonoidHom.toRatLinearMap M M₂ _ _ _ _) := by
  intro f g h
  ext x
  exact LinearMap.congr_fun h x
#align add_monoid_hom.to_rat_linear_map_injective AddMonoidHom.toRatLinearMap_injective

@[simp]
theorem AddMonoidHom.coe_toRatLinearMap [AddCommGroup M] [Module ℚ M] [AddCommGroup M₂]
    [Module ℚ M₂] (f : M →+ M₂) : ⇑f.toRatLinearMap = f :=
  rfl
#align add_monoid_hom.coe_to_rat_linear_map AddMonoidHom.coe_toRatLinearMap

namespace LinearMap

section SMul

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R₂ M₂]
variable {σ₁₂ : R →+* R₂}

variable {S' T' : Type*}
variable [Monoid S'] [DistribMulAction S' M] [SMulCommClass R S' M]
variable [Monoid T'] [DistribMulAction T' M] [SMulCommClass R T' M]

instance : SMul S'ᵈᵐᵃ (M →ₛₗ[σ₁₂] M₂) where
  smul a f :=
    { toFun := a • (f : M → M₂)
      map_add' := fun x y ↦ by simp only [DomMulAct.smul_apply, f.map_add, smul_add]
      map_smul' := fun c x ↦ by simp_rw [DomMulAct.smul_apply, ← smul_comm, f.map_smulₛₗ] }

theorem _root_.DomMulAct.smul_linearMap_apply (a : S'ᵈᵐᵃ) (f : M →ₛₗ[σ₁₂] M₂) (x : M) :
    (a • f) x = f (DomMulAct.mk.symm a • x) :=
  rfl

@[simp]
theorem _root_.DomMulAct.mk_smul_linearMap_apply (a : S') (f : M →ₛₗ[σ₁₂] M₂) (x : M) :
    (DomMulAct.mk a • f) x = f (a • x) :=
  rfl

theorem  _root_.DomMulAct.coe_smul_linearMap (a : S'ᵈᵐᵃ) (f : M →ₛₗ[σ₁₂] M₂) :
    (a • f : M →ₛₗ[σ₁₂] M₂) = a • (f : M → M₂) :=
  rfl

instance [SMulCommClass S' T' M] : SMulCommClass S'ᵈᵐᵃ T'ᵈᵐᵃ (M →ₛₗ[σ₁₂] M₂) :=
  ⟨fun s t f ↦ ext fun m ↦ by simp_rw [DomMulAct.smul_linearMap_apply, smul_comm]⟩

end SMul


section Actions

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]
variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

section SMul

variable [Monoid S] [DistribMulAction S M₂] [SMulCommClass R₂ S M₂]
variable [Monoid S₃] [DistribMulAction S₃ M₃] [SMulCommClass R₃ S₃ M₃]
variable [Monoid T] [DistribMulAction T M₂] [SMulCommClass R₂ T M₂]

instance {S'} [Monoid S'] [DistribMulAction S' M] [SMulCommClass R S' M] :
    DistribMulAction S'ᵈᵐᵃ (M →ₛₗ[σ₁₂] M₂) where
  one_smul _ := ext fun _ ↦ congr_arg _ (one_smul _ _)
  mul_smul _ _ _ := ext fun _ ↦ congr_arg _ (mul_smul _ _ _)
  smul_add _ _ _ := ext fun _ ↦ rfl
  smul_zero _ := ext fun _ ↦ rfl

end SMul

section Module

variable [Semiring S] [Module S M] [Module S M₂] [SMulCommClass R₂ S M₂]

instance [NoZeroSMulDivisors S M₂] : NoZeroSMulDivisors S (M →ₛₗ[σ₁₂] M₂) :=
  coe_injective.noZeroSMulDivisors _ rfl coe_smul

instance [SMulCommClass R S M] : Module Sᵈᵐᵃ (M →ₛₗ[σ₁₂] M₂) where
  add_smul _ _ _ := ext fun _ ↦ by
    simp_rw [add_apply, DomMulAct.smul_linearMap_apply, ← map_add, ← add_smul]; rfl
  zero_smul _ := ext fun _ ↦ by erw [DomMulAct.smul_linearMap_apply, zero_smul, map_zero]; rfl

end Module

end Actions

end LinearMap
