/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.NoZeroSMulDivisors.Pi
import Mathlib.Algebra.Ring.Opposite
import Mathlib.GroupTheory.GroupAction.DomAct.Basic

/-!
# Further results on (semi)linear maps
-/


assert_not_exists Submonoid Finset Star

open Function

universe u u' v w x y z

variable {R R' S M M' : Type*}

namespace LinearMap

section SMul

variable [Semiring R] [Semiring R']
variable [AddCommMonoid M] [AddCommMonoid M']
variable [Module R M] [Module R' M']
variable {σ₁₂ : R →+* R'}

variable {S' T' : Type*}
variable [Monoid S'] [DistribMulAction S' M] [SMulCommClass R S' M]
variable [Monoid T'] [DistribMulAction T' M] [SMulCommClass R T' M]

instance : SMul S'ᵈᵃ (M →ₛₗ[σ₁₂] M') where
  smul a f :=
    { toFun := a • (f : M → M')
      map_add' := fun x y ↦ by simp only [DomAct.smul_apply, f.map_add, smul_add]
      map_smul' := fun c x ↦ by simp_rw [DomAct.smul_apply, ← smul_comm, f.map_smulₛₗ] }

theorem _root_.DomAct.smul_linearMap_apply (a : S'ᵈᵃ) (f : M →ₛₗ[σ₁₂] M') (x : M) :
    (a • f) x = f (DomAct.mk.symm a • x) :=
  rfl

@[deprecated (since := "2025-04-02")]
alias _root_.DomMulAct.smul_linearMap_apply := _root_.DomAct.smul_linearMap_apply

@[simp]
theorem _root_.DomAct.mk_smul_linearMap_apply (a : S') (f : M →ₛₗ[σ₁₂] M') (x : M) :
    (DomAct.mk a • f) x = f (a • x) :=
  rfl

@[deprecated (since := "2025-04-02")]
alias _root_.DomMulAct.mk_smul_linearMap_apply := _root_.DomAct.mk_smul_linearMap_apply

theorem _root_.DomAct.coe_smul_linearMap (a : S'ᵈᵃ) (f : M →ₛₗ[σ₁₂] M') :
    (a • f : M →ₛₗ[σ₁₂] M') = a • (f : M → M') :=
  rfl

@[deprecated (since := "2025-04-02")]
alias _root_.DomMulAct.coe_smul_linearMap := _root_.DomAct.coe_smul_linearMap

instance [SMulCommClass S' T' M] : SMulCommClass S'ᵈᵃ T'ᵈᵃ (M →ₛₗ[σ₁₂] M') :=
  ⟨fun s t f ↦ ext fun m ↦ by simp_rw [DomAct.smul_linearMap_apply, smul_comm]⟩

end SMul


section Actions

variable [Semiring R] [Semiring R']
variable [AddCommMonoid M] [AddCommMonoid M']
variable [Module R M] [Module R' M']
variable {σ₁₂ : R →+* R'}

section SMul

instance {S'} [Monoid S'] [DistribMulAction S' M] [SMulCommClass R S' M] :
    DistribMulAction S'ᵈᵃ (M →ₛₗ[σ₁₂] M') where
  one_smul _ := ext fun _ ↦ congr_arg _ (one_smul _ _)
  mul_smul _ _ _ := ext fun _ ↦ congr_arg _ (mul_smul _ _ _)
  smul_add _ _ _ := ext fun _ ↦ rfl
  smul_zero _ := ext fun _ ↦ rfl

end SMul

section Module

variable [Semiring S] [Module S M] [Module S M'] [SMulCommClass R' S M']

instance [NoZeroSMulDivisors S M'] : NoZeroSMulDivisors S (M →ₛₗ[σ₁₂] M') :=
  coe_injective.noZeroSMulDivisors _ rfl coe_smul

instance [SMulCommClass R S M] : Module Sᵈᵃ (M →ₛₗ[σ₁₂] M') where
  add_smul _ _ _ := ext fun _ ↦ by
    simp_rw [add_apply, DomAct.smul_linearMap_apply, ← map_add, ← add_smul]; rfl
  zero_smul _ := ext fun _ ↦ by erw [DomAct.smul_linearMap_apply, zero_smul, map_zero]; rfl

end Module

end Actions

end LinearMap
