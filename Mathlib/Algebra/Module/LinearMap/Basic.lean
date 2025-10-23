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


assert_not_exists Submonoid Finset TrivialStar

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

instance : SMul S'ᵈᵐᵃ (M →ₛₗ[σ₁₂] M') where
  smul a f :=
    { toFun := a • (f : M → M')
      map_add' := fun x y ↦ by simp only [DomMulAct.smul_apply, f.map_add, smul_add]
      map_smul' := fun c x ↦ by simp_rw [DomMulAct.smul_apply, ← smul_comm, f.map_smulₛₗ] }

theorem _root_.DomMulAct.smul_linearMap_apply (a : S'ᵈᵐᵃ) (f : M →ₛₗ[σ₁₂] M') (x : M) :
    (a • f) x = f (DomMulAct.mk.symm a • x) :=
  rfl

@[simp]
theorem _root_.DomMulAct.mk_smul_linearMap_apply (a : S') (f : M →ₛₗ[σ₁₂] M') (x : M) :
    (DomMulAct.mk a • f) x = f (a • x) :=
  rfl

theorem _root_.DomMulAct.coe_smul_linearMap (a : S'ᵈᵐᵃ) (f : M →ₛₗ[σ₁₂] M') :
    (a • f : M →ₛₗ[σ₁₂] M') = a • (f : M → M') :=
  rfl

instance [SMulCommClass S' T' M] : SMulCommClass S'ᵈᵐᵃ T'ᵈᵐᵃ (M →ₛₗ[σ₁₂] M') :=
  ⟨fun s t f ↦ ext fun m ↦ by simp_rw [DomMulAct.smul_linearMap_apply, smul_comm]⟩

end SMul


section Actions

variable [Semiring R] [Semiring R']
variable [AddCommMonoid M] [AddCommMonoid M']
variable [Module R M] [Module R' M']
variable {σ₁₂ : R →+* R'}

section SMul

instance {S'} [Monoid S'] [DistribMulAction S' M] [SMulCommClass R S' M] :
    DistribMulAction S'ᵈᵐᵃ (M →ₛₗ[σ₁₂] M') where
  one_smul _ := ext fun _ ↦ congr_arg _ (one_smul _ _)
  mul_smul _ _ _ := ext fun _ ↦ congr_arg _ (mul_smul _ _ _)
  smul_add _ _ _ := ext fun _ ↦ rfl
  smul_zero _ := ext fun _ ↦ rfl

end SMul

section Module

variable [Semiring S] [Module S M] [Module S M'] [SMulCommClass R' S M']

instance [NoZeroSMulDivisors S M'] : NoZeroSMulDivisors S (M →ₛₗ[σ₁₂] M') :=
  coe_injective.noZeroSMulDivisors _ rfl coe_smul

instance [SMulCommClass R S M] : Module Sᵈᵐᵃ (M →ₛₗ[σ₁₂] M') where
  add_smul _ _ _ := ext fun _ ↦ by
    simp_rw [add_apply, DomMulAct.smul_linearMap_apply, ← map_add, ← add_smul]; rfl
  zero_smul _ := ext fun _ ↦ by erw [DomMulAct.smul_linearMap_apply, zero_smul, map_zero]; rfl

end Module

end Actions

end LinearMap
