/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Torsion.Pi
public import Mathlib.GroupTheory.GroupAction.DomAct.Basic

/-!
# Further results on (semi)linear maps
-/

@[expose] public section


assert_not_exists Submonoid Finset TrivialStar

open Function

universe u u' v w x y z

variable {R R' S M M' : Type*}

namespace LinearMap

section toFunAsLinearMap

variable {R M N A : Type*} [Semiring R] [Semiring A]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [Module A N] [SMulCommClass R A N]

variable (R M N A) in
/-- `A`-linearly coerce an `R`-linear map from `M` to `N` to a function, when `N` has
commuting `R`-module and `A`-module structures. -/
def ltoFun : (M →ₗ[R] N) →ₗ[A] (M → N) where
  toFun f := f.toFun
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma ltoFun_apply {f : M →ₗ[R] N} : ltoFun R M N A f = f := rfl

end toFunAsLinearMap

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

instance [Module.IsTorsionFree S M'] : Module.IsTorsionFree S (M →ₛₗ[σ₁₂] M') :=
  coe_injective.moduleIsTorsionFree _ coe_smul

instance [SMulCommClass R S M] : Module Sᵈᵐᵃ (M →ₛₗ[σ₁₂] M') where
  add_smul _ _ _ := ext fun _ ↦ by
    simp_rw [add_apply, DomMulAct.smul_linearMap_apply, ← map_add, ← add_smul]; rfl
  zero_smul _ := ext fun _ ↦ by
    simp [DomMulAct.smul_linearMap_apply, DomMulAct.mk, MulOpposite.opEquiv]

end Module

end Actions

section mulLeftRight
variable {R A : Type*} [Semiring R]

section nonUnitalSemiring
variable (R A) [NonUnitalSemiring A] [Module R A]

@[simp]
theorem mulLeft_mul [SMulCommClass R A A] (a b : A) :
    mulLeft R (a * b) = (mulLeft R a).comp (mulLeft R b) := by
  ext
  simp only [mulLeft_apply, comp_apply, mul_assoc]

@[simp]
theorem mulRight_mul [IsScalarTower R A A] (a b : A) :
    mulRight R (a * b) = (mulRight R b).comp (mulRight R a) := by
  ext
  simp only [mulRight_apply, comp_apply, mul_assoc]

end nonUnitalSemiring

section nonAssocSemiring
variable [NonAssocSemiring A] [Module R A]

@[simp] lemma mulLeft_inj [SMulCommClass R A A] {a b : A} :
    mulLeft R a = mulLeft R b ↔ a = b :=
  ⟨fun h => by simpa using LinearMap.ext_iff.mp h 1, fun h => h ▸ rfl⟩

@[simp] lemma mulRight_inj [IsScalarTower R A A] {a b : A} :
    mulRight R a = mulRight R b ↔ a = b :=
  ⟨fun h => by simpa using LinearMap.ext_iff.mp h 1, fun h => h ▸ rfl⟩

section
variable (R A)

@[simp]
theorem mulLeft_one [SMulCommClass R A A] : mulLeft R (1 : A) = LinearMap.id := ext one_mul

@[simp]
theorem mulLeft_eq_zero_iff [SMulCommClass R A A] (a : A) : mulLeft R a = 0 ↔ a = 0 :=
  mulLeft_zero_eq_zero R A ▸ mulLeft_inj

@[simp]
theorem mulRight_one [IsScalarTower R A A] : mulRight R (1 : A) = LinearMap.id :=
  ext mul_one

@[simp]
theorem mulRight_eq_zero_iff [IsScalarTower R A A] (a : A) : mulRight R a = 0 ↔ a = 0 :=
  mulRight_zero_eq_zero R A ▸ mulRight_inj

end
end nonAssocSemiring
end mulLeftRight

end LinearMap
