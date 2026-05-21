/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Restriction of scalars for continuous linear maps
-/

@[expose] public section

section RestrictScalars

namespace ContinuousLinearMap

section Semiring

variable {A M₁ M₂ R S : Type*} [Semiring A] [Semiring R] [Semiring S]
  [AddCommMonoid M₁] [Module A M₁] [Module R M₁] [TopologicalSpace M₁]
  [AddCommMonoid M₂] [Module A M₂] [Module R M₂] [TopologicalSpace M₂]
  [LinearMap.CompatibleSMul M₁ M₂ R A]

variable (R) in
/-- If `A` is an `R`-algebra, then a continuous `A`-linear map can be interpreted as a continuous
`R`-linear map. We assume `LinearMap.CompatibleSMul M₁ M₂ R A` to match assumptions of
`LinearMap.map_smul_of_tower`. -/
def restrictScalars (f : M₁ →L[A] M₂) : M₁ →L[R] M₂ :=
  ⟨(f : M₁ →ₗ[A] M₂).restrictScalars R, f.continuous⟩

@[simp]
theorem coe_restrictScalars (f : M₁ →L[A] M₂) :
    (f.restrictScalars R : M₁ →ₗ[R] M₂) = (f : M₁ →ₗ[A] M₂).restrictScalars R := rfl

@[simp]
theorem coe_restrictScalars' (f : M₁ →L[A] M₂) : ⇑(f.restrictScalars R) = f := rfl

@[simp]
theorem toContinuousAddMonoidHom_restrictScalars (f : M₁ →L[A] M₂) :
    ↑(f.restrictScalars R) = (f : ContinuousAddMonoidHom M₁ M₂) := rfl

@[simp] lemma restrictScalars_zero : (0 : M₁ →L[A] M₂).restrictScalars R = 0 := rfl

@[simp]
lemma restrictScalars_add [ContinuousAdd M₂] (f g : M₁ →L[A] M₂) :
    (f + g).restrictScalars R = f.restrictScalars R + g.restrictScalars R := rfl

variable [Module S M₂] [ContinuousConstSMul S M₂] [SMulCommClass A S M₂] [SMulCommClass R S M₂]

@[simp]
theorem restrictScalars_smul (c : S) (f : M₁ →L[A] M₂) :
    (c • f).restrictScalars R = c • f.restrictScalars R :=
  rfl

variable [ContinuousAdd M₂]

variable (A R S M₁ M₂) in
/-- `ContinuousLinearMap.restrictScalars` as a `LinearMap`. See also
`ContinuousLinearMap.restrictScalarsL`. -/
def restrictScalarsₗ : (M₁ →L[A] M₂) →ₗ[S] M₁ →L[R] M₂ where
  toFun := restrictScalars R
  map_add' := restrictScalars_add
  map_smul' := restrictScalars_smul

@[simp]
theorem coe_restrictScalarsₗ : ⇑(restrictScalarsₗ A M₁ M₂ R S) = restrictScalars R := rfl

end Semiring

section Ring
variable {A R S M₁ M₂ : Type*} [Ring A] [Ring R] [Ring S]
  [AddCommGroup M₁] [Module A M₁] [Module R M₁] [TopologicalSpace M₁]
  [AddCommGroup M₂] [Module A M₂] [Module R M₂] [TopologicalSpace M₂]
  [LinearMap.CompatibleSMul M₁ M₂ R A] [IsTopologicalAddGroup M₂]

@[simp]
lemma restrictScalars_sub (f g : M₁ →L[A] M₂) :
    (f - g).restrictScalars R = f.restrictScalars R - g.restrictScalars R := rfl

@[simp]
lemma restrictScalars_neg (f : M₁ →L[A] M₂) : (-f).restrictScalars R = -f.restrictScalars R := rfl

end Ring

end ContinuousLinearMap

end RestrictScalars
