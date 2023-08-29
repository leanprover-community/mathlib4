/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Group.Action
import Mathlib.GroupTheory.GroupAction.DomAct.Basic
/-!
# Action of `DomMulAct` and `DomAddAct` on `α →ₘ[μ] β`

If `M` acts on `α` by measure-preserving transformations, then `Mᵈᵐᵃ` acts on `α →ₘ[μ] β` by sending
each function `f` to `f ∘ (DomMulAct.mk.symm c • ·)`. We define this action and basic instances
about it.

## Implementation notes

In fact, it suffices to require that `(c • ·)` is only quasi measure-preserving but we don't have a
typeclass for quasi measure-preserving actions yet.

## Keywords

-/

open MeasureTheory

namespace DomMulAct

variable {M N α β} [MeasurableSpace M] [MeasurableSpace N] [MeasurableSpace α]
  {μ : MeasureTheory.Measure α} [TopologicalSpace β]

section SMul

variable [SMul M α] [MeasurableSMul M α] [SMulInvariantMeasure M α μ]

@[to_additive]
instance : SMul Mᵈᵐᵃ (α →ₘ[μ] β) where
  smul c f := f.compMeasurePreserving (mk.symm c • ·) (measurePreserving_smul _ _)

@[to_additive]
theorem smul_aeeqFun_aeeq (c : Mᵈᵐᵃ) (f : α →ₘ[μ] β) :
    c • f =ᵐ[μ] (f <| mk.symm c • ·) :=
  f.coeFn_compMeasurePreserving _

@[to_additive (attr := simp)]
theorem mk_smul_mk_aeeqFun (c : M) (f : α → β) (hf : AEStronglyMeasurable f μ) :
    mk c • AEEqFun.mk f hf = AEEqFun.mk (f <| c • ·)
      (hf.comp_measurePreserving (measurePreserving_smul _ _)) :=
  rfl

@[to_additive (attr := simp)]
theorem smul_aeeqFun_const (c : Mᵈᵐᵃ) (b : β) :
    c • (AEEqFun.const α b : α →ₘ[μ] β) = AEEqFun.const α b :=
  rfl

instance [SMul N β] [ContinuousConstSMul N β] : SMulCommClass Mᵈᵐᵃ N (α →ₘ[μ] β) where
  smul_comm := by rintro _ _ ⟨_⟩; rfl
                  -- ⊢ m✝ • n✝ • Quot.mk Setoid.r a✝ = n✝ • m✝ • Quot.mk Setoid.r a✝
                                  -- 🎉 no goals

instance [SMul N β] [ContinuousConstSMul N β] : SMulCommClass N Mᵈᵐᵃ (α →ₘ[μ] β) :=
  .symm _ _ _

@[to_additive]
instance [SMul N α] [MeasurableSMul N α] [SMulInvariantMeasure N α μ] [SMulCommClass M N α] :
    SMulCommClass Mᵈᵐᵃ Nᵈᵐᵃ (α →ₘ[μ] β) where
  smul_comm := mk.surjective.forall.2 fun c₁ ↦ mk.surjective.forall.2 fun c₂ ↦
    (AEEqFun.induction_on · fun f hf ↦ by simp only [mk_smul_mk_aeeqFun, smul_comm])

instance [Zero β] : SMulZeroClass Mᵈᵐᵃ (α →ₘ[μ] β) where
  smul_zero _ := rfl

-- TODO: add `AEEqFun.addZeroClass`
instance [AddMonoid β] [ContinuousAdd β] : DistribSMul Mᵈᵐᵃ (α →ₘ[μ] β) where
  smul_add := by rintro _ ⟨⟩ ⟨⟩; rfl
                 -- ⊢ a✝² • (Quot.mk Setoid.r a✝¹ + Quot.mk Setoid.r a✝) = a✝² • Quot.mk Setoid.r  …
                                 -- 🎉 no goals

end SMul

section MulAction

variable [Monoid M] [MulAction M α] [MeasurableSMul M α] [SMulInvariantMeasure M α μ]

@[to_additive]
instance : MulAction Mᵈᵐᵃ (α →ₘ[μ] β) where
  one_smul := (AEEqFun.induction_on · fun _ _ ↦ by
    simp only [← mk_one, mk_smul_mk_aeeqFun, one_smul])
  mul_smul := mk.surjective.forall.2 fun _ ↦ mk.surjective.forall.2 fun _ ↦
    (AEEqFun.induction_on · fun _ _ ↦ by simp only [← mk_mul, mk_smul_mk_aeeqFun, mul_smul])

instance [Monoid β] [ContinuousMul β] : MulDistribMulAction Mᵈᵐᵃ (α →ₘ[μ] β) where
  smul_one _ := rfl
  smul_mul := by rintro _ ⟨⟩ ⟨⟩; rfl
                 -- ⊢ r✝ • (Quot.mk Setoid.r a✝¹ * Quot.mk Setoid.r a✝) = r✝ • Quot.mk Setoid.r a✝ …
                                 -- 🎉 no goals

instance [AddMonoid β] [ContinuousAdd β] : DistribMulAction Mᵈᵐᵃ (α →ₘ[μ] β) where
  smul_zero := smul_zero
  smul_add := smul_add

end MulAction

end DomMulAct
