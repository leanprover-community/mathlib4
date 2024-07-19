/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Data.Set.Function

#align_import group_theory.group_action.pi from "leanprover-community/mathlib"@"bbeb185db4ccee8ed07dc48449414ebfa39cb821"

/-!
# Pi instances for multiplicative actions

This file defines instances for `MulAction` and related structures on `Pi` types.

## See also

* `GroupTheory.GroupAction.option`
* `GroupTheory.GroupAction.prod`
* `GroupTheory.GroupAction.sigma`
* `GroupTheory.GroupAction.sum`
-/


universe u v w

variable {I : Type u}

-- The indexing type
variable {f : I → Type v}

-- The family of types already equipped with instances
variable (x y : ∀ i, f i) (i : I)

namespace Pi

instance smulZeroClass (α) {n : ∀ i, Zero <| f i} [∀ i, SMulZeroClass α <| f i] :
  @SMulZeroClass α (∀ i : I, f i) (@Pi.instZero I f n) where
  smul_zero _ := funext fun _ => smul_zero _
#align pi.smul_zero_class Pi.smulZeroClass

instance smulZeroClass' {g : I → Type*} {n : ∀ i, Zero <| g i} [∀ i, SMulZeroClass (f i) (g i)] :
  @SMulZeroClass (∀ i, f i) (∀ i : I, g i) (@Pi.instZero I g n) where
  smul_zero := by intros; ext x; exact smul_zero _
#align pi.smul_zero_class' Pi.smulZeroClass'

instance distribSMul (α) {n : ∀ i, AddZeroClass <| f i} [∀ i, DistribSMul α <| f i] :
  @DistribSMul α (∀ i : I, f i) (@Pi.addZeroClass I f n) where
  smul_zero _ := funext fun _ => smul_zero _
  smul_add _ _ _ := funext fun _ => smul_add _ _ _
#align pi.distrib_smul Pi.distribSMul

instance distribSMul' {g : I → Type*} {n : ∀ i, AddZeroClass <| g i}
  [∀ i, DistribSMul (f i) (g i)] :
  @DistribSMul (∀ i, f i) (∀ i : I, g i) (@Pi.addZeroClass I g n) where
  smul_zero := by intros; ext x; exact smul_zero _
  smul_add := by intros; ext x; exact smul_add _ _ _
#align pi.distrib_smul' Pi.distribSMul'

instance distribMulAction (α) {m : Monoid α} {n : ∀ i, AddMonoid <| f i}
    [∀ i, DistribMulAction α <| f i] : @DistribMulAction α (∀ i : I, f i) m (@Pi.addMonoid I f n) :=
  { Pi.mulAction _, Pi.distribSMul _ with }
#align pi.distrib_mul_action Pi.distribMulAction

instance distribMulAction' {g : I → Type*} {m : ∀ i, Monoid (f i)} {n : ∀ i, AddMonoid <| g i}
    [∀ i, DistribMulAction (f i) (g i)] :
    @DistribMulAction (∀ i, f i) (∀ i : I, g i) (@Pi.monoid I f m) (@Pi.addMonoid I g n) :=
  { Pi.mulAction', Pi.distribSMul' with }
#align pi.distrib_mul_action' Pi.distribMulAction'

theorem single_smul {α} [Monoid α] [∀ i, AddMonoid <| f i] [∀ i, DistribMulAction α <| f i]
    [DecidableEq I] (i : I) (r : α) (x : f i) : single i (r • x) = r • single i x :=
  single_op (fun i : I => (r • · : f i → f i)) (fun _ => smul_zero _) _ _
#align pi.single_smul Pi.single_smul

-- Porting note: Lean4 cannot infer the non-dependent function `f := fun _ => β`
/-- A version of `Pi.single_smul` for non-dependent functions. It is useful in cases where Lean
fails to apply `Pi.single_smul`. -/
theorem single_smul' {α β} [Monoid α] [AddMonoid β] [DistribMulAction α β] [DecidableEq I] (i : I)
    (r : α) (x : β) : single (f := fun _ => β) i (r • x) = r • single (f := fun _ => β) i x :=
  single_smul (f := fun _ => β) i r x
#align pi.single_smul' Pi.single_smul'

theorem single_smul₀ {g : I → Type*} [∀ i, MonoidWithZero (f i)] [∀ i, AddMonoid (g i)]
    [∀ i, DistribMulAction (f i) (g i)] [DecidableEq I] (i : I) (r : f i) (x : g i) :
    single i (r • x) = single i r • single i x :=
  single_op₂ (fun i : I => ((· • ·) : f i → g i → g i)) (fun _ => smul_zero _) _ _ _
#align pi.single_smul₀ Pi.single_smul₀

instance mulDistribMulAction (α) {m : Monoid α} {n : ∀ i, Monoid <| f i}
    [∀ i, MulDistribMulAction α <| f i] :
    @MulDistribMulAction α (∀ i : I, f i) m (@Pi.monoid I f n) :=
  { Pi.mulAction _ with
    smul_one := fun _ => funext fun _ => smul_one _
    smul_mul := fun _ _ _ => funext fun _ => smul_mul' _ _ _ }
#align pi.mul_distrib_mul_action Pi.mulDistribMulAction

instance mulDistribMulAction' {g : I → Type*} {m : ∀ i, Monoid (f i)} {n : ∀ i, Monoid <| g i}
    [∀ i, MulDistribMulAction (f i) (g i)] :
    @MulDistribMulAction (∀ i, f i) (∀ i : I, g i) (@Pi.monoid I f m) (@Pi.monoid I g n) where
  smul_mul := by
    intros
    ext x
    apply smul_mul'
  smul_one := by
    intros
    ext x
    apply smul_one
#align pi.mul_distrib_mul_action' Pi.mulDistribMulAction'

end Pi
