/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Data.Set.Function
import Mathlib.GroupTheory.GroupAction.Defs

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

@[to_additive]
instance smul' {g : I → Type*} [∀ i, SMul (f i) (g i)] : SMul (∀ i, f i) (∀ i : I, g i) :=
  ⟨fun s x => fun i => s i • x i⟩
#align pi.has_smul' Pi.smul'
#align pi.has_vadd' Pi.vadd'

@[to_additive (attr := simp)]
theorem smul_apply' {g : I → Type*} [∀ i, SMul (f i) (g i)] (s : ∀ i, f i) (x : ∀ i, g i) :
    (s • x) i = s i • x i :=
  rfl
#align pi.smul_apply' Pi.smul_apply'
#align pi.vadd_apply' Pi.vadd_apply'

-- Porting note: `to_additive` fails to correctly translate name
@[to_additive Pi.vaddAssocClass]
instance isScalarTower {α β : Type*} [SMul α β] [∀ i, SMul β <| f i]
    [∀ i, SMul α <| f i] [∀ i, IsScalarTower α β (f i)] : IsScalarTower α β (∀ i : I, f i) :=
  ⟨fun x y z => funext fun i => smul_assoc x y (z i)⟩
#align pi.is_scalar_tower Pi.isScalarTower
#align pi.vadd_assoc_class Pi.vaddAssocClass

@[to_additive Pi.vaddAssocClass']
instance isScalarTower' {g : I → Type*} {α : Type*} [∀ i, SMul α <| f i]
    [∀ i, SMul (f i) (g i)] [∀ i, SMul α <| g i] [∀ i, IsScalarTower α (f i) (g i)] :
    IsScalarTower α (∀ i : I, f i) (∀ i : I, g i) :=
  ⟨fun x y z => funext fun i => smul_assoc x (y i) (z i)⟩
#align pi.is_scalar_tower' Pi.isScalarTower'
#align pi.vadd_assoc_class' Pi.vaddAssocClass'

@[to_additive Pi.vaddAssocClass'']
instance isScalarTower'' {g : I → Type*} {h : I → Type*} [∀ i, SMul (f i) (g i)]
    [∀ i, SMul (g i) (h i)] [∀ i, SMul (f i) (h i)] [∀ i, IsScalarTower (f i) (g i) (h i)] :
    IsScalarTower (∀ i, f i) (∀ i, g i) (∀ i, h i) :=
  ⟨fun x y z => funext fun i => smul_assoc (x i) (y i) (z i)⟩
#align pi.is_scalar_tower'' Pi.isScalarTower''
#align pi.vadd_assoc_class'' Pi.vaddAssocClass''

@[to_additive]
instance smulCommClass {α β : Type*} [∀ i, SMul α <| f i] [∀ i, SMul β <| f i]
    [∀ i, SMulCommClass α β (f i)] : SMulCommClass α β (∀ i : I, f i) :=
  ⟨fun x y z => funext fun i => smul_comm x y (z i)⟩
#align pi.smul_comm_class Pi.smulCommClass
#align pi.vadd_comm_class Pi.vaddCommClass

@[to_additive]
instance smulCommClass' {g : I → Type*} {α : Type*} [∀ i, SMul α <| g i]
    [∀ i, SMul (f i) (g i)] [∀ i, SMulCommClass α (f i) (g i)] :
    SMulCommClass α (∀ i : I, f i) (∀ i : I, g i) :=
  ⟨fun x y z => funext fun i => smul_comm x (y i) (z i)⟩
#align pi.smul_comm_class' Pi.smulCommClass'
#align pi.vadd_comm_class' Pi.vaddCommClass'

@[to_additive]
instance smulCommClass'' {g : I → Type*} {h : I → Type*} [∀ i, SMul (g i) (h i)]
    [∀ i, SMul (f i) (h i)] [∀ i, SMulCommClass (f i) (g i) (h i)] :
    SMulCommClass (∀ i, f i) (∀ i, g i) (∀ i, h i) :=
  ⟨fun x y z => funext fun i => smul_comm (x i) (y i) (z i)⟩
#align pi.smul_comm_class'' Pi.smulCommClass''
#align pi.vadd_comm_class'' Pi.vaddCommClass''

@[to_additive]
instance isCentralScalar {α : Type*} [∀ i, SMul α <| f i] [∀ i, SMul αᵐᵒᵖ <| f i]
    [∀ i, IsCentralScalar α (f i)] : IsCentralScalar α (∀ i, f i) :=
  ⟨fun _ _ => funext fun _ => op_smul_eq_smul _ _⟩

/-- If `f i` has a faithful scalar action for a given `i`, then so does `Π i, f i`. This is
not an instance as `i` cannot be inferred. -/
@[to_additive
  "If `f i` has a faithful additive action for a given `i`, then
  so does `Π i, f i`. This is not an instance as `i` cannot be inferred"]
theorem faithfulSMul_at {α : Type*} [∀ i, SMul α <| f i] [∀ i, Nonempty (f i)] (i : I)
    [FaithfulSMul α (f i)] : FaithfulSMul α (∀ i, f i) :=
  ⟨fun h =>
    eq_of_smul_eq_smul fun a : f i => by
      classical
        have :=
          congr_fun (h <| Function.update (fun j => Classical.choice (‹∀ i, Nonempty (f i)› j)) i a)
            i
        simpa using this⟩
#align pi.has_faithful_smul_at Pi.faithfulSMul_at
#align pi.has_faithful_vadd_at Pi.faithfulVAdd_at

@[to_additive]
instance faithfulSMul {α : Type*} [Nonempty I] [∀ i, SMul α <| f i] [∀ i, Nonempty (f i)]
    [∀ i, FaithfulSMul α (f i)] : FaithfulSMul α (∀ i, f i) :=
  let ⟨i⟩ := ‹Nonempty I›
  faithfulSMul_at i
#align pi.has_faithful_smul Pi.faithfulSMul
#align pi.has_faithful_vadd Pi.faithfulVAdd

@[to_additive]
instance mulAction (α) {m : Monoid α} [∀ i, MulAction α <| f i] :
    @MulAction α (∀ i : I, f i) m where
  smul := (· • ·)
  mul_smul _ _ _ := funext fun _ => mul_smul _ _ _
  one_smul _ := funext fun _ => one_smul α _
#align pi.mul_action Pi.mulAction
#align pi.add_action Pi.addAction

@[to_additive]
instance mulAction' {g : I → Type*} {m : ∀ i, Monoid (f i)} [∀ i, MulAction (f i) (g i)] :
    @MulAction (∀ i, f i) (∀ i : I, g i)
      (@Pi.monoid I f m) where
  smul := (· • ·)
  mul_smul _ _ _ := funext fun _ => mul_smul _ _ _
  one_smul _ := funext fun _ => one_smul _ _
#align pi.mul_action' Pi.mulAction'
#align pi.add_action' Pi.addAction'

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

namespace Function

/-- Non-dependent version of `Pi.smul`. Lean gets confused by the dependent instance if this
is not present. -/
@[to_additive
  "Non-dependent version of `Pi.vadd`. Lean gets confused by the dependent instance
  if this is not present."]
instance hasSMul {ι R M : Type*} [SMul R M] : SMul R (ι → M) :=
  Pi.instSMul
#align function.has_smul Function.hasSMul
#align function.has_vadd Function.hasVAdd

/-- Non-dependent version of `Pi.smulCommClass`. Lean gets confused by the dependent instance if
this is not present. -/
@[to_additive
  "Non-dependent version of `Pi.vaddCommClass`. Lean gets confused by the dependent
  instance if this is not present."]
instance smulCommClass {ι α β M : Type*} [SMul α M] [SMul β M] [SMulCommClass α β M] :
    SMulCommClass α β (ι → M) :=
  Pi.smulCommClass
#align function.smul_comm_class Function.smulCommClass
#align function.vadd_comm_class Function.vaddCommClass

@[to_additive]
theorem update_smul {α : Type*} [∀ i, SMul α (f i)] [DecidableEq I] (c : α) (f₁ : ∀ i, f i)
    (i : I) (x₁ : f i) : update (c • f₁) i (c • x₁) = c • update f₁ i x₁ :=
  funext fun j => (apply_update (β := f) (fun _ => (c • ·)) f₁ i x₁ j).symm
#align function.update_smul Function.update_smul
#align function.update_vadd Function.update_vadd

end Function

namespace Set

@[to_additive]
theorem piecewise_smul {α : Type*} [∀ i, SMul α (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)]
    (c : α) (f₁ g₁ : ∀ i, f i) : s.piecewise (c • f₁) (c • g₁) = c • s.piecewise f₁ g₁ :=
  s.piecewise_op (δ' := f) f₁ _ fun _ => (c • ·)
#align set.piecewise_smul Set.piecewise_smul
#align set.piecewise_vadd Set.piecewise_vadd

end Set

section Extend

@[to_additive]
theorem Function.extend_smul {R α β γ : Type*} [SMul R γ] (r : R) (f : α → β) (g : α → γ)
    (e : β → γ) : Function.extend f (r • g) (r • e) = r • Function.extend f g e :=
  funext fun x => by
  -- Porting note: Lean4 is unable to automatically call `Classical.propDecidable`
  haveI : Decidable (∃ a : α, f a = x) := Classical.propDecidable _
  simp only [extend_def, Pi.smul_apply]
  split_ifs <;>
  rfl
#align function.extend_smul Function.extend_smul
#align function.extend_vadd Function.extend_vadd

end Extend
