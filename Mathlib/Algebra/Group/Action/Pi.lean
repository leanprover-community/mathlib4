/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Set.Piecewise

/-!
# Pi instances for multiplicative actions

This file defines instances for `MulAction` and related structures on `Pi` types.

## See also

* `Mathlib/Algebra/Group/Action/Option.lean`
* `Mathlib/Algebra/Group/Action/Prod.lean`
* `Mathlib/Algebra/Group/Action/Sigma.lean`
* `Mathlib/Algebra/Group/Action/Sum.lean`
-/

assert_not_exists MonoidWithZero

variable {ι M N : Type*} {α β γ : ι → Type*} (i : ι)

namespace Pi

@[to_additive]
instance smul' [∀ i, SMul (α i) (β i)] : SMul (∀ i, α i) (∀ i, β i) where smul s x i := s i • x i

@[to_additive]
lemma smul_def' [∀ i, SMul (α i) (β i)] (s : ∀ i, α i) (x : ∀ i, β i) : s • x = fun i ↦ s i • x i :=
  rfl

@[to_additive (attr := simp)]
lemma smul_apply' [∀ i, SMul (α i) (β i)] (s : ∀ i, α i) (x : ∀ i, β i) : (s • x) i = s i • x i :=
  rfl

@[to_additive]
instance isScalarTower [SMul M N] [∀ i, SMul N (α i)] [∀ i, SMul M (α i)]
    [∀ i, IsScalarTower M N (α i)] : IsScalarTower M N (∀ i, α i) where
  smul_assoc x y z := funext fun i ↦ smul_assoc x y (z i)

@[to_additive]
instance isScalarTower' [∀ i, SMul M (α i)] [∀ i, SMul (α i) (β i)] [∀ i, SMul M (β i)]
    [∀ i, IsScalarTower M (α i) (β i)] : IsScalarTower M (∀ i, α i) (∀ i, β i) where
  smul_assoc x y z := funext fun i ↦ smul_assoc x (y i) (z i)

@[to_additive]
instance isScalarTower'' [∀ i, SMul (α i) (β i)] [∀ i, SMul (β i) (γ i)] [∀ i, SMul (α i) (γ i)]
    [∀ i, IsScalarTower (α i) (β i) (γ i)] : IsScalarTower (∀ i, α i) (∀ i, β i) (∀ i, γ i) where
  smul_assoc x y z := funext fun i ↦ smul_assoc (x i) (y i) (z i)

@[to_additive]
instance smulCommClass [∀ i, SMul M (α i)] [∀ i, SMul N (α i)] [∀ i, SMulCommClass M N (α i)] :
    SMulCommClass M N (∀ i, α i) where
  smul_comm x y z := funext fun i ↦ smul_comm x y (z i)

@[to_additive]
instance smulCommClass' [∀ i, SMul M (β i)] [∀ i, SMul (α i) (β i)]
    [∀ i, SMulCommClass M (α i) (β i)] : SMulCommClass M (∀ i, α i) (∀ i, β i) :=
  ⟨fun x y z => funext fun i ↦ smul_comm x (y i) (z i)⟩

@[to_additive]
instance smulCommClass'' [∀ i, SMul (β i) (γ i)] [∀ i, SMul (α i) (γ i)]
    [∀ i, SMulCommClass (α i) (β i) (γ i)] : SMulCommClass (∀ i, α i) (∀ i, β i) (∀ i, γ i) where
  smul_comm x y z := funext fun i ↦ smul_comm (x i) (y i) (z i)

@[to_additive]
instance isCentralScalar [∀ i, SMul M (α i)] [∀ i, SMul Mᵐᵒᵖ (α i)] [∀ i, IsCentralScalar M (α i)] :
    IsCentralScalar M (∀ i, α i) where
  op_smul_eq_smul _ _ := funext fun _ ↦ op_smul_eq_smul _ _

/-- If `α i` has a faithful scalar action for a given `i`, then so does `Π i, α i`. This is
not an instance as `i` cannot be inferred. -/
@[to_additive
/-- If `α i` has a faithful additive action for a given `i`, then
so does `Π i, α i`. This is not an instance as `i` cannot be inferred -/]
lemma faithfulSMul_at [∀ i, SMul M (α i)] [∀ i, Nonempty (α i)] (i : ι) [FaithfulSMul M (α i)] :
    FaithfulSMul M (∀ i, α i) where
  eq_of_smul_eq_smul h := eq_of_smul_eq_smul fun a : α i => by
    classical
    simpa using
      congr_fun (h <| Function.update (fun j => Classical.choice (‹∀ i, Nonempty (α i)› j)) i a) i

@[to_additive]
instance faithfulSMul [Nonempty ι] [∀ i, SMul M (α i)] [∀ i, Nonempty (α i)]
    [∀ i, FaithfulSMul M (α i)] : FaithfulSMul M (∀ i, α i) :=
  let ⟨i⟩ := ‹Nonempty ι›
  faithfulSMul_at i

@[to_additive]
instance mulAction (M) {m : Monoid M} [∀ i, MulAction M (α i)] : @MulAction M (∀ i, α i) m where
  smul := (· • ·)
  mul_smul _ _ _ := funext fun _ ↦ mul_smul _ _ _
  one_smul _ := funext fun _ ↦ one_smul _ _

@[to_additive]
instance mulAction' {m : ∀ i, Monoid (α i)} [∀ i, MulAction (α i) (β i)] :
    @MulAction (∀ i, α i) (∀ i, β i)
      (@Pi.monoid ι α m) where
  smul := (· • ·)
  mul_smul _ _ _ := funext fun _ ↦ mul_smul _ _ _
  one_smul _ := funext fun _ ↦ one_smul _ _

end Pi

namespace Function

/-- Non-dependent version of `Pi.smul`. Lean gets confused by the dependent instance if this
is not present. -/
@[to_additive
/-- Non-dependent version of `Pi.vadd`. Lean gets confused by the dependent instance
if this is not present. -/]
instance hasSMul {α : Type*} [SMul M α] : SMul M (ι → α) := Pi.instSMul

/-- Non-dependent version of `Pi.smulCommClass`. Lean gets confused by the dependent instance if
this is not present. -/
@[to_additive
  /-- Non-dependent version of `Pi.vaddCommClass`. Lean gets confused by the dependent
  instance if this is not present. -/]
instance smulCommClass {α : Type*} [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass M N (ι → α) := Pi.smulCommClass

@[to_additive]
lemma update_smul [∀ i, SMul M (α i)] [DecidableEq ι] (c : M) (f₁ : ∀ i, α i)
    (i : ι) (x₁ : α i) : update (c • f₁) i (c • x₁) = c • update f₁ i x₁ :=
  funext fun j => (apply_update (β := α) (fun _ ↦ (c • ·)) f₁ i x₁ j).symm

@[to_additive]
lemma extend_smul {M α β : Type*} [SMul M β] (r : M) (f : ι → α) (g : ι → β) (e : α → β) :
    extend f (r • g) (r • e) = r • extend f g e := by
  funext x
  classical
  simp only [extend_def, Pi.smul_apply]
  split_ifs <;> rfl

end Function

namespace Set

@[to_additive]
lemma piecewise_smul [∀ i, SMul M (α i)] (s : Set ι) [∀ i, Decidable (i ∈ s)]
    (c : M) (f₁ g₁ : ∀ i, α i) : s.piecewise (c • f₁) (c • g₁) = c • s.piecewise f₁ g₁ :=
  s.piecewise_op (δ' := α) f₁ _ fun _ ↦ (c • ·)

end Set
