/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# Additive and Multiplicative for group actions

## Tags

group action
-/

assert_not_exists MonoidWithZero

open Function (Injective Surjective)

variable {M α β γ : Type*}

section

open Additive Multiplicative

instance Additive.vadd [SMul α β] : VAdd (Additive α) β where vadd a := (a.toMul • ·)

instance Multiplicative.smul [VAdd α β] : SMul (Multiplicative α) β where smul a := (a.toAdd +ᵥ ·)

@[simp] lemma toMul_smul [SMul α β] (a:Additive α) (b : β) : (a.toMul : α) • b = a +ᵥ b := rfl

@[simp] lemma ofMul_vadd [SMul α β] (a : α) (b : β) : ofMul a +ᵥ b = a • b := rfl

@[simp] lemma toAdd_vadd [VAdd α β] (a:Multiplicative α) (b : β) : (a.toAdd : α) +ᵥ b = a • b := rfl

@[simp] lemma ofAdd_smul [VAdd α β] (a : α) (b : β) : ofAdd a • b = a +ᵥ b := rfl

-- Porting note: I don't know why `one_smul` can do without an explicit α and `mul_smul` can't.
instance Additive.addAction [Monoid α] [MulAction α β] : AddAction (Additive α) β where
  zero_vadd := MulAction.one_smul
  add_vadd := MulAction.mul_smul (α := α)

instance Multiplicative.mulAction [AddMonoid α] [AddAction α β] :
    MulAction (Multiplicative α) β where
  one_smul := AddAction.zero_vadd
  mul_smul := AddAction.add_vadd (G := α)

instance Additive.vaddCommClass [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    VAddCommClass (Additive α) (Additive β) γ :=
  ⟨@smul_comm α β _ _ _ _⟩

instance Multiplicative.smulCommClass [VAdd α γ] [VAdd β γ] [VAddCommClass α β γ] :
    SMulCommClass (Multiplicative α) (Multiplicative β) γ :=
  ⟨@vadd_comm α β _ _ _ _⟩

end

/-- The tautological additive action by `Additive (Function.End α)` on `α`. -/
instance AddAction.functionEnd : AddAction (Additive (Function.End α)) α := inferInstance

/-- The additive monoid hom representing an additive monoid action.

When `M` is a group, see `AddAction.toPermHom`. -/
def AddAction.toEndHom [AddMonoid M] [AddAction M α] : M →+ Additive (Function.End α) :=
  MonoidHom.toAdditive'' MulAction.toEndHom

/-- The additive action induced by a hom to `Additive (Function.End α)`

See note [reducible non-instances]. -/
abbrev AddAction.ofEndHom [AddMonoid M] (f : M →+ Additive (Function.End α)) : AddAction M α :=
  AddAction.compHom α f
