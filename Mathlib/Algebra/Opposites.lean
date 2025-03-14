/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Nontrivial.Basic
import Mathlib.Logic.IsEmpty

/-!
# Multiplicative opposite and algebraic operations on it

In this file we define `MulOpposite α = αᵐᵒᵖ` to be the multiplicative opposite of `α`. It inherits
all additive algebraic structures on `α` (in other files), and reverses the order of multipliers in
multiplicative structures, i.e., `op (x * y) = op y * op x`, where `MulOpposite.op` is the
canonical map from `α` to `αᵐᵒᵖ`.

We also define `AddOpposite α = αᵃᵒᵖ` to be the additive opposite of `α`. It inherits all
multiplicative algebraic structures on `α` (in other files), and reverses the order of summands in
additive structures, i.e. `op (x + y) = op y + op x`, where `AddOpposite.op` is the canonical map
from `α` to `αᵃᵒᵖ`.

## Notation

* `αᵐᵒᵖ = MulOpposite α`
* `αᵃᵒᵖ = AddOpposite α`

## Implementation notes

In mathlib3 `αᵐᵒᵖ` was just a type synonym for `α`, marked irreducible after the API
was developed. In mathlib4 we use a structure with one field, because it is not possible
to change the reducibility of a declaration after its definition, and because Lean 4 has
definitional eta reduction for structures (Lean 3 does not).

## Tags

multiplicative opposite, additive opposite
-/

variable {α β : Type*}

open Function

/-- Auxiliary type to implement `MulOpposite` and `AddOpposite`.

It turns out to be convenient to have `MulOpposite α = AddOpposite α` true by definition, in the
same way that it is convenient to have `Additive α = α`; this means that we also get the defeq
`AddOpposite (Additive α) = MulOpposite α`, which is convenient when working with quotients.

This is a compromise between making `MulOpposite α = AddOpposite α = α` (what we had in Lean 3) and
having no defeqs within those three types (which we had as of https://github.com/leanprover-community/mathlib4/pull/1036). -/
structure PreOpposite (α : Type*) : Type _ where
  /-- The element of `PreOpposite α` that represents `x : α`. -/ op' ::
  /-- The element of `α` represented by `x : PreOpposite α`. -/ unop' : α

/-- Multiplicative opposite of a type. This type inherits all additive structures on `α` and
reverses left and right in multiplication. -/
@[to_additive
      "Additive opposite of a type. This type inherits all multiplicative structures on `α` and
      reverses left and right in addition."]
def MulOpposite (α : Type*) : Type _ := PreOpposite α

/-- Multiplicative opposite of a type. -/
postfix:max "ᵐᵒᵖ" => MulOpposite

/-- Additive opposite of a type. -/
postfix:max "ᵃᵒᵖ" => AddOpposite

namespace MulOpposite

/-- The element of `MulOpposite α` that represents `x : α`. -/
@[to_additive "The element of `αᵃᵒᵖ` that represents `x : α`."]
def op : α → αᵐᵒᵖ :=
  PreOpposite.op'

/-- The element of `α` represented by `x : αᵐᵒᵖ`. -/
@[to_additive (attr := pp_nodot) "The element of `α` represented by `x : αᵃᵒᵖ`."]
def unop : αᵐᵒᵖ → α :=
  PreOpposite.unop'

@[to_additive (attr := simp)]
theorem unop_op (x : α) : unop (op x) = x := rfl

@[to_additive (attr := simp)]
theorem op_unop (x : αᵐᵒᵖ) : op (unop x) = x :=
  rfl

@[to_additive (attr := simp)]
theorem op_comp_unop : (op : α → αᵐᵒᵖ) ∘ unop = id :=
  rfl

@[to_additive (attr := simp)]
theorem unop_comp_op : (unop : αᵐᵒᵖ → α) ∘ op = id :=
  rfl

/-- A recursor for `MulOpposite`. Use as `induction x`. -/
@[to_additive (attr := simp, elab_as_elim, induction_eliminator, cases_eliminator)
  "A recursor for `AddOpposite`. Use as `induction x`."]
protected def rec' {F : αᵐᵒᵖ → Sort*} (h : ∀ X, F (op X)) : ∀ X, F X := fun X ↦ h (unop X)

/-- The canonical bijection between `α` and `αᵐᵒᵖ`. -/
@[to_additive (attr := simps -fullyApplied apply symm_apply)
  "The canonical bijection between `α` and `αᵃᵒᵖ`."]
def opEquiv : α ≃ αᵐᵒᵖ :=
  ⟨op, unop, unop_op, op_unop⟩

@[to_additive]
theorem op_bijective : Bijective (op : α → αᵐᵒᵖ) :=
  opEquiv.bijective

@[to_additive]
theorem unop_bijective : Bijective (unop : αᵐᵒᵖ → α) :=
  opEquiv.symm.bijective

@[to_additive]
theorem op_injective : Injective (op : α → αᵐᵒᵖ) :=
  op_bijective.injective

@[to_additive]
theorem op_surjective : Surjective (op : α → αᵐᵒᵖ) :=
  op_bijective.surjective

@[to_additive]
theorem unop_injective : Injective (unop : αᵐᵒᵖ → α) :=
  unop_bijective.injective

@[to_additive]
theorem unop_surjective : Surjective (unop : αᵐᵒᵖ → α) :=
  unop_bijective.surjective

@[to_additive (attr := simp)]
theorem op_inj {x y : α} : op x = op y ↔ x = y := iff_of_eq <| PreOpposite.op'.injEq _ _

@[to_additive (attr := simp, nolint simpComm)]
theorem unop_inj {x y : αᵐᵒᵖ} : unop x = unop y ↔ x = y :=
  unop_injective.eq_iff

attribute [nolint simpComm] AddOpposite.unop_inj

@[to_additive (attr := simp)] lemma «forall» {p : αᵐᵒᵖ → Prop} : (∀ a, p a) ↔ ∀ a, p (op a) :=
  op_surjective.forall

@[to_additive (attr := simp)] lemma «exists» {p : αᵐᵒᵖ → Prop} : (∃ a, p a) ↔ ∃ a, p (op a) :=
  op_surjective.exists

@[to_additive] instance instNontrivial [Nontrivial α] : Nontrivial αᵐᵒᵖ := op_injective.nontrivial

@[to_additive] instance instInhabited [Inhabited α] : Inhabited αᵐᵒᵖ := ⟨op default⟩

@[to_additive]
instance instSubsingleton [Subsingleton α] : Subsingleton αᵐᵒᵖ := unop_injective.subsingleton

@[to_additive] instance instUnique [Unique α] : Unique αᵐᵒᵖ := Unique.mk' _

@[to_additive] instance instIsEmpty [IsEmpty α] : IsEmpty αᵐᵒᵖ := Function.isEmpty unop

@[to_additive]
instance instDecidableEq [DecidableEq α] : DecidableEq αᵐᵒᵖ := unop_injective.decidableEq

instance instZero [Zero α] : Zero αᵐᵒᵖ where zero := op 0

@[to_additive] instance instOne [One α] : One αᵐᵒᵖ where one := op 1

instance instAdd [Add α] : Add αᵐᵒᵖ where add x y := op (unop x + unop y)
instance instSub [Sub α] : Sub αᵐᵒᵖ where sub x y := op (unop x - unop y)
instance instNeg [Neg α] : Neg αᵐᵒᵖ where neg x := op <| -unop x

instance instInvolutiveNeg [InvolutiveNeg α] : InvolutiveNeg αᵐᵒᵖ where
  neg_neg _ := unop_injective <| neg_neg _

@[to_additive] instance instMul [Mul α] : Mul αᵐᵒᵖ where mul x y := op (unop y * unop x)
@[to_additive] instance instInv [Inv α] : Inv αᵐᵒᵖ where inv x := op <| (unop x)⁻¹

@[to_additive]
instance instInvolutiveInv [InvolutiveInv α] : InvolutiveInv αᵐᵒᵖ where
  inv_inv _ := unop_injective <| inv_inv _

@[to_additive] instance instSMul [SMul α β] : SMul α βᵐᵒᵖ where smul c x := op (c • unop x)

@[simp] lemma op_zero [Zero α] : op (0 : α) = 0 := rfl

@[simp] lemma unop_zero [Zero α] : unop (0 : αᵐᵒᵖ) = 0 := rfl

@[to_additive (attr := simp)] lemma op_one [One α] : op (1 : α) = 1 := rfl

@[to_additive (attr := simp)] lemma unop_one [One α] : unop (1 : αᵐᵒᵖ) = 1 := rfl

@[simp] lemma op_add [Add α] (x y : α) : op (x + y) = op x + op y := rfl

@[simp] lemma unop_add [Add α] (x y : αᵐᵒᵖ) : unop (x + y) = unop x + unop y := rfl

@[simp] lemma op_neg [Neg α] (x : α) : op (-x) = -op x := rfl

@[simp] lemma unop_neg [Neg α] (x : αᵐᵒᵖ) : unop (-x) = -unop x := rfl

@[to_additive (attr := simp)] lemma op_mul [Mul α] (x y : α) : op (x * y) = op y * op x := rfl

@[to_additive (attr := simp)]
lemma unop_mul [Mul α] (x y : αᵐᵒᵖ) : unop (x * y) = unop y * unop x := rfl

@[to_additive (attr := simp)] lemma op_inv [Inv α] (x : α) : op x⁻¹ = (op x)⁻¹ := rfl

@[to_additive (attr := simp)] lemma unop_inv [Inv α] (x : αᵐᵒᵖ) : unop x⁻¹ = (unop x)⁻¹ := rfl

@[simp] lemma op_sub [Sub α] (x y : α) : op (x - y) = op x - op y := rfl

@[simp] lemma unop_sub [Sub α] (x y : αᵐᵒᵖ) : unop (x - y) = unop x - unop y := rfl

@[to_additive (attr := simp)]
lemma op_smul [SMul α β] (a : α) (b : β) : op (a • b) = a • op b := rfl

@[to_additive (attr := simp)]
lemma unop_smul [SMul α β] (a : α) (b : βᵐᵒᵖ) : unop (a • b) = a • unop b := rfl

@[simp, nolint simpComm]
theorem unop_eq_zero_iff [Zero α] (a : αᵐᵒᵖ) : a.unop = (0 : α) ↔ a = (0 : αᵐᵒᵖ) :=
  unop_injective.eq_iff' rfl

@[simp]
theorem op_eq_zero_iff [Zero α] (a : α) : op a = (0 : αᵐᵒᵖ) ↔ a = (0 : α) :=
  op_injective.eq_iff' rfl

theorem unop_ne_zero_iff [Zero α] (a : αᵐᵒᵖ) : a.unop ≠ (0 : α) ↔ a ≠ (0 : αᵐᵒᵖ) :=
  not_congr <| unop_eq_zero_iff a

theorem op_ne_zero_iff [Zero α] (a : α) : op a ≠ (0 : αᵐᵒᵖ) ↔ a ≠ (0 : α) :=
  not_congr <| op_eq_zero_iff a

@[to_additive (attr := simp, nolint simpComm)]
theorem unop_eq_one_iff [One α] (a : αᵐᵒᵖ) : a.unop = 1 ↔ a = 1 :=
  unop_injective.eq_iff' rfl

attribute [nolint simpComm] AddOpposite.unop_eq_zero_iff

@[to_additive (attr := simp)]
lemma op_eq_one_iff [One α] (a : α) : op a = 1 ↔ a = 1 := op_injective.eq_iff

end MulOpposite

namespace AddOpposite

instance instOne [One α] : One αᵃᵒᵖ where one := op 1

@[simp] lemma op_one [One α] : op (1 : α) = 1 := rfl

@[simp] lemma unop_one [One α] : unop 1 = (1 : α) := rfl

@[simp] lemma op_eq_one_iff [One α] {a : α} : op a = 1 ↔ a = 1 := op_injective.eq_iff

@[simp] lemma unop_eq_one_iff [One α] {a : αᵃᵒᵖ} : unop a = 1 ↔ a = 1 := unop_injective.eq_iff

attribute [nolint simpComm] unop_eq_one_iff

instance instMul [Mul α] : Mul αᵃᵒᵖ where mul a b := op (unop a * unop b)

@[simp] lemma op_mul [Mul α] (a b : α) : op (a * b) = op a * op b := rfl

@[simp] lemma unop_mul [Mul α] (a b : αᵃᵒᵖ) : unop (a * b) = unop a * unop b := rfl

instance instInv [Inv α] : Inv αᵃᵒᵖ where inv a := op (unop a)⁻¹

instance instInvolutiveInv [InvolutiveInv α] : InvolutiveInv αᵃᵒᵖ where
  inv_inv _ := unop_injective <| inv_inv _

@[simp] lemma op_inv [Inv α] (a : α) : op a⁻¹ = (op a)⁻¹ := rfl

@[simp] lemma unop_inv [Inv α] (a : αᵃᵒᵖ) : unop a⁻¹ = (unop a)⁻¹ := rfl

instance instDiv [Div α] : Div αᵃᵒᵖ where div a b := op (unop a / unop b)

@[simp] lemma op_div [Div α] (a b : α) : op (a / b) = op a / op b := rfl

@[simp] lemma unop_div [Div α] (a b : αᵃᵒᵖ) : unop (a / b) = unop a / unop b := rfl

end AddOpposite
