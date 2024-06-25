/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Nontrivial.Basic
import Mathlib.Logic.IsEmpty

#align_import algebra.opposites from "leanprover-community/mathlib"@"7a89b1aed52bcacbcc4a8ad515e72c5c07268940"

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
having no defeqs within those three types (which we had as of mathlib4#1036). -/
structure PreOpposite (α : Type*) : Type _ where
  /-- The element of `PreOpposite α` that represents `x : α`. -/ op' ::
  /-- The element of `α` represented by `x : PreOpposite α`. -/ unop' : α

/-- Multiplicative opposite of a type. This type inherits all additive structures on `α` and
reverses left and right in multiplication. -/
@[to_additive
      "Additive opposite of a type. This type inherits all multiplicative structures on `α` and
      reverses left and right in addition."]
def MulOpposite (α : Type*) : Type _ := PreOpposite α
#align mul_opposite MulOpposite
#align add_opposite AddOpposite
-- Porting note: the attribute `pp_nodot` does not exist yet; `op` and `unop` were
-- both tagged with it in mathlib3


/-- Multiplicative opposite of a type. -/
postfix:max "ᵐᵒᵖ" => MulOpposite

/-- Additive opposite of a type. -/
postfix:max "ᵃᵒᵖ" => AddOpposite

namespace MulOpposite

/-- The element of `MulOpposite α` that represents `x : α`. -/
@[to_additive "The element of `αᵃᵒᵖ` that represents `x : α`."]
def op : α → αᵐᵒᵖ :=
  PreOpposite.op'
#align mul_opposite.op MulOpposite.op
#align add_opposite.op AddOpposite.op

/-- The element of `α` represented by `x : αᵐᵒᵖ`. -/
@[to_additive "The element of `α` represented by `x : αᵃᵒᵖ`."]
def unop : αᵐᵒᵖ → α :=
  PreOpposite.unop'
#align mul_opposite.unop MulOpposite.unop
#align add_opposite.unop AddOpposite.unop

@[to_additive (attr := simp)]
theorem unop_op (x : α) : unop (op x) = x := rfl
#align mul_opposite.unop_op MulOpposite.unop_op
#align add_opposite.unop_op AddOpposite.unop_op

@[to_additive (attr := simp)]
theorem op_unop (x : αᵐᵒᵖ) : op (unop x) = x :=
  rfl
#align mul_opposite.op_unop MulOpposite.op_unop
#align add_opposite.op_unop AddOpposite.op_unop

@[to_additive (attr := simp)]
theorem op_comp_unop : (op : α → αᵐᵒᵖ) ∘ unop = id :=
  rfl
#align mul_opposite.op_comp_unop MulOpposite.op_comp_unop
#align add_opposite.op_comp_unop AddOpposite.op_comp_unop

@[to_additive (attr := simp)]
theorem unop_comp_op : (unop : αᵐᵒᵖ → α) ∘ op = id :=
  rfl
#align mul_opposite.unop_comp_op MulOpposite.unop_comp_op
#align add_opposite.unop_comp_op AddOpposite.unop_comp_op

/-- A recursor for `MulOpposite`. Use as `induction x using MulOpposite.rec'`. -/
@[to_additive (attr := simp, elab_as_elim)
  "A recursor for `AddOpposite`. Use as `induction x using AddOpposite.rec'`."]
protected def rec' {F : αᵐᵒᵖ → Sort*} (h : ∀ X, F (op X)) : ∀ X, F X := fun X ↦ h (unop X)
#align mul_opposite.rec MulOpposite.rec'
#align add_opposite.rec AddOpposite.rec'

/-- The canonical bijection between `α` and `αᵐᵒᵖ`. -/
@[to_additive (attr := simps (config := .asFn) apply symm_apply)
  "The canonical bijection between `α` and `αᵃᵒᵖ`."]
def opEquiv : α ≃ αᵐᵒᵖ :=
  ⟨op, unop, unop_op, op_unop⟩
#align mul_opposite.op_equiv MulOpposite.opEquiv
#align mul_opposite.op_equiv_apply MulOpposite.opEquiv_apply
#align mul_opposite.op_equiv_symm_apply MulOpposite.opEquiv_symm_apply
#align add_opposite.op_equiv AddOpposite.opEquiv

@[to_additive]
theorem op_bijective : Bijective (op : α → αᵐᵒᵖ) :=
  opEquiv.bijective
#align mul_opposite.op_bijective MulOpposite.op_bijective
#align add_opposite.op_bijective AddOpposite.op_bijective

@[to_additive]
theorem unop_bijective : Bijective (unop : αᵐᵒᵖ → α) :=
  opEquiv.symm.bijective
#align mul_opposite.unop_bijective MulOpposite.unop_bijective
#align add_opposite.unop_bijective AddOpposite.unop_bijective

@[to_additive]
theorem op_injective : Injective (op : α → αᵐᵒᵖ) :=
  op_bijective.injective
#align mul_opposite.op_injective MulOpposite.op_injective
#align add_opposite.op_injective AddOpposite.op_injective

@[to_additive]
theorem op_surjective : Surjective (op : α → αᵐᵒᵖ) :=
  op_bijective.surjective
#align mul_opposite.op_surjective MulOpposite.op_surjective
#align add_opposite.op_surjective AddOpposite.op_surjective

@[to_additive]
theorem unop_injective : Injective (unop : αᵐᵒᵖ → α) :=
  unop_bijective.injective
#align mul_opposite.unop_injective MulOpposite.unop_injective
#align add_opposite.unop_injective AddOpposite.unop_injective

@[to_additive]
theorem unop_surjective : Surjective (unop : αᵐᵒᵖ → α) :=
  unop_bijective.surjective
#align mul_opposite.unop_surjective MulOpposite.unop_surjective
#align add_opposite.unop_surjective AddOpposite.unop_surjective

@[to_additive (attr := simp)]
theorem op_inj {x y : α} : op x = op y ↔ x = y := iff_of_eq <| PreOpposite.op'.injEq _ _
#align mul_opposite.op_inj MulOpposite.op_inj
#align add_opposite.op_inj AddOpposite.op_inj

@[to_additive (attr := simp, nolint simpComm)]
theorem unop_inj {x y : αᵐᵒᵖ} : unop x = unop y ↔ x = y :=
  unop_injective.eq_iff
#align mul_opposite.unop_inj MulOpposite.unop_inj
#align add_opposite.unop_inj AddOpposite.unop_inj

attribute [nolint simpComm] AddOpposite.unop_inj

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
#align mul_opposite.op_zero MulOpposite.op_zero

@[simp] lemma unop_zero [Zero α] : unop (0 : αᵐᵒᵖ) = 0 := rfl
#align mul_opposite.unop_zero MulOpposite.unop_zero

@[to_additive (attr := simp)] lemma op_one [One α] : op (1 : α) = 1 := rfl
#align mul_opposite.op_one MulOpposite.op_one
#align add_opposite.op_zero AddOpposite.op_zero

@[to_additive (attr := simp)] lemma unop_one [One α] : unop (1 : αᵐᵒᵖ) = 1 := rfl
#align mul_opposite.unop_one MulOpposite.unop_one
#align add_opposite.unop_zero AddOpposite.unop_zero

@[simp] lemma op_add [Add α] (x y : α) : op (x + y) = op x + op y := rfl
#align mul_opposite.op_add MulOpposite.op_add

@[simp] lemma unop_add [Add α] (x y : αᵐᵒᵖ) : unop (x + y) = unop x + unop y := rfl
#align mul_opposite.unop_add MulOpposite.unop_add

@[simp] lemma op_neg [Neg α] (x : α) : op (-x) = -op x := rfl
#align mul_opposite.op_neg MulOpposite.op_neg

@[simp] lemma unop_neg [Neg α] (x : αᵐᵒᵖ) : unop (-x) = -unop x := rfl
#align mul_opposite.unop_neg MulOpposite.unop_neg

@[to_additive (attr := simp)] lemma op_mul [Mul α] (x y : α) : op (x * y) = op y * op x := rfl
#align mul_opposite.op_mul MulOpposite.op_mul
#align add_opposite.op_add AddOpposite.op_add

@[to_additive (attr := simp)]
lemma unop_mul [Mul α] (x y : αᵐᵒᵖ) : unop (x * y) = unop y * unop x := rfl
#align mul_opposite.unop_mul MulOpposite.unop_mul
#align add_opposite.unop_add AddOpposite.unop_add

@[to_additive (attr := simp)] lemma op_inv [Inv α] (x : α) : op x⁻¹ = (op x)⁻¹ := rfl
#align mul_opposite.op_inv MulOpposite.op_inv
#align add_opposite.op_neg AddOpposite.op_neg

@[to_additive (attr := simp)] lemma unop_inv [Inv α] (x : αᵐᵒᵖ) : unop x⁻¹ = (unop x)⁻¹ := rfl
#align mul_opposite.unop_inv MulOpposite.unop_inv
#align add_opposite.unop_neg AddOpposite.unop_neg

@[simp] lemma op_sub [Sub α] (x y : α) : op (x - y) = op x - op y := rfl
#align mul_opposite.op_sub MulOpposite.op_sub

@[simp] lemma unop_sub [Sub α] (x y : αᵐᵒᵖ) : unop (x - y) = unop x - unop y := rfl
#align mul_opposite.unop_sub MulOpposite.unop_sub

@[to_additive (attr := simp)]
lemma op_smul [SMul α β] (a : α) (b : β) : op (a • b) = a • op b := rfl
#align mul_opposite.op_smul MulOpposite.op_smul
#align add_opposite.op_vadd AddOpposite.op_vadd

@[to_additive (attr := simp)]
lemma unop_smul [SMul α β] (a : α) (b : βᵐᵒᵖ) : unop (a • b) = a • unop b := rfl
#align mul_opposite.unop_smul MulOpposite.unop_smul
#align add_opposite.unop_vadd AddOpposite.unop_vadd

@[simp, nolint simpComm]
theorem unop_eq_zero_iff [Zero α] (a : αᵐᵒᵖ) : a.unop = (0 : α) ↔ a = (0 : αᵐᵒᵖ) :=
  unop_injective.eq_iff' rfl
#align mul_opposite.unop_eq_zero_iff MulOpposite.unop_eq_zero_iff

@[simp]
theorem op_eq_zero_iff [Zero α] (a : α) : op a = (0 : αᵐᵒᵖ) ↔ a = (0 : α) :=
  op_injective.eq_iff' rfl
#align mul_opposite.op_eq_zero_iff MulOpposite.op_eq_zero_iff

theorem unop_ne_zero_iff [Zero α] (a : αᵐᵒᵖ) : a.unop ≠ (0 : α) ↔ a ≠ (0 : αᵐᵒᵖ) :=
  not_congr <| unop_eq_zero_iff a
#align mul_opposite.unop_ne_zero_iff MulOpposite.unop_ne_zero_iff

theorem op_ne_zero_iff [Zero α] (a : α) : op a ≠ (0 : αᵐᵒᵖ) ↔ a ≠ (0 : α) :=
  not_congr <| op_eq_zero_iff a
#align mul_opposite.op_ne_zero_iff MulOpposite.op_ne_zero_iff

@[to_additive (attr := simp, nolint simpComm)]
theorem unop_eq_one_iff [One α] (a : αᵐᵒᵖ) : a.unop = 1 ↔ a = 1 :=
  unop_injective.eq_iff' rfl
#align mul_opposite.unop_eq_one_iff MulOpposite.unop_eq_one_iff
#align add_opposite.unop_eq_zero_iff AddOpposite.unop_eq_zero_iff

attribute [nolint simpComm] AddOpposite.unop_eq_zero_iff

@[to_additive (attr := simp)]
lemma op_eq_one_iff [One α] (a : α) : op a = 1 ↔ a = 1 := op_injective.eq_iff
#align mul_opposite.op_eq_one_iff MulOpposite.op_eq_one_iff
#align add_opposite.op_eq_zero_iff AddOpposite.op_eq_zero_iff

end MulOpposite

namespace AddOpposite

instance instOne [One α] : One αᵃᵒᵖ where one := op 1

@[simp] lemma op_one [One α] : op (1 : α) = 1 := rfl
#align add_opposite.op_one AddOpposite.op_one

@[simp] lemma unop_one [One α] : unop 1 = (1 : α) := rfl
#align add_opposite.unop_one AddOpposite.unop_one

@[simp] lemma op_eq_one_iff [One α] {a : α} : op a = 1 ↔ a = 1 := op_injective.eq_iff
#align add_opposite.op_eq_one_iff AddOpposite.op_eq_one_iff

@[simp] lemma unop_eq_one_iff [One α] {a : αᵃᵒᵖ} : unop a = 1 ↔ a = 1 := unop_injective.eq_iff
#align add_opposite.unop_eq_one_iff AddOpposite.unop_eq_one_iff

attribute [nolint simpComm] unop_eq_one_iff

instance instMul [Mul α] : Mul αᵃᵒᵖ where mul a b := op (unop a * unop b)

@[simp] lemma op_mul [Mul α] (a b : α) : op (a * b) = op a * op b := rfl
#align add_opposite.op_mul AddOpposite.op_mul

@[simp] lemma unop_mul [Mul α] (a b : αᵃᵒᵖ) : unop (a * b) = unop a * unop b := rfl
#align add_opposite.unop_mul AddOpposite.unop_mul

instance instInv [Inv α] : Inv αᵃᵒᵖ where inv a := op (unop a)⁻¹

instance instInvolutiveInv [InvolutiveInv α] : InvolutiveInv αᵃᵒᵖ where
  inv_inv _ := unop_injective <| inv_inv _

@[simp] lemma op_inv [Inv α] (a : α) : op a⁻¹ = (op a)⁻¹ := rfl
#align add_opposite.op_inv AddOpposite.op_inv

@[simp] lemma unop_inv [Inv α] (a : αᵃᵒᵖ) : unop a⁻¹ = (unop a)⁻¹ := rfl
#align add_opposite.unop_inv AddOpposite.unop_inv

instance instDiv [Div α] : Div αᵃᵒᵖ where div a b := op (unop a / unop b)

@[simp] lemma op_div [Div α] (a b : α) : op (a / b) = op a / op b := rfl
#align add_opposite.op_div AddOpposite.op_div

@[simp] lemma unop_div [Div α] (a b : αᵃᵒᵖ) : unop (a / b) = unop a / unop b := rfl
#align add_opposite.unop_div AddOpposite.unop_div

end AddOpposite
