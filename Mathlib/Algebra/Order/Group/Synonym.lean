/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Order.Synonym

/-!
# Group structure on the order type synonyms

Transfer algebraic instances from `α` to `αᵒᵈ`, `Lex α`, and `Colex α`.
-/

@[expose] public section


open OrderDual

variable {α β : Type*}

/-! ### `OrderDual` -/

set_option linter.translateRedundant false in
attribute [to_additive self] OrderDual.ofDual_injective

@[to_additive]
instance [One α] : One αᵒᵈ where one := toDual 1

@[to_additive]
instance [Mul α] : Mul αᵒᵈ where mul a b := toDual (ofDual a * ofDual b)

@[to_additive]
instance [Inv α] : Inv αᵒᵈ where inv a := toDual (ofDual a)⁻¹

@[to_additive]
instance [Div α] : Div αᵒᵈ where div a b := toDual (ofDual a / ofDual b)

@[to_additive]
instance OrderDual.instSMul [SMul β α] : SMul β αᵒᵈ where smul b a := toDual (b • ofDual a)

@[to_additive]
instance OrderDual.instSMul' [SMul β α] : SMul βᵒᵈ α where smul b a := ofDual b • a

@[to_additive existing OrderDual.instSMul]
instance OrderDual.instPow [Pow α β] : Pow αᵒᵈ β where pow a b := toDual (ofDual a ^ b)

@[to_additive existing OrderDual.instSMul']
instance OrderDual.instPow' [Pow α β] : Pow α βᵒᵈ where pow a b := a ^ ofDual b

@[to_additive]
instance [Semigroup α] : Semigroup αᵒᵈ :=
  ofDual_injective.semigroup ofDual (fun _ _ => rfl)

@[to_additive]
instance [CommSemigroup α] : CommSemigroup αᵒᵈ :=
  ofDual_injective.commSemigroup ofDual (fun _ _ => rfl)

@[to_additive]
instance [Mul α] [IsLeftCancelMul α] : IsLeftCancelMul αᵒᵈ :=
  ofDual_injective.isLeftCancelMul ofDual (fun _ _ => rfl)

@[to_additive]
instance [Mul α] [IsRightCancelMul α] : IsRightCancelMul αᵒᵈ :=
  ofDual_injective.isRightCancelMul ofDual (fun _ _ => rfl)

@[to_additive]
instance [Mul α] [IsCancelMul α] : IsCancelMul αᵒᵈ :=
  ofDual_injective.isCancelMul ofDual (fun _ _ => rfl)

@[to_additive]
instance [LeftCancelSemigroup α] : LeftCancelSemigroup αᵒᵈ :=
  ofDual_injective.leftCancelSemigroup ofDual (fun _ _ => rfl)

@[to_additive]
instance [RightCancelSemigroup α] : RightCancelSemigroup αᵒᵈ :=
  ofDual_injective.rightCancelSemigroup ofDual (fun _ _ => rfl)

@[to_additive]
instance [MulOneClass α] : MulOneClass αᵒᵈ :=
  ofDual_injective.mulOneClass ofDual rfl (fun _ _ => rfl)

@[to_additive]
instance [Monoid α] : Monoid αᵒᵈ :=
  ofDual_injective.monoid ofDual rfl (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]
instance OrderDual.instCommMonoid [CommMonoid α] : CommMonoid αᵒᵈ :=
  ofDual_injective.commMonoid ofDual rfl (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]
instance [LeftCancelMonoid α] : LeftCancelMonoid αᵒᵈ :=
  ofDual_injective.leftCancelMonoid ofDual rfl (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]
instance [RightCancelMonoid α] : RightCancelMonoid αᵒᵈ :=
  ofDual_injective.rightCancelMonoid ofDual rfl (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]
instance [CancelMonoid α] : CancelMonoid αᵒᵈ :=
  ofDual_injective.cancelMonoid ofDual rfl (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]
instance OrderDual.instCancelCommMonoid [CancelCommMonoid α] : CancelCommMonoid αᵒᵈ :=
  ofDual_injective.cancelCommMonoid ofDual rfl (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]
instance [InvolutiveInv α] : InvolutiveInv αᵒᵈ :=
  ofDual_injective.involutiveInv ofDual (fun _ => rfl)

@[to_additive]
instance [DivInvMonoid α] : DivInvMonoid αᵒᵈ :=
  ofDual_injective.divInvMonoid ofDual rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]
instance [DivisionMonoid α] : DivisionMonoid αᵒᵈ :=
  ofDual_injective.divisionMonoid ofDual rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]
instance [DivisionCommMonoid α] : DivisionCommMonoid αᵒᵈ :=
  ofDual_injective.divisionCommMonoid ofDual rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]
instance OrderDual.instGroup [Group α] : Group αᵒᵈ :=
  ofDual_injective.group ofDual rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive]
instance [CommGroup α] : CommGroup αᵒᵈ :=
  ofDual_injective.commGroup ofDual rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

@[to_additive (attr := simp)]
theorem toDual_one [One α] : toDual (1 : α) = 1 := rfl

@[to_additive (attr := simp)]
theorem ofDual_one [One α] : (ofDual 1 : α) = 1 := rfl

@[to_additive (attr := simp)] lemma toDual_eq_one [One α] {a : α} : toDual a = 1 ↔ a = 1 :=
  toDual_inj
@[to_additive (attr := simp)] lemma ofDual_eq_one [One α] {a : αᵒᵈ} : ofDual a = 1 ↔ a = 1 :=
  ofDual_inj

@[to_additive (attr := simp)]
theorem toDual_mul [Mul α] (a b : α) : toDual (a * b) = toDual a * toDual b := rfl

@[to_additive (attr := simp)]
theorem ofDual_mul [Mul α] (a b : αᵒᵈ) : ofDual (a * b) = ofDual a * ofDual b := rfl

@[to_additive (attr := simp)]
theorem toDual_inv [Inv α] (a : α) : toDual a⁻¹ = (toDual a)⁻¹ := rfl

@[to_additive (attr := simp)]
theorem ofDual_inv [Inv α] (a : αᵒᵈ) : ofDual a⁻¹ = (ofDual a)⁻¹ := rfl

@[to_additive (attr := simp)]
theorem toDual_div [Div α] (a b : α) : toDual (a / b) = toDual a / toDual b := rfl

@[to_additive (attr := simp)]
theorem ofDual_div [Div α] (a b : αᵒᵈ) : ofDual (a / b) = ofDual a / ofDual b := rfl

theorem toDual_pow [Pow α β] (a : α) (b : β) : toDual (a ^ b) = toDual a ^ b := rfl

theorem ofDual_pow [Pow α β] (a : αᵒᵈ) (b : β) : ofDual (a ^ b) = ofDual a ^ b := rfl

theorem pow_toDual [Pow α β] (a : α) (b : β) : a ^ toDual b = a ^ b := rfl

theorem pow_ofDual [Pow α β] (a : α) (b : βᵒᵈ) : a ^ ofDual b = a ^ b := rfl

@[simp]
theorem toDual_smul [SMul β α] (b : β) (a : α) : toDual (b • a) = b • toDual a := rfl

@[simp]
theorem ofDual_smul [SMul β α] (b : β) (a : αᵒᵈ) : ofDual (b • a) = b • ofDual a := rfl

@[simp]
theorem toDual_smul' [SMul β α] (b : β) (a : α) : (toDual b) • a = b • a := rfl

@[simp]
theorem ofDual_smul' [SMul β α] (b : βᵒᵈ) (a : α) : (ofDual b) • a = b • a := rfl

attribute [to_additive existing toDual_smul] toDual_pow
attribute [to_additive existing ofDual_smul] ofDual_pow
attribute [to_additive existing toDual_smul'] pow_toDual
attribute [to_additive existing ofDual_smul'] pow_ofDual
attribute [simp] toDual_pow ofDual_pow pow_toDual pow_ofDual

section Monoid
variable [Monoid α]

@[to_additive (attr := simp)]
lemma isLeftRegular_toDual {a : α} : IsLeftRegular (toDual a) ↔ IsLeftRegular a :=
  ⟨fun h b c hbc => toDual_inj.mp (@h (toDual b) (toDual c) (congrArg toDual hbc)),
   fun h b c hbc => OrderDual.ext (@h (ofDual b) (ofDual c) (congrArg ofDual hbc))⟩

@[to_additive (attr := simp)]
lemma isLeftRegular_ofDual {a : αᵒᵈ} : IsLeftRegular (ofDual a) ↔ IsLeftRegular a :=
  ⟨fun h b c hbc => OrderDual.ext (@h (ofDual b) (ofDual c) (congrArg ofDual hbc)),
   fun h b c hbc => toDual_inj.mp (@h (toDual b) (toDual c) (congrArg toDual hbc))⟩

@[to_additive (attr := simp)]
lemma isRightRegular_toDual {a : α} : IsRightRegular (toDual a) ↔ IsRightRegular a :=
  ⟨fun h b c hbc => toDual_inj.mp (@h (toDual b) (toDual c) (congrArg toDual hbc)),
   fun h b c hbc => OrderDual.ext (@h (ofDual b) (ofDual c) (congrArg ofDual hbc))⟩

@[to_additive (attr := simp)]
lemma isRightRegular_ofDual {a : αᵒᵈ} : IsRightRegular (ofDual a) ↔ IsRightRegular a :=
  ⟨fun h b c hbc => OrderDual.ext (@h (ofDual b) (ofDual c) (congrArg ofDual hbc)),
   fun h b c hbc => toDual_inj.mp (@h (toDual b) (toDual c) (congrArg toDual hbc))⟩

@[to_additive (attr := simp)]
lemma isRegular_toDual {a : α} : IsRegular (toDual a) ↔ IsRegular a :=
  ⟨fun h => ⟨isLeftRegular_toDual.mp h.left, isRightRegular_toDual.mp h.right⟩,
   fun h => ⟨isLeftRegular_toDual.mpr h.left, isRightRegular_toDual.mpr h.right⟩⟩

@[to_additive (attr := simp)]
lemma isRegular_ofDual {a : αᵒᵈ} : IsRegular (ofDual a) ↔ IsRegular a :=
  ⟨fun h => ⟨isLeftRegular_ofDual.mp h.left, isRightRegular_ofDual.mp h.right⟩,
   fun h => ⟨isLeftRegular_ofDual.mpr h.left, isRightRegular_ofDual.mpr h.right⟩⟩

end Monoid

/-! ### Lexicographical order -/


@[to_additive]
instance [h : One α] : One (Lex α) := h

@[to_additive]
instance [h : Mul α] : Mul (Lex α) := h

@[to_additive]
instance [h : Inv α] : Inv (Lex α) := h

@[to_additive]
instance [h : Div α] : Div (Lex α) := h

@[to_additive (attr := to_additive) (reorder := 1 2) Lex.instSMul]
instance Lex.instPow [h : Pow α β] : Pow (Lex α) β := h

@[to_additive (attr := to_additive) (reorder := 1 2) Lex.instSMul']
instance Lex.instPow' [h : Pow α β] : Pow α (Lex β) := h

@[to_additive]
instance [h : Semigroup α] : Semigroup (Lex α) := h

@[to_additive]
instance [h : CommSemigroup α] : CommSemigroup (Lex α) := h

@[to_additive]
instance [Mul α] [IsLeftCancelMul α] : IsLeftCancelMul (Lex α) :=
  inferInstanceAs <| IsLeftCancelMul α

@[to_additive]
instance [Mul α] [IsRightCancelMul α] : IsRightCancelMul (Lex α) :=
  inferInstanceAs <| IsRightCancelMul α

@[to_additive]
instance [Mul α] [IsCancelMul α] : IsCancelMul (Lex α) :=
  inferInstanceAs <| IsCancelMul α

@[to_additive]
instance [h : LeftCancelSemigroup α] : LeftCancelSemigroup (Lex α) := h

@[to_additive]
instance [h : RightCancelSemigroup α] : RightCancelSemigroup (Lex α) := h

@[to_additive]
instance [h : MulOneClass α] : MulOneClass (Lex α) := h

@[to_additive]
instance [h : Monoid α] : Monoid (Lex α) := h

@[to_additive]
instance [h : CommMonoid α] : CommMonoid (Lex α) := h

@[to_additive]
instance [h : LeftCancelMonoid α] : LeftCancelMonoid (Lex α) := h

@[to_additive]
instance [h : RightCancelMonoid α] : RightCancelMonoid (Lex α) := h

@[to_additive]
instance [h : CancelMonoid α] : CancelMonoid (Lex α) := h

@[to_additive]
instance [h : CancelCommMonoid α] : CancelCommMonoid (Lex α) := h

@[to_additive]
instance [h : InvolutiveInv α] : InvolutiveInv (Lex α) := h

@[to_additive]
instance [h : DivInvMonoid α] : DivInvMonoid (Lex α) := h

@[to_additive]
instance [h : DivisionMonoid α] : DivisionMonoid (Lex α) := h

@[to_additive]
instance [h : DivisionCommMonoid α] : DivisionCommMonoid (Lex α) := h

@[to_additive]
instance [h : Group α] : Group (Lex α) := h

@[to_additive]
instance [h : CommGroup α] : CommGroup (Lex α) := h

@[to_additive (attr := simp)]
theorem toLex_one [One α] : toLex (1 : α) = 1 := rfl

@[to_additive (attr := simp)]
theorem toLex_eq_one [One α] {a : α} : toLex a = 1 ↔ a = 1 := .rfl

@[to_additive (attr := simp)]
theorem ofLex_one [One α] : (ofLex 1 : α) = 1 := rfl

@[to_additive (attr := simp)]
theorem ofLex_eq_one [One α] {a : Lex α} : ofLex a = 1 ↔ a = 1 := .rfl

@[to_additive (attr := simp)]
theorem toLex_mul [Mul α] (a b : α) : toLex (a * b) = toLex a * toLex b := rfl

@[to_additive (attr := simp)]
theorem ofLex_mul [Mul α] (a b : Lex α) : ofLex (a * b) = ofLex a * ofLex b := rfl

@[to_additive (attr := simp)]
theorem toLex_inv [Inv α] (a : α) : toLex a⁻¹ = (toLex a)⁻¹ := rfl

@[to_additive (attr := simp)]
theorem ofLex_inv [Inv α] (a : Lex α) : ofLex a⁻¹ = (ofLex a)⁻¹ := rfl

@[to_additive (attr := simp)]
theorem toLex_div [Div α] (a b : α) : toLex (a / b) = toLex a / toLex b := rfl

@[to_additive (attr := simp)]
theorem ofLex_div [Div α] (a b : Lex α) : ofLex (a / b) = ofLex a / ofLex b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toLex_smul]
theorem toLex_pow [Pow α β] (a : α) (b : β) : toLex (a ^ b) = toLex a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofLex_smul]
theorem ofLex_pow [Pow α β] (a : Lex α) (b : β) : ofLex (a ^ b) = ofLex a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toLex_smul']
theorem pow_toLex [Pow α β] (a : α) (b : β) : a ^ toLex b = a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofLex_smul']
theorem pow_ofLex [Pow α β] (a : α) (b : Lex β) : a ^ ofLex b = a ^ b := rfl

section Monoid
variable [Monoid α]

@[to_additive (attr := simp)]
lemma isLeftRegular_toLex {a : α} : IsLeftRegular (toLex a) ↔ IsLeftRegular a := .rfl

@[to_additive (attr := simp)]
lemma isLeftRegular_ofLex {a : Lex α} : IsLeftRegular (ofLex a) ↔ IsLeftRegular a := .rfl

@[to_additive (attr := simp)]
lemma isRightRegular_toLex {a : α} : IsRightRegular (toLex a) ↔ IsRightRegular a := .rfl

@[to_additive (attr := simp)]
lemma isRightRegular_ofLex {a : Lex α} : IsRightRegular (ofLex a) ↔ IsRightRegular a := .rfl

@[to_additive (attr := simp)]
lemma isRegular_toLex {a : α} : IsRegular (toLex a) ↔ IsRegular a := .rfl

@[to_additive (attr := simp)]
lemma isRegular_ofLex {a : Lex α} : IsRegular (ofLex a) ↔ IsRegular a := .rfl

end Monoid

/-! ### Colexicographical order -/


@[to_additive]
instance [h : One α] : One (Colex α) := h

@[to_additive]
instance [h : Mul α] : Mul (Colex α) := h

@[to_additive]
instance [h : Inv α] : Inv (Colex α) := h

@[to_additive]
instance [h : Div α] : Div (Colex α) := h

@[to_additive (attr := to_additive) (reorder := 1 2) Colex.instSMul]
instance Colex.instPow [h : Pow α β] : Pow (Colex α) β := h

@[to_additive (attr := to_additive) (reorder := 1 2) Colex.instSMul']
instance Colex.instPow' [h : Pow α β] : Pow α (Colex β) := h

@[to_additive]
instance [h : Semigroup α] : Semigroup (Colex α) := h

@[to_additive]
instance [h : CommSemigroup α] : CommSemigroup (Colex α) := h

@[to_additive]
instance [Mul α] [IsLeftCancelMul α] : IsLeftCancelMul (Colex α) :=
  inferInstanceAs <| IsLeftCancelMul α

@[to_additive]
instance [Mul α] [IsRightCancelMul α] : IsRightCancelMul (Colex α) :=
  inferInstanceAs <| IsRightCancelMul α

@[to_additive]
instance [Mul α] [IsCancelMul α] : IsCancelMul (Colex α) :=
  inferInstanceAs <| IsCancelMul α

@[to_additive]
instance [h : LeftCancelSemigroup α] : LeftCancelSemigroup (Colex α) := h

@[to_additive]
instance [h : RightCancelSemigroup α] : RightCancelSemigroup (Colex α) := h

@[to_additive]
instance [h : MulOneClass α] : MulOneClass (Colex α) := h

@[to_additive]
instance [h : Monoid α] : Monoid (Colex α) := h

@[to_additive]
instance [h : CommMonoid α] : CommMonoid (Colex α) := h

@[to_additive]
instance [h : LeftCancelMonoid α] : LeftCancelMonoid (Colex α) := h

@[to_additive]
instance [h : RightCancelMonoid α] : RightCancelMonoid (Colex α) := h

@[to_additive]
instance [h : CancelMonoid α] : CancelMonoid (Colex α) := h

@[to_additive]
instance [h : CancelCommMonoid α] : CancelCommMonoid (Colex α) := h

@[to_additive]
instance [h : InvolutiveInv α] : InvolutiveInv (Colex α) := h

@[to_additive]
instance [h : DivInvMonoid α] : DivInvMonoid (Colex α) := h

@[to_additive]
instance [h : DivisionMonoid α] : DivisionMonoid (Colex α) := h

@[to_additive]
instance [h : DivisionCommMonoid α] : DivisionCommMonoid (Colex α) := h

@[to_additive]
instance [h : Group α] : Group (Colex α) := h

@[to_additive]
instance [h : CommGroup α] : CommGroup (Colex α) := h

@[to_additive (attr := simp)]
theorem toColex_one [One α] : toColex (1 : α) = 1 := rfl

@[to_additive (attr := simp)]
theorem toColex_eq_one [One α] {a : α} : toColex a = 1 ↔ a = 1 := .rfl

@[to_additive (attr := simp)]
theorem ofColex_one [One α] : (ofColex 1 : α) = 1 := rfl

@[to_additive (attr := simp)]
theorem ofColex_eq_one [One α] {a : Colex α} : ofColex a = 1 ↔ a = 1 := .rfl

@[to_additive (attr := simp)]
theorem toColex_mul [Mul α] (a b : α) : toColex (a * b) = toColex a * toColex b := rfl

@[to_additive (attr := simp)]
theorem ofColex_mul [Mul α] (a b : Colex α) : ofColex (a * b) = ofColex a * ofColex b := rfl

@[to_additive (attr := simp)]
theorem toColex_inv [Inv α] (a : α) : toColex a⁻¹ = (toColex a)⁻¹ := rfl

@[to_additive (attr := simp)]
theorem ofColex_inv [Inv α] (a : Colex α) : ofColex a⁻¹ = (ofColex a)⁻¹ := rfl

@[to_additive (attr := simp)]
theorem toColex_div [Div α] (a b : α) : toColex (a / b) = toColex a / toColex b := rfl

@[to_additive (attr := simp)]
theorem ofColex_div [Div α] (a b : Colex α) : ofColex (a / b) = ofColex a / ofColex b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toColex_smul]
theorem toColex_pow [Pow α β] (a : α) (b : β) : toColex (a ^ b) = toColex a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofColex_smul]
theorem ofColex_pow [Pow α β] (a : Colex α) (b : β) : ofColex (a ^ b) = ofColex a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) toColex_smul']
theorem pow_toColex [Pow α β] (a : α) (b : β) : a ^ toColex b = a ^ b := rfl

@[to_additive (attr := simp, to_additive) (reorder := 1 2, 4 5) ofColex_smul']
theorem pow_ofColex [Pow α β] (a : α) (b : Colex β) : a ^ ofColex b = a ^ b := rfl

section Monoid
variable [Monoid α]

@[to_additive (attr := simp)]
lemma isLeftRegular_toColex {a : α} : IsLeftRegular (toColex a) ↔ IsLeftRegular a := .rfl

@[to_additive (attr := simp)]
lemma isLeftRegular_ofColex {a : Colex α} : IsLeftRegular (ofColex a) ↔ IsLeftRegular a := .rfl

@[to_additive (attr := simp)]
lemma isRightRegular_toColex {a : α} : IsRightRegular (toColex a) ↔ IsRightRegular a := .rfl

@[to_additive (attr := simp)]
lemma isRightRegular_ofColex {a : Colex α} : IsRightRegular (ofColex a) ↔ IsRightRegular a := .rfl

@[to_additive (attr := simp)]
lemma isRegular_toColex {a : α} : IsRegular (toColex a) ↔ IsRegular a := .rfl

@[to_additive (attr := simp)]
lemma isRegular_ofColex {a : Colex α} : IsRegular (ofColex a) ↔ IsRegular a := .rfl

end Monoid
