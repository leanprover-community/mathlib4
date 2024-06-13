/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
import Aesop
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Int.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs

#align_import algebra.group.basic from "leanprover-community/mathlib"@"a07d750983b94c530ab69a726862c2ab6802b38c"

/-!
# Basic lemmas about semigroups, monoids, and groups

This file lists various basic lemmas about semigroups, monoids, and groups. Most proofs are
one-liners from the corresponding axioms. For the definitions of semigroups, monoids and groups, see
`Algebra/Group/Defs.lean`.
-/

assert_not_exists MonoidWithZero
assert_not_exists DenselyOrdered

open Function

universe u

variable {α β G M : Type*}

section ite
variable [Pow α β]

@[to_additive (attr := simp) dite_smul]
lemma pow_dite (p : Prop) [Decidable p] (a : α) (b : p → β) (c : ¬ p → β) :
    a ^ (if h : p then b h else c h) = if h : p then a ^ b h else a ^ c h := by split_ifs <;> rfl

@[to_additive (attr := simp) smul_dite]
lemma dite_pow (p : Prop) [Decidable p] (a : p → α) (b : ¬ p → α) (c : β) :
    (if h : p then a h else b h) ^ c = if h : p then a h ^ c else b h ^ c := by split_ifs <;> rfl

@[to_additive (attr := simp) ite_smul]
lemma pow_ite (p : Prop) [Decidable p] (a : α) (b c : β) :
    a ^ (if p then b else c) = if p then a ^ b else a ^ c := pow_dite _ _ _ _

@[to_additive (attr := simp) smul_ite]
lemma ite_pow (p : Prop) [Decidable p] (a b : α) (c : β) :
    (if p then a else b) ^ c = if p then a ^ c else b ^ c := dite_pow _ _ _ _

set_option linter.existingAttributeWarning false in
attribute [to_additive (attr := simp)] dite_smul smul_dite ite_smul smul_ite

end ite

section IsLeftCancelMul

variable [Mul G] [IsLeftCancelMul G]

@[to_additive]
theorem mul_right_injective (a : G) : Injective (a * ·) := fun _ _ ↦ mul_left_cancel
#align mul_right_injective mul_right_injective
#align add_right_injective add_right_injective

@[to_additive (attr := simp)]
theorem mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c :=
  (mul_right_injective a).eq_iff
#align mul_right_inj mul_right_inj
#align add_right_inj add_right_inj

@[to_additive]
theorem mul_ne_mul_right (a : G) {b c : G} : a * b ≠ a * c ↔ b ≠ c :=
  (mul_right_injective a).ne_iff
#align mul_ne_mul_right mul_ne_mul_right
#align add_ne_add_right add_ne_add_right

end IsLeftCancelMul

section IsRightCancelMul

variable [Mul G] [IsRightCancelMul G]

@[to_additive]
theorem mul_left_injective (a : G) : Function.Injective (· * a) := fun _ _ ↦ mul_right_cancel
#align mul_left_injective mul_left_injective
#align add_left_injective add_left_injective

@[to_additive (attr := simp)]
theorem mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c :=
  (mul_left_injective a).eq_iff
#align mul_left_inj mul_left_inj
#align add_left_inj add_left_inj

@[to_additive]
theorem mul_ne_mul_left (a : G) {b c : G} : b * a ≠ c * a ↔ b ≠ c :=
  (mul_left_injective a).ne_iff
#align mul_ne_mul_left mul_ne_mul_left
#align add_ne_add_left add_ne_add_left

end IsRightCancelMul

section Semigroup
variable [Semigroup α]

@[to_additive]
instance Semigroup.to_isAssociative : Std.Associative (α := α)  (· * ·) := ⟨mul_assoc⟩
#align semigroup.to_is_associative Semigroup.to_isAssociative
#align add_semigroup.to_is_associative AddSemigroup.to_isAssociative

/-- Composing two multiplications on the left by `y` then `x`
is equal to a multiplication on the left by `x * y`.
-/
@[to_additive (attr := simp) "Composing two additions on the left by `y` then `x`
is equal to an addition on the left by `x + y`."]
theorem comp_mul_left (x y : α) : (x * ·) ∘ (y * ·) = (x * y * ·) := by
  ext z
  simp [mul_assoc]
#align comp_mul_left comp_mul_left
#align comp_add_left comp_add_left

/-- Composing two multiplications on the right by `y` and `x`
is equal to a multiplication on the right by `y * x`.
-/
@[to_additive (attr := simp) "Composing two additions on the right by `y` and `x`
is equal to an addition on the right by `y + x`."]
theorem comp_mul_right (x y : α) : (· * x) ∘ (· * y) = (· * (y * x)) := by
  ext z
  simp [mul_assoc]
#align comp_mul_right comp_mul_right
#align comp_add_right comp_add_right

end Semigroup

@[to_additive]
instance CommMagma.to_isCommutative [CommMagma G] : Std.Commutative (α := G) (· * ·) := ⟨mul_comm⟩
#align comm_semigroup.to_is_commutative CommMagma.to_isCommutative
#align add_comm_semigroup.to_is_commutative AddCommMagma.to_isCommutative

section MulOneClass

variable {M : Type u} [MulOneClass M]

@[to_additive]
theorem ite_mul_one {P : Prop} [Decidable P] {a b : M} :
    ite P (a * b) 1 = ite P a 1 * ite P b 1 := by
  by_cases h:P <;> simp [h]
#align ite_mul_one ite_mul_one
#align ite_add_zero ite_add_zero

@[to_additive]
theorem ite_one_mul {P : Prop} [Decidable P] {a b : M} :
    ite P 1 (a * b) = ite P 1 a * ite P 1 b := by
  by_cases h:P <;> simp [h]
#align ite_one_mul ite_one_mul
#align ite_zero_add ite_zero_add

@[to_additive]
theorem eq_one_iff_eq_one_of_mul_eq_one {a b : M} (h : a * b = 1) : a = 1 ↔ b = 1 := by
  constructor <;> (rintro rfl; simpa using h)
#align eq_one_iff_eq_one_of_mul_eq_one eq_one_iff_eq_one_of_mul_eq_one
#align eq_zero_iff_eq_zero_of_add_eq_zero eq_zero_iff_eq_zero_of_add_eq_zero

@[to_additive]
theorem one_mul_eq_id : ((1 : M) * ·) = id :=
  funext one_mul
#align one_mul_eq_id one_mul_eq_id
#align zero_add_eq_id zero_add_eq_id

@[to_additive]
theorem mul_one_eq_id : (· * (1 : M)) = id :=
  funext mul_one
#align mul_one_eq_id mul_one_eq_id
#align add_zero_eq_id add_zero_eq_id

end MulOneClass

section CommSemigroup

variable [CommSemigroup G]

@[to_additive]
theorem mul_left_comm : ∀ a b c : G, a * (b * c) = b * (a * c) :=
  left_comm Mul.mul mul_comm mul_assoc
#align mul_left_comm mul_left_comm
#align add_left_comm add_left_comm

@[to_additive]
theorem mul_right_comm : ∀ a b c : G, a * b * c = a * c * b :=
  right_comm Mul.mul mul_comm mul_assoc
#align mul_right_comm mul_right_comm
#align add_right_comm add_right_comm

@[to_additive]
theorem mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a * c * (b * d) := by
  simp only [mul_left_comm, mul_assoc]
#align mul_mul_mul_comm mul_mul_mul_comm
#align add_add_add_comm add_add_add_comm

@[to_additive]
theorem mul_rotate (a b c : G) : a * b * c = b * c * a := by
  simp only [mul_left_comm, mul_comm]
#align mul_rotate mul_rotate
#align add_rotate add_rotate

@[to_additive]
theorem mul_rotate' (a b c : G) : a * (b * c) = b * (c * a) := by
  simp only [mul_left_comm, mul_comm]
#align mul_rotate' mul_rotate'
#align add_rotate' add_rotate'

end CommSemigroup

section AddCommSemigroup
set_option linter.deprecated false

variable {M : Type u} [AddCommSemigroup M]

theorem bit0_add (a b : M) : bit0 (a + b) = bit0 a + bit0 b :=
  add_add_add_comm _ _ _ _
#align bit0_add bit0_add

theorem bit1_add [One M] (a b : M) : bit1 (a + b) = bit0 a + bit1 b :=
  (congr_arg (· + (1 : M)) <| bit0_add a b : _).trans (add_assoc _ _ _)
#align bit1_add bit1_add

theorem bit1_add' [One M] (a b : M) : bit1 (a + b) = bit1 a + bit0 b := by
  rw [add_comm, bit1_add, add_comm]
#align bit1_add' bit1_add'

end AddCommSemigroup

section AddMonoid
set_option linter.deprecated false

variable {M : Type u} [AddMonoid M] {a b c : M}

@[simp]
theorem bit0_zero : bit0 (0 : M) = 0 :=
  add_zero _
#align bit0_zero bit0_zero

@[simp]
theorem bit1_zero [One M] : bit1 (0 : M) = 1 := by rw [bit1, bit0_zero, zero_add]
#align bit1_zero bit1_zero

end AddMonoid

attribute [local simp] mul_assoc sub_eq_add_neg

section Monoid
variable [Monoid M] {a b c : M} {m n : ℕ}

@[to_additive boole_nsmul]
lemma pow_boole (P : Prop) [Decidable P] (a : M) :
    (a ^ if P then 1 else 0) = if P then a else 1 := by simp only [pow_ite, pow_one, pow_zero]
#align pow_boole pow_boole

@[to_additive nsmul_add_sub_nsmul]
lemma pow_mul_pow_sub (a : M) (h : m ≤ n) : a ^ m * a ^ (n - m) = a ^ n := by
  rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel h]
#align pow_mul_pow_sub pow_mul_pow_sub
#align nsmul_add_sub_nsmul nsmul_add_sub_nsmul

@[to_additive sub_nsmul_nsmul_add]
lemma pow_sub_mul_pow (a : M) (h : m ≤ n) : a ^ (n - m) * a ^ m = a ^ n := by
  rw [← pow_add, Nat.sub_add_cancel h]
#align pow_sub_mul_pow pow_sub_mul_pow
#align sub_nsmul_nsmul_add sub_nsmul_nsmul_add

@[to_additive sub_one_nsmul_add]
lemma mul_pow_sub_one (hn : n ≠ 0) (a : M) : a * a ^ (n - 1) = a ^ n := by
  rw [← pow_succ', Nat.sub_add_cancel $ Nat.one_le_iff_ne_zero.2 hn]

@[to_additive add_sub_one_nsmul]
lemma pow_sub_one_mul (hn : n ≠ 0) (a : M) : a ^ (n - 1) * a = a ^ n := by
  rw [← pow_succ, Nat.sub_add_cancel $ Nat.one_le_iff_ne_zero.2 hn]

/-- If `x ^ n = 1`, then `x ^ m` is the same as `x ^ (m % n)` -/
@[to_additive nsmul_eq_mod_nsmul "If `n • x = 0`, then `m • x` is the same as `(m % n) • x`"]
lemma pow_eq_pow_mod (m : ℕ) (ha : a ^ n = 1) : a ^ m = a ^ (m % n) := by
  calc
    a ^ m = a ^ (m % n + n * (m / n)) := by rw [Nat.mod_add_div]
    _ = a ^ (m % n) := by simp [pow_add, pow_mul, ha]
#align pow_eq_pow_mod pow_eq_pow_mod
#align nsmul_eq_mod_nsmul nsmul_eq_mod_nsmul

@[to_additive] lemma pow_mul_pow_eq_one : ∀ n, a * b = 1 → a ^ n * b ^ n = 1
  | 0, _ => by simp
  | n + 1, h =>
    calc
      a ^ n.succ * b ^ n.succ = a ^ n * a * (b * b ^ n) := by rw [pow_succ, pow_succ']
      _ = a ^ n * (a * b) * b ^ n := by simp only [mul_assoc]
      _ = 1 := by simp [h, pow_mul_pow_eq_one]
#align pow_mul_pow_eq_one pow_mul_pow_eq_one
#align nsmul_add_nsmul_eq_zero nsmul_add_nsmul_eq_zero

end Monoid

section CommMonoid
variable [CommMonoid M] {x y z : M}

@[to_additive]
theorem inv_unique (hy : x * y = 1) (hz : x * z = 1) : y = z :=
  left_inv_eq_right_inv (Trans.trans (mul_comm _ _) hy) hz
#align inv_unique inv_unique
#align neg_unique neg_unique

@[to_additive nsmul_add] lemma mul_pow (a b : M) : ∀ n, (a * b) ^ n = a ^ n * b ^ n
  | 0 => by rw [pow_zero, pow_zero, pow_zero, one_mul]
  | n + 1 => by rw [pow_succ', pow_succ', pow_succ', mul_pow, mul_mul_mul_comm]
#align mul_pow mul_pow
#align nsmul_add nsmul_add

end CommMonoid

section LeftCancelMonoid

variable {M : Type u} [LeftCancelMonoid M] {a b : M}

@[to_additive (attr := simp)]
theorem mul_right_eq_self : a * b = a ↔ b = 1 := calc
  a * b = a ↔ a * b = a * 1 := by rw [mul_one]
  _ ↔ b = 1 := mul_left_cancel_iff
#align mul_right_eq_self mul_right_eq_self
#align add_right_eq_self add_right_eq_self

@[to_additive (attr := simp)]
theorem self_eq_mul_right : a = a * b ↔ b = 1 :=
  eq_comm.trans mul_right_eq_self
#align self_eq_mul_right self_eq_mul_right
#align self_eq_add_right self_eq_add_right

@[to_additive]
theorem mul_right_ne_self : a * b ≠ a ↔ b ≠ 1 := mul_right_eq_self.not
#align mul_right_ne_self mul_right_ne_self
#align add_right_ne_self add_right_ne_self

@[to_additive]
theorem self_ne_mul_right : a ≠ a * b ↔ b ≠ 1 := self_eq_mul_right.not
#align self_ne_mul_right self_ne_mul_right
#align self_ne_add_right self_ne_add_right

end LeftCancelMonoid

section RightCancelMonoid

variable {M : Type u} [RightCancelMonoid M] {a b : M}

@[to_additive (attr := simp)]
theorem mul_left_eq_self : a * b = b ↔ a = 1 := calc
  a * b = b ↔ a * b = 1 * b := by rw [one_mul]
  _ ↔ a = 1 := mul_right_cancel_iff
#align mul_left_eq_self mul_left_eq_self
#align add_left_eq_self add_left_eq_self

@[to_additive (attr := simp)]
theorem self_eq_mul_left : b = a * b ↔ a = 1 :=
  eq_comm.trans mul_left_eq_self
#align self_eq_mul_left self_eq_mul_left
#align self_eq_add_left self_eq_add_left

@[to_additive]
theorem mul_left_ne_self : a * b ≠ b ↔ a ≠ 1 := mul_left_eq_self.not
#align mul_left_ne_self mul_left_ne_self
#align add_left_ne_self add_left_ne_self

@[to_additive]
theorem self_ne_mul_left : b ≠ a * b ↔ a ≠ 1 := self_eq_mul_left.not
#align self_ne_mul_left self_ne_mul_left
#align self_ne_add_left self_ne_add_left

end RightCancelMonoid

section CancelCommMonoid
variable [CancelCommMonoid α] {a b c d : α}

@[to_additive] lemma eq_iff_eq_of_mul_eq_mul (h : a * b = c * d) : a = c ↔ b = d := by aesop
@[to_additive] lemma ne_iff_ne_of_mul_eq_mul (h : a * b = c * d) : a ≠ c ↔ b ≠ d := by aesop

end CancelCommMonoid

section InvolutiveInv

variable [InvolutiveInv G] {a b : G}

@[to_additive (attr := simp)]
theorem inv_involutive : Function.Involutive (Inv.inv : G → G) :=
  inv_inv
#align inv_involutive inv_involutive
#align neg_involutive neg_involutive

@[to_additive (attr := simp)]
theorem inv_surjective : Function.Surjective (Inv.inv : G → G) :=
  inv_involutive.surjective
#align inv_surjective inv_surjective
#align neg_surjective neg_surjective

@[to_additive]
theorem inv_injective : Function.Injective (Inv.inv : G → G) :=
  inv_involutive.injective
#align inv_injective inv_injective
#align neg_injective neg_injective

@[to_additive (attr := simp)]
theorem inv_inj : a⁻¹ = b⁻¹ ↔ a = b :=
  inv_injective.eq_iff
#align inv_inj inv_inj
#align neg_inj neg_inj

@[to_additive]
theorem inv_eq_iff_eq_inv : a⁻¹ = b ↔ a = b⁻¹ :=
  ⟨fun h => h ▸ (inv_inv a).symm, fun h => h.symm ▸ inv_inv b⟩
#align inv_eq_iff_eq_inv inv_eq_iff_eq_inv
#align neg_eq_iff_eq_neg neg_eq_iff_eq_neg

variable (G)

@[to_additive]
theorem inv_comp_inv : Inv.inv ∘ Inv.inv = @id G :=
  inv_involutive.comp_self
#align inv_comp_inv inv_comp_inv
#align neg_comp_neg neg_comp_neg

@[to_additive]
theorem leftInverse_inv : LeftInverse (fun a : G ↦ a⁻¹) fun a ↦ a⁻¹ :=
  inv_inv
#align left_inverse_inv leftInverse_inv
#align left_inverse_neg leftInverse_neg

@[to_additive]
theorem rightInverse_inv : RightInverse (fun a : G ↦ a⁻¹) fun a ↦ a⁻¹ :=
  inv_inv
#align right_inverse_inv rightInverse_inv
#align right_inverse_neg rightInverse_neg

end InvolutiveInv

section DivInvMonoid

variable [DivInvMonoid G] {a b c : G}

@[to_additive, field_simps] -- The attributes are out of order on purpose
theorem inv_eq_one_div (x : G) : x⁻¹ = 1 / x := by rw [div_eq_mul_inv, one_mul]
#align inv_eq_one_div inv_eq_one_div
#align neg_eq_zero_sub neg_eq_zero_sub

@[to_additive]
theorem mul_one_div (x y : G) : x * (1 / y) = x / y := by
  rw [div_eq_mul_inv, one_mul, div_eq_mul_inv]
#align mul_one_div mul_one_div
#align add_zero_sub add_zero_sub

@[to_additive]
theorem mul_div_assoc (a b c : G) : a * b / c = a * (b / c) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc _ _ _]
#align mul_div_assoc mul_div_assoc
#align add_sub_assoc add_sub_assoc

@[to_additive, field_simps] -- The attributes are out of order on purpose
theorem mul_div_assoc' (a b c : G) : a * (b / c) = a * b / c :=
  (mul_div_assoc _ _ _).symm
#align mul_div_assoc' mul_div_assoc'
#align add_sub_assoc' add_sub_assoc'

@[to_additive (attr := simp)]
theorem one_div (a : G) : 1 / a = a⁻¹ :=
  (inv_eq_one_div a).symm
#align one_div one_div
#align zero_sub zero_sub

@[to_additive]
theorem mul_div (a b c : G) : a * (b / c) = a * b / c := by simp only [mul_assoc, div_eq_mul_inv]
#align mul_div mul_div
#align add_sub add_sub

@[to_additive]
theorem div_eq_mul_one_div (a b : G) : a / b = a * (1 / b) := by rw [div_eq_mul_inv, one_div]
#align div_eq_mul_one_div div_eq_mul_one_div
#align sub_eq_add_zero_sub sub_eq_add_zero_sub

end DivInvMonoid

section DivInvOneMonoid

variable [DivInvOneMonoid G]

@[to_additive (attr := simp)]
theorem div_one (a : G) : a / 1 = a := by simp [div_eq_mul_inv]
#align div_one div_one
#align sub_zero sub_zero

@[to_additive]
theorem one_div_one : (1 : G) / 1 = 1 :=
  div_one _
#align one_div_one one_div_one
#align zero_sub_zero zero_sub_zero

end DivInvOneMonoid

section DivisionMonoid

variable [DivisionMonoid α] {a b c d : α}

attribute [local simp] mul_assoc div_eq_mul_inv

@[to_additive]
theorem eq_inv_of_mul_eq_one_right (h : a * b = 1) : b = a⁻¹ :=
  (inv_eq_of_mul_eq_one_right h).symm
#align eq_inv_of_mul_eq_one_right eq_inv_of_mul_eq_one_right
#align eq_neg_of_add_eq_zero_right eq_neg_of_add_eq_zero_right

@[to_additive]
theorem eq_one_div_of_mul_eq_one_left (h : b * a = 1) : b = 1 / a := by
  rw [eq_inv_of_mul_eq_one_left h, one_div]
#align eq_one_div_of_mul_eq_one_left eq_one_div_of_mul_eq_one_left
#align eq_zero_sub_of_add_eq_zero_left eq_zero_sub_of_add_eq_zero_left

@[to_additive]
theorem eq_one_div_of_mul_eq_one_right (h : a * b = 1) : b = 1 / a := by
  rw [eq_inv_of_mul_eq_one_right h, one_div]
#align eq_one_div_of_mul_eq_one_right eq_one_div_of_mul_eq_one_right
#align eq_zero_sub_of_add_eq_zero_right eq_zero_sub_of_add_eq_zero_right

@[to_additive]
theorem eq_of_div_eq_one (h : a / b = 1) : a = b :=
  inv_injective <| inv_eq_of_mul_eq_one_right <| by rwa [← div_eq_mul_inv]
#align eq_of_div_eq_one eq_of_div_eq_one
#align eq_of_sub_eq_zero eq_of_sub_eq_zero

lemma eq_of_inv_mul_eq_one (h : a⁻¹ * b = 1) : a = b := by simpa using eq_inv_of_mul_eq_one_left h
lemma eq_of_mul_inv_eq_one (h : a * b⁻¹ = 1) : a = b := by simpa using eq_inv_of_mul_eq_one_left h

@[to_additive]
theorem div_ne_one_of_ne : a ≠ b → a / b ≠ 1 :=
  mt eq_of_div_eq_one
#align div_ne_one_of_ne div_ne_one_of_ne
#align sub_ne_zero_of_ne sub_ne_zero_of_ne

variable (a b c)

@[to_additive]
theorem one_div_mul_one_div_rev : 1 / a * (1 / b) = 1 / (b * a) := by simp
#align one_div_mul_one_div_rev one_div_mul_one_div_rev
#align zero_sub_add_zero_sub_rev zero_sub_add_zero_sub_rev

@[to_additive]
theorem inv_div_left : a⁻¹ / b = (b * a)⁻¹ := by simp
#align inv_div_left inv_div_left
#align neg_sub_left neg_sub_left

@[to_additive (attr := simp)]
theorem inv_div : (a / b)⁻¹ = b / a := by simp
#align inv_div inv_div
#align neg_sub neg_sub

@[to_additive]
theorem one_div_div : 1 / (a / b) = b / a := by simp
#align one_div_div one_div_div
#align zero_sub_sub zero_sub_sub

@[to_additive]
theorem one_div_one_div : 1 / (1 / a) = a := by simp
#align one_div_one_div one_div_one_div
#align zero_sub_zero_sub zero_sub_zero_sub

@[to_additive]
theorem div_eq_div_iff_comm : a / b = c / d ↔ b / a = d / c :=
  inv_inj.symm.trans <| by simp only [inv_div]

@[to_additive SubtractionMonoid.toSubNegZeroMonoid]
instance (priority := 100) DivisionMonoid.toDivInvOneMonoid : DivInvOneMonoid α :=
  { DivisionMonoid.toDivInvMonoid with
    inv_one := by simpa only [one_div, inv_inv] using (inv_div (1 : α) 1).symm }

@[to_additive (attr := simp)]
lemma inv_pow (a : α) : ∀ n : ℕ, a⁻¹ ^ n = (a ^ n)⁻¹
  | 0 => by rw [pow_zero, pow_zero, inv_one]
  | n + 1 => by rw [pow_succ', pow_succ, inv_pow _ n, mul_inv_rev]
#align inv_pow inv_pow
#align neg_nsmul neg_nsmul

-- the attributes are intentionally out of order. `smul_zero` proves `zsmul_zero`.
@[to_additive zsmul_zero, simp]
lemma one_zpow : ∀ n : ℤ, (1 : α) ^ n = 1
  | (n : ℕ)    => by rw [zpow_natCast, one_pow]
  | .negSucc n => by rw [zpow_negSucc, one_pow, inv_one]
#align one_zpow one_zpow
#align zsmul_zero zsmul_zero

@[to_additive (attr := simp) neg_zsmul]
lemma zpow_neg (a : α) : ∀ n : ℤ, a ^ (-n) = (a ^ n)⁻¹
  | (n + 1 : ℕ) => DivInvMonoid.zpow_neg' _ _
  | 0 => by
    change a ^ (0 : ℤ) = (a ^ (0 : ℤ))⁻¹
    simp
  | Int.negSucc n => by
    rw [zpow_negSucc, inv_inv, ← zpow_natCast]
    rfl
#align zpow_neg zpow_neg
#align neg_zsmul neg_zsmul

@[to_additive neg_one_zsmul_add]
lemma mul_zpow_neg_one (a b : α) : (a * b) ^ (-1 : ℤ) = b ^ (-1 : ℤ) * a ^ (-1 : ℤ) := by
  simp only [zpow_neg, zpow_one, mul_inv_rev]
#align mul_zpow_neg_one mul_zpow_neg_one
#align neg_one_zsmul_add neg_one_zsmul_add

@[to_additive zsmul_neg]
lemma inv_zpow (a : α) : ∀ n : ℤ, a⁻¹ ^ n = (a ^ n)⁻¹
  | (n : ℕ)    => by rw [zpow_natCast, zpow_natCast, inv_pow]
  | .negSucc n => by rw [zpow_negSucc, zpow_negSucc, inv_pow]
#align inv_zpow inv_zpow
#align zsmul_neg zsmul_neg

@[to_additive (attr := simp) zsmul_neg']
lemma inv_zpow' (a : α) (n : ℤ) : a⁻¹ ^ n = a ^ (-n) := by rw [inv_zpow, zpow_neg]
#align inv_zpow' inv_zpow'
#align zsmul_neg' zsmul_neg'

@[to_additive nsmul_zero_sub]
lemma one_div_pow (a : α) (n : ℕ) : (1 / a) ^ n = 1 / a ^ n := by simp only [one_div, inv_pow]
#align one_div_pow one_div_pow
#align nsmul_zero_sub nsmul_zero_sub

@[to_additive zsmul_zero_sub]
lemma one_div_zpow (a : α) (n : ℤ) : (1 / a) ^ n = 1 / a ^ n := by simp only [one_div, inv_zpow]
#align one_div_zpow one_div_zpow
#align zsmul_zero_sub zsmul_zero_sub

variable {a b c}

@[to_additive (attr := simp)]
theorem inv_eq_one : a⁻¹ = 1 ↔ a = 1 :=
  inv_injective.eq_iff' inv_one
#align inv_eq_one inv_eq_one
#align neg_eq_zero neg_eq_zero

@[to_additive (attr := simp)]
theorem one_eq_inv : 1 = a⁻¹ ↔ a = 1 :=
  eq_comm.trans inv_eq_one
#align one_eq_inv one_eq_inv
#align zero_eq_neg zero_eq_neg

@[to_additive]
theorem inv_ne_one : a⁻¹ ≠ 1 ↔ a ≠ 1 :=
  inv_eq_one.not
#align inv_ne_one inv_ne_one
#align neg_ne_zero neg_ne_zero

@[to_additive]
theorem eq_of_one_div_eq_one_div (h : 1 / a = 1 / b) : a = b := by
  rw [← one_div_one_div a, h, one_div_one_div]
#align eq_of_one_div_eq_one_div eq_of_one_div_eq_one_div
#align eq_of_zero_sub_eq_zero_sub eq_of_zero_sub_eq_zero_sub

-- Note that `mul_zsmul` and `zpow_mul` have the primes swapped
-- when additivised since their argument order,
-- and therefore the more "natural" choice of lemma, is reversed.
@[to_additive mul_zsmul'] lemma zpow_mul (a : α) : ∀ m n : ℤ, a ^ (m * n) = (a ^ m) ^ n
  | (m : ℕ), (n : ℕ) => by
    rw [zpow_natCast, zpow_natCast, ← pow_mul, ← zpow_natCast]
    rfl
  | (m : ℕ), .negSucc n => by
    rw [zpow_natCast, zpow_negSucc, ← pow_mul, Int.ofNat_mul_negSucc, zpow_neg, inv_inj,
      ← zpow_natCast]
  | .negSucc m, (n : ℕ) => by
    rw [zpow_natCast, zpow_negSucc, ← inv_pow, ← pow_mul, Int.negSucc_mul_ofNat, zpow_neg, inv_pow,
      inv_inj, ← zpow_natCast]
  | .negSucc m, .negSucc n => by
    rw [zpow_negSucc, zpow_negSucc, Int.negSucc_mul_negSucc, inv_pow, inv_inv, ← pow_mul, ←
      zpow_natCast]
    rfl
#align zpow_mul zpow_mul
#align mul_zsmul' mul_zsmul'

@[to_additive mul_zsmul]
lemma zpow_mul' (a : α) (m n : ℤ) : a ^ (m * n) = (a ^ n) ^ m := by rw [Int.mul_comm, zpow_mul]
#align zpow_mul' zpow_mul'
#align mul_zsmul mul_zsmul

#noalign zpow_bit0
#noalign bit0_zsmul
#noalign zpow_bit0'
#noalign bit0_zsmul'
#noalign zpow_bit1
#noalign bit1_zsmul

variable (a b c)

@[to_additive, field_simps] -- The attributes are out of order on purpose
theorem div_div_eq_mul_div : a / (b / c) = a * c / b := by simp
#align div_div_eq_mul_div div_div_eq_mul_div
#align sub_sub_eq_add_sub sub_sub_eq_add_sub

@[to_additive (attr := simp)]
theorem div_inv_eq_mul : a / b⁻¹ = a * b := by simp
#align div_inv_eq_mul div_inv_eq_mul
#align sub_neg_eq_add sub_neg_eq_add

@[to_additive]
theorem div_mul_eq_div_div_swap : a / (b * c) = a / c / b := by
  simp only [mul_assoc, mul_inv_rev, div_eq_mul_inv]
#align div_mul_eq_div_div_swap div_mul_eq_div_div_swap
#align sub_add_eq_sub_sub_swap sub_add_eq_sub_sub_swap

end DivisionMonoid

section SubtractionMonoid

set_option linter.deprecated false

lemma bit0_neg [SubtractionMonoid α] (a : α) : bit0 (-a) = -bit0 a := (neg_add_rev _ _).symm
#align bit0_neg bit0_neg

end SubtractionMonoid

section DivisionCommMonoid

variable [DivisionCommMonoid α] (a b c d : α)

attribute [local simp] mul_assoc mul_comm mul_left_comm div_eq_mul_inv

@[to_additive neg_add]
theorem mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by simp
#align mul_inv mul_inv
#align neg_add neg_add

@[to_additive]
theorem inv_div' : (a / b)⁻¹ = a⁻¹ / b⁻¹ := by simp
#align inv_div' inv_div'
#align neg_sub' neg_sub'

@[to_additive]
theorem div_eq_inv_mul : a / b = b⁻¹ * a := by simp
#align div_eq_inv_mul div_eq_inv_mul
#align sub_eq_neg_add sub_eq_neg_add

@[to_additive]
theorem inv_mul_eq_div : a⁻¹ * b = b / a := by simp
#align inv_mul_eq_div inv_mul_eq_div
#align neg_add_eq_sub neg_add_eq_sub

@[to_additive]
theorem inv_mul' : (a * b)⁻¹ = a⁻¹ / b := by simp
#align inv_mul' inv_mul'
#align neg_add' neg_add'

@[to_additive]
theorem inv_div_inv : a⁻¹ / b⁻¹ = b / a := by simp
#align inv_div_inv inv_div_inv
#align neg_sub_neg neg_sub_neg

@[to_additive]
theorem inv_inv_div_inv : (a⁻¹ / b⁻¹)⁻¹ = a / b := by simp
#align inv_inv_div_inv inv_inv_div_inv
#align neg_neg_sub_neg neg_neg_sub_neg

@[to_additive]
theorem one_div_mul_one_div : 1 / a * (1 / b) = 1 / (a * b) := by simp
#align one_div_mul_one_div one_div_mul_one_div
#align zero_sub_add_zero_sub zero_sub_add_zero_sub

@[to_additive]
theorem div_right_comm : a / b / c = a / c / b := by simp
#align div_right_comm div_right_comm
#align sub_right_comm sub_right_comm

@[to_additive, field_simps]
theorem div_div : a / b / c = a / (b * c) := by simp
#align div_div div_div
#align sub_sub sub_sub

@[to_additive]
theorem div_mul : a / b * c = a / (b / c) := by simp
#align div_mul div_mul
#align sub_add sub_add

@[to_additive]
theorem mul_div_left_comm : a * (b / c) = b * (a / c) := by simp
#align mul_div_left_comm mul_div_left_comm
#align add_sub_left_comm add_sub_left_comm

@[to_additive]
theorem mul_div_right_comm : a * b / c = a / c * b := by simp
#align mul_div_right_comm mul_div_right_comm
#align add_sub_right_comm add_sub_right_comm

@[to_additive]
theorem div_mul_eq_div_div : a / (b * c) = a / b / c := by simp
#align div_mul_eq_div_div div_mul_eq_div_div
#align sub_add_eq_sub_sub sub_add_eq_sub_sub

@[to_additive, field_simps]
theorem div_mul_eq_mul_div : a / b * c = a * c / b := by simp
#align div_mul_eq_mul_div div_mul_eq_mul_div
#align sub_add_eq_add_sub sub_add_eq_add_sub

@[to_additive]
theorem one_div_mul_eq_div : 1 / a * b = b / a := by simp

@[to_additive]
theorem mul_comm_div : a / b * c = a * (c / b) := by simp
#align mul_comm_div mul_comm_div
#align add_comm_sub add_comm_sub

@[to_additive]
theorem div_mul_comm : a / b * c = c / b * a := by simp
#align div_mul_comm div_mul_comm
#align sub_add_comm sub_add_comm

@[to_additive]
theorem div_mul_eq_div_mul_one_div : a / (b * c) = a / b * (1 / c) := by simp
#align div_mul_eq_div_mul_one_div div_mul_eq_div_mul_one_div
#align sub_add_eq_sub_add_zero_sub sub_add_eq_sub_add_zero_sub

@[to_additive]
theorem div_div_div_eq : a / b / (c / d) = a * d / (b * c) := by simp
#align div_div_div_eq div_div_div_eq
#align sub_sub_sub_eq sub_sub_sub_eq

@[to_additive]
theorem div_div_div_comm : a / b / (c / d) = a / c / (b / d) := by simp
#align div_div_div_comm div_div_div_comm
#align sub_sub_sub_comm sub_sub_sub_comm

@[to_additive]
theorem div_mul_div_comm : a / b * (c / d) = a * c / (b * d) := by simp
#align div_mul_div_comm div_mul_div_comm
#align sub_add_sub_comm sub_add_sub_comm

@[to_additive]
theorem mul_div_mul_comm : a * b / (c * d) = a / c * (b / d) := by simp
#align mul_div_mul_comm mul_div_mul_comm
#align add_sub_add_comm add_sub_add_comm

@[to_additive zsmul_add] lemma mul_zpow : ∀ n : ℤ, (a * b) ^ n = a ^ n * b ^ n
  | (n : ℕ) => by simp_rw [zpow_natCast, mul_pow]
  | .negSucc n => by simp_rw [zpow_negSucc, ← inv_pow, mul_inv, mul_pow]
#align mul_zpow mul_zpow
#align zsmul_add zsmul_add

@[to_additive (attr := simp) nsmul_sub]
lemma div_pow (a b : α) (n : ℕ) : (a / b) ^ n = a ^ n / b ^ n := by
  simp only [div_eq_mul_inv, mul_pow, inv_pow]
#align div_pow div_pow
#align nsmul_sub nsmul_sub

@[to_additive (attr := simp) zsmul_sub]
lemma div_zpow (a b : α) (n : ℤ) : (a / b) ^ n = a ^ n / b ^ n := by
  simp only [div_eq_mul_inv, mul_zpow, inv_zpow]
#align div_zpow div_zpow
#align zsmul_sub zsmul_sub

end DivisionCommMonoid

section Group

variable [Group G] {a b c d : G} {n : ℤ}

@[to_additive (attr := simp)]
theorem div_eq_inv_self : a / b = b⁻¹ ↔ a = 1 := by rw [div_eq_mul_inv, mul_left_eq_self]
#align div_eq_inv_self div_eq_inv_self
#align sub_eq_neg_self sub_eq_neg_self

@[to_additive]
theorem mul_left_surjective (a : G) : Surjective (a * ·) :=
  fun x ↦ ⟨a⁻¹ * x, mul_inv_cancel_left a x⟩
#align mul_left_surjective mul_left_surjective
#align add_left_surjective add_left_surjective

@[to_additive]
theorem mul_right_surjective (a : G) : Function.Surjective fun x ↦ x * a := fun x ↦
  ⟨x * a⁻¹, inv_mul_cancel_right x a⟩
#align mul_right_surjective mul_right_surjective
#align add_right_surjective add_right_surjective

@[to_additive]
theorem eq_mul_inv_of_mul_eq (h : a * c = b) : a = b * c⁻¹ := by simp [h.symm]
#align eq_mul_inv_of_mul_eq eq_mul_inv_of_mul_eq
#align eq_add_neg_of_add_eq eq_add_neg_of_add_eq

@[to_additive]
theorem eq_inv_mul_of_mul_eq (h : b * a = c) : a = b⁻¹ * c := by simp [h.symm]
#align eq_inv_mul_of_mul_eq eq_inv_mul_of_mul_eq
#align eq_neg_add_of_add_eq eq_neg_add_of_add_eq

@[to_additive]
theorem inv_mul_eq_of_eq_mul (h : b = a * c) : a⁻¹ * b = c := by simp [h]
#align inv_mul_eq_of_eq_mul inv_mul_eq_of_eq_mul
#align neg_add_eq_of_eq_add neg_add_eq_of_eq_add

@[to_additive]
theorem mul_inv_eq_of_eq_mul (h : a = c * b) : a * b⁻¹ = c := by simp [h]
#align mul_inv_eq_of_eq_mul mul_inv_eq_of_eq_mul
#align add_neg_eq_of_eq_add add_neg_eq_of_eq_add

@[to_additive]
theorem eq_mul_of_mul_inv_eq (h : a * c⁻¹ = b) : a = b * c := by simp [h.symm]
#align eq_mul_of_mul_inv_eq eq_mul_of_mul_inv_eq
#align eq_add_of_add_neg_eq eq_add_of_add_neg_eq

@[to_additive]
theorem eq_mul_of_inv_mul_eq (h : b⁻¹ * a = c) : a = b * c := by simp [h.symm, mul_inv_cancel_left]
#align eq_mul_of_inv_mul_eq eq_mul_of_inv_mul_eq
#align eq_add_of_neg_add_eq eq_add_of_neg_add_eq

@[to_additive]
theorem mul_eq_of_eq_inv_mul (h : b = a⁻¹ * c) : a * b = c := by rw [h, mul_inv_cancel_left]
#align mul_eq_of_eq_inv_mul mul_eq_of_eq_inv_mul
#align add_eq_of_eq_neg_add add_eq_of_eq_neg_add

@[to_additive]
theorem mul_eq_of_eq_mul_inv (h : a = c * b⁻¹) : a * b = c := by simp [h]
#align mul_eq_of_eq_mul_inv mul_eq_of_eq_mul_inv
#align add_eq_of_eq_add_neg add_eq_of_eq_add_neg

@[to_additive]
theorem mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹ :=
  ⟨eq_inv_of_mul_eq_one_left, fun h ↦ by rw [h, mul_left_inv]⟩
#align mul_eq_one_iff_eq_inv mul_eq_one_iff_eq_inv
#align add_eq_zero_iff_eq_neg add_eq_zero_iff_eq_neg

@[to_additive]
theorem mul_eq_one_iff_inv_eq : a * b = 1 ↔ a⁻¹ = b := by
  rw [mul_eq_one_iff_eq_inv, inv_eq_iff_eq_inv]
#align mul_eq_one_iff_inv_eq mul_eq_one_iff_inv_eq
#align add_eq_zero_iff_neg_eq add_eq_zero_iff_neg_eq

@[to_additive]
theorem eq_inv_iff_mul_eq_one : a = b⁻¹ ↔ a * b = 1 :=
  mul_eq_one_iff_eq_inv.symm
#align eq_inv_iff_mul_eq_one eq_inv_iff_mul_eq_one
#align eq_neg_iff_add_eq_zero eq_neg_iff_add_eq_zero

@[to_additive]
theorem inv_eq_iff_mul_eq_one : a⁻¹ = b ↔ a * b = 1 :=
  mul_eq_one_iff_inv_eq.symm
#align inv_eq_iff_mul_eq_one inv_eq_iff_mul_eq_one
#align neg_eq_iff_add_eq_zero neg_eq_iff_add_eq_zero

@[to_additive]
theorem eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b :=
  ⟨fun h ↦ by rw [h, inv_mul_cancel_right], fun h ↦ by rw [← h, mul_inv_cancel_right]⟩
#align eq_mul_inv_iff_mul_eq eq_mul_inv_iff_mul_eq
#align eq_add_neg_iff_add_eq eq_add_neg_iff_add_eq

@[to_additive]
theorem eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c :=
  ⟨fun h ↦ by rw [h, mul_inv_cancel_left], fun h ↦ by rw [← h, inv_mul_cancel_left]⟩
#align eq_inv_mul_iff_mul_eq eq_inv_mul_iff_mul_eq
#align eq_neg_add_iff_add_eq eq_neg_add_iff_add_eq

@[to_additive]
theorem inv_mul_eq_iff_eq_mul : a⁻¹ * b = c ↔ b = a * c :=
  ⟨fun h ↦ by rw [← h, mul_inv_cancel_left], fun h ↦ by rw [h, inv_mul_cancel_left]⟩
#align inv_mul_eq_iff_eq_mul inv_mul_eq_iff_eq_mul
#align neg_add_eq_iff_eq_add neg_add_eq_iff_eq_add

@[to_additive]
theorem mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b :=
  ⟨fun h ↦ by rw [← h, inv_mul_cancel_right], fun h ↦ by rw [h, mul_inv_cancel_right]⟩
#align mul_inv_eq_iff_eq_mul mul_inv_eq_iff_eq_mul
#align add_neg_eq_iff_eq_add add_neg_eq_iff_eq_add

@[to_additive]
theorem mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b := by rw [mul_eq_one_iff_eq_inv, inv_inv]
#align mul_inv_eq_one mul_inv_eq_one
#align add_neg_eq_zero add_neg_eq_zero

@[to_additive]
theorem inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b := by rw [mul_eq_one_iff_eq_inv, inv_inj]
#align inv_mul_eq_one inv_mul_eq_one
#align neg_add_eq_zero neg_add_eq_zero

@[to_additive (attr := simp)]
theorem conj_eq_one_iff : a * b * a⁻¹ = 1 ↔ b = 1 := by
  rw [mul_inv_eq_one, mul_right_eq_self]

@[to_additive]
theorem div_left_injective : Function.Injective fun a ↦ a / b := by
  -- FIXME this could be by `simpa`, but it fails. This is probably a bug in `simpa`.
  simp only [div_eq_mul_inv]
  exact fun a a' h ↦ mul_left_injective b⁻¹ h
#align div_left_injective div_left_injective
#align sub_left_injective sub_left_injective

@[to_additive]
theorem div_right_injective : Function.Injective fun a ↦ b / a := by
  -- FIXME see above
  simp only [div_eq_mul_inv]
  exact fun a a' h ↦ inv_injective (mul_right_injective b h)
#align div_right_injective div_right_injective
#align sub_right_injective sub_right_injective

@[to_additive (attr := simp)]
theorem div_mul_cancel (a b : G) : a / b * b = a := by
  rw [div_eq_mul_inv, inv_mul_cancel_right a b]
#align div_mul_cancel' div_mul_cancel
#align sub_add_cancel sub_add_cancel

@[to_additive (attr := simp) sub_self]
theorem div_self' (a : G) : a / a = 1 := by rw [div_eq_mul_inv, mul_right_inv a]
#align div_self' div_self'
#align sub_self sub_self

@[to_additive (attr := simp)]
theorem mul_div_cancel_right (a b : G) : a * b / b = a := by
  rw [div_eq_mul_inv, mul_inv_cancel_right a b]
#align mul_div_cancel'' mul_div_cancel_right
#align add_sub_cancel add_sub_cancel_right

@[to_additive (attr := simp)]
lemma div_mul_cancel_right (a b : G) : a / (b * a) = b⁻¹ := by rw [← inv_div, mul_div_cancel_right]
#align div_mul_cancel''' div_mul_cancel_right
#align sub_add_cancel'' sub_add_cancel_right

@[to_additive (attr := simp)]
theorem mul_div_mul_right_eq_div (a b c : G) : a * c / (b * c) = a / b := by
  rw [div_mul_eq_div_div_swap]; simp only [mul_left_inj, eq_self_iff_true, mul_div_cancel_right]
#align mul_div_mul_right_eq_div mul_div_mul_right_eq_div
#align add_sub_add_right_eq_sub add_sub_add_right_eq_sub

@[to_additive eq_sub_of_add_eq]
theorem eq_div_of_mul_eq' (h : a * c = b) : a = b / c := by simp [← h]
#align eq_div_of_mul_eq' eq_div_of_mul_eq'
#align eq_sub_of_add_eq eq_sub_of_add_eq

@[to_additive sub_eq_of_eq_add]
theorem div_eq_of_eq_mul'' (h : a = c * b) : a / b = c := by simp [h]
#align div_eq_of_eq_mul'' div_eq_of_eq_mul''
#align sub_eq_of_eq_add sub_eq_of_eq_add

@[to_additive]
theorem eq_mul_of_div_eq (h : a / c = b) : a = b * c := by simp [← h]
#align eq_mul_of_div_eq eq_mul_of_div_eq
#align eq_add_of_sub_eq eq_add_of_sub_eq

@[to_additive]
theorem mul_eq_of_eq_div (h : a = c / b) : a * b = c := by simp [h]
#align mul_eq_of_eq_div mul_eq_of_eq_div
#align add_eq_of_eq_sub add_eq_of_eq_sub

@[to_additive (attr := simp)]
theorem div_right_inj : a / b = a / c ↔ b = c :=
  div_right_injective.eq_iff
#align div_right_inj div_right_inj
#align sub_right_inj sub_right_inj

@[to_additive (attr := simp)]
theorem div_left_inj : b / a = c / a ↔ b = c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_left_inj _
#align div_left_inj div_left_inj
#align sub_left_inj sub_left_inj

@[to_additive (attr := simp) sub_add_sub_cancel]
theorem div_mul_div_cancel' (a b c : G) : a / b * (b / c) = a / c := by
  rw [← mul_div_assoc, div_mul_cancel]
#align div_mul_div_cancel' div_mul_div_cancel'
#align sub_add_sub_cancel sub_add_sub_cancel

@[to_additive (attr := simp) sub_sub_sub_cancel_right]
theorem div_div_div_cancel_right' (a b c : G) : a / c / (b / c) = a / b := by
  rw [← inv_div c b, div_inv_eq_mul, div_mul_div_cancel']
#align div_div_div_cancel_right' div_div_div_cancel_right'
#align sub_sub_sub_cancel_right sub_sub_sub_cancel_right

@[to_additive]
theorem div_eq_one : a / b = 1 ↔ a = b :=
  ⟨eq_of_div_eq_one, fun h ↦ by rw [h, div_self']⟩
#align div_eq_one div_eq_one
#align sub_eq_zero sub_eq_zero

alias ⟨_, div_eq_one_of_eq⟩ := div_eq_one
#align div_eq_one_of_eq div_eq_one_of_eq

alias ⟨_, sub_eq_zero_of_eq⟩ := sub_eq_zero
#align sub_eq_zero_of_eq sub_eq_zero_of_eq

@[to_additive]
theorem div_ne_one : a / b ≠ 1 ↔ a ≠ b :=
  not_congr div_eq_one
#align div_ne_one div_ne_one
#align sub_ne_zero sub_ne_zero

@[to_additive (attr := simp)]
theorem div_eq_self : a / b = a ↔ b = 1 := by rw [div_eq_mul_inv, mul_right_eq_self, inv_eq_one]
#align div_eq_self div_eq_self
#align sub_eq_self sub_eq_self

@[to_additive eq_sub_iff_add_eq]
theorem eq_div_iff_mul_eq' : a = b / c ↔ a * c = b := by rw [div_eq_mul_inv, eq_mul_inv_iff_mul_eq]
#align eq_div_iff_mul_eq' eq_div_iff_mul_eq'
#align eq_sub_iff_add_eq eq_sub_iff_add_eq

@[to_additive]
theorem div_eq_iff_eq_mul : a / b = c ↔ a = c * b := by rw [div_eq_mul_inv, mul_inv_eq_iff_eq_mul]
#align div_eq_iff_eq_mul div_eq_iff_eq_mul
#align sub_eq_iff_eq_add sub_eq_iff_eq_add

@[to_additive]
theorem eq_iff_eq_of_div_eq_div (H : a / b = c / d) : a = b ↔ c = d := by
  rw [← div_eq_one, H, div_eq_one]
#align eq_iff_eq_of_div_eq_div eq_iff_eq_of_div_eq_div
#align eq_iff_eq_of_sub_eq_sub eq_iff_eq_of_sub_eq_sub

@[to_additive]
theorem leftInverse_div_mul_left (c : G) : Function.LeftInverse (fun x ↦ x / c) fun x ↦ x * c :=
  fun x ↦ mul_div_cancel_right x c
#align left_inverse_div_mul_left leftInverse_div_mul_left
#align left_inverse_sub_add_left leftInverse_sub_add_left

@[to_additive]
theorem leftInverse_mul_left_div (c : G) : Function.LeftInverse (fun x ↦ x * c) fun x ↦ x / c :=
  fun x ↦ div_mul_cancel x c
#align left_inverse_mul_left_div leftInverse_mul_left_div
#align left_inverse_add_left_sub leftInverse_add_left_sub

@[to_additive]
theorem leftInverse_mul_right_inv_mul (c : G) :
    Function.LeftInverse (fun x ↦ c * x) fun x ↦ c⁻¹ * x :=
  fun x ↦ mul_inv_cancel_left c x
#align left_inverse_mul_right_inv_mul leftInverse_mul_right_inv_mul
#align left_inverse_add_right_neg_add leftInverse_add_right_neg_add

@[to_additive]
theorem leftInverse_inv_mul_mul_right (c : G) :
    Function.LeftInverse (fun x ↦ c⁻¹ * x) fun x ↦ c * x :=
  fun x ↦ inv_mul_cancel_left c x
#align left_inverse_inv_mul_mul_right leftInverse_inv_mul_mul_right
#align left_inverse_neg_add_add_right leftInverse_neg_add_add_right

@[to_additive (attr := simp) natAbs_nsmul_eq_zero]
lemma pow_natAbs_eq_one : a ^ n.natAbs = 1 ↔ a ^ n = 1 := by cases n <;> simp

set_option linter.existingAttributeWarning false in
@[to_additive, deprecated pow_natAbs_eq_one (since := "2024-02-14")]
lemma exists_pow_eq_one_of_zpow_eq_one (hn : n ≠ 0) (h : a ^ n = 1) :
    ∃ n : ℕ, 0 < n ∧ a ^ n = 1 := ⟨_, Int.natAbs_pos.2 hn, pow_natAbs_eq_one.2 h⟩
#align exists_npow_eq_one_of_zpow_eq_one exists_pow_eq_one_of_zpow_eq_one
#align exists_nsmul_eq_zero_of_zsmul_eq_zero exists_nsmul_eq_zero_of_zsmul_eq_zero

attribute [deprecated natAbs_nsmul_eq_zero (since := "2024-02-14")]
exists_nsmul_eq_zero_of_zsmul_eq_zero

@[to_additive sub_nsmul]
lemma pow_sub (a : G) {m n : ℕ} (h : n ≤ m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ :=
  eq_mul_inv_of_mul_eq <| by rw [← pow_add, Nat.sub_add_cancel h]
#align pow_sub pow_sub
#align sub_nsmul sub_nsmul

@[to_additive sub_nsmul_neg]
theorem inv_pow_sub (a : G) {m n : ℕ} (h : n ≤ m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n := by
  rw [pow_sub a⁻¹ h, inv_pow, inv_pow, inv_inv]
#align inv_pow_sub inv_pow_sub
#align sub_nsmul_neg sub_nsmul_neg

@[to_additive add_one_zsmul]
lemma zpow_add_one (a : G) : ∀ n : ℤ, a ^ (n + 1) = a ^ n * a
  | (n : ℕ) => by simp only [← Int.ofNat_succ, zpow_natCast, pow_succ]
  | .negSucc 0 => by simp [Int.negSucc_eq', Int.add_left_neg]
  | .negSucc (n + 1) => by
    rw [zpow_negSucc, pow_succ', mul_inv_rev, inv_mul_cancel_right]
    rw [Int.negSucc_eq, Int.neg_add, Int.neg_add_cancel_right]
    exact zpow_negSucc _ _
#align zpow_add_one zpow_add_one
#align add_one_zsmul add_one_zsmul

@[to_additive sub_one_zsmul]
lemma zpow_sub_one (a : G) (n : ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ :=
  calc
    a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ := (mul_inv_cancel_right _ _).symm
    _ = a ^ n * a⁻¹ := by rw [← zpow_add_one, Int.sub_add_cancel]
#align zpow_sub_one zpow_sub_one
#align sub_one_zsmul sub_one_zsmul

@[to_additive add_zsmul]
lemma zpow_add (a : G) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n using Int.induction_on with
  | hz => simp
  | hp n ihn => simp only [← Int.add_assoc, zpow_add_one, ihn, mul_assoc]
  | hn n ihn => rw [zpow_sub_one, ← mul_assoc, ← ihn, ← zpow_sub_one, Int.add_sub_assoc]
#align zpow_add zpow_add
#align add_zsmul add_zsmul

@[to_additive one_add_zsmul]
lemma zpow_one_add (a : G) (n : ℤ) : a ^ (1 + n) = a * a ^ n := by rw [zpow_add, zpow_one]
#align zpow_one_add zpow_one_add
#align one_add_zsmul one_add_zsmul

@[to_additive add_zsmul_self]
lemma mul_self_zpow (a : G) (n : ℤ) : a * a ^ n = a ^ (n + 1) := by
  rw [Int.add_comm, zpow_add, zpow_one]
#align mul_self_zpow mul_self_zpow
#align add_zsmul_self add_zsmul_self

@[to_additive add_self_zsmul]
lemma mul_zpow_self (a : G) (n : ℤ) : a ^ n * a = a ^ (n + 1) := (zpow_add_one ..).symm
#align mul_zpow_self mul_zpow_self
#align add_self_zsmul add_self_zsmul

@[to_additive sub_zsmul] lemma zpow_sub (a : G) (m n : ℤ) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
  rw [Int.sub_eq_add_neg, zpow_add, zpow_neg]
#align zpow_sub zpow_sub
#align sub_zsmul sub_zsmul

@[to_additive] lemma zpow_mul_comm (a : G) (m n : ℤ) : a ^ m * a ^ n = a ^ n * a ^ m := by
  rw [← zpow_add, Int.add_comm, zpow_add]
#align zpow_mul_comm zpow_mul_comm
#align zsmul_add_comm zsmul_add_comm

theorem zpow_eq_zpow_emod {x : G} (m : ℤ) {n : ℤ} (h : x ^ n = 1) :
    x ^ m = x ^ (m % n) :=
  calc
    x ^ m = x ^ (m % n + n * (m / n)) := by rw [Int.emod_add_ediv]
    _ = x ^ (m % n) := by simp [zpow_add, zpow_mul, h]

theorem zpow_eq_zpow_emod' {x : G} (m : ℤ) {n : ℕ} (h : x ^ n = 1) :
    x ^ m = x ^ (m % (n : ℤ)) := zpow_eq_zpow_emod m (by simpa)

/-- To show a property of all powers of `g` it suffices to show it is closed under multiplication
by `g` and `g⁻¹` on the left. For subgroups generated by more than one element, see
`Subgroup.closure_induction_left`. -/
@[to_additive "To show a property of all multiples of `g` it suffices to show it is closed under
addition by `g` and `-g` on the left. For additive subgroups generated by more than one element, see
`AddSubgroup.closure_induction_left`."]
lemma zpow_induction_left {g : G} {P : G → Prop} (h_one : P (1 : G))
    (h_mul : ∀ a, P a → P (g * a)) (h_inv : ∀ a, P a → P (g⁻¹ * a)) (n : ℤ) : P (g ^ n) := by
  induction' n using Int.induction_on with n ih n ih
  · rwa [zpow_zero]
  · rw [Int.add_comm, zpow_add, zpow_one]
    exact h_mul _ ih
  · rw [Int.sub_eq_add_neg, Int.add_comm, zpow_add, zpow_neg_one]
    exact h_inv _ ih
#align zpow_induction_left zpow_induction_left
#align zsmul_induction_left zsmul_induction_left

/-- To show a property of all powers of `g` it suffices to show it is closed under multiplication
by `g` and `g⁻¹` on the right. For subgroups generated by more than one element, see
`Subgroup.closure_induction_right`. -/
@[to_additive "To show a property of all multiples of `g` it suffices to show it is closed under
addition by `g` and `-g` on the right. For additive subgroups generated by more than one element,
see `AddSubgroup.closure_induction_right`."]
lemma zpow_induction_right {g : G} {P : G → Prop} (h_one : P (1 : G))
    (h_mul : ∀ a, P a → P (a * g)) (h_inv : ∀ a, P a → P (a * g⁻¹)) (n : ℤ) : P (g ^ n) := by
  induction' n using Int.induction_on with n ih n ih
  · rwa [zpow_zero]
  · rw [zpow_add_one]
    exact h_mul _ ih
  · rw [zpow_sub_one]
    exact h_inv _ ih
#align zpow_induction_right zpow_induction_right
#align zsmul_induction_right zsmul_induction_right

end Group

section CommGroup

variable [CommGroup G] {a b c d : G}

attribute [local simp] mul_assoc mul_comm mul_left_comm div_eq_mul_inv

@[to_additive]
theorem div_eq_of_eq_mul' {a b c : G} (h : a = b * c) : a / b = c := by
  rw [h, div_eq_mul_inv, mul_comm, inv_mul_cancel_left]
#align div_eq_of_eq_mul' div_eq_of_eq_mul'
#align sub_eq_of_eq_add' sub_eq_of_eq_add'

@[to_additive (attr := simp)]
theorem mul_div_mul_left_eq_div (a b c : G) : c * a / (c * b) = a / b := by
  rw [div_eq_mul_inv, mul_inv_rev, mul_comm b⁻¹ c⁻¹, mul_comm c a, mul_assoc, ← mul_assoc c,
    mul_right_inv, one_mul, div_eq_mul_inv]
#align mul_div_mul_left_eq_div mul_div_mul_left_eq_div
#align add_sub_add_left_eq_sub add_sub_add_left_eq_sub

@[to_additive eq_sub_of_add_eq']
theorem eq_div_of_mul_eq'' (h : c * a = b) : a = b / c := by simp [h.symm]
#align eq_div_of_mul_eq'' eq_div_of_mul_eq''
#align eq_sub_of_add_eq' eq_sub_of_add_eq'

@[to_additive]
theorem eq_mul_of_div_eq' (h : a / b = c) : a = b * c := by simp [h.symm]
#align eq_mul_of_div_eq' eq_mul_of_div_eq'
#align eq_add_of_sub_eq' eq_add_of_sub_eq'

@[to_additive]
theorem mul_eq_of_eq_div' (h : b = c / a) : a * b = c := by
  rw [h, div_eq_mul_inv, mul_comm c, mul_inv_cancel_left]
#align mul_eq_of_eq_div' mul_eq_of_eq_div'
#align add_eq_of_eq_sub' add_eq_of_eq_sub'

@[to_additive sub_sub_self]
theorem div_div_self' (a b : G) : a / (a / b) = b := by simp
#align div_div_self' div_div_self'
#align sub_sub_self sub_sub_self

@[to_additive]
theorem div_eq_div_mul_div (a b c : G) : a / b = c / b * (a / c) := by simp [mul_left_comm c]
#align div_eq_div_mul_div div_eq_div_mul_div
#align sub_eq_sub_add_sub sub_eq_sub_add_sub

@[to_additive (attr := simp)]
theorem div_div_cancel (a b : G) : a / (a / b) = b :=
  div_div_self' a b
#align div_div_cancel div_div_cancel
#align sub_sub_cancel sub_sub_cancel

@[to_additive (attr := simp)]
theorem div_div_cancel_left (a b : G) : a / b / a = b⁻¹ := by simp
#align div_div_cancel_left div_div_cancel_left
#align sub_sub_cancel_left sub_sub_cancel_left

@[to_additive eq_sub_iff_add_eq']
theorem eq_div_iff_mul_eq'' : a = b / c ↔ c * a = b := by rw [eq_div_iff_mul_eq', mul_comm]
#align eq_div_iff_mul_eq'' eq_div_iff_mul_eq''
#align eq_sub_iff_add_eq' eq_sub_iff_add_eq'

@[to_additive]
theorem div_eq_iff_eq_mul' : a / b = c ↔ a = b * c := by rw [div_eq_iff_eq_mul, mul_comm]
#align div_eq_iff_eq_mul' div_eq_iff_eq_mul'
#align sub_eq_iff_eq_add' sub_eq_iff_eq_add'

@[to_additive (attr := simp)]
theorem mul_div_cancel_left (a b : G) : a * b / a = b := by rw [div_eq_inv_mul, inv_mul_cancel_left]
#align mul_div_cancel''' mul_div_cancel_left
#align add_sub_cancel' add_sub_cancel_left

@[to_additive (attr := simp)]
theorem mul_div_cancel (a b : G) : a * (b / a) = b := by
  rw [← mul_div_assoc, mul_div_cancel_left]
#align mul_div_cancel'_right mul_div_cancel
#align add_sub_cancel'_right add_sub_cancel

@[to_additive (attr := simp)]
theorem div_mul_cancel_left (a b : G) : a / (a * b) = b⁻¹ := by rw [← inv_div, mul_div_cancel_left]
#align div_mul_cancel'' div_mul_cancel_left
#align sub_add_cancel' sub_add_cancel_left

-- This lemma is in the `simp` set under the name `mul_inv_cancel_comm_assoc`,
-- along with the additive version `add_neg_cancel_comm_assoc`,
-- defined in `Algebra.Group.Commute`
@[to_additive]
theorem mul_mul_inv_cancel'_right (a b : G) : a * (b * a⁻¹) = b := by
  rw [← div_eq_mul_inv, mul_div_cancel a b]
#align mul_mul_inv_cancel'_right mul_mul_inv_cancel'_right
#align add_add_neg_cancel'_right add_add_neg_cancel'_right

@[to_additive (attr := simp)]
theorem mul_mul_div_cancel (a b c : G) : a * c * (b / c) = a * b := by
  rw [mul_assoc, mul_div_cancel]
#align mul_mul_div_cancel mul_mul_div_cancel
#align add_add_sub_cancel add_add_sub_cancel

@[to_additive (attr := simp)]
theorem div_mul_mul_cancel (a b c : G) : a / c * (b * c) = a * b := by
  rw [mul_left_comm, div_mul_cancel, mul_comm]
#align div_mul_mul_cancel div_mul_mul_cancel
#align sub_add_add_cancel sub_add_add_cancel

@[to_additive (attr := simp) sub_add_sub_cancel']
theorem div_mul_div_cancel'' (a b c : G) : a / b * (c / a) = c / b := by
  rw [mul_comm]; apply div_mul_div_cancel'
#align div_mul_div_cancel'' div_mul_div_cancel''
#align sub_add_sub_cancel' sub_add_sub_cancel'

@[to_additive (attr := simp)]
theorem mul_div_div_cancel (a b c : G) : a * b / (a / c) = b * c := by
  rw [← div_mul, mul_div_cancel_left]
#align mul_div_div_cancel mul_div_div_cancel
#align add_sub_sub_cancel add_sub_sub_cancel

@[to_additive (attr := simp)]
theorem div_div_div_cancel_left (a b c : G) : c / a / (c / b) = b / a := by
  rw [← inv_div b c, div_inv_eq_mul, mul_comm, div_mul_div_cancel']
#align div_div_div_cancel_left div_div_div_cancel_left
#align sub_sub_sub_cancel_left sub_sub_sub_cancel_left

@[to_additive]
theorem div_eq_div_iff_mul_eq_mul : a / b = c / d ↔ a * d = c * b := by
  rw [div_eq_iff_eq_mul, div_mul_eq_mul_div, eq_comm, div_eq_iff_eq_mul']
  simp only [mul_comm, eq_comm]
#align div_eq_div_iff_mul_eq_mul div_eq_div_iff_mul_eq_mul
#align sub_eq_sub_iff_add_eq_add sub_eq_sub_iff_add_eq_add

@[to_additive]
theorem div_eq_div_iff_div_eq_div : a / b = c / d ↔ a / c = b / d := by
  rw [div_eq_iff_eq_mul, div_mul_eq_mul_div, div_eq_iff_eq_mul', mul_div_assoc]
#align div_eq_div_iff_div_eq_div div_eq_div_iff_div_eq_div
#align sub_eq_sub_iff_sub_eq_sub sub_eq_sub_iff_sub_eq_sub

end CommGroup

section multiplicative

variable [Monoid β] (p r : α → α → Prop) [IsTotal α r] (f : α → α → β)

@[to_additive additive_of_symmetric_of_isTotal]
lemma multiplicative_of_symmetric_of_isTotal
    (hsymm : Symmetric p) (hf_swap : ∀ {a b}, p a b → f a b * f b a = 1)
    (hmul : ∀ {a b c}, r a b → r b c → p a b → p b c → p a c → f a c = f a b * f b c)
    {a b c : α} (pab : p a b) (pbc : p b c) (pac : p a c) : f a c = f a b * f b c := by
  have hmul' : ∀ {b c}, r b c → p a b → p b c → p a c → f a c = f a b * f b c := by
    intros b c rbc pab pbc pac
    obtain rab | rba := total_of r a b
    · exact hmul rab rbc pab pbc pac
    rw [← one_mul (f a c), ← hf_swap pab, mul_assoc]
    obtain rac | rca := total_of r a c
    · rw [hmul rba rac (hsymm pab) pac pbc]
    · rw [hmul rbc rca pbc (hsymm pac) (hsymm pab), mul_assoc, hf_swap (hsymm pac), mul_one]
  obtain rbc | rcb := total_of r b c
  · exact hmul' rbc pab pbc pac
  · rw [hmul' rcb pac (hsymm pbc) pab, mul_assoc, hf_swap (hsymm pbc), mul_one]
#align multiplicative_of_symmetric_of_is_total multiplicative_of_symmetric_of_isTotal
#align additive_of_symmetric_of_is_total additive_of_symmetric_of_isTotal

/-- If a binary function from a type equipped with a total relation `r` to a monoid is
  anti-symmetric (i.e. satisfies `f a b * f b a = 1`), in order to show it is multiplicative
  (i.e. satisfies `f a c = f a b * f b c`), we may assume `r a b` and `r b c` are satisfied.
  We allow restricting to a subset specified by a predicate `p`. -/
@[to_additive additive_of_isTotal "If a binary function from a type equipped with a total relation
`r` to an additive monoid is anti-symmetric (i.e. satisfies `f a b + f b a = 0`), in order to show
it is additive (i.e. satisfies `f a c = f a b + f b c`), we may assume `r a b` and `r b c` are
satisfied. We allow restricting to a subset specified by a predicate `p`."]
theorem multiplicative_of_isTotal (p : α → Prop) (hswap : ∀ {a b}, p a → p b → f a b * f b a = 1)
    (hmul : ∀ {a b c}, r a b → r b c → p a → p b → p c → f a c = f a b * f b c) {a b c : α}
    (pa : p a) (pb : p b) (pc : p c) : f a c = f a b * f b c := by
  apply multiplicative_of_symmetric_of_isTotal (fun a b => p a ∧ p b) r f fun _ _ => And.symm
  · simp_rw [and_imp]; exact @hswap
  · exact fun rab rbc pab _pbc pac => hmul rab rbc pab.1 pab.2 pac.2
  exacts [⟨pa, pb⟩, ⟨pb, pc⟩, ⟨pa, pc⟩]
#align multiplicative_of_is_total multiplicative_of_isTotal
#align additive_of_is_total additive_of_isTotal

end multiplicative

@[deprecated (since := "2024-03-20")] alias div_mul_cancel' := div_mul_cancel
@[deprecated (since := "2024-03-20")] alias mul_div_cancel'' := mul_div_cancel_right
-- The name `add_sub_cancel` was reused
-- @[deprecated (since := "2024-03-20")] alias add_sub_cancel := add_sub_cancel_right
@[deprecated (since := "2024-03-20")] alias div_mul_cancel''' := div_mul_cancel_right
@[deprecated (since := "2024-03-20")] alias sub_add_cancel'' := sub_add_cancel_right
@[deprecated (since := "2024-03-20")] alias mul_div_cancel''' := mul_div_cancel_left
@[deprecated (since := "2024-03-20")] alias add_sub_cancel' := add_sub_cancel_left
@[deprecated (since := "2024-03-20")] alias mul_div_cancel'_right := mul_div_cancel
@[deprecated (since := "2024-03-20")] alias add_sub_cancel'_right := add_sub_cancel
@[deprecated (since := "2024-03-20")] alias div_mul_cancel'' := div_mul_cancel_left
@[deprecated (since := "2024-03-20")] alias sub_add_cancel' := sub_add_cancel_left
