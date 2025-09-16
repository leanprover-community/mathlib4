/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
import Aesop
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Int.Init
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs

/-!
# Basic lemmas about semigroups, monoids, and groups

This file lists various basic lemmas about semigroups, monoids, and groups. Most proofs are
one-liners from the corresponding axioms. For the definitions of semigroups, monoids and groups, see
`Algebra/Group/Defs.lean`.
-/

assert_not_exists MonoidWithZero DenselyOrdered

open Function

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

section Semigroup
variable [Semigroup α]

@[to_additive]
instance Semigroup.to_isAssociative : Std.Associative (α := α) (· * ·) := ⟨mul_assoc⟩

/-- Composing two multiplications on the left by `y` then `x`
is equal to a multiplication on the left by `x * y`.
-/
@[to_additive (attr := simp) /-- Composing two additions on the left by `y` then `x`
is equal to an addition on the left by `x + y`. -/]
theorem comp_mul_left (x y : α) : (x * ·) ∘ (y * ·) = (x * y * ·) := by
  ext z
  simp [mul_assoc]

/-- Composing two multiplications on the right by `y` and `x`
is equal to a multiplication on the right by `y * x`.
-/
@[to_additive (attr := simp) /-- Composing two additions on the right by `y` and `x`
is equal to an addition on the right by `y + x`. -/]
theorem comp_mul_right (x y : α) : (· * x) ∘ (· * y) = (· * (y * x)) := by
  ext z
  simp [mul_assoc]

end Semigroup

@[to_additive]
instance CommMagma.to_isCommutative [CommMagma G] : Std.Commutative (α := G) (· * ·) := ⟨mul_comm⟩

section MulOneClass

variable [MulOneClass M]

@[to_additive]
theorem ite_mul_one {P : Prop} [Decidable P] {a b : M} :
    ite P (a * b) 1 = ite P a 1 * ite P b 1 := by
  by_cases h : P <;> simp [h]

@[to_additive]
theorem ite_one_mul {P : Prop} [Decidable P] {a b : M} :
    ite P 1 (a * b) = ite P 1 a * ite P 1 b := by
  by_cases h : P <;> simp [h]

@[to_additive]
theorem eq_one_iff_eq_one_of_mul_eq_one {a b : M} (h : a * b = 1) : a = 1 ↔ b = 1 := by
  constructor <;> (rintro rfl; simpa using h)

@[to_additive]
theorem one_mul_eq_id : ((1 : M) * ·) = id :=
  funext one_mul

@[to_additive]
theorem mul_one_eq_id : (· * (1 : M)) = id :=
  funext mul_one

end MulOneClass

section CommSemigroup

variable [CommSemigroup G]

@[to_additive]
theorem mul_left_comm (a b c : G) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, mul_comm a, mul_assoc]

@[to_additive]
theorem mul_right_comm (a b c : G) : a * b * c = a * c * b := by
  rw [mul_assoc, mul_comm b, mul_assoc]

@[to_additive]
theorem mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a * c * (b * d) := by
  simp only [mul_left_comm, mul_assoc]

@[to_additive]
theorem mul_rotate (a b c : G) : a * b * c = b * c * a := by
  simp only [mul_left_comm, mul_comm]

@[to_additive]
theorem mul_rotate' (a b c : G) : a * (b * c) = b * (c * a) := by
  simp only [mul_left_comm, mul_comm]

end CommSemigroup

attribute [local simp] mul_assoc sub_eq_add_neg

section Monoid
variable [Monoid M] {a b : M} {m n : ℕ}

@[to_additive boole_nsmul]
lemma pow_boole (P : Prop) [Decidable P] (a : M) :
    (a ^ if P then 1 else 0) = if P then a else 1 := by simp only [pow_ite, pow_one, pow_zero]

@[to_additive nsmul_add_sub_nsmul]
lemma pow_mul_pow_sub (a : M) (h : m ≤ n) : a ^ m * a ^ (n - m) = a ^ n := by
  rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel h]

@[to_additive sub_nsmul_nsmul_add]
lemma pow_sub_mul_pow (a : M) (h : m ≤ n) : a ^ (n - m) * a ^ m = a ^ n := by
  rw [← pow_add, Nat.sub_add_cancel h]

@[to_additive sub_one_nsmul_add]
lemma mul_pow_sub_one (hn : n ≠ 0) (a : M) : a * a ^ (n - 1) = a ^ n := by
  rw [← pow_succ', Nat.sub_add_cancel <| Nat.one_le_iff_ne_zero.2 hn]

@[to_additive add_sub_one_nsmul]
lemma pow_sub_one_mul (hn : n ≠ 0) (a : M) : a ^ (n - 1) * a = a ^ n := by
  rw [← pow_succ, Nat.sub_add_cancel <| Nat.one_le_iff_ne_zero.2 hn]

/-- If `x ^ n = 1`, then `x ^ m` is the same as `x ^ (m % n)` -/
@[to_additive nsmul_eq_mod_nsmul /-- If `n • x = 0`, then `m • x` is the same as `(m % n) • x` -/]
lemma pow_eq_pow_mod (m : ℕ) (ha : a ^ n = 1) : a ^ m = a ^ (m % n) := by
  calc
    a ^ m = a ^ (m % n + n * (m / n)) := by rw [Nat.mod_add_div]
    _ = a ^ (m % n) := by simp [pow_add, pow_mul, ha]

@[to_additive] lemma pow_mul_pow_eq_one : ∀ n, a * b = 1 → a ^ n * b ^ n = 1
  | 0, _ => by simp
  | n + 1, h =>
    calc
      a ^ n.succ * b ^ n.succ = a ^ n * a * (b * b ^ n) := by rw [pow_succ, pow_succ']
      _ = a ^ n * (a * b) * b ^ n := by simp only [mul_assoc]
      _ = 1 := by simp [h, pow_mul_pow_eq_one]

@[to_additive (attr := simp)]
lemma mul_left_iterate (a : M) : ∀ n : ℕ, (a * ·)^[n] = (a ^ n * ·)
  | 0 => by ext; simp
  | n + 1 => by simp [pow_succ, mul_left_iterate]

@[to_additive (attr := simp)]
lemma mul_right_iterate (a : M) : ∀ n : ℕ, (· * a)^[n] = (· * a ^ n)
  | 0 => by ext; simp
  | n + 1 => by simp [pow_succ', mul_right_iterate]

/-- Version of `mul_left_iterate` that is fully applied, for `rw`. -/
@[to_additive /-- Version of `add_left_iterate` that is fully applied, for `rw`. -/]
lemma mul_left_iterate_apply (a b : M) : (a * ·)^[n] b = a ^ n * b := by simp

/-- Version of `mul_right_iterate` that is fully applied, for `rw`. -/
@[to_additive /-- Version of `add_right_iterate` that is fully applied, for `rw`. -/ ]
lemma mul_right_iterate_apply (a b : M) : (· * a)^[n] b = b * a ^ n := by simp

@[to_additive]
lemma mul_left_iterate_apply_one (a : M) : (a * ·)^[n] 1 = a ^ n := by simp

@[to_additive]
lemma mul_right_iterate_apply_one (a : M) : (· * a)^[n] 1 = a ^ n := by simp [mul_right_iterate]

@[to_additive (attr := simp)]
lemma pow_iterate (k : ℕ) : ∀ n : ℕ, (fun x : M ↦ x ^ k)^[n] = (· ^ k ^ n)
  | 0 => by ext; simp
  | n + 1 => by ext; simp [pow_iterate, Nat.pow_succ', pow_mul]

end Monoid

section CommMonoid
variable [CommMonoid M] {x y z : M}

@[to_additive]
theorem inv_unique (hy : x * y = 1) (hz : x * z = 1) : y = z :=
  left_inv_eq_right_inv (Trans.trans (mul_comm _ _) hy) hz

@[to_additive nsmul_add] lemma mul_pow (a b : M) : ∀ n, (a * b) ^ n = a ^ n * b ^ n
  | 0 => by rw [pow_zero, pow_zero, pow_zero, one_mul]
  | n + 1 => by rw [pow_succ', pow_succ', pow_succ', mul_pow, mul_mul_mul_comm]

end CommMonoid

section LeftCancelMonoid

variable [Monoid M] [IsLeftCancelMul M] {a b : M}

@[to_additive (attr := simp)]
theorem mul_eq_left : a * b = a ↔ b = 1 := calc
  a * b = a ↔ a * b = a * 1 := by rw [mul_one]
  _ ↔ b = 1 := mul_left_cancel_iff

@[deprecated (since := "2025-03-05")] alias mul_right_eq_self := mul_eq_left
@[deprecated (since := "2025-03-05")] alias add_right_eq_self := add_eq_left

set_option linter.existingAttributeWarning false in
attribute [to_additive existing] mul_right_eq_self

@[to_additive (attr := simp)]
theorem left_eq_mul : a = a * b ↔ b = 1 :=
  eq_comm.trans mul_eq_left

@[deprecated (since := "2025-03-05")] alias self_eq_mul_right := left_eq_mul
@[deprecated (since := "2025-03-05")] alias self_eq_add_right := left_eq_add

set_option linter.existingAttributeWarning false in
attribute [to_additive existing] self_eq_mul_right

@[to_additive]
theorem mul_ne_left : a * b ≠ a ↔ b ≠ 1 := mul_eq_left.not

@[deprecated (since := "2025-03-05")] alias mul_right_ne_self := mul_ne_left
@[deprecated (since := "2025-03-05")] alias add_right_ne_self := add_ne_left

set_option linter.existingAttributeWarning false in
attribute [to_additive existing] mul_right_ne_self

@[to_additive]
theorem left_ne_mul : a ≠ a * b ↔ b ≠ 1 := left_eq_mul.not

@[deprecated (since := "2025-03-05")] alias self_ne_mul_right := left_ne_mul
@[deprecated (since := "2025-03-05")] alias self_ne_add_right := left_ne_add

set_option linter.existingAttributeWarning false in
attribute [to_additive existing] self_ne_mul_right

end LeftCancelMonoid

section RightCancelMonoid

variable [Monoid M] [IsRightCancelMul M] {a b : M}

@[to_additive (attr := simp)]
theorem mul_eq_right : a * b = b ↔ a = 1 := calc
  a * b = b ↔ a * b = 1 * b := by rw [one_mul]
  _ ↔ a = 1 := mul_right_cancel_iff

@[deprecated (since := "2025-03-05")] alias mul_left_eq_self := mul_eq_right
@[deprecated (since := "2025-03-05")] alias add_left_eq_self := add_eq_right

set_option linter.existingAttributeWarning false in
attribute [to_additive existing] mul_left_eq_self

@[to_additive (attr := simp)]
theorem right_eq_mul : b = a * b ↔ a = 1 :=
  eq_comm.trans mul_eq_right

@[deprecated (since := "2025-03-05")] alias self_eq_mul_left := right_eq_mul
@[deprecated (since := "2025-03-05")] alias self_eq_add_left := right_eq_add

set_option linter.existingAttributeWarning false in
attribute [to_additive existing] self_eq_mul_left

@[to_additive]
theorem mul_ne_right : a * b ≠ b ↔ a ≠ 1 := mul_eq_right.not

@[deprecated (since := "2025-03-05")] alias mul_left_ne_self := mul_ne_right
@[deprecated (since := "2025-03-05")] alias add_left_ne_self := add_ne_right

set_option linter.existingAttributeWarning false in
attribute [to_additive existing] mul_left_ne_self

@[to_additive]
theorem right_ne_mul : b ≠ a * b ↔ a ≠ 1 := right_eq_mul.not

@[deprecated (since := "2025-03-05")] alias self_ne_mul_left := right_ne_mul
@[deprecated (since := "2025-03-05")] alias self_ne_add_left := right_ne_add

set_option linter.existingAttributeWarning false in
attribute [to_additive existing] self_ne_mul_left

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

@[to_additive (attr := simp)]
theorem inv_surjective : Function.Surjective (Inv.inv : G → G) :=
  inv_involutive.surjective

@[to_additive]
theorem inv_injective : Function.Injective (Inv.inv : G → G) :=
  inv_involutive.injective

@[to_additive (attr := simp)]
theorem inv_inj : a⁻¹ = b⁻¹ ↔ a = b :=
  inv_injective.eq_iff

@[to_additive]
theorem inv_eq_iff_eq_inv : a⁻¹ = b ↔ a = b⁻¹ :=
  ⟨fun h => h ▸ (inv_inv a).symm, fun h => h.symm ▸ inv_inv b⟩

variable (G)

@[to_additive]
theorem inv_comp_inv : Inv.inv ∘ Inv.inv = @id G :=
  inv_involutive.comp_self

@[to_additive]
theorem leftInverse_inv : LeftInverse (fun a : G ↦ a⁻¹) fun a ↦ a⁻¹ :=
  inv_inv

@[to_additive]
theorem rightInverse_inv : RightInverse (fun a : G ↦ a⁻¹) fun a ↦ a⁻¹ :=
  inv_inv

end InvolutiveInv

section DivInvMonoid

variable [DivInvMonoid G]

@[to_additive]
theorem mul_one_div (x y : G) : x * (1 / y) = x / y := by
  rw [div_eq_mul_inv, one_mul, div_eq_mul_inv]

@[to_additive, field_simps] -- The attributes are out of order on purpose
theorem mul_div_assoc' (a b c : G) : a * (b / c) = a * b / c :=
  (mul_div_assoc _ _ _).symm

@[to_additive]
theorem mul_div (a b c : G) : a * (b / c) = a * b / c := by simp only [mul_assoc, div_eq_mul_inv]

@[to_additive]
theorem div_eq_mul_one_div (a b : G) : a / b = a * (1 / b) := by rw [div_eq_mul_inv, one_div]

end DivInvMonoid

section DivInvOneMonoid

variable [DivInvOneMonoid G]

@[to_additive (attr := simp)]
theorem div_one (a : G) : a / 1 = a := by simp [div_eq_mul_inv]

@[to_additive]
theorem one_div_one : (1 : G) / 1 = 1 :=
  div_one _

end DivInvOneMonoid

section DivisionMonoid

variable [DivisionMonoid α] {a b c d : α}

attribute [local simp] mul_assoc div_eq_mul_inv

@[to_additive]
theorem eq_inv_of_mul_eq_one_right (h : a * b = 1) : b = a⁻¹ :=
  (inv_eq_of_mul_eq_one_right h).symm

@[to_additive]
theorem eq_one_div_of_mul_eq_one_left (h : b * a = 1) : b = 1 / a := by
  rw [eq_inv_of_mul_eq_one_left h, one_div]

@[to_additive]
theorem eq_one_div_of_mul_eq_one_right (h : a * b = 1) : b = 1 / a := by
  rw [eq_inv_of_mul_eq_one_right h, one_div]

@[to_additive]
theorem eq_of_div_eq_one (h : a / b = 1) : a = b :=
  inv_injective <| inv_eq_of_mul_eq_one_right <| by rwa [← div_eq_mul_inv]

@[to_additive]
lemma eq_of_inv_mul_eq_one (h : a⁻¹ * b = 1) : a = b := by simpa using eq_inv_of_mul_eq_one_left h

@[to_additive]
lemma eq_of_mul_inv_eq_one (h : a * b⁻¹ = 1) : a = b := by simpa using eq_inv_of_mul_eq_one_left h

@[to_additive]
theorem div_ne_one_of_ne : a ≠ b → a / b ≠ 1 :=
  mt eq_of_div_eq_one

variable (a b c)

@[to_additive]
theorem one_div_mul_one_div_rev : 1 / a * (1 / b) = 1 / (b * a) := by simp

@[to_additive]
theorem inv_div_left : a⁻¹ / b = (b * a)⁻¹ := by simp

@[to_additive (attr := simp)]
theorem inv_div : (a / b)⁻¹ = b / a := by simp

@[to_additive]
theorem one_div_div : 1 / (a / b) = b / a := by simp

@[to_additive]
theorem one_div_one_div : 1 / (1 / a) = a := by simp

@[to_additive]
theorem div_eq_div_iff_comm : a / b = c / d ↔ b / a = d / c :=
  inv_inj.symm.trans <| by simp only [inv_div]

@[to_additive]
instance (priority := 100) DivisionMonoid.toDivInvOneMonoid : DivInvOneMonoid α :=
  { DivisionMonoid.toDivInvMonoid with
    inv_one := by simpa only [one_div, inv_inv] using (inv_div (1 : α) 1).symm }

@[to_additive (attr := simp)]
lemma inv_pow (a : α) : ∀ n : ℕ, a⁻¹ ^ n = (a ^ n)⁻¹
  | 0 => by rw [pow_zero, pow_zero, inv_one]
  | n + 1 => by rw [pow_succ', pow_succ, inv_pow _ n, mul_inv_rev]

-- the attributes are intentionally out of order. `smul_zero` proves `zsmul_zero`.
@[to_additive zsmul_zero, simp]
lemma one_zpow : ∀ n : ℤ, (1 : α) ^ n = 1
  | (n : ℕ) => by rw [zpow_natCast, one_pow]
  | .negSucc n => by rw [zpow_negSucc, one_pow, inv_one]

@[to_additive (attr := simp) neg_zsmul]
lemma zpow_neg (a : α) : ∀ n : ℤ, a ^ (-n) = (a ^ n)⁻¹
  | (_ + 1 : ℕ) => DivInvMonoid.zpow_neg' _ _
  | 0 => by simp
  | Int.negSucc n => by
    rw [zpow_negSucc, inv_inv, ← zpow_natCast]
    rfl

@[to_additive neg_one_zsmul_add]
lemma mul_zpow_neg_one (a b : α) : (a * b) ^ (-1 : ℤ) = b ^ (-1 : ℤ) * a ^ (-1 : ℤ) := by
  simp only [zpow_neg, zpow_one, mul_inv_rev]

@[to_additive zsmul_neg]
lemma inv_zpow (a : α) : ∀ n : ℤ, a⁻¹ ^ n = (a ^ n)⁻¹
  | (n : ℕ) => by rw [zpow_natCast, zpow_natCast, inv_pow]
  | .negSucc n => by rw [zpow_negSucc, zpow_negSucc, inv_pow]

@[to_additive (attr := simp) zsmul_neg']
lemma inv_zpow' (a : α) (n : ℤ) : a⁻¹ ^ n = a ^ (-n) := by rw [inv_zpow, zpow_neg]

@[to_additive nsmul_zero_sub]
lemma one_div_pow (a : α) (n : ℕ) : (1 / a) ^ n = 1 / a ^ n := by simp only [one_div, inv_pow]

@[to_additive zsmul_zero_sub]
lemma one_div_zpow (a : α) (n : ℤ) : (1 / a) ^ n = 1 / a ^ n := by simp only [one_div, inv_zpow]

variable {a b c}

@[to_additive (attr := simp)]
theorem inv_eq_one : a⁻¹ = 1 ↔ a = 1 :=
  inv_injective.eq_iff' inv_one

@[to_additive (attr := simp)]
theorem one_eq_inv : 1 = a⁻¹ ↔ a = 1 :=
  eq_comm.trans inv_eq_one

@[to_additive]
theorem inv_ne_one : a⁻¹ ≠ 1 ↔ a ≠ 1 :=
  inv_eq_one.not

@[to_additive]
theorem eq_of_one_div_eq_one_div (h : 1 / a = 1 / b) : a = b := by
  rw [← one_div_one_div a, h, one_div_one_div]

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

@[to_additive mul_zsmul]
lemma zpow_mul' (a : α) (m n : ℤ) : a ^ (m * n) = (a ^ n) ^ m := by rw [Int.mul_comm, zpow_mul]

@[to_additive]
theorem zpow_comm (a : α) (m n : ℤ) : (a ^ m) ^ n = (a ^ n) ^ m := by rw [← zpow_mul, zpow_mul']

variable (a b c)

@[to_additive, field_simps] -- The attributes are out of order on purpose
theorem div_div_eq_mul_div : a / (b / c) = a * c / b := by simp

@[to_additive (attr := simp)]
theorem div_inv_eq_mul : a / b⁻¹ = a * b := by simp

@[to_additive]
theorem div_mul_eq_div_div_swap : a / (b * c) = a / c / b := by
  simp only [mul_assoc, mul_inv_rev, div_eq_mul_inv]

end DivisionMonoid

section DivisionCommMonoid

variable [DivisionCommMonoid α] (a b c d : α)

attribute [local simp] mul_assoc mul_comm mul_left_comm div_eq_mul_inv

@[to_additive neg_add]
theorem mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by simp

@[to_additive]
theorem inv_div' : (a / b)⁻¹ = a⁻¹ / b⁻¹ := by simp

@[to_additive]
theorem div_eq_inv_mul : a / b = b⁻¹ * a := by simp

@[to_additive]
theorem inv_mul_eq_div : a⁻¹ * b = b / a := by simp

@[to_additive] lemma inv_div_comm (a b : α) : a⁻¹ / b = b⁻¹ / a := by simp

@[to_additive]
theorem inv_mul' : (a * b)⁻¹ = a⁻¹ / b := by simp

@[to_additive]
theorem inv_div_inv : a⁻¹ / b⁻¹ = b / a := by simp

@[to_additive]
theorem inv_inv_div_inv : (a⁻¹ / b⁻¹)⁻¹ = a / b := by simp

@[to_additive]
theorem one_div_mul_one_div : 1 / a * (1 / b) = 1 / (a * b) := by simp

@[to_additive]
theorem div_right_comm : a / b / c = a / c / b := by simp

@[to_additive, field_simps]
theorem div_div : a / b / c = a / (b * c) := by simp

@[to_additive]
theorem div_mul : a / b * c = a / (b / c) := by simp

@[to_additive]
theorem mul_div_left_comm : a * (b / c) = b * (a / c) := by simp

@[to_additive]
theorem mul_div_right_comm : a * b / c = a / c * b := by simp

@[to_additive]
theorem div_mul_eq_div_div : a / (b * c) = a / b / c := by simp

@[to_additive, field_simps]
theorem div_mul_eq_mul_div : a / b * c = a * c / b := by simp

@[to_additive]
theorem one_div_mul_eq_div : 1 / a * b = b / a := by simp

@[to_additive]
theorem mul_comm_div : a / b * c = a * (c / b) := by simp

@[to_additive]
theorem div_mul_comm : a / b * c = c / b * a := by simp

@[to_additive]
theorem div_mul_eq_div_mul_one_div : a / (b * c) = a / b * (1 / c) := by simp

@[to_additive]
theorem div_div_div_eq : a / b / (c / d) = a * d / (b * c) := by simp

@[to_additive]
theorem div_div_div_comm : a / b / (c / d) = a / c / (b / d) := by simp

@[to_additive]
theorem div_mul_div_comm : a / b * (c / d) = a * c / (b * d) := by simp

@[to_additive]
theorem mul_div_mul_comm : a * b / (c * d) = a / c * (b / d) := by simp

@[to_additive zsmul_add] lemma mul_zpow : ∀ n : ℤ, (a * b) ^ n = a ^ n * b ^ n
  | (n : ℕ) => by simp_rw [zpow_natCast, mul_pow]
  | .negSucc n => by simp_rw [zpow_negSucc, ← inv_pow, mul_inv, mul_pow]

@[to_additive nsmul_sub]
lemma div_pow (a b : α) (n : ℕ) : (a / b) ^ n = a ^ n / b ^ n := by
  simp only [div_eq_mul_inv, mul_pow, inv_pow]

@[to_additive zsmul_sub]
lemma div_zpow (a b : α) (n : ℤ) : (a / b) ^ n = a ^ n / b ^ n := by
  simp only [div_eq_mul_inv, mul_zpow, inv_zpow]

attribute [field_simps] div_pow div_zpow

end DivisionCommMonoid

section Group

variable [Group G] {a b c d : G} {n : ℤ}

@[to_additive (attr := simp)]
theorem div_eq_inv_self : a / b = b⁻¹ ↔ a = 1 := by rw [div_eq_mul_inv, mul_eq_right]

@[to_additive]
theorem mul_left_surjective (a : G) : Surjective (a * ·) :=
  fun x ↦ ⟨a⁻¹ * x, mul_inv_cancel_left a x⟩

@[to_additive]
theorem mul_right_surjective (a : G) : Function.Surjective fun x ↦ x * a := fun x ↦
  ⟨x * a⁻¹, inv_mul_cancel_right x a⟩

@[to_additive]
theorem eq_mul_inv_of_mul_eq (h : a * c = b) : a = b * c⁻¹ := by simp [h.symm]

@[to_additive]
theorem eq_inv_mul_of_mul_eq (h : b * a = c) : a = b⁻¹ * c := by simp [h.symm]

@[to_additive]
theorem inv_mul_eq_of_eq_mul (h : b = a * c) : a⁻¹ * b = c := by simp [h]

@[to_additive]
theorem mul_inv_eq_of_eq_mul (h : a = c * b) : a * b⁻¹ = c := by simp [h]

@[to_additive]
theorem eq_mul_of_mul_inv_eq (h : a * c⁻¹ = b) : a = b * c := by simp [h.symm]

@[to_additive]
theorem eq_mul_of_inv_mul_eq (h : b⁻¹ * a = c) : a = b * c := by simp [h.symm, mul_inv_cancel_left]

@[to_additive]
theorem mul_eq_of_eq_inv_mul (h : b = a⁻¹ * c) : a * b = c := by rw [h, mul_inv_cancel_left]

@[to_additive]
theorem mul_eq_of_eq_mul_inv (h : a = c * b⁻¹) : a * b = c := by simp [h]

@[to_additive]
theorem mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹ :=
  ⟨eq_inv_of_mul_eq_one_left, fun h ↦ by rw [h, inv_mul_cancel]⟩

@[to_additive]
theorem mul_eq_one_iff_inv_eq : a * b = 1 ↔ a⁻¹ = b := by
  rw [mul_eq_one_iff_eq_inv, inv_eq_iff_eq_inv]

/-- Variant of `mul_eq_one_iff_eq_inv` with swapped equality. -/
@[to_additive]
theorem mul_eq_one_iff_eq_inv' : a * b = 1 ↔ b = a⁻¹ := by
  rw [mul_eq_one_iff_inv_eq, eq_comm]

/-- Variant of `mul_eq_one_iff_inv_eq` with swapped equality. -/
@[to_additive]
theorem mul_eq_one_iff_inv_eq' : a * b = 1 ↔ b⁻¹ = a := by
  rw [mul_eq_one_iff_eq_inv, eq_comm]

@[to_additive]
theorem eq_inv_iff_mul_eq_one : a = b⁻¹ ↔ a * b = 1 :=
  mul_eq_one_iff_eq_inv.symm

@[to_additive]
theorem inv_eq_iff_mul_eq_one : a⁻¹ = b ↔ a * b = 1 :=
  mul_eq_one_iff_inv_eq.symm

@[to_additive]
theorem eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b :=
  ⟨fun h ↦ by rw [h, inv_mul_cancel_right], fun h ↦ by rw [← h, mul_inv_cancel_right]⟩

@[to_additive]
theorem eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c :=
  ⟨fun h ↦ by rw [h, mul_inv_cancel_left], fun h ↦ by rw [← h, inv_mul_cancel_left]⟩

@[to_additive]
theorem inv_mul_eq_iff_eq_mul : a⁻¹ * b = c ↔ b = a * c :=
  ⟨fun h ↦ by rw [← h, mul_inv_cancel_left], fun h ↦ by rw [h, inv_mul_cancel_left]⟩

@[to_additive]
theorem mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b :=
  ⟨fun h ↦ by rw [← h, inv_mul_cancel_right], fun h ↦ by rw [h, mul_inv_cancel_right]⟩

@[to_additive]
theorem mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b := by rw [mul_eq_one_iff_eq_inv, inv_inv]

@[to_additive]
theorem inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b := by rw [mul_eq_one_iff_eq_inv, inv_inj]

@[to_additive (attr := simp)]
theorem conj_eq_one_iff : a * b * a⁻¹ = 1 ↔ b = 1 := by
  rw [mul_inv_eq_one, mul_eq_left]

@[to_additive]
theorem div_left_injective : Function.Injective fun a ↦ a / b := by
  -- FIXME this could be by `simpa`, but it fails. This is probably a bug in `simpa`.
  simp only [div_eq_mul_inv]
  exact fun a a' h ↦ mul_left_injective b⁻¹ h

@[to_additive]
theorem div_right_injective : Function.Injective fun a ↦ b / a := by
  -- FIXME see above
  simp only [div_eq_mul_inv]
  exact fun a a' h ↦ inv_injective (mul_right_injective b h)

@[to_additive (attr := simp)]
lemma div_mul_cancel_right (a b : G) : a / (b * a) = b⁻¹ := by rw [← inv_div, mul_div_cancel_right]

@[to_additive (attr := simp)]
theorem mul_div_mul_right_eq_div (a b c : G) : a * c / (b * c) = a / b := by
  rw [div_mul_eq_div_div_swap]; simp only [mul_div_cancel_right]

@[to_additive eq_sub_of_add_eq]
theorem eq_div_of_mul_eq' (h : a * c = b) : a = b / c := by simp [← h]

@[to_additive sub_eq_of_eq_add]
theorem div_eq_of_eq_mul'' (h : a = c * b) : a / b = c := by simp [h]

@[to_additive]
theorem eq_mul_of_div_eq (h : a / c = b) : a = b * c := by simp [← h]

@[to_additive]
theorem mul_eq_of_eq_div (h : a = c / b) : a * b = c := by simp [h]

@[to_additive (attr := simp)]
theorem div_right_inj : a / b = a / c ↔ b = c :=
  div_right_injective.eq_iff

@[to_additive (attr := simp)]
theorem div_left_inj : b / a = c / a ↔ b = c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_left_inj _

@[to_additive (attr := simp)]
theorem div_mul_div_cancel (a b c : G) : a / b * (b / c) = a / c := by
  rw [← mul_div_assoc, div_mul_cancel]

@[to_additive (attr := simp)]
theorem div_div_div_cancel_right (a b c : G) : a / c / (b / c) = a / b := by
  rw [← inv_div c b, div_inv_eq_mul, div_mul_div_cancel]

@[to_additive]
theorem div_eq_one : a / b = 1 ↔ a = b :=
  ⟨eq_of_div_eq_one, fun h ↦ by rw [h, div_self']⟩

alias ⟨_, div_eq_one_of_eq⟩ := div_eq_one

alias ⟨_, sub_eq_zero_of_eq⟩ := sub_eq_zero

@[to_additive]
theorem div_ne_one : a / b ≠ 1 ↔ a ≠ b :=
  not_congr div_eq_one

@[to_additive (attr := simp)]
theorem div_eq_self : a / b = a ↔ b = 1 := by rw [div_eq_mul_inv, mul_eq_left, inv_eq_one]

@[to_additive eq_sub_iff_add_eq]
theorem eq_div_iff_mul_eq' : a = b / c ↔ a * c = b := by rw [div_eq_mul_inv, eq_mul_inv_iff_mul_eq]

@[to_additive]
theorem div_eq_iff_eq_mul : a / b = c ↔ a = c * b := by rw [div_eq_mul_inv, mul_inv_eq_iff_eq_mul]

@[to_additive]
theorem eq_iff_eq_of_div_eq_div (H : a / b = c / d) : a = b ↔ c = d := by
  rw [← div_eq_one, H, div_eq_one]

@[to_additive]
theorem leftInverse_div_mul_left (c : G) : Function.LeftInverse (fun x ↦ x / c) fun x ↦ x * c :=
  fun x ↦ mul_div_cancel_right x c

@[to_additive]
theorem leftInverse_mul_left_div (c : G) : Function.LeftInverse (fun x ↦ x * c) fun x ↦ x / c :=
  fun x ↦ div_mul_cancel x c

@[to_additive]
theorem leftInverse_mul_right_inv_mul (c : G) :
    Function.LeftInverse (fun x ↦ c * x) fun x ↦ c⁻¹ * x :=
  fun x ↦ mul_inv_cancel_left c x

@[to_additive]
theorem leftInverse_inv_mul_mul_right (c : G) :
    Function.LeftInverse (fun x ↦ c⁻¹ * x) fun x ↦ c * x :=
  fun x ↦ inv_mul_cancel_left c x

@[to_additive (attr := simp) natAbs_nsmul_eq_zero]
lemma pow_natAbs_eq_one : a ^ n.natAbs = 1 ↔ a ^ n = 1 := by cases n <;> simp

@[to_additive sub_nsmul]
lemma pow_sub (a : G) {m n : ℕ} (h : n ≤ m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ :=
  eq_mul_inv_of_mul_eq <| by rw [← pow_add, Nat.sub_add_cancel h]

@[to_additive sub_nsmul_neg]
theorem inv_pow_sub (a : G) {m n : ℕ} (h : n ≤ m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n := by
  rw [pow_sub a⁻¹ h, inv_pow, inv_pow, inv_inv]

@[to_additive add_one_zsmul]
lemma zpow_add_one (a : G) : ∀ n : ℤ, a ^ (n + 1) = a ^ n * a
  | (n : ℕ) => by simp only [← Int.natCast_succ, zpow_natCast, pow_succ]
  | -1 => by simp [Int.add_left_neg]
  | .negSucc (n + 1) => by
    rw [zpow_negSucc, pow_succ', mul_inv_rev, inv_mul_cancel_right]
    rw [Int.negSucc_eq, Int.neg_add, Int.neg_add_cancel_right]
    exact zpow_negSucc _ _

@[to_additive sub_one_zsmul]
lemma zpow_sub_one (a : G) (n : ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ :=
  calc
    a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ := (mul_inv_cancel_right _ _).symm
    _ = a ^ n * a⁻¹ := by rw [← zpow_add_one, Int.sub_add_cancel]

@[to_additive add_zsmul]
lemma zpow_add (a : G) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => simp
  | succ n ihn => simp only [← Int.add_assoc, zpow_add_one, ihn, mul_assoc]
  | pred n ihn => rw [zpow_sub_one, ← mul_assoc, ← ihn, ← zpow_sub_one, Int.add_sub_assoc]

@[to_additive one_add_zsmul]
lemma zpow_one_add (a : G) (n : ℤ) : a ^ (1 + n) = a * a ^ n := by rw [zpow_add, zpow_one]

@[to_additive add_zsmul_self]
lemma mul_self_zpow (a : G) (n : ℤ) : a * a ^ n = a ^ (n + 1) := by
  rw [Int.add_comm, zpow_add, zpow_one]

@[to_additive add_self_zsmul]
lemma mul_zpow_self (a : G) (n : ℤ) : a ^ n * a = a ^ (n + 1) := (zpow_add_one ..).symm

@[to_additive sub_zsmul] lemma zpow_sub (a : G) (m n : ℤ) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
  rw [Int.sub_eq_add_neg, zpow_add, zpow_neg]

@[to_additive natCast_sub_natCast_zsmul]
lemma zpow_natCast_sub_natCast (a : G) (m n : ℕ) : a ^ (m - n : ℤ) = a ^ m / a ^ n := by
  simpa [div_eq_mul_inv] using zpow_sub a m n

@[to_additive natCast_sub_one_zsmul]
lemma zpow_natCast_sub_one (a : G) (n : ℕ) : a ^ (n - 1 : ℤ) = a ^ n / a := by
  simpa [div_eq_mul_inv] using zpow_sub a n 1

@[to_additive one_sub_natCast_zsmul]
lemma zpow_one_sub_natCast (a : G) (n : ℕ) : a ^ (1 - n : ℤ) = a / a ^ n := by
  simpa [div_eq_mul_inv] using zpow_sub a 1 n

@[to_additive] lemma zpow_mul_comm (a : G) (m n : ℤ) : a ^ m * a ^ n = a ^ n * a ^ m := by
  rw [← zpow_add, Int.add_comm, zpow_add]

theorem zpow_eq_zpow_emod {x : G} (m : ℤ) {n : ℤ} (h : x ^ n = 1) :
    x ^ m = x ^ (m % n) :=
  calc
    x ^ m = x ^ (m % n + n * (m / n)) := by rw [Int.emod_add_mul_ediv]
    _ = x ^ (m % n) := by simp [zpow_add, zpow_mul, h]

theorem zpow_eq_zpow_emod' {x : G} (m : ℤ) {n : ℕ} (h : x ^ n = 1) :
    x ^ m = x ^ (m % (n : ℤ)) := zpow_eq_zpow_emod m (by simpa)

@[to_additive (attr := simp)]
lemma zpow_iterate (k : ℤ) : ∀ n : ℕ, (fun x : G ↦ x ^ k)^[n] = (· ^ k ^ n)
  | 0 => by ext; simp [Int.pow_zero]
  | n + 1 => by ext; simp [zpow_iterate, Int.pow_succ', zpow_mul]

/-- To show a property of all powers of `g` it suffices to show it is closed under multiplication
by `g` and `g⁻¹` on the left. For subgroups generated by more than one element, see
`Subgroup.closure_induction_left`. -/
@[to_additive /-- To show a property of all multiples of `g` it suffices to show it is closed under
addition by `g` and `-g` on the left. For additive subgroups generated by more than one element, see
`AddSubgroup.closure_induction_left`. -/]
lemma zpow_induction_left {g : G} {P : G → Prop} (h_one : P (1 : G))
    (h_mul : ∀ a, P a → P (g * a)) (h_inv : ∀ a, P a → P (g⁻¹ * a)) (n : ℤ) : P (g ^ n) := by
  induction n with
  | zero => rwa [zpow_zero]
  | succ n ih =>
    rw [Int.add_comm, zpow_add, zpow_one]
    exact h_mul _ ih
  | pred n ih =>
    rw [Int.sub_eq_add_neg, Int.add_comm, zpow_add, zpow_neg_one]
    exact h_inv _ ih

/-- To show a property of all powers of `g` it suffices to show it is closed under multiplication
by `g` and `g⁻¹` on the right. For subgroups generated by more than one element, see
`Subgroup.closure_induction_right`. -/
@[to_additive /-- To show a property of all multiples of `g` it suffices to show it is closed under
addition by `g` and `-g` on the right. For additive subgroups generated by more than one element,
see `AddSubgroup.closure_induction_right`. -/]
lemma zpow_induction_right {g : G} {P : G → Prop} (h_one : P (1 : G))
    (h_mul : ∀ a, P a → P (a * g)) (h_inv : ∀ a, P a → P (a * g⁻¹)) (n : ℤ) : P (g ^ n) := by
  induction n with
  | zero => rwa [zpow_zero]
  | succ n ih =>
    rw [zpow_add_one]
    exact h_mul _ ih
  | pred n ih =>
    rw [zpow_sub_one]
    exact h_inv _ ih

end Group

section CommGroup

variable [CommGroup G] {a b c d : G}

attribute [local simp] mul_assoc mul_comm mul_left_comm div_eq_mul_inv

@[to_additive]
theorem div_eq_of_eq_mul' {a b c : G} (h : a = b * c) : a / b = c := by
  rw [h, div_eq_mul_inv, mul_comm, inv_mul_cancel_left]

@[to_additive (attr := simp)]
theorem mul_div_mul_left_eq_div (a b c : G) : c * a / (c * b) = a / b := by
  rw [div_eq_mul_inv, mul_inv_rev, mul_comm b⁻¹ c⁻¹, mul_comm c a, mul_assoc, ← mul_assoc c,
    mul_inv_cancel, one_mul, div_eq_mul_inv]

@[to_additive eq_sub_of_add_eq']
theorem eq_div_of_mul_eq'' (h : c * a = b) : a = b / c := by simp [h.symm]

@[to_additive]
theorem eq_mul_of_div_eq' (h : a / b = c) : a = b * c := by simp [h.symm]

@[to_additive]
theorem mul_eq_of_eq_div' (h : b = c / a) : a * b = c := by
  rw [h, div_eq_mul_inv, mul_comm c, mul_inv_cancel_left]

@[to_additive sub_sub_self]
theorem div_div_self' (a b : G) : a / (a / b) = b := by simp

@[to_additive]
theorem div_eq_div_mul_div (a b c : G) : a / b = c / b * (a / c) := by simp [mul_left_comm c]

@[to_additive (attr := simp)]
theorem div_div_cancel (a b : G) : a / (a / b) = b :=
  div_div_self' a b

@[to_additive (attr := simp)]
theorem div_div_cancel_left (a b : G) : a / b / a = b⁻¹ := by simp

@[to_additive eq_sub_iff_add_eq']
theorem eq_div_iff_mul_eq'' : a = b / c ↔ c * a = b := by rw [eq_div_iff_mul_eq', mul_comm]

@[to_additive]
theorem div_eq_iff_eq_mul' : a / b = c ↔ a = b * c := by rw [div_eq_iff_eq_mul, mul_comm]

@[to_additive (attr := simp)]
theorem mul_div_cancel_left (a b : G) : a * b / a = b := by rw [div_eq_inv_mul, inv_mul_cancel_left]

@[to_additive (attr := simp)]
theorem mul_div_cancel (a b : G) : a * (b / a) = b := by
  rw [← mul_div_assoc, mul_div_cancel_left]

@[to_additive (attr := simp)]
theorem div_mul_cancel_left (a b : G) : a / (a * b) = b⁻¹ := by rw [← inv_div, mul_div_cancel_left]

-- This lemma is in the `simp` set under the name `mul_inv_cancel_comm_assoc`,
-- along with the additive version `add_neg_cancel_comm_assoc`,
-- defined in `Algebra.Group.Commute`
@[to_additive]
theorem mul_mul_inv_cancel'_right (a b : G) : a * (b * a⁻¹) = b := by
  rw [← div_eq_mul_inv, mul_div_cancel a b]

@[to_additive (attr := simp)]
theorem mul_mul_div_cancel (a b c : G) : a * c * (b / c) = a * b := by
  rw [mul_assoc, mul_div_cancel]

@[to_additive (attr := simp)]
theorem div_mul_mul_cancel (a b c : G) : a / c * (b * c) = a * b := by
  rw [mul_left_comm, div_mul_cancel, mul_comm]

@[to_additive (attr := simp)]
theorem div_mul_div_cancel' (a b c : G) : a / b * (c / a) = c / b := by
  rw [mul_comm]; apply div_mul_div_cancel

@[to_additive (attr := simp)]
theorem mul_div_div_cancel (a b c : G) : a * b / (a / c) = b * c := by
  rw [← div_mul, mul_div_cancel_left]

@[to_additive (attr := simp)]
theorem div_div_div_cancel_left (a b c : G) : c / a / (c / b) = b / a := by
  rw [← inv_div b c, div_inv_eq_mul, mul_comm, div_mul_div_cancel]

@[to_additive]
theorem div_eq_div_iff_mul_eq_mul : a / b = c / d ↔ a * d = c * b := by
  rw [div_eq_iff_eq_mul, div_mul_eq_mul_div, eq_comm, div_eq_iff_eq_mul']
  simp only [mul_comm, eq_comm]

@[to_additive]
theorem mul_inv_eq_mul_inv_iff_mul_eq_mul : a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b := by
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]

@[to_additive]
theorem inv_mul_eq_inv_mul_iff_mul_eq_mul : b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b := by
  rw [← div_eq_inv_mul, ← div_eq_inv_mul, div_eq_div_iff_mul_eq_mul]

@[to_additive]
theorem div_eq_div_iff_div_eq_div : a / b = c / d ↔ a / c = b / d := by
  rw [div_eq_iff_eq_mul, div_mul_eq_mul_div, div_eq_iff_eq_mul', mul_div_assoc]

@[to_additive (attr := simp)]
lemma const_div_involutive (a : G) : Function.Involutive (a / ·) :=
  fun _ ↦ div_div_cancel ..

end CommGroup

section multiplicative

variable [Monoid β] (p r : α → α → Prop) [IsTotal α r] (f : α → α → β)

@[to_additive additive_of_symmetric_of_isTotal]
lemma multiplicative_of_symmetric_of_isTotal
    (hsymm : Symmetric p) (hf_swap : ∀ {a b}, p a b → f a b * f b a = 1)
    (hmul : ∀ {a b c}, r a b → r b c → p a b → p b c → p a c → f a c = f a b * f b c)
    {a b c : α} (pab : p a b) (pbc : p b c) (pac : p a c) : f a c = f a b * f b c := by
  have hmul' : ∀ {b c}, r b c → p a b → p b c → p a c → f a c = f a b * f b c := by
    intro b c rbc pab pbc pac
    obtain rab | rba := total_of r a b
    · exact hmul rab rbc pab pbc pac
    rw [← one_mul (f a c), ← hf_swap pab, mul_assoc]
    obtain rac | rca := total_of r a c
    · rw [hmul rba rac (hsymm pab) pac pbc]
    · rw [hmul rbc rca pbc (hsymm pac) (hsymm pab), mul_assoc, hf_swap (hsymm pac), mul_one]
  obtain rbc | rcb := total_of r b c
  · exact hmul' rbc pab pbc pac
  · rw [hmul' rcb pac (hsymm pbc) pab, mul_assoc, hf_swap (hsymm pbc), mul_one]

/-- If a binary function from a type equipped with a total relation `r` to a monoid is
  anti-symmetric (i.e. satisfies `f a b * f b a = 1`), in order to show it is multiplicative
  (i.e. satisfies `f a c = f a b * f b c`), we may assume `r a b` and `r b c` are satisfied.
  We allow restricting to a subset specified by a predicate `p`. -/
@[to_additive additive_of_isTotal /-- If a binary function from a type equipped with a total
  relation `r` to an additive monoid is anti-symmetric (i.e. satisfies `f a b + f b a = 0`), in
  order to show it is additive (i.e. satisfies `f a c = f a b + f b c`), we may assume `r a b` and
  `r b c` are satisfied. We allow restricting to a subset specified by a predicate `p`. -/]
theorem multiplicative_of_isTotal (p : α → Prop) (hswap : ∀ {a b}, p a → p b → f a b * f b a = 1)
    (hmul : ∀ {a b c}, r a b → r b c → p a → p b → p c → f a c = f a b * f b c) {a b c : α}
    (pa : p a) (pb : p b) (pc : p c) : f a c = f a b * f b c := by
  apply multiplicative_of_symmetric_of_isTotal (fun a b => p a ∧ p b) r f fun _ _ => And.symm
  · simp_rw [and_imp]; exact @hswap
  · exact fun rab rbc pab _pbc pac => hmul rab rbc pab.1 pab.2 pac.2
  exacts [⟨pa, pb⟩, ⟨pb, pc⟩, ⟨pa, pc⟩]

end multiplicative

/-- An auxiliary lemma that can be used to prove `⇑(f ^ n) = ⇑f^[n]`. -/
@[to_additive]
lemma hom_coe_pow {F : Type*} [Monoid F] (c : F → M → M) (h1 : c 1 = id)
    (hmul : ∀ f g, c (f * g) = c f ∘ c g) (f : F) : ∀ n, c (f ^ n) = (c f)^[n]
  | 0 => by
    rw [pow_zero, h1]
    rfl
  | n + 1 => by rw [pow_succ, iterate_succ, hmul, hom_coe_pow c h1 hmul f n]

/-!
# Instances for `grind`.
-/

open Lean

variable (α : Type*)

instance AddCommMonoid.toGrindNatModule [s : AddCommMonoid α] :
    Grind.NatModule α :=
  { s with
    nsmul := ⟨s.nsmul⟩
    zero_nsmul := AddMonoid.nsmul_zero
    add_one_nsmul n a := by change (n + 1) • a = n • a + a; rw [add_nsmul, one_nsmul] }

instance AddCommGroup.toGrindIntModule [s : AddCommGroup α] :
    Grind.IntModule α :=
  { s with
    nsmul := ⟨s.nsmul⟩
    zsmul := ⟨s.zsmul⟩
    zero_zsmul := SubNegMonoid.zsmul_zero'
    one_zsmul := one_zsmul
    add_zsmul n m a := add_zsmul a n m
    zsmul_natCast_eq_nsmul n a := by simp }

instance IsRightCancelAdd.toGrindAddRightCancel [AddSemigroup α] [IsRightCancelAdd α] :
    Grind.AddRightCancel α where
  add_right_cancel _ _ _ := add_right_cancel
