/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
import Mathlib.Algebra.Group.Defs

/-!
# Basic lemmas about semigroups, monoids, and groups

This file lists various basic lemmas about semigroups, monoids, and groups. Most proofs are
one-liners from the corresponding axioms. For the definitions of semigroups, monoids and groups, see
`Algebra/Group/Defs.lean`.
-/


open Function

universe u

variable {α β G : Type _}

section Semigroup

/-- Composing two multiplications on the left by `y` then `x`
is equal to a multiplication on the left by `x * y`.
-/
@[simp, to_additive "Composing two additions on the left by `y` then `x`
is equal to a addition on the left by `x + y`."]
theorem comp_mul_left [Semigroup α] (x y : α) : (x * ·) ∘ (y * ·) = (x * y * ·) := by
  ext z
  simp [mul_assoc]

/-- Composing two multiplications on the right by `y` and `x`
is equal to a multiplication on the right by `y * x`.
-/
@[simp, to_additive "Composing two additions on the right by `y` and `x`
is equal to a addition on the right by `y + x`."]
theorem comp_mul_right [Semigroup α] (x y : α) : (· * x) ∘ (· * y) = (· * (y * x)) := by
  ext z
  simp [mul_assoc]

end Semigroup

section MulOneClass

variable {M : Type u} [MulOneClass M]

@[to_additive]
theorem ite_mul_one {P : Prop} [Decidable P] {a b : M} :
    ite P (a * b) 1 = ite P a 1 * ite P b 1 := by
  by_cases h:P <;> simp [h]

@[to_additive]
theorem ite_one_mul {P : Prop} [Decidable P] {a b : M} :
    ite P 1 (a * b) = ite P 1 a * ite P 1 b := by
  by_cases h:P <;> simp [h]

@[to_additive]
theorem eq_one_iff_eq_one_of_mul_eq_one {a b : M} (h : a * b = 1) : a = 1 ↔ b = 1 := by
  constructor <;> (rintro rfl; simpa using h)

@[to_additive]
theorem one_mul_eq_id : (· * ·) (1 : M) = id :=
  funext one_mul

@[to_additive]
theorem mul_one_eq_id : (· * (1 : M)) = id :=
  funext mul_one

end MulOneClass

section CommSemigroup

variable [CommSemigroup G]

@[to_additive]
theorem mul_left_comm : ∀ a b c : G, a * (b * c) = b * (a * c) :=
  left_comm Mul.mul mul_comm mul_assoc

@[to_additive]
theorem mul_right_comm : ∀ a b c : G, a * b * c = a * c * b :=
  right_comm Mul.mul mul_comm mul_assoc

@[to_additive]
theorem mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a * c * (b * d) :=
  by simp only [mul_left_comm, mul_assoc]

@[to_additive]
theorem mul_rotate (a b c : G) : a * b * c = b * c * a :=
  by simp only [mul_left_comm, mul_comm]

@[to_additive]
theorem mul_rotate' (a b c : G) : a * (b * c) = b * (c * a) :=
  by simp only [mul_left_comm, mul_comm]

end CommSemigroup

attribute [local simp] mul_assoc sub_eq_add_neg

section CommMonoid

variable {M : Type u} [CommMonoid M] {x y z : M}

@[to_additive]
theorem inv_unique (hy : x * y = 1) (hz : x * z = 1) : y = z :=
  left_inv_eq_right_inv (Trans.trans (mul_comm _ _) hy) hz

end CommMonoid

section LeftCancelMonoid

variable {M : Type u} [LeftCancelMonoid M] {a b : M}

@[simp, to_additive]
theorem mul_right_eq_self : a * b = a ↔ b = 1 := calc
  a * b = a ↔ a * b = a * 1 := by rw [mul_one]
  _ ↔ b = 1 := mul_left_cancel_iff

@[simp, to_additive]
theorem self_eq_mul_right : a = a * b ↔ b = 1 :=
  eq_comm.trans mul_right_eq_self

end LeftCancelMonoid

section RightCancelMonoid

variable {M : Type u} [RightCancelMonoid M] {a b : M}

@[simp, to_additive]
theorem mul_left_eq_self : a * b = b ↔ a = 1 := calc
  a * b = b ↔ a * b = 1 * b := by rw [one_mul]
  _ ↔ a = 1 := mul_right_cancel_iff

@[simp, to_additive]
theorem self_eq_mul_left : b = a * b ↔ a = 1 :=
  eq_comm.trans mul_left_eq_self

end RightCancelMonoid

section HasInvolutiveInv

variable [HasInvolutiveInv G] {a b : G}

@[simp, to_additive]
theorem inv_involutive : Function.Involutive (Inv.inv : G → G) :=
  inv_inv

@[simp, to_additive]
theorem inv_surjective : Function.Surjective (Inv.inv : G → G) :=
  inv_involutive.surjective

@[to_additive]
theorem inv_injective : Function.Injective (Inv.inv : G → G) :=
  inv_involutive.injective

@[simp, to_additive]
theorem inv_inj {a b : G} : a⁻¹ = b⁻¹ ↔ a = b :=
  inv_injective.eq_iff

@[to_additive]
theorem eq_inv_of_eq_inv (h : a = b⁻¹) : b = a⁻¹ := by simp [h]

@[to_additive]
theorem eq_inv_iff_eq_inv : a = b⁻¹ ↔ b = a⁻¹ :=
  ⟨eq_inv_of_eq_inv, eq_inv_of_eq_inv⟩

@[to_additive]
theorem inv_eq_iff_inv_eq : a⁻¹ = b ↔ b⁻¹ = a :=
  eq_comm.trans <| eq_inv_iff_eq_inv.trans eq_comm

variable (G)

@[to_additive]
theorem inv_comp_inv : Inv.inv ∘ Inv.inv = @id G :=
  inv_involutive.comp_self

@[to_additive]
theorem left_inverse_inv : LeftInverse (fun a : G => a⁻¹) fun a => a⁻¹ :=
  inv_inv

@[to_additive]
theorem right_inverse_inv : LeftInverse (fun a : G => a⁻¹) fun a => a⁻¹ :=
  inv_inv

end HasInvolutiveInv

section DivInvMonoid

variable [DivInvMonoid G] {a b c : G}

@[to_additive, field_simps] -- The attributes are out of order on purpose
theorem inv_eq_one_div (x : G) : x⁻¹ = 1 / x := by rw [div_eq_mul_inv, one_mul]

@[to_additive]
theorem mul_one_div (x y : G) : x * (1 / y) = x / y :=
  by rw [div_eq_mul_inv, one_mul, div_eq_mul_inv]

@[to_additive]
theorem mul_div_assoc (a b c : G) : a * b / c = a * (b / c) :=
  by rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc _ _ _]

@[to_additive, field_simps] -- The attributes are out of order on purpose
theorem mul_div_assoc' (a b c : G) : a * (b / c) = a * b / c :=
  (mul_div_assoc _ _ _).symm

@[simp, to_additive]
theorem one_div (a : G) : 1 / a = a⁻¹ :=
  (inv_eq_one_div a).symm

@[to_additive]
theorem mul_div (a b c : G) : a * (b / c) = a * b / c := by simp only [mul_assoc, div_eq_mul_inv]

@[to_additive]
theorem div_eq_mul_one_div (a b : G) : a / b = a * (1 / b) := by rw [div_eq_mul_inv, one_div]

end DivInvMonoid

section DivInvOneMonoid

variable [DivInvOneMonoid G]

@[simp, to_additive]
theorem div_one (a : G) : a / 1 = a := by simp [div_eq_mul_inv]

@[to_additive]
theorem one_div_one : (1 : G) / 1 = 1 :=
  div_one _

end DivInvOneMonoid

section DivisionMonoid

variable [DivisionMonoid α] {a b c : α}

attribute [local simp] mul_assoc div_eq_mul_inv

@[to_additive]
theorem inv_eq_of_mul_eq_one_left (h : a * b = 1) : b⁻¹ = a :=
  by rw [← inv_eq_of_mul_eq_one_right h, inv_inv]

@[to_additive]
theorem eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹ :=
  (inv_eq_of_mul_eq_one_left h).symm

@[to_additive]
theorem eq_inv_of_mul_eq_one_right (h : a * b = 1) : b = a⁻¹ :=
  (inv_eq_of_mul_eq_one_right h).symm

@[to_additive]
theorem eq_one_div_of_mul_eq_one_left (h : b * a = 1) : b = 1 / a :=
  by rw [eq_inv_of_mul_eq_one_left h, one_div]

@[to_additive]
theorem eq_one_div_of_mul_eq_one_right (h : a * b = 1) : b = 1 / a :=
  by rw [eq_inv_of_mul_eq_one_right h, one_div]

@[to_additive]
theorem eq_of_div_eq_one (h : a / b = 1) : a = b :=
  inv_injective <| inv_eq_of_mul_eq_one_right <| by rwa [← div_eq_mul_inv]

@[to_additive]
theorem div_ne_one_of_ne : a ≠ b → a / b ≠ 1 :=
  mt eq_of_div_eq_one

variable (a b c)

@[to_additive]
theorem one_div_mul_one_div_rev : 1 / a * (1 / b) = 1 / (b * a) := by simp

@[to_additive]
theorem inv_div_left : a⁻¹ / b = (b * a)⁻¹ := by simp

@[simp, to_additive]
theorem inv_div : (a / b)⁻¹ = b / a := by simp

@[to_additive]
theorem one_div_div : 1 / (a / b) = b / a := by simp

@[to_additive]
theorem one_div_one_div : 1 / (1 / a) = a := by simp

@[to_additive SubtractionMonoid.toSubNegZeroMonoid]
instance (priority := 100) DivisionMonoid.toDivInvOneMonoid : DivInvOneMonoid α :=
  { DivisionMonoid.toDivInvMonoid with
    inv_one := by simpa only [one_div, inv_inv] using (inv_div (1 : α) 1).symm }

-- FIXME this isn't being copied by `to_additive`
-- FIXME how to set priority?
attribute [instance] SubtractionMonoid.toSubNegZeroMonoid

variable {a b c}

@[simp, to_additive]
theorem inv_eq_one : a⁻¹ = 1 ↔ a = 1 :=
  inv_injective.eq_iff' inv_one

@[simp, to_additive]
theorem one_eq_inv : 1 = a⁻¹ ↔ a = 1 :=
  eq_comm.trans inv_eq_one

@[to_additive]
theorem inv_ne_one : a⁻¹ ≠ 1 ↔ a ≠ 1 :=
  inv_eq_one.not

@[to_additive]
theorem eq_of_one_div_eq_one_div (h : 1 / a = 1 / b) : a = b :=
  by rw [← one_div_one_div a, h, one_div_one_div]

variable (a b c)

@[to_additive, field_simps] -- The attributes are out of order on purpose
theorem div_div_eq_mul_div : a / (b / c) = a * c / b := by simp

@[simp, to_additive]
theorem div_inv_eq_mul : a / b⁻¹ = a * b := by simp

@[to_additive]
theorem div_mul_eq_div_div_swap : a / (b * c) = a / c / b :=
  by simp only [mul_assoc, mul_inv_rev, div_eq_mul_inv]

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

end DivisionCommMonoid

section Group

variable [Group G] {a b c d : G}

@[simp, to_additive]
theorem div_eq_inv_self : a / b = b⁻¹ ↔ a = 1 := by rw [div_eq_mul_inv, mul_left_eq_self]

@[to_additive]
theorem mul_left_surjective (a : G) : Function.Surjective ((· * ·) a) :=
  fun x => ⟨a⁻¹ * x, mul_inv_cancel_left a x⟩

@[to_additive]
theorem mul_right_surjective (a : G) : Function.Surjective fun x => x * a := fun x =>
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
  ⟨eq_inv_of_mul_eq_one_left, fun h => by rw [h, mul_left_inv]⟩

@[to_additive]
theorem mul_eq_one_iff_inv_eq : a * b = 1 ↔ a⁻¹ = b :=
  by rw [mul_eq_one_iff_eq_inv, eq_inv_iff_eq_inv, eq_comm]

@[to_additive]
theorem eq_inv_iff_mul_eq_one : a = b⁻¹ ↔ a * b = 1 :=
  mul_eq_one_iff_eq_inv.symm

@[to_additive]
theorem inv_eq_iff_mul_eq_one : a⁻¹ = b ↔ a * b = 1 :=
  mul_eq_one_iff_inv_eq.symm

@[to_additive]
theorem eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b :=
  ⟨fun h => by rw [h, inv_mul_cancel_right], fun h => by rw [← h, mul_inv_cancel_right]⟩

@[to_additive]
theorem eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c :=
  ⟨fun h => by rw [h, mul_inv_cancel_left], fun h => by rw [← h, inv_mul_cancel_left]⟩

@[to_additive]
theorem inv_mul_eq_iff_eq_mul : a⁻¹ * b = c ↔ b = a * c :=
  ⟨fun h => by rw [← h, mul_inv_cancel_left], fun h => by rw [h, inv_mul_cancel_left]⟩

@[to_additive]
theorem mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b :=
  ⟨fun h => by rw [← h, inv_mul_cancel_right], fun h => by rw [h, mul_inv_cancel_right]⟩

@[to_additive]
theorem mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b := by rw [mul_eq_one_iff_eq_inv, inv_inv]

@[to_additive]
theorem inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b := by rw [mul_eq_one_iff_eq_inv, inv_inj]

@[to_additive]
theorem div_left_injective : Function.Injective fun a => a / b := by
  -- FIXME this could be by `simpa`, but it fails. This is probably a bug in `simpa`.
  simp only [div_eq_mul_inv]
  exact fun a a' h => mul_left_injective b⁻¹ h

@[to_additive]
theorem div_right_injective : Function.Injective fun a => b / a := by
  -- FIXME see above
  simp only [div_eq_mul_inv]
  exact fun a a' h => inv_injective (mul_right_injective b h)

@[simp, to_additive sub_add_cancel]
theorem div_mul_cancel' (a b : G) : a / b * b = a :=
  by rw [div_eq_mul_inv, inv_mul_cancel_right a b]

@[simp, to_additive sub_self]
theorem div_self' (a : G) : a / a = 1 := by rw [div_eq_mul_inv, mul_right_inv a]

@[simp, to_additive add_sub_cancel]
theorem mul_div_cancel'' (a b : G) : a * b / b = a :=
  by rw [div_eq_mul_inv, mul_inv_cancel_right a b]

@[simp, to_additive]
theorem mul_div_mul_right_eq_div (a b c : G) : a * c / (b * c) = a / b := by
  rw [div_mul_eq_div_div_swap] <;> simp only [mul_left_inj, eq_self_iff_true, mul_div_cancel'']

@[to_additive eq_sub_of_add_eq]
theorem eq_div_of_mul_eq' (h : a * c = b) : a = b / c := by simp [← h]

@[to_additive sub_eq_of_eq_add]
theorem div_eq_of_eq_mul'' (h : a = c * b) : a / b = c := by simp [h]

@[to_additive]
theorem eq_mul_of_div_eq (h : a / c = b) : a = b * c := by simp [← h]

@[to_additive]
theorem mul_eq_of_eq_div (h : a = c / b) : a * b = c := by simp [h]

@[simp, to_additive]
theorem div_right_inj : a / b = a / c ↔ b = c :=
  div_right_injective.eq_iff

@[simp, to_additive]
theorem div_left_inj : b / a = c / a ↔ b = c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_left_inj _

@[simp, to_additive sub_add_sub_cancel]
theorem div_mul_div_cancel' (a b c : G) : a / b * (b / c) = a / c :=
  by rw [← mul_div_assoc, div_mul_cancel']

@[simp, to_additive sub_sub_sub_cancel_right]
theorem div_div_div_cancel_right' (a b c : G) : a / c / (b / c) = a / b := by
  rw [← inv_div c b, div_inv_eq_mul, div_mul_div_cancel']

@[to_additive]
theorem div_eq_one : a / b = 1 ↔ a = b :=
  ⟨eq_of_div_eq_one, fun h => by rw [h, div_self']⟩

alias div_eq_one ↔ _ div_eq_one_of_eq

alias sub_eq_zero ↔ _ sub_eq_zero_of_eq

@[to_additive]
theorem div_ne_one : a / b ≠ 1 ↔ a ≠ b :=
  not_congr div_eq_one

@[simp, to_additive]
theorem div_eq_self : a / b = a ↔ b = 1 := by rw [div_eq_mul_inv, mul_right_eq_self, inv_eq_one]

@[to_additive eq_sub_iff_add_eq]
theorem eq_div_iff_mul_eq' : a = b / c ↔ a * c = b := by rw [div_eq_mul_inv, eq_mul_inv_iff_mul_eq]

@[to_additive]
theorem div_eq_iff_eq_mul : a / b = c ↔ a = c * b := by rw [div_eq_mul_inv, mul_inv_eq_iff_eq_mul]

@[to_additive]
theorem eq_iff_eq_of_div_eq_div (H : a / b = c / d) : a = b ↔ c = d :=
  by rw [← div_eq_one, H, div_eq_one]

@[to_additive]
theorem left_inverse_div_mul_left (c : G) : Function.LeftInverse (fun x => x / c) fun x => x * c :=
  fun x => mul_div_cancel'' x c

@[to_additive]
theorem left_inverse_mul_left_div (c : G) : Function.LeftInverse (fun x => x * c) fun x => x / c :=
  fun x => div_mul_cancel' x c

@[to_additive]
theorem left_inverse_mul_right_inv_mul (c : G) :
    Function.LeftInverse (fun x => c * x) fun x => c⁻¹ * x :=
  fun x => mul_inv_cancel_left c x

@[to_additive]
theorem left_inverse_inv_mul_mul_right (c : G) :
    Function.LeftInverse (fun x => c⁻¹ * x) fun x => c * x :=
  fun x => inv_mul_cancel_left c x

-- TODO @[to_additive]
theorem exists_npow_eq_one_of_zpow_eq_one {n : ℤ} (hn : n ≠ 0) {x : G} (h : x ^ n = 1) :
    ∃ n : ℕ, 0 < n ∧ x ^ n = 1 := by
  cases' n with n n
  · rw [zpow_of_nat] at h
    refine' ⟨n, Nat.pos_of_ne_zero fun n0 => hn ?_, h⟩
    rw [n0]
    rfl
  · rw [zpow_neg_succ_of_nat, inv_eq_one] at h
    refine' ⟨n + 1, n.succ_pos, h⟩

end Group

section CommGroup

variable [CommGroup G] {a b c d : G}

attribute [local simp] mul_assoc mul_comm mul_left_comm div_eq_mul_inv

@[to_additive]
theorem div_eq_of_eq_mul' {a b c : G} (h : a = b * c) : a / b = c := by
  rw [h, div_eq_mul_inv, mul_comm, inv_mul_cancel_left]

@[simp, to_additive]
theorem mul_div_mul_left_eq_div (a b c : G) : c * a / (c * b) = a / b := by
  rw [div_eq_mul_inv, mul_inv_rev, mul_comm b⁻¹ c⁻¹, mul_comm c a, mul_assoc, ←mul_assoc c,
    mul_right_inv, one_mul, div_eq_mul_inv]

@[to_additive eq_sub_of_add_eq']
theorem eq_div_of_mul_eq'' (h : c * a = b) : a = b / c := by simp [h.symm]

@[to_additive]
theorem eq_mul_of_div_eq' (h : a / b = c) : a = b * c := by simp [h.symm]

@[to_additive]
theorem mul_eq_of_eq_div' (h : b = c / a) : a * b = c := by
  simp [h]
  rw [mul_comm c, mul_inv_cancel_left]

@[to_additive sub_sub_self]
theorem div_div_self' (a b : G) : a / (a / b) = b := by simpa using mul_inv_cancel_left a b

@[to_additive]
theorem div_eq_div_mul_div (a b c : G) : a / b = c / b * (a / c) := by simp [mul_left_comm c]

@[simp, to_additive]
theorem div_div_cancel (a b : G) : a / (a / b) = b :=
  div_div_self' a b

@[simp, to_additive]
theorem div_div_cancel_left (a b : G) : a / b / a = b⁻¹ := by simp

@[to_additive eq_sub_iff_add_eq']
theorem eq_div_iff_mul_eq'' : a = b / c ↔ c * a = b := by rw [eq_div_iff_mul_eq', mul_comm]

@[to_additive]
theorem div_eq_iff_eq_mul' : a / b = c ↔ a = b * c := by rw [div_eq_iff_eq_mul, mul_comm]

@[simp, to_additive add_sub_cancel']
theorem mul_div_cancel''' (a b : G) : a * b / a = b := by rw [div_eq_inv_mul, inv_mul_cancel_left]

@[simp, to_additive]
theorem mul_div_cancel'_right (a b : G) : a * (b / a) = b :=
  by rw [← mul_div_assoc, mul_div_cancel''']

@[simp, to_additive sub_add_cancel']
theorem div_mul_cancel'' (a b : G) : a / (a * b) = b⁻¹ := by rw [← inv_div, mul_div_cancel''']

-- This lemma is in the `simp` set under the name `mul_inv_cancel_comm_assoc`,
-- along with the additive version `add_neg_cancel_comm_assoc`,
-- defined  in `algebra/group/commute`
@[to_additive]
theorem mul_mul_inv_cancel'_right (a b : G) : a * (b * a⁻¹) = b :=
  by rw [← div_eq_mul_inv, mul_div_cancel'_right a b]

@[simp, to_additive]
theorem mul_mul_div_cancel (a b c : G) : a * c * (b / c) = a * b :=
  by rw [mul_assoc, mul_div_cancel'_right]

@[simp, to_additive]
theorem div_mul_mul_cancel (a b c : G) : a / c * (b * c) = a * b :=
  by rw [mul_left_comm, div_mul_cancel', mul_comm]

@[simp, to_additive sub_add_sub_cancel']
theorem div_mul_div_cancel'' (a b c : G) : a / b * (c / a) = c / b :=
  by rw [mul_comm] <;> apply div_mul_div_cancel'

@[simp, to_additive]
theorem mul_div_div_cancel (a b c : G) : a * b / (a / c) = b * c :=
  by rw [← div_mul, mul_div_cancel''']

@[simp, to_additive]
theorem div_div_div_cancel_left (a b c : G) : c / a / (c / b) = b / a := by
  rw [← inv_div b c, div_inv_eq_mul, mul_comm, div_mul_div_cancel']

@[to_additive]
theorem div_eq_div_iff_mul_eq_mul : a / b = c / d ↔ a * d = c * b := by
  rw [div_eq_iff_eq_mul, div_mul_eq_mul_div, eq_comm, div_eq_iff_eq_mul']
  simp only [mul_comm, eq_comm]
  rfl

@[to_additive]
theorem div_eq_div_iff_div_eq_div : a / b = c / d ↔ a / c = b / d := by
  rw [div_eq_iff_eq_mul, div_mul_eq_mul_div, div_eq_iff_eq_mul', mul_div_assoc]

end CommGroup
