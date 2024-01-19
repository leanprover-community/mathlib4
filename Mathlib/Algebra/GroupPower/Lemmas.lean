/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import Mathlib.Data.Int.Cast.Lemmas

#align_import algebra.group_power.lemmas from "leanprover-community/mathlib"@"a07d750983b94c530ab69a726862c2ab6802b38c"

/-!
# Lemmas about power operations on monoids and groups

This file contains lemmas about `Monoid.pow`, `Group.pow`, `nsmul`, and `zsmul`
which require additional imports besides those available in `Mathlib.Algebra.GroupPower.Basic`.
-/

open Int

universe u v w x y z u₁ u₂

variable {α : Type*} {M : Type u} {N : Type v} {G : Type w} {H : Type x} {A : Type y} {B : Type z}
  {R : Type u₁} {S : Type u₂}

section bit0_bit1

set_option linter.deprecated false

-- The next four lemmas allow us to replace multiplication by a numeral with a `zsmul` expression.
-- They are used by the `noncomm_ring` tactic, to normalise expressions before passing to `abel`.
theorem bit0_mul [NonUnitalNonAssocRing R] {n r : R} : bit0 n * r = (2 : ℤ) • (n * r) := by
  dsimp [bit0]
  rw [add_mul, ← one_add_one_eq_two, add_zsmul, one_zsmul]
#align bit0_mul bit0_mul

theorem mul_bit0 [NonUnitalNonAssocRing R] {n r : R} : r * bit0 n = (2 : ℤ) • (r * n) := by
  dsimp [bit0]
  rw [mul_add, ← one_add_one_eq_two, add_zsmul, one_zsmul]
#align mul_bit0 mul_bit0

theorem bit1_mul [NonAssocRing R] {n r : R} : bit1 n * r = (2 : ℤ) • (n * r) + r := by
  dsimp [bit1]
  rw [add_mul, bit0_mul, one_mul]
#align bit1_mul bit1_mul

theorem mul_bit1 [NonAssocRing R] {n r : R} : r * bit1 n = (2 : ℤ) • (r * n) + r := by
  dsimp [bit1]
  rw [mul_add, mul_bit0, mul_one]
#align mul_bit1 mul_bit1

end bit0_bit1

/-- Note this holds in marginally more generality than `Int.cast_mul` -/
theorem Int.cast_mul_eq_zsmul_cast [AddCommGroupWithOne α] :
    ∀ m n, ((m * n : ℤ) : α) = m • (n : α) :=
  fun m =>
  Int.inductionOn' m 0 (by simp) (fun k _ ih n => by simp [add_mul, add_zsmul, ih]) fun k _ ih n =>
    by simp [sub_mul, sub_zsmul, ih, ← sub_eq_add_neg]
#align int.cast_mul_eq_zsmul_cast Int.cast_mul_eq_zsmul_cast

section OrderedSemiring

variable [OrderedSemiring R] {a : R}

theorem pow_le_pow_of_le_one_aux (h : 0 ≤ a) (ha : a ≤ 1) (i : ℕ) :
    ∀ k : ℕ, a ^ (i + k) ≤ a ^ i
  | 0 => by simp
  | k + 1 => by
    rw [← add_assoc, ← one_mul (a ^ i), pow_succ]
    exact mul_le_mul ha (pow_le_pow_of_le_one_aux h ha _ _) (pow_nonneg h _) zero_le_one
-- Porting note: no #align because private in Lean 3

theorem pow_le_pow_of_le_one (h : 0 ≤ a) (ha : a ≤ 1) {i j : ℕ} (hij : i ≤ j) : a ^ j ≤ a ^ i := by
  let ⟨k, hk⟩ := Nat.exists_eq_add_of_le hij
  rw [hk]; exact pow_le_pow_of_le_one_aux h ha _ _
#align pow_le_pow_of_le_one pow_le_pow_of_le_one

theorem pow_le_of_le_one (h₀ : 0 ≤ a) (h₁ : a ≤ 1) {n : ℕ} (hn : n ≠ 0) : a ^ n ≤ a :=
  (pow_one a).subst (pow_le_pow_of_le_one h₀ h₁ (Nat.pos_of_ne_zero hn))
#align pow_le_of_le_one pow_le_of_le_one

theorem sq_le (h₀ : 0 ≤ a) (h₁ : a ≤ 1) : a ^ 2 ≤ a :=
  pow_le_of_le_one h₀ h₁ two_ne_zero
#align sq_le sq_le

end OrderedSemiring

section LinearOrderedSemiring

variable [LinearOrderedSemiring R]

theorem sign_cases_of_C_mul_pow_nonneg {C r : R} (h : ∀ n : ℕ, 0 ≤ C * r ^ n) :
    C = 0 ∨ 0 < C ∧ 0 ≤ r := by
  have : 0 ≤ C := by simpa only [pow_zero, mul_one] using h 0
  refine' this.eq_or_lt.elim (fun h => Or.inl h.symm) fun hC => Or.inr ⟨hC, _⟩
  refine' nonneg_of_mul_nonneg_right _ hC
  simpa only [pow_one] using h 1
set_option linter.uppercaseLean3 false in
#align sign_cases_of_C_mul_pow_nonneg sign_cases_of_C_mul_pow_nonneg

end LinearOrderedSemiring

namespace Int

lemma natAbs_sq (x : ℤ) : (x.natAbs : ℤ) ^ 2 = x ^ 2 := by rw [sq, Int.natAbs_mul_self', sq]
#align int.nat_abs_sq Int.natAbs_sq

alias natAbs_pow_two := natAbs_sq
#align int.nat_abs_pow_two Int.natAbs_pow_two

theorem natAbs_le_self_sq (a : ℤ) : (Int.natAbs a : ℤ) ≤ a ^ 2 := by
  rw [← Int.natAbs_sq a, sq]
  norm_cast
  apply Nat.le_mul_self
#align int.abs_le_self_sq Int.natAbs_le_self_sq

alias natAbs_le_self_pow_two := natAbs_le_self_sq

theorem le_self_sq (b : ℤ) : b ≤ b ^ 2 :=
  le_trans le_natAbs (natAbs_le_self_sq _)
#align int.le_self_sq Int.le_self_sq

alias le_self_pow_two := le_self_sq
#align int.le_self_pow_two Int.le_self_pow_two

end Int

variable (M G A)

/-- Additive homomorphisms from `ℤ` are defined by the image of `1`. -/
def zmultiplesHom [AddGroup A] :
    A ≃ (ℤ →+ A) where
  toFun x :=
  { toFun := fun n => n • x
    map_zero' := zero_zsmul x
    map_add' := fun _ _ => add_zsmul _ _ _ }
  invFun f := f 1
  left_inv := one_zsmul
  right_inv f := AddMonoidHom.ext_int <| one_zsmul (f 1)
#align zmultiples_hom zmultiplesHom

/-- Monoid homomorphisms from `Multiplicative ℤ` are defined by the image
of `Multiplicative.ofAdd 1`. -/
def zpowersHom [Group G] : G ≃ (Multiplicative ℤ →* G) :=
  Additive.ofMul.trans <| (zmultiplesHom _).trans <| AddMonoidHom.toMultiplicative''
#align zpowers_hom zpowersHom

attribute [to_additive existing zmultiplesHom] zpowersHom

variable {M G A}

theorem zpowersHom_apply [Group G] (x : G) (n : Multiplicative ℤ) :
    zpowersHom G x n = x ^ (Multiplicative.toAdd n) :=
  rfl
#align zpowers_hom_apply zpowersHom_apply

theorem zpowersHom_symm_apply [Group G] (f : Multiplicative ℤ →* G) :
    (zpowersHom G).symm f = f (Multiplicative.ofAdd 1) :=
  rfl
#align zpowers_hom_symm_apply zpowersHom_symm_apply

-- todo: can `to_additive` generate the following lemmas automatically?

theorem zmultiplesHom_apply [AddGroup A] (x : A) (n : ℤ) : zmultiplesHom A x n = n • x :=
  rfl
#align zmultiples_hom_apply zmultiplesHom_apply

attribute [to_additive existing (attr := simp) zmultiplesHom_apply] zpowersHom_apply

theorem zmultiplesHom_symm_apply [AddGroup A] (f : ℤ →+ A) : (zmultiplesHom A).symm f = f 1 :=
  rfl
#align zmultiples_hom_symm_apply zmultiplesHom_symm_apply

attribute [to_additive existing (attr := simp) zmultiplesHom_symm_apply] zpowersHom_symm_apply

theorem MonoidHom.apply_mint [Group M] (f : Multiplicative ℤ →* M) (n : Multiplicative ℤ) :
    f n = f (Multiplicative.ofAdd 1) ^ (Multiplicative.toAdd n) := by
  rw [← zpowersHom_symm_apply, ← zpowersHom_apply, Equiv.apply_symm_apply]
#align monoid_hom.apply_mint MonoidHom.apply_mint

/-! `MonoidHom.ext_mint` is defined in `Data.Int.Cast` -/

/-! `AddMonoidHom.ext_nat` is defined in `Data.Nat.Cast` -/

theorem AddMonoidHom.apply_int [AddGroup M] (f : ℤ →+ M) (n : ℤ) : f n = n • f 1 := by
  rw [← zmultiplesHom_symm_apply, ← zmultiplesHom_apply, Equiv.apply_symm_apply]
#align add_monoid_hom.apply_int AddMonoidHom.apply_int

/-! `AddMonoidHom.ext_int` is defined in `Data.Int.Cast` -/

variable (M G A)

/-- If `M` is commutative, `zpowersHom` is a multiplicative equivalence. -/
def zpowersMulHom [CommGroup G] : G ≃* (Multiplicative ℤ →* G) :=
  { zpowersHom G with map_mul' := fun a b => MonoidHom.ext fun n => by simp [mul_zpow] }
#align zpowers_mul_hom zpowersMulHom

/-- If `M` is commutative, `zmultiplesHom` is an additive equivalence. -/
def zmultiplesAddHom [AddCommGroup A] : A ≃+ (ℤ →+ A) :=
  { zmultiplesHom A with map_add' := fun a b => AddMonoidHom.ext fun n => by simp [zsmul_add] }
#align zmultiples_add_hom zmultiplesAddHom

variable {M G A}

@[simp]
theorem zpowersMulHom_apply [CommGroup G] (x : G) (n : Multiplicative ℤ) :
    zpowersMulHom G x n = x ^ (Multiplicative.toAdd n) :=
  rfl
#align zpowers_mul_hom_apply zpowersMulHom_apply

@[simp]
theorem zpowersMulHom_symm_apply [CommGroup G] (f : Multiplicative ℤ →* G) :
    (zpowersMulHom G).symm f = f (Multiplicative.ofAdd 1) :=
  rfl
#align zpowers_mul_hom_symm_apply zpowersMulHom_symm_apply

@[simp]
theorem zmultiplesAddHom_apply [AddCommGroup A] (x : A) (n : ℤ) :
    zmultiplesAddHom A x n = n • x :=
  rfl
#align zmultiples_add_hom_apply zmultiplesAddHom_apply

@[simp]
theorem zmultiplesAddHom_symm_apply [AddCommGroup A] (f : ℤ →+ A) :
    (zmultiplesAddHom A).symm f = f 1 :=
  rfl
#align zmultiples_add_hom_symm_apply zmultiplesAddHom_symm_apply
@[simp] theorem pow_eq {m : ℤ} {n : ℕ} : m.pow n = m ^ n := by simp
