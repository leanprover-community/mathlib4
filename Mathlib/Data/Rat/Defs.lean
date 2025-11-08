/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Rat.Init
import Mathlib.Order.Basic
import Mathlib.Tactic.Common
import Mathlib.Data.Nat.Basic

/-!
# Basics for the Rational Numbers

## Summary

We define the integral domain structure on `ℚ` and prove basic lemmas about it.
The definition of the field structure on `ℚ` will be done in `Mathlib/Algebra/Field/Rat.lean`
once the `Field` class has been defined.

## Main Definitions

- `Rat.divInt n d` constructs a rational number `q = n / d` from `n d : ℤ`.

## Notation

- `/.` is infix notation for `Rat.divInt`.

-/

-- TODO: If `Inv` was defined earlier than `Algebra.Group.Defs`, we could have
-- assert_not_exists Monoid
assert_not_exists MonoidWithZero Lattice PNat Nat.gcd_greatest

open Function

namespace Rat
variable {q : ℚ}

theorem pos (a : ℚ) : 0 < a.den := Nat.pos_of_ne_zero a.den_nz

lemma mk'_num_den (q : ℚ) : mk' q.num q.den q.den_nz q.reduced = q := rfl

@[simp]
theorem ofInt_eq_cast (n : ℤ) : ofInt n = Int.cast n :=
  rfl

lemma intCast_injective : Injective (Int.cast : ℤ → ℚ) := fun _ _ ↦ congr_arg num
lemma natCast_injective : Injective (Nat.cast : ℕ → ℚ) :=
  intCast_injective.comp fun _ _ ↦ Int.natCast_inj.1

@[deprecated (since := "2025-10-24")] alias intCast_eq_zero := intCast_eq_zero_iff
@[deprecated (since := "2025-10-24")] alias natCast_eq_zero := natCast_eq_zero_iff

@[simp high, norm_cast] lemma intCast_eq_one_iff {n : ℤ} : (n : ℚ) = 1 ↔ n = 1 := intCast_inj

@[deprecated (since := "2025-10-24")] alias intCast_eq_one := intCast_eq_one_iff

@[simp high, norm_cast] lemma natCast_eq_one_iff {n : ℕ} : (n : ℚ) = 1 ↔ n = 1 := natCast_inj

@[deprecated (since := "2025-10-24")] alias natCast_eq_one := natCast_eq_one_iff

lemma mkRat_eq_divInt (n d) : mkRat n d = n /. d := rfl

@[simp] lemma mk'_zero (d) (h : d ≠ 0) (w) : mk' 0 d h w = 0 := by congr; simp_all

lemma num_ne_zero {q : ℚ} : q.num ≠ 0 ↔ q ≠ 0 := num_eq_zero.not

@[simp] lemma den_ne_zero (q : ℚ) : q.den ≠ 0 := q.den_pos.ne'

@[simp]
theorem divInt_eq_zero {a b : ℤ} (b0 : b ≠ 0) : a /. b = 0 ↔ a = 0 := by
  rw [← zero_divInt b, divInt_eq_divInt_iff b0 b0, Int.zero_mul, Int.mul_eq_zero, or_iff_left b0]

theorem divInt_ne_zero {a b : ℤ} (b0 : b ≠ 0) : a /. b ≠ 0 ↔ a ≠ 0 :=
  (divInt_eq_zero b0).not

-- TODO: Rename `mkRat_num_den` in Lean core
alias mkRat_num_den' := mkRat_self

theorem intCast_eq_divInt (z : ℤ) : (z : ℚ) = z /. 1 := mk'_eq_divInt

theorem lift_binop_eq (f : ℚ → ℚ → ℚ) (f₁ : ℤ → ℤ → ℤ → ℤ → ℤ) (f₂ : ℤ → ℤ → ℤ → ℤ → ℤ)
    (fv :
      ∀ {n₁ d₁ h₁ c₁ n₂ d₂ h₂ c₂},
        f ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ = f₁ n₁ d₁ n₂ d₂ /. f₂ n₁ d₁ n₂ d₂)
    (f0 : ∀ {n₁ d₁ n₂ d₂}, d₁ ≠ 0 → d₂ ≠ 0 → f₂ n₁ d₁ n₂ d₂ ≠ 0) (a b c d : ℤ)
    (b0 : b ≠ 0) (d0 : d ≠ 0)
    (H :
      ∀ {n₁ d₁ n₂ d₂}, a * d₁ = n₁ * b → c * d₂ = n₂ * d →
        f₁ n₁ d₁ n₂ d₂ * f₂ a b c d = f₁ a b c d * f₂ n₁ d₁ n₂ d₂) :
    f (a /. b) (c /. d) = f₁ a b c d /. f₂ a b c d := by
  generalize ha : a /. b = x; obtain ⟨n₁, d₁, h₁, c₁⟩ := x; rw [mk'_eq_divInt] at ha
  generalize hc : c /. d = x; obtain ⟨n₂, d₂, h₂, c₂⟩ := x; rw [mk'_eq_divInt] at hc
  rw [fv]
  have d₁0 := Int.ofNat_ne_zero.2 h₁
  have d₂0 := Int.ofNat_ne_zero.2 h₂
  exact (divInt_eq_divInt_iff (f0 d₁0 d₂0) (f0 b0 d0)).2
    (H ((divInt_eq_divInt_iff b0 d₁0).1 ha) ((divInt_eq_divInt_iff d0 d₂0).1 hc))

attribute [simp] divInt_add_divInt

attribute [simp] neg_divInt

lemma neg_def (q : ℚ) : -q = -q.num /. q.den := by rw [← neg_divInt, num_divInt_den]

@[simp] lemma divInt_neg (n d : ℤ) : n /. -d = -n /. d := divInt_neg' ..

lemma mk'_mul_mk' (n₁ n₂ : ℤ) (d₁ d₂ : ℕ) (hd₁ hd₂ hnd₁ hnd₂) (h₁₂ : n₁.natAbs.Coprime d₂)
    (h₂₁ : n₂.natAbs.Coprime d₁) :
    mk' n₁ d₁ hd₁ hnd₁ * mk' n₂ d₂ hd₂ hnd₂ = mk' (n₁ * n₂) (d₁ * d₂) (Nat.mul_ne_zero hd₁ hd₂) (by
      rw [Int.natAbs_mul]; exact (hnd₁.mul_left h₂₁).mul_right (h₁₂.mul_left hnd₂)) := by
  rw [mul_def]; simp [mk_eq_normalize]

lemma mul_eq_mkRat (q r : ℚ) : q * r = mkRat (q.num * r.num) (q.den * r.den) := by
  rw [mul_def, normalize_eq_mkRat]

@[deprecated (since := "2025-08-25")] alias divInt_eq_divInt := divInt_eq_divInt_iff

lemma pow_eq_mkRat (q : ℚ) (n : ℕ) : q ^ n = mkRat (q.num ^ n) (q.den ^ n) := by
  rw [pow_def, mk_eq_mkRat]

lemma pow_eq_divInt (q : ℚ) (n : ℕ) : q ^ n = q.num ^ n /. q.den ^ n := by
  rw [pow_def, mk_eq_divInt, Int.natCast_pow]

@[simp] lemma mk'_pow (num : ℤ) (den : ℕ) (hd hdn) (n : ℕ) :
    mk' num den hd hdn ^ n = mk' (num ^ n) (den ^ n)
      (by simp [Nat.pow_eq_zero, hd]) (by rw [Int.natAbs_pow]; exact hdn.pow _ _) := rfl

@[deprecated (since := "2025-08-25")] alias inv_divInt' := inv_divInt

@[simp] lemma inv_mkRat (a : ℤ) (b : ℕ) : (mkRat a b)⁻¹ = b /. a := by
  rw [mkRat_eq_divInt, inv_divInt]

@[deprecated (since := "2025-08-25")] alias inv_def' := inv_def

@[simp] lemma divInt_div_divInt (n₁ d₁ n₂ d₂) :
    (n₁ /. d₁) / (n₂ /. d₂) = (n₁ * d₂) /. (d₁ * n₂) := by
  rw [div_def, inv_divInt, divInt_mul_divInt]

lemma div_def' (q r : ℚ) : q / r = (q.num * r.den) /. (q.den * r.num) := by
  rw [← divInt_div_divInt, num_divInt_den, num_divInt_den]

variable (a b c : ℚ)

@[simp] lemma divInt_one (n : ℤ) : n /. 1 = n := by simp [divInt, mkRat, normalize]

lemma divInt_one_one : 1 /. 1 = 1 := by rw [divInt_one, Rat.intCast_one]

protected theorem zero_ne_one : 0 ≠ (1 : ℚ) := by
  rw [ne_comm, ← divInt_one_one, divInt_ne_zero] <;> omega

attribute [simp] mkRat_eq_zero

-- Extra instances to short-circuit type class resolution
-- TODO(Mario): this instance slows down Mathlib.Data.Real.Basic
instance nontrivial : Nontrivial ℚ where exists_pair_ne := ⟨1, 0, by decide⟩

/-! ### The rational numbers are a group -/

instance addCommGroup : AddCommGroup ℚ where
  zero_add := Rat.zero_add
  add_zero := Rat.add_zero
  add_comm := Rat.add_comm
  add_assoc := Rat.add_assoc
  neg_add_cancel := Rat.neg_add_cancel
  sub_eq_add_neg := Rat.sub_eq_add_neg
  nsmul := (· * ·)
  zsmul := (· * ·)
  nsmul_zero := Rat.zero_mul
  nsmul_succ n q := by
    change ((n + 1 : Int) : Rat) * q = _
    rw [Rat.intCast_add, Rat.add_mul, Rat.intCast_one, Rat.one_mul]
    rfl
  zsmul_zero' := Rat.zero_mul
  zsmul_succ' _ _ := by simp [Rat.add_mul]
  zsmul_neg' _ _ := by rw [Int.negSucc_eq, Rat.intCast_neg, Rat.neg_mul]; rfl

instance addGroup : AddGroup ℚ := by infer_instance

instance addCommMonoid : AddCommMonoid ℚ := by infer_instance

instance addMonoid : AddMonoid ℚ := by infer_instance

instance addLeftCancelSemigroup : AddLeftCancelSemigroup ℚ := by infer_instance

instance addRightCancelSemigroup : AddRightCancelSemigroup ℚ := by infer_instance

instance addCommSemigroup : AddCommSemigroup ℚ := by infer_instance

instance addSemigroup : AddSemigroup ℚ := by infer_instance

instance commMonoid : CommMonoid ℚ where
  mul_one := Rat.mul_one
  one_mul := Rat.one_mul
  mul_comm := Rat.mul_comm
  mul_assoc := Rat.mul_assoc
  npow n q := q ^ n
  npow_zero := Rat.pow_zero
  npow_succ n q := Rat.pow_succ q n

instance monoid : Monoid ℚ := by infer_instance

instance commSemigroup : CommSemigroup ℚ := by infer_instance

instance semigroup : Semigroup ℚ := by infer_instance

theorem eq_iff_mul_eq_mul {p q : ℚ} : p = q ↔ p.num * q.den = q.num * p.den := by
  conv =>
    lhs
    rw [← num_divInt_den p, ← num_divInt_den q]
  apply Rat.divInt_eq_divInt_iff <;>
    · rw [← Int.natCast_zero, Ne, Int.ofNat_inj]
      apply den_nz

@[simp]
theorem den_neg_eq_den (q : ℚ) : (-q).den = q.den :=
  rfl

@[simp]
theorem num_neg_eq_neg_num (q : ℚ) : (-q).num = -q.num :=
  rfl

-- Not `@[simp]` as `num_ofNat` is stronger.
theorem num_zero : Rat.num 0 = 0 :=
  rfl

-- Not `@[simp]` as `den_ofNat` is stronger.
theorem den_zero : Rat.den 0 = 1 :=
  rfl

lemma zero_of_num_zero {q : ℚ} (hq : q.num = 0) : q = 0 := by simpa [hq] using q.num_divInt_den.symm

theorem zero_iff_num_zero {q : ℚ} : q = 0 ↔ q.num = 0 :=
  ⟨fun _ => by simp [*], zero_of_num_zero⟩

-- `Not `@[simp]` as `num_ofNat` is stronger.
theorem num_one : (1 : ℚ).num = 1 :=
  rfl

@[simp]
theorem den_one : (1 : ℚ).den = 1 :=
  rfl

theorem mk_num_ne_zero_of_ne_zero {q : ℚ} {n d : ℤ} (hq : q ≠ 0) (hqnd : q = n /. d) : n ≠ 0 :=
  fun this => hq <| by simpa [this] using hqnd

theorem mk_denom_ne_zero_of_ne_zero {q : ℚ} {n d : ℤ} (hq : q ≠ 0) (hqnd : q = n /. d) : d ≠ 0 :=
  fun this => hq <| by simpa [this] using hqnd

theorem divInt_ne_zero_of_ne_zero {n d : ℤ} (h : n ≠ 0) (hd : d ≠ 0) : n /. d ≠ 0 :=
  (divInt_ne_zero hd).mpr h

section Casts

protected theorem add_divInt (a b c : ℤ) : (a + b) /. c = a /. c + b /. c :=
  if h : c = 0 then by simp [h]
  else by
    rw [divInt_add_divInt _ _ h h, divInt_eq_divInt_iff h (Int.mul_ne_zero h h)]
    simp [Int.add_mul, Int.mul_assoc]

lemma intCast_div_eq_divInt (n d : ℤ) : (n : ℚ) / d = n /. d := by rw [divInt_eq_div]

theorem natCast_div_eq_divInt (n d : ℕ) : (n : ℚ) / d = n /. d := Rat.intCast_div_eq_divInt n d

theorem divInt_mul_divInt_cancel {x : ℤ} (hx : x ≠ 0) (n d : ℤ) : n /. x * (x /. d) = n /. d := by
  by_cases hd : d = 0
  · rw [hd]
    simp
  rw [divInt_mul_divInt, x.mul_comm, divInt_mul_right hx]

theorem coe_int_num_of_den_eq_one {q : ℚ} (hq : q.den = 1) : (q.num : ℚ) = q := by
  conv_rhs => rw [← num_divInt_den q, hq]
  rw [intCast_eq_divInt]
  rfl

lemma eq_num_of_isInt {q : ℚ} (h : q.isInt) : q = q.num := by
  rw [Rat.isInt, Nat.beq_eq_true_eq] at h
  exact (Rat.coe_int_num_of_den_eq_one h).symm

theorem den_eq_one_iff (r : ℚ) : r.den = 1 ↔ ↑r.num = r :=
  ⟨Rat.coe_int_num_of_den_eq_one, fun h => h ▸ Rat.den_intCast r.num⟩

instance canLift : CanLift ℚ ℤ (↑) fun q => q.den = 1 :=
  ⟨fun q hq => ⟨q.num, coe_int_num_of_den_eq_one hq⟩⟩

-- Will be subsumed by `Int.coe_inj` after we have defined
-- `LinearOrderedField ℚ` (which implies characteristic zero).
theorem coe_int_inj (m n : ℤ) : (m : ℚ) = n ↔ m = n :=
  ⟨congr_arg num, congr_arg _⟩

end Casts

/--
A version of `Rat.casesOn` that uses `/` instead of `Rat.mk'`. Use as
```lean
cases r with
| div p q nonzero coprime =>
```
-/
@[elab_as_elim, cases_eliminator, induction_eliminator]
def divCasesOn {C : ℚ → Sort*} (a : ℚ)
    (div : ∀ (n : ℤ) (d : ℕ), d ≠ 0 → n.natAbs.Coprime d → C (n / d)) : C a :=
  a.casesOn fun n d nz red => by rw [Rat.mk'_eq_divInt, Rat.divInt_eq_div]; exact div n d nz red

end Rat
