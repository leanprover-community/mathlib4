/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Int.Defs
import Mathlib.Data.Rat.Init
import Mathlib.Order.Basic
import Mathlib.Tactic.Common

#align_import data.rat.defs from "leanprover-community/mathlib"@"18a5306c091183ac90884daa9373fa3b178e8607"

/-!
# Basics for the Rational Numbers

## Summary

We define the integral domain structure on `ℚ` and prove basic lemmas about it.
The definition of the field structure on `ℚ` will be done in `Mathlib.Data.Rat.Basic` once the
`Field` class has been defined.

## Main Definitions

- `Rat.divInt n d` constructs a rational number `q = n / d` from `n d : ℤ`.

## Notations

- `/.` is infix notation for `Rat.divInt`.

-/

-- TODO: If `Inv` was defined earlier than `Algebra.Group.Defs`, we could have
-- assert_not_exists Monoid
assert_not_exists MonoidWithZero
assert_not_exists Lattice
assert_not_exists PNat
assert_not_exists Nat.dvd_mul

open Function

namespace Rat
variable {q : ℚ}

-- Porting note: the definition of `ℚ` has changed; in mathlib3 this was a field.
theorem pos (a : ℚ) : 0 < a.den := Nat.pos_of_ne_zero a.den_nz
#align rat.pos Rat.pos

#align rat.of_int Rat.ofInt

lemma mk'_num_den (q : ℚ) : mk' q.num q.den q.den_nz q.reduced = q := rfl

@[simp]
theorem ofInt_eq_cast (n : ℤ) : ofInt n = Int.cast n :=
  rfl
#align rat.of_int_eq_cast Rat.ofInt_eq_cast

-- TODO: Replace `Rat.ofNat_num`/`Rat.ofNat_den` in Batteries
-- See note [no_index around OfNat.ofNat]
@[simp] lemma num_ofNat (n : ℕ) : num (no_index (OfNat.ofNat n)) = OfNat.ofNat n := rfl
@[simp] lemma den_ofNat (n : ℕ) : den (no_index (OfNat.ofNat n)) = 1 := rfl

@[simp, norm_cast] lemma num_natCast (n : ℕ) : num n = n := rfl
#align rat.coe_nat_num Rat.num_natCast

@[simp, norm_cast] lemma den_natCast (n : ℕ) : den n = 1 := rfl
#align rat.coe_nat_denom Rat.den_natCast

-- TODO: Replace `intCast_num`/`intCast_den` the names in Batteries
@[simp, norm_cast] lemma num_intCast (n : ℤ) : (n : ℚ).num = n := rfl
#align rat.coe_int_num Rat.num_intCast

@[simp, norm_cast] lemma den_intCast (n : ℤ) : (n : ℚ).den = 1 := rfl
#align rat.coe_int_denom Rat.den_intCast

@[deprecated (since := "2024-04-29")] alias coe_int_num := num_intCast
@[deprecated (since := "2024-04-29")] alias coe_int_den := den_intCast

lemma intCast_injective : Injective (Int.cast : ℤ → ℚ) := fun _ _ ↦ congr_arg num
lemma natCast_injective : Injective (Nat.cast : ℕ → ℚ) :=
  intCast_injective.comp fun _ _ ↦ Int.natCast_inj.1

-- We want to use these lemmas earlier than the lemmas simp can prove them with
@[simp, nolint simpNF, norm_cast] lemma natCast_inj {m n : ℕ} : (m : ℚ) = n ↔ m = n :=
  natCast_injective.eq_iff
@[simp, nolint simpNF, norm_cast] lemma intCast_eq_zero {n : ℤ} : (n : ℚ) = 0 ↔ n = 0 := intCast_inj
@[simp, nolint simpNF, norm_cast] lemma natCast_eq_zero {n : ℕ} : (n : ℚ) = 0 ↔ n = 0 := natCast_inj
@[simp, nolint simpNF, norm_cast] lemma intCast_eq_one {n : ℤ} : (n : ℚ) = 1 ↔ n = 1 := intCast_inj
@[simp, nolint simpNF, norm_cast] lemma natCast_eq_one {n : ℕ} : (n : ℚ) = 1 ↔ n = 1 := natCast_inj

#noalign rat.mk_pnat
#noalign rat.mk_pnat_eq
#noalign rat.zero_mk_pnat

-- Porting note (#11215): TODO Should this be namespaced?
#align rat.mk_nat mkRat

lemma mkRat_eq_divInt (n d) : mkRat n d = n /. d := rfl
#align rat.mk_nat_eq Rat.mkRat_eq_divInt

#align rat.mk_zero Rat.divInt_zero
#align rat.zero_mk_nat Rat.zero_mkRat
#align rat.zero_mk Rat.zero_divInt

@[simp] lemma mk'_zero (d) (h : d ≠ 0) (w) : mk' 0 d h w = 0 := by congr; simp_all

@[simp]
lemma num_eq_zero {q : ℚ} : q.num = 0 ↔ q = 0 := by
  induction q
  constructor
  · rintro rfl
    exact mk'_zero _ _ _
  · exact congr_arg num

lemma num_ne_zero {q : ℚ} : q.num ≠ 0 ↔ q ≠ 0 := num_eq_zero.not
#align rat.num_ne_zero_of_ne_zero Rat.num_ne_zero

@[simp] lemma den_ne_zero (q : ℚ) : q.den ≠ 0 := q.den_pos.ne'

#noalign rat.nonneg

@[simp] lemma num_nonneg : 0 ≤ q.num ↔ 0 ≤ q := by
  simp [Int.le_iff_lt_or_eq, instLE, Rat.blt, Int.not_lt]; tauto
#align rat.num_nonneg_iff_zero_le Rat.num_nonneg

@[simp]
theorem divInt_eq_zero {a b : ℤ} (b0 : b ≠ 0) : a /. b = 0 ↔ a = 0 := by
  rw [← zero_divInt b, divInt_eq_iff b0 b0, Int.zero_mul, Int.mul_eq_zero, or_iff_left b0]
#align rat.mk_eq_zero Rat.divInt_eq_zero

theorem divInt_ne_zero {a b : ℤ} (b0 : b ≠ 0) : a /. b ≠ 0 ↔ a ≠ 0 :=
  (divInt_eq_zero b0).not
#align rat.mk_ne_zero Rat.divInt_ne_zero

#align rat.mk_eq Rat.divInt_eq_iff
#align rat.div_mk_div_cancel_left Rat.divInt_mul_right

-- Porting note: this can move to Batteries
theorem normalize_eq_mk' (n : Int) (d : Nat) (h : d ≠ 0) (c : Nat.gcd (Int.natAbs n) d = 1) :
    normalize n d h = mk' n d h c := (mk_eq_normalize ..).symm

-- TODO: Rename `mkRat_num_den` in Batteries
@[simp] alias mkRat_num_den' := mkRat_self

-- TODO: Rename `Rat.divInt_self` to `Rat.num_divInt_den` in Batteries
lemma num_divInt_den (q : ℚ) : q.num /. q.den = q := divInt_self _
#align rat.num_denom Rat.num_divInt_den

lemma mk'_eq_divInt {n d h c} : (⟨n, d, h, c⟩ : ℚ) = n /. d := (num_divInt_den _).symm
#align rat.num_denom' Rat.mk'_eq_divInt

theorem intCast_eq_divInt (z : ℤ) : (z : ℚ) = z /. 1 := mk'_eq_divInt
#align rat.coe_int_eq_mk Rat.intCast_eq_divInt

-- TODO: Rename `divInt_self` in Batteries to `num_divInt_den`
@[simp] lemma divInt_self' {n : ℤ} (hn : n ≠ 0) : n /. n = 1 := by
  simpa using divInt_mul_right (n := 1) (d := 1) hn

/-- Define a (dependent) function or prove `∀ r : ℚ, p r` by dealing with rational
numbers of the form `n /. d` with `0 < d` and coprime `n`, `d`. -/
@[elab_as_elim]
def numDenCasesOn.{u} {C : ℚ → Sort u} :
    ∀ (a : ℚ) (_ : ∀ n d, 0 < d → (Int.natAbs n).Coprime d → C (n /. d)), C a
  | ⟨n, d, h, c⟩, H => by rw [mk'_eq_divInt]; exact H n d (Nat.pos_of_ne_zero h) c
#align rat.num_denom_cases_on Rat.numDenCasesOn

/-- Define a (dependent) function or prove `∀ r : ℚ, p r` by dealing with rational
numbers of the form `n /. d` with `d ≠ 0`. -/
@[elab_as_elim]
def numDenCasesOn'.{u} {C : ℚ → Sort u} (a : ℚ) (H : ∀ (n : ℤ) (d : ℕ), d ≠ 0 → C (n /. d)) :
    C a :=
  numDenCasesOn a fun n d h _ => H n d h.ne'
#align rat.num_denom_cases_on' Rat.numDenCasesOn'

/-- Define a (dependent) function or prove `∀ r : ℚ, p r` by dealing with rational
numbers of the form `mk' n d` with `d ≠ 0`. -/
@[elab_as_elim]
def numDenCasesOn''.{u} {C : ℚ → Sort u} (a : ℚ)
    (H : ∀ (n : ℤ) (d : ℕ) (nz red), C (mk' n d nz red)) : C a :=
  numDenCasesOn a fun n d h h' ↦ by rw [← mk_eq_divInt _ _ h.ne' h']; exact H n d h.ne' _

#align rat.add Rat.add

-- Porting note: there's already an instance for `Add ℚ` is in Batteries.

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
  generalize ha : a /. b = x; cases' x with n₁ d₁ h₁ c₁; rw [mk'_eq_divInt] at ha
  generalize hc : c /. d = x; cases' x with n₂ d₂ h₂ c₂; rw [mk'_eq_divInt] at hc
  rw [fv]
  have d₁0 := Int.ofNat_ne_zero.2 h₁
  have d₂0 := Int.ofNat_ne_zero.2 h₂
  exact (divInt_eq_iff (f0 d₁0 d₂0) (f0 b0 d0)).2
    (H ((divInt_eq_iff b0 d₁0).1 ha) ((divInt_eq_iff d0 d₂0).1 hc))
#align rat.lift_binop_eq Rat.lift_binop_eq

attribute [simp] divInt_add_divInt

@[deprecated divInt_add_divInt (since := "2024-03-18")]
theorem add_def'' {a b c d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) :
    a /. b + c /. d = (a * d + c * b) /. (b * d) := divInt_add_divInt _ _ b0 d0

#align rat.add_def Rat.add_def''
#align rat.neg Rat.neg

attribute [simp] neg_divInt
#align rat.neg_def Rat.neg_divInt

lemma neg_def (q : ℚ) : -q = -q.num /. q.den := by rw [← neg_divInt, num_divInt_den]

@[simp] lemma divInt_neg (n d : ℤ) : n /. -d = -n /. d := divInt_neg' ..
#align rat.mk_neg_denom Rat.divInt_neg

@[deprecated (since := "2024-03-18")] alias divInt_neg_den := divInt_neg

attribute [simp] divInt_sub_divInt

@[deprecated divInt_sub_divInt (since := "2024-03-18")]
lemma sub_def'' {a b c d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) :
    a /. b - c /. d = (a * d - c * b) /. (b * d) := divInt_sub_divInt _ _ b0 d0
#align rat.sub_def Rat.sub_def''

#align rat.mul Rat.mul

@[simp]
lemma divInt_mul_divInt' (n₁ d₁ n₂ d₂ : ℤ) : (n₁ /. d₁) * (n₂ /. d₂) = (n₁ * n₂) /. (d₁ * d₂) := by
  obtain rfl | h₁ := eq_or_ne d₁ 0
  · simp
  obtain rfl | h₂ := eq_or_ne d₂ 0
  · simp
  exact divInt_mul_divInt _ _ h₁ h₂
#align rat.mul_def Rat.divInt_mul_divInt'

attribute [simp] mkRat_mul_mkRat

lemma mk'_mul_mk' (n₁ n₂ : ℤ) (d₁ d₂ : ℕ) (hd₁ hd₂ hnd₁ hnd₂) (h₁₂ : n₁.natAbs.Coprime d₂)
    (h₂₁ : n₂.natAbs.Coprime d₁) :
    mk' n₁ d₁ hd₁ hnd₁ * mk' n₂ d₂ hd₂ hnd₂ = mk' (n₁ * n₂) (d₁ * d₂) (Nat.mul_ne_zero hd₁ hd₂) (by
      rw [Int.natAbs_mul]; exact (hnd₁.mul h₂₁).mul_right (h₁₂.mul hnd₂)) := by
  rw [mul_def]; dsimp; simp [mk_eq_normalize]

lemma mul_eq_mkRat (q r : ℚ) : q * r = mkRat (q.num * r.num) (q.den * r.den) := by
  rw [mul_def, normalize_eq_mkRat]

-- TODO: Rename `divInt_eq_iff` in Batteries to `divInt_eq_divInt`
alias divInt_eq_divInt := divInt_eq_iff

@[deprecated (since := "2024-04-29")] alias mul_num_den := mul_eq_mkRat
#align rat.mul_num_denom Rat.mul_eq_mkRat

instance instPowNat : Pow ℚ ℕ where
  pow q n := ⟨q.num ^ n, q.den ^ n, by simp [Nat.pow_eq_zero], by
    rw [Int.natAbs_pow]; exact q.reduced.pow _ _⟩

lemma pow_def (q : ℚ) (n : ℕ) :
    q ^ n = ⟨q.num ^ n, q.den ^ n,
      by simp [Nat.pow_eq_zero],
      by rw [Int.natAbs_pow]; exact q.reduced.pow _ _⟩ := rfl

lemma pow_eq_mkRat (q : ℚ) (n : ℕ) : q ^ n = mkRat (q.num ^ n) (q.den ^ n) := by
  rw [pow_def, mk_eq_mkRat]

lemma pow_eq_divInt (q : ℚ) (n : ℕ) : q ^ n = q.num ^ n /. q.den ^ n := by
  rw [pow_def, mk_eq_divInt, Int.natCast_pow]

@[simp] lemma num_pow (q : ℚ) (n : ℕ) : (q ^ n).num = q.num ^ n := rfl
@[simp] lemma den_pow (q : ℚ) (n : ℕ) : (q ^ n).den = q.den ^ n := rfl

@[simp] lemma mk'_pow (num : ℤ) (den : ℕ) (hd hdn) (n : ℕ) :
    mk' num den hd hdn ^ n = mk' (num ^ n) (den ^ n)
      (by simp [Nat.pow_eq_zero, hd]) (by rw [Int.natAbs_pow]; exact hdn.pow _ _) := rfl

#align rat.inv Rat.inv

instance : Inv ℚ :=
  ⟨Rat.inv⟩

@[simp] lemma inv_divInt' (a b : ℤ) : (a /. b)⁻¹ = b /. a := inv_divInt ..
#align rat.inv_def Rat.inv_divInt

@[simp] lemma inv_mkRat (a : ℤ) (b : ℕ) : (mkRat a b)⁻¹ = b /. a := by
  rw [mkRat_eq_divInt, inv_divInt']

lemma inv_def' (q : ℚ) : q⁻¹ = q.den /. q.num := by rw [← inv_divInt', num_divInt_den]
#align rat.inv_def' Rat.inv_def'

@[simp] lemma divInt_div_divInt (n₁ d₁ n₂ d₂) :
    (n₁ /. d₁) / (n₂ /. d₂) = (n₁ * d₂) /. (d₁ * n₂) := by
  rw [div_def, inv_divInt, divInt_mul_divInt']

lemma div_def' (q r : ℚ) : q / r = (q.num * r.den) /. (q.den * r.num) := by
  rw [← divInt_div_divInt, num_divInt_den, num_divInt_den]

@[deprecated (since := "2024-04-15")] alias div_num_den := div_def'
#align rat.div_num_denom Rat.div_def'

variable (a b c : ℚ)

protected lemma add_zero : a + 0 = a := by simp [add_def, normalize_eq_mkRat]
#align rat.add_zero Rat.add_zero

protected lemma zero_add : 0 + a = a := by simp [add_def, normalize_eq_mkRat]
#align rat.zero_add Rat.zero_add

protected lemma add_comm : a + b = b + a := by
  simp [add_def, Int.add_comm, Int.mul_comm, Nat.mul_comm]
#align rat.add_comm Rat.add_comm

protected theorem add_assoc : a + b + c = a + (b + c) :=
  numDenCasesOn' a fun n₁ d₁ h₁ ↦ numDenCasesOn' b fun n₂ d₂ h₂ ↦ numDenCasesOn' c fun n₃ d₃ h₃ ↦ by
    simp only [ne_eq, Int.natCast_eq_zero, h₁, not_false_eq_true, h₂, divInt_add_divInt,
      Int.mul_eq_zero, or_self, h₃]
    rw [Int.mul_assoc, Int.add_mul, Int.add_mul, Int.mul_assoc, Int.add_assoc]
    congr 2
    ac_rfl
#align rat.add_assoc Rat.add_assoc

protected lemma add_left_neg : -a + a = 0 := by
  simp [add_def, normalize_eq_mkRat, Int.neg_mul, Int.add_comm, ← Int.sub_eq_add_neg]
#align rat.add_left_neg Rat.add_left_neg

@[deprecated zero_divInt (since := "2024-03-18")]
lemma divInt_zero_one : 0 /. 1 = 0 := zero_divInt _
#align rat.mk_zero_one Rat.zero_divInt

@[simp] lemma divInt_one (n : ℤ) : n /. 1 = n := by simp [divInt, mkRat, normalize]
@[simp] lemma mkRat_one (n : ℤ) : mkRat n 1 = n := by simp [mkRat_eq_divInt]

lemma divInt_one_one : 1 /. 1 = 1 := by rw [divInt_one]; rfl
#align rat.mk_one_one Rat.divInt_one_one

@[deprecated divInt_one (since := "2024-03-18")]
lemma divInt_neg_one_one : -1 /. 1 = -1 := by rw [divInt_one]; rfl
#align rat.mk_neg_one_one Rat.divInt_neg_one_one

#align rat.mul_one Rat.mul_one
#align rat.one_mul Rat.one_mul
#align rat.mul_comm Rat.mul_comm

protected theorem mul_assoc : a * b * c = a * (b * c) :=
  numDenCasesOn' a fun n₁ d₁ h₁ =>
    numDenCasesOn' b fun n₂ d₂ h₂ =>
      numDenCasesOn' c fun n₃ d₃ h₃ => by
        simp [h₁, h₂, h₃, Int.mul_comm, Nat.mul_assoc, Int.mul_left_comm]
#align rat.mul_assoc Rat.mul_assoc

protected theorem add_mul : (a + b) * c = a * c + b * c :=
  numDenCasesOn' a fun n₁ d₁ h₁ ↦ numDenCasesOn' b fun n₂ d₂ h₂ ↦ numDenCasesOn' c fun n₃ d₃ h₃ ↦ by
    simp only [ne_eq, Int.natCast_eq_zero, h₁, not_false_eq_true, h₂, divInt_add_divInt,
      Int.mul_eq_zero, or_self, h₃, divInt_mul_divInt]
    rw [← divInt_mul_right (Int.natCast_ne_zero.2 h₃), Int.add_mul, Int.add_mul]
    ac_rfl
#align rat.add_mul Rat.add_mul

protected theorem mul_add : a * (b + c) = a * b + a * c := by
  rw [Rat.mul_comm, Rat.add_mul, Rat.mul_comm, Rat.mul_comm c a]
#align rat.mul_add Rat.mul_add

protected theorem zero_ne_one : 0 ≠ (1 : ℚ) := by
  rw [ne_comm, ← divInt_one_one, divInt_ne_zero] <;> omega
#align rat.zero_ne_one Rat.zero_ne_one

attribute [simp] mkRat_eq_zero

protected theorem mul_inv_cancel : a ≠ 0 → a * a⁻¹ = 1 :=
  numDenCasesOn' a fun n d hd hn ↦ by
    simp [hd] at hn;
    simp [-divInt_ofNat, mkRat_eq_divInt, Int.mul_comm, Int.mul_ne_zero hn (Int.ofNat_ne_zero.2 hd)]
#align rat.mul_inv_cancel Rat.mul_inv_cancel

protected theorem inv_mul_cancel (h : a ≠ 0) : a⁻¹ * a = 1 :=
  Eq.trans (Rat.mul_comm _ _) (Rat.mul_inv_cancel _ h)
#align rat.inv_mul_cancel Rat.inv_mul_cancel

-- Porting note: we already have a `DecidableEq ℚ`.

-- Extra instances to short-circuit type class resolution
-- TODO(Mario): this instance slows down Mathlib.Data.Real.Basic
instance nontrivial : Nontrivial ℚ where exists_pair_ne := ⟨1, 0, by decide⟩

/-! ### The rational numbers are a group -/

instance addCommGroup : AddCommGroup ℚ where
  zero := 0
  add := (· + ·)
  neg := Neg.neg
  zero_add := Rat.zero_add
  add_zero := Rat.add_zero
  add_comm := Rat.add_comm
  add_assoc := Rat.add_assoc
  add_left_neg := Rat.add_left_neg
  sub_eq_add_neg := Rat.sub_eq_add_neg
  nsmul := nsmulRec
  zsmul := zsmulRec

instance addGroup : AddGroup ℚ := by infer_instance

instance addCommMonoid : AddCommMonoid ℚ := by infer_instance

instance addMonoid : AddMonoid ℚ := by infer_instance

instance addLeftCancelSemigroup : AddLeftCancelSemigroup ℚ := by infer_instance

instance addRightCancelSemigroup : AddRightCancelSemigroup ℚ := by infer_instance

instance addCommSemigroup : AddCommSemigroup ℚ := by infer_instance

instance addSemigroup : AddSemigroup ℚ := by infer_instance

instance commMonoid : CommMonoid ℚ where
  one := 1
  mul := (· * ·)
  mul_one := Rat.mul_one
  one_mul := Rat.one_mul
  mul_comm := Rat.mul_comm
  mul_assoc := Rat.mul_assoc
  npow n q := q ^ n
  npow_zero := by intros; apply Rat.ext <;> simp [Int.pow_zero]
  npow_succ n q := by
    dsimp
    rw [← q.mk'_num_den, mk'_pow, mk'_mul_mk']
    · congr
    · rw [mk'_pow, Int.natAbs_pow]
      exact q.reduced.pow_left _
    · rw [mk'_pow]
      exact q.reduced.pow_right _

instance monoid : Monoid ℚ := by infer_instance

instance commSemigroup : CommSemigroup ℚ := by infer_instance

instance semigroup : Semigroup ℚ := by infer_instance

#align rat.denom_ne_zero Rat.den_nz

theorem eq_iff_mul_eq_mul {p q : ℚ} : p = q ↔ p.num * q.den = q.num * p.den := by
  conv =>
    lhs
    rw [← num_divInt_den p, ← num_divInt_den q]
  apply Rat.divInt_eq_iff <;>
    · rw [← Int.natCast_zero, Ne, Int.ofNat_inj]
      apply den_nz
#align rat.eq_iff_mul_eq_mul Rat.eq_iff_mul_eq_mul

@[simp]
theorem den_neg_eq_den (q : ℚ) : (-q).den = q.den :=
  rfl
#align rat.denom_neg_eq_denom Rat.den_neg_eq_den

@[simp]
theorem num_neg_eq_neg_num (q : ℚ) : (-q).num = -q.num :=
  rfl
#align rat.num_neg_eq_neg_num Rat.num_neg_eq_neg_num

@[simp]
theorem num_zero : Rat.num 0 = 0 :=
  rfl
#align rat.num_zero Rat.num_zero

@[simp]
theorem den_zero : Rat.den 0 = 1 :=
  rfl
#align rat.denom_zero Rat.den_zero

lemma zero_of_num_zero {q : ℚ} (hq : q.num = 0) : q = 0 := by simpa [hq] using q.num_divInt_den.symm
#align rat.zero_of_num_zero Rat.zero_of_num_zero

theorem zero_iff_num_zero {q : ℚ} : q = 0 ↔ q.num = 0 :=
  ⟨fun _ => by simp [*], zero_of_num_zero⟩
#align rat.zero_iff_num_zero Rat.zero_iff_num_zero

@[simp]
theorem num_one : (1 : ℚ).num = 1 :=
  rfl
#align rat.num_one Rat.num_one

@[simp]
theorem den_one : (1 : ℚ).den = 1 :=
  rfl
#align rat.denom_one Rat.den_one

theorem mk_num_ne_zero_of_ne_zero {q : ℚ} {n d : ℤ} (hq : q ≠ 0) (hqnd : q = n /. d) : n ≠ 0 :=
  fun this => hq <| by simpa [this] using hqnd
#align rat.mk_num_ne_zero_of_ne_zero Rat.mk_num_ne_zero_of_ne_zero

theorem mk_denom_ne_zero_of_ne_zero {q : ℚ} {n d : ℤ} (hq : q ≠ 0) (hqnd : q = n /. d) : d ≠ 0 :=
  fun this => hq <| by simpa [this] using hqnd
#align rat.mk_denom_ne_zero_of_ne_zero Rat.mk_denom_ne_zero_of_ne_zero

theorem divInt_ne_zero_of_ne_zero {n d : ℤ} (h : n ≠ 0) (hd : d ≠ 0) : n /. d ≠ 0 :=
  (divInt_ne_zero hd).mpr h
#align rat.mk_ne_zero_of_ne_zero Rat.divInt_ne_zero_of_ne_zero

protected lemma nonneg_antisymm : 0 ≤ q → 0 ≤ -q → q = 0 := by
  simp_rw [← num_eq_zero, Int.le_antisymm_iff, ← num_nonneg, num_neg_eq_neg_num, Int.neg_nonneg]
  tauto
#align rat.nonneg_antisymm Rat.nonneg_antisymm

protected lemma nonneg_total (a : ℚ) : 0 ≤ a ∨ 0 ≤ -a := by
  simp_rw [← num_nonneg, num_neg_eq_neg_num, Int.neg_nonneg]; exact Int.le_total _ _
#align rat.nonneg_total Rat.nonneg_total

#align rat.decidable_nonneg Rat.instDecidableLe

section Casts

protected theorem add_divInt (a b c : ℤ) : (a + b) /. c = a /. c + b /. c :=
  if h : c = 0 then by simp [h]
  else by
    rw [divInt_add_divInt _ _ h h, divInt_eq_iff h (Int.mul_ne_zero h h)]
    simp [Int.add_mul, Int.mul_assoc]
#align rat.add_mk Rat.add_divInt

theorem divInt_eq_div (n d : ℤ) : n /. d = (n : ℚ) / d := by simp [div_def']
#align rat.mk_eq_div Rat.divInt_eq_div

lemma intCast_div_eq_divInt (n d : ℤ) : (n : ℚ) / (d) = n /. d := by rw [divInt_eq_div]
#align rat.coe_int_div_eq_mk Rat.intCast_div_eq_divInt

theorem natCast_div_eq_divInt (n d : ℕ) : (n : ℚ) / d = n /. d := Rat.intCast_div_eq_divInt n d

theorem divInt_mul_divInt_cancel {x : ℤ} (hx : x ≠ 0) (n d : ℤ) : n /. x * (x /. d) = n /. d := by
  by_cases hd : d = 0
  · rw [hd]
    simp
  rw [divInt_mul_divInt _ _ hx hd, x.mul_comm, divInt_mul_right hx]
#align rat.mk_mul_mk_cancel Rat.divInt_mul_divInt_cancel

theorem coe_int_num_of_den_eq_one {q : ℚ} (hq : q.den = 1) : (q.num : ℚ) = q := by
  conv_rhs => rw [← num_divInt_den q, hq]
  rw [intCast_eq_divInt]
  rfl
#align rat.coe_int_num_of_denom_eq_one Rat.coe_int_num_of_den_eq_one

lemma eq_num_of_isInt {q : ℚ} (h : q.isInt) : q = q.num := by
  rw [Rat.isInt, Nat.beq_eq_true_eq] at h
  exact (Rat.coe_int_num_of_den_eq_one h).symm

theorem den_eq_one_iff (r : ℚ) : r.den = 1 ↔ ↑r.num = r :=
  ⟨Rat.coe_int_num_of_den_eq_one, fun h => h ▸ Rat.den_intCast r.num⟩
#align rat.denom_eq_one_iff Rat.den_eq_one_iff

instance canLift : CanLift ℚ ℤ (↑) fun q => q.den = 1 :=
  ⟨fun q hq => ⟨q.num, coe_int_num_of_den_eq_one hq⟩⟩
#align rat.can_lift Rat.canLift

@[deprecated (since := "2024-04-05")] alias coe_int_eq_divInt := intCast_eq_divInt
@[deprecated (since := "2024-04-05")] alias coe_int_div_eq_divInt := intCast_div_eq_divInt

-- Will be subsumed by `Int.coe_inj` after we have defined
-- `LinearOrderedField ℚ` (which implies characteristic zero).
theorem coe_int_inj (m n : ℤ) : (m : ℚ) = n ↔ m = n :=
  ⟨congr_arg num, congr_arg _⟩
#align rat.coe_int_inj Rat.coe_int_inj

end Casts
end Rat
