/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.Rat.Init
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Algebra.GroupWithZero.Basic

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


namespace Rat

-- Porting note: the definition of `ℚ` has changed; in mathlib3 this was a field.
theorem pos (a : ℚ) : 0 < a.den := Nat.pos_of_ne_zero a.den_nz
#align rat.pos Rat.pos

#align rat.of_int Rat.ofInt

@[simp]
theorem ofInt_eq_cast (n : ℤ) : ofInt n = Int.cast n :=
  rfl
#align rat.of_int_eq_cast Rat.ofInt_eq_cast

@[simp, norm_cast]
theorem coe_int_num (n : ℤ) : (n : ℚ).num = n :=
  rfl
#align rat.coe_int_num Rat.coe_int_num

@[simp, norm_cast]
theorem coe_int_den (n : ℤ) : (n : ℚ).den = 1 :=
  rfl
#align rat.coe_int_denom Rat.coe_int_den

#noalign rat.mk_pnat

-- Porting note: TODO Should this be namespaced?
#align rat.mk_nat mkRat

#noalign rat.mk_pnat_eq

theorem mkRat_eq (n d) : mkRat n d = n /. d :=
  rfl
#align rat.mk_nat_eq Rat.mkRat_eq

#align rat.mk_zero Rat.divInt_zero

@[simp]
theorem zero_mk (d) (h : d ≠ 0) (w) : mk' 0 d h w = 0 := by congr

#noalign rat.zero_mk_pnat

#align rat.zero_mk_nat Rat.zero_mkRat
#align rat.zero_mk Rat.zero_divInt

@[simp]
lemma num_eq_zero {q : ℚ} : q.num = 0 ↔ q = 0 := by
  induction q
  constructor
  · rintro rfl
    exact zero_mk _ _ _
  · exact congr_arg num

lemma num_ne_zero {q : ℚ} : q.num ≠ 0 ↔ q ≠ 0 := num_eq_zero.not

@[simp]
theorem divInt_eq_zero {a b : ℤ} (b0 : b ≠ 0) : a /. b = 0 ↔ a = 0 := by
  rw [← zero_divInt b, divInt_eq_iff b0 b0, zero_mul, mul_eq_zero, or_iff_left b0]
#align rat.mk_eq_zero Rat.divInt_eq_zero

theorem divInt_ne_zero {a b : ℤ} (b0 : b ≠ 0) : a /. b ≠ 0 ↔ a ≠ 0 :=
  (divInt_eq_zero b0).not
#align rat.mk_ne_zero Rat.divInt_ne_zero

#align rat.mk_eq Rat.divInt_eq_iff
#align rat.div_mk_div_cancel_left Rat.divInt_mul_right

-- Porting note: this can move to Std4
theorem normalize_eq_mk' (n : Int) (d : Nat) (h : d ≠ 0) (c : Nat.gcd (Int.natAbs n) d = 1) :
    normalize n d h = mk' n d h c := (mk_eq_normalize ..).symm

-- Porting note: removing as a `@[simp]` lemma as
-- theorem Rat.divInt_ofNat : ∀ (num : ℤ) (den : ℕ), num /. ↑den = mkRat num den
-- applies to the LHS.
-- @[simp]
theorem num_den : ∀ {a : ℚ}, a.num /. a.den = a := divInt_self _
#align rat.num_denom Rat.num_den

theorem num_den' {n d h c} : (⟨n, d, h, c⟩ : ℚ) = n /. d := num_den.symm
#align rat.num_denom' Rat.num_den'

theorem coe_int_eq_divInt (z : ℤ) : (z : ℚ) = z /. 1 := num_den'
#align rat.coe_int_eq_mk Rat.coe_int_eq_divInt

/-- Define a (dependent) function or prove `∀ r : ℚ, p r` by dealing with rational
numbers of the form `n /. d` with `0 < d` and coprime `n`, `d`. -/
@[elab_as_elim]
def numDenCasesOn.{u} {C : ℚ → Sort u} :
    ∀ (a : ℚ) (_ : ∀ n d, 0 < d → (Int.natAbs n).Coprime d → C (n /. d)), C a
  | ⟨n, d, h, c⟩, H => by rw [num_den']; exact H n d (Nat.pos_of_ne_zero h) c
#align rat.num_denom_cases_on Rat.numDenCasesOn

/-- Define a (dependent) function or prove `∀ r : ℚ, p r` by dealing with rational
numbers of the form `n /. d` with `d ≠ 0`. -/
@[elab_as_elim]
def numDenCasesOn'.{u} {C : ℚ → Sort u} (a : ℚ) (H : ∀ (n : ℤ) (d : ℕ), d ≠ 0 → C (n /. d)) :
    C a :=
  numDenCasesOn a fun n d h _ => H n d h.ne'
#align rat.num_denom_cases_on' Rat.numDenCasesOn'

#align rat.add Rat.add

-- Porting note: there's already an instance for `Add ℚ` is in Std.

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
  generalize ha : a /. b = x; cases' x with n₁ d₁ h₁ c₁; rw [num_den'] at ha
  generalize hc : c /. d = x; cases' x with n₂ d₂ h₂ c₂; rw [num_den'] at hc
  rw [fv]
  have d₁0 := ne_of_gt (Int.ofNat_lt.2 <| Nat.pos_of_ne_zero h₁)
  have d₂0 := ne_of_gt (Int.ofNat_lt.2 <| Nat.pos_of_ne_zero h₂)
  exact (divInt_eq_iff (f0 d₁0 d₂0) (f0 b0 d0)).2
    (H ((divInt_eq_iff b0 d₁0).1 ha) ((divInt_eq_iff d0 d₂0).1 hc))
#align rat.lift_binop_eq Rat.lift_binop_eq

@[simp]
theorem add_def'' {a b c d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) :
    a /. b + c /. d = (a * d + c * b) /. (b * d) := divInt_add_divInt _ _ b0 d0

#align rat.add_def Rat.add_def''
#align rat.neg Rat.neg

-- Porting note: there's already an instance for `Neg ℚ` is in Std.

-- Porting note: Std has explicit arguments here
@[simp]
theorem neg_def {a b : ℤ} : -(a /. b) = -a /. b := neg_divInt a b
#align rat.neg_def Rat.neg_def

@[simp]
theorem divInt_neg_den (n d : ℤ) : n /. -d = -n /. d := divInt_neg' ..
#align rat.mk_neg_denom Rat.divInt_neg_den

@[simp]
theorem sub_def'' {a b c d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) :
    a /. b - c /. d = (a * d - c * b) /. (b * d) := divInt_sub_divInt _ _ b0 d0
#align rat.sub_def Rat.sub_def''

#align rat.mul Rat.mul

-- Porting note: there's already an instance for `Mul ℚ` in Std.
@[simp]
theorem mul_def' {a b c d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) : a /. b * (c /. d) = a * c /. (b * d) :=
  divInt_mul_divInt _ _ b0 d0
#align rat.mul_def Rat.mul_def'

#align rat.inv Rat.inv

instance : Inv ℚ :=
  ⟨Rat.inv⟩

-- Porting note: there's already an instance for `Div ℚ` is in Std.

@[simp]
theorem inv_def' {a b : ℤ} : (a /. b)⁻¹ = b /. a := inv_divInt ..
#align rat.inv_def Rat.inv_def'

variable (a b c : ℚ)

-- Porting note: TODO this is a workaround.
attribute [-simp] divInt_ofNat

protected theorem add_zero : a + 0 = a :=
  numDenCasesOn' a fun n d h => by
    rw [← zero_divInt d, add_def'', zero_mul, add_zero, divInt_mul_right] <;> simp [h]
#align rat.add_zero Rat.add_zero

protected theorem zero_add : 0 + a = a :=
  numDenCasesOn' a fun n d h => by
    rw [← zero_divInt d, add_def'', zero_mul, zero_add, divInt_mul_right] <;> simp [h]
#align rat.zero_add Rat.zero_add

protected theorem add_comm : a + b = b + a :=
  numDenCasesOn' a fun n₁ d₁ h₁ => numDenCasesOn' b fun n₂ d₂ h₂ => by
    simp [h₁, h₂, add_comm, mul_comm]
#align rat.add_comm Rat.add_comm

protected theorem add_assoc : a + b + c = a + (b + c) :=
  numDenCasesOn' a fun n₁ d₁ h₁ =>
    numDenCasesOn' b fun n₂ d₂ h₂ =>
      numDenCasesOn' c fun n₃ d₃ h₃ => by
        simp only [ne_eq, Nat.cast_eq_zero, h₁, not_false_eq_true, h₂, add_def'', mul_eq_zero,
          or_self, h₃]
        rw [mul_assoc, add_mul, add_mul, mul_assoc, add_assoc]
        congr 2
        ac_rfl
#align rat.add_assoc Rat.add_assoc

protected theorem add_left_neg : -a + a = 0 :=
  numDenCasesOn' a fun n d h => by simp [h, mkRat_add_mkRat]
#align rat.add_left_neg Rat.add_left_neg

theorem divInt_zero_one : 0 /. 1 = 0 :=
  show divInt _ _ = _ by
    rw [divInt]
    simp
#align rat.mk_zero_one Rat.divInt_zero_one

@[simp]
theorem divInt_one_one : 1 /. 1 = 1 :=
  show divInt _ _ = _ by
    rw [divInt]
    simp [mkRat, normalize]
    rfl
#align rat.mk_one_one Rat.divInt_one_one

@[simp]
theorem divInt_neg_one_one : -1 /. 1 = -1 :=
  show divInt _ _ = _ by
    rw [divInt]
    simp [mkRat, normalize]
    rfl
#align rat.mk_neg_one_one Rat.divInt_neg_one_one

theorem divInt_one (n : ℤ) : n /. 1 = n :=
  show divInt _ _ = _ by
    rw [divInt]
    simp [mkRat, normalize]
    rfl

theorem mkRat_one {n : ℤ} : mkRat n 1 = n := by
  simp [Rat.mkRat_eq, Rat.divInt_one]

#align rat.mul_one Rat.mul_one
#align rat.one_mul Rat.one_mul
#align rat.mul_comm Rat.mul_comm

protected theorem mul_assoc : a * b * c = a * (b * c) :=
  numDenCasesOn' a fun n₁ d₁ h₁ =>
    numDenCasesOn' b fun n₂ d₂ h₂ =>
      numDenCasesOn' c fun n₃ d₃ h₃ => by
        simp [h₁, h₂, h₃, mul_ne_zero, mul_comm, mul_assoc, mul_left_comm]
#align rat.mul_assoc Rat.mul_assoc

protected theorem add_mul : (a + b) * c = a * c + b * c :=
  numDenCasesOn' a fun n₁ d₁ h₁ =>
    numDenCasesOn' b fun n₂ d₂ h₂ =>
      numDenCasesOn' c fun n₃ d₃ h₃ => by
        simp only [ne_eq, Nat.cast_eq_zero, h₁, not_false_eq_true, h₂, add_def'', mul_eq_zero,
          or_self, h₃, mul_def']
        rw [← divInt_mul_right (Int.coe_nat_ne_zero.2 h₃), add_mul, add_mul]
        ac_rfl
#align rat.add_mul Rat.add_mul

protected theorem mul_add : a * (b + c) = a * b + a * c := by
  rw [Rat.mul_comm, Rat.add_mul, Rat.mul_comm, Rat.mul_comm c a]
#align rat.mul_add Rat.mul_add

protected theorem zero_ne_one : 0 ≠ (1 : ℚ) := by
  rw [ne_comm, ← divInt_one_one, divInt_ne_zero one_ne_zero]
  exact one_ne_zero
#align rat.zero_ne_one Rat.zero_ne_one

protected theorem mul_inv_cancel : a ≠ 0 → a * a⁻¹ = 1 :=
  numDenCasesOn' a fun n d h a0 => by
    have n0 : n ≠ 0 := mt (by rintro rfl; simp) a0
    simpa [h, n0, mul_comm] using @divInt_mul_right 1 1 (n * d) (by simp [h, n0])
#align rat.mul_inv_cancel Rat.mul_inv_cancel

protected theorem inv_mul_cancel (h : a ≠ 0) : a⁻¹ * a = 1 :=
  Eq.trans (Rat.mul_comm _ _) (Rat.mul_inv_cancel _ h)
#align rat.inv_mul_cancel Rat.inv_mul_cancel

-- Porting note: we already have a `DecidableEq ℚ`.

/-! At this point in the import hierarchy we have not defined the `Field` typeclass.
Instead we'll instantiate `CommRing` and `CommGroupWithZero` at this point.
The `Rat.field` instance and any field-specific lemmas can be found in `Mathlib.Data.Rat.Basic`.
-/

instance commRing : CommRing ℚ where
  zero := 0
  add := (· + ·)
  neg := Neg.neg
  one := 1
  mul := (· * ·)
  zero_add := Rat.zero_add
  add_zero := Rat.add_zero
  add_comm := Rat.add_comm
  add_assoc := Rat.add_assoc
  add_left_neg := Rat.add_left_neg
  mul_one := Rat.mul_one
  one_mul := Rat.one_mul
  mul_comm := Rat.mul_comm
  mul_assoc := Rat.mul_assoc
  zero_mul := Rat.zero_mul
  mul_zero := Rat.mul_zero
  left_distrib := Rat.mul_add
  right_distrib := Rat.add_mul
  sub_eq_add_neg := Rat.sub_eq_add_neg
  intCast := fun n => n
  natCast n := Int.cast n
  natCast_zero := rfl
  natCast_succ n := by
    simp only [coe_int_eq_divInt, add_def'' one_ne_zero one_ne_zero,
      ← divInt_one_one, Nat.cast_add, Nat.cast_one, mul_one]

instance commGroupWithZero : CommGroupWithZero ℚ :=
  { exists_pair_ne := ⟨0, 1, Rat.zero_ne_one⟩
    inv_zero := by
      change Rat.inv 0 = 0
      rw [Rat.inv_def]
      rfl
    mul_inv_cancel := Rat.mul_inv_cancel
    mul_zero := mul_zero
    zero_mul := zero_mul }

instance isDomain : IsDomain ℚ :=
  NoZeroDivisors.to_isDomain _

-- Extra instances to short-circuit type class resolution
-- TODO(Mario): this instance slows down Mathlib.Data.Real.Basic
instance nontrivial : Nontrivial ℚ := by infer_instance

instance commSemiring : CommSemiring ℚ := by infer_instance

instance semiring : Semiring ℚ := by infer_instance

instance addCommGroup : AddCommGroup ℚ := by infer_instance

instance addGroup : AddGroup ℚ := by infer_instance

instance addCommMonoid : AddCommMonoid ℚ := by infer_instance

instance addMonoid : AddMonoid ℚ := by infer_instance

instance addLeftCancelSemigroup : AddLeftCancelSemigroup ℚ := by infer_instance

instance addRightCancelSemigroup : AddRightCancelSemigroup ℚ := by infer_instance

instance addCommSemigroup : AddCommSemigroup ℚ := by infer_instance

instance addSemigroup : AddSemigroup ℚ := by infer_instance

instance commMonoid : CommMonoid ℚ := by infer_instance

instance monoid : Monoid ℚ := by infer_instance

instance commSemigroup : CommSemigroup ℚ := by infer_instance

instance semigroup : Semigroup ℚ := by infer_instance

#align rat.denom_ne_zero Rat.den_nz

theorem eq_iff_mul_eq_mul {p q : ℚ} : p = q ↔ p.num * q.den = q.num * p.den := by
  conv =>
    lhs
    rw [← @num_den p, ← @num_den q]
  apply Rat.divInt_eq_iff <;>
    · rw [← Nat.cast_zero, Ne, Int.ofNat_inj]
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

theorem zero_of_num_zero {q : ℚ} (hq : q.num = 0) : q = 0 := by
  have : q = q.num /. q.den := num_den.symm
  simpa [hq] using this
#align rat.zero_of_num_zero Rat.zero_of_num_zero

theorem zero_iff_num_zero {q : ℚ} : q = 0 ↔ q.num = 0 :=
  ⟨fun _ => by simp [*], zero_of_num_zero⟩
#align rat.zero_iff_num_zero Rat.zero_iff_num_zero

theorem num_ne_zero_of_ne_zero {q : ℚ} (h : q ≠ 0) : q.num ≠ 0 := fun hq0 : q.num = 0 =>
  h <| zero_of_num_zero hq0
#align rat.num_ne_zero_of_ne_zero Rat.num_ne_zero_of_ne_zero

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

theorem mul_num_den (q r : ℚ) : q * r = q.num * r.num /. ↑(q.den * r.den) := by
  have hq' : (↑q.den : ℤ) ≠ 0 := by have := den_nz q; simpa
  have hr' : (↑r.den : ℤ) ≠ 0 := by have := den_nz r; simpa
  suffices q.num /. ↑q.den * (r.num /. ↑r.den) = q.num * r.num /. ↑(q.den * r.den) by
    simpa [num_den] using this
  simp [mul_def' hq' hr']
#align rat.mul_num_denom Rat.mul_num_den

theorem div_num_den (q r : ℚ) : q / r = q.num * r.den /. (q.den * r.num) :=
  if hr : r.num = 0 then by
    have hr' : r = 0 := zero_of_num_zero hr
    simp [*]
  else
    calc
      q / r = q * r⁻¹ := div_eq_mul_inv q r
      _ = q.num /. q.den * (r.num /. r.den)⁻¹ := by simp [num_den]
      _ = q.num /. q.den * (r.den /. r.num) := by rw [inv_def']
      _ = q.num * r.den /. (q.den * r.num) := mul_def' (by simpa using den_nz q) hr
#align rat.div_num_denom Rat.div_num_den

section Casts

protected theorem add_divInt (a b c : ℤ) : (a + b) /. c = a /. c + b /. c :=
  if h : c = 0 then by simp [h]
  else by
    rw [add_def'' h h, divInt_eq_iff h (mul_ne_zero h h)]
    simp [add_mul, mul_assoc]
#align rat.add_mk Rat.add_divInt

theorem divInt_eq_div (n d : ℤ) : n /. d = (n : ℚ) / d := by
  by_cases d0 : d = 0
  · simp [d0, div_zero]
  simp [division_def, coe_int_eq_divInt, mul_def' one_ne_zero d0]
#align rat.mk_eq_div Rat.divInt_eq_div

theorem divInt_mul_divInt_cancel {x : ℤ} (hx : x ≠ 0) (n d : ℤ) : n /. x * (x /. d) = n /. d := by
  by_cases hd : d = 0
  · rw [hd]
    simp
  rw [mul_def' hx hd, mul_comm x, divInt_mul_right hx]
#align rat.mk_mul_mk_cancel Rat.divInt_mul_divInt_cancel

theorem divInt_div_divInt_cancel_left {x : ℤ} (hx : x ≠ 0) (n d : ℤ) :
    n /. x / (d /. x) = n /. d := by
  rw [div_eq_mul_inv, inv_def', divInt_mul_divInt_cancel hx]
#align rat.mk_div_mk_cancel_left Rat.divInt_div_divInt_cancel_left

theorem divInt_div_divInt_cancel_right {x : ℤ} (hx : x ≠ 0) (n d : ℤ) :
    x /. n / (x /. d) = d /. n := by
  rw [div_eq_mul_inv, inv_def', mul_comm, divInt_mul_divInt_cancel hx]
#align rat.mk_div_mk_cancel_right Rat.divInt_div_divInt_cancel_right

theorem coe_int_div_eq_divInt {n d : ℤ} : (n : ℚ) / (d) = n /. d := by
  repeat' rw [coe_int_eq_divInt]
  exact divInt_div_divInt_cancel_left one_ne_zero n d
#align rat.coe_int_div_eq_mk Rat.coe_int_div_eq_divInt

-- Porting note: see porting note above about `Int.cast`@[simp]
theorem num_div_den (r : ℚ) : (r.num : ℚ) / (r.den : ℚ) = r := by
  rw [← Int.cast_ofNat]
  erw [← divInt_eq_div, num_den]
#align rat.num_div_denom Rat.num_div_den

theorem coe_int_num_of_den_eq_one {q : ℚ} (hq : q.den = 1) : (q.num : ℚ) = q := by
  conv_rhs => rw [← @num_den q, hq]
  rw [coe_int_eq_divInt]
  rfl
#align rat.coe_int_num_of_denom_eq_one Rat.coe_int_num_of_den_eq_one

lemma eq_num_of_isInt {q : ℚ} (h : q.isInt) : q = q.num := by
  rw [Rat.isInt, Nat.beq_eq_true_eq] at h
  exact (Rat.coe_int_num_of_den_eq_one h).symm

theorem den_eq_one_iff (r : ℚ) : r.den = 1 ↔ ↑r.num = r :=
  ⟨Rat.coe_int_num_of_den_eq_one, fun h => h ▸ Rat.coe_int_den r.num⟩
#align rat.denom_eq_one_iff Rat.den_eq_one_iff

instance canLift : CanLift ℚ ℤ (↑) fun q => q.den = 1 :=
  ⟨fun q hq => ⟨q.num, coe_int_num_of_den_eq_one hq⟩⟩
#align rat.can_lift Rat.canLift

theorem coe_nat_eq_divInt (n : ℕ) : ↑n = n /. 1 := by
  rw [← Int.cast_ofNat, coe_int_eq_divInt]
#align rat.coe_nat_eq_mk Rat.coe_nat_eq_divInt

@[simp, norm_cast]
theorem coe_nat_num (n : ℕ) : (n : ℚ).num = n := by
  rw [← Int.cast_ofNat, coe_int_num]
#align rat.coe_nat_num Rat.coe_nat_num

@[simp, norm_cast]
theorem coe_nat_den (n : ℕ) : (n : ℚ).den = 1 := by
  rw [← Int.cast_ofNat, coe_int_den]
#align rat.coe_nat_denom Rat.coe_nat_den

-- Will be subsumed by `Int.coe_inj` after we have defined
-- `LinearOrderedField ℚ` (which implies characteristic zero).
theorem coe_int_inj (m n : ℤ) : (m : ℚ) = n ↔ m = n :=
  ⟨congr_arg num, congr_arg _⟩
#align rat.coe_int_inj Rat.coe_int_inj

end Casts

theorem mkRat_eq_div {n : ℤ} {d : ℕ} : mkRat n d = n / d := by
  simp only [mkRat, zero_mk]
  by_cases h : d = 0
  · simp [h]
  · simp [h, HDiv.hDiv, Rat.div, Div.div]
    unfold Rat.inv
    have h₁ : 0 < d := Nat.pos_iff_ne_zero.2 h
    have h₂ : ¬ (d : ℤ) < 0 := of_decide_eq_false rfl
    simp [h₁, h₂, ← Rat.normalize_eq_mk', Rat.normalize_eq_mkRat, ← mkRat_one,
      Rat.mkRat_mul_mkRat]

end Rat

-- Guard against import creep.
assert_not_exists Field
assert_not_exists PNat
assert_not_exists Nat.dvd_mul
assert_not_exists IsDomain.toCancelMonoidWithZero
