/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.Rat.Init
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Dvd.Basic
import Mathlib.Algebra.Ring.Regular
import Mathlib.Data.Nat.Gcd.Basic
import Mathlib.Data.PNat.Defs

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

#align rat.of_int Rat.ofInt

instance : IntCast ℚ :=
  ⟨ofInt⟩

@[simp]
theorem of_int_eq_cast (n : ℤ) : ofInt n = Int.cast n :=
  rfl
#align rat.of_int_eq_cast Rat.of_int_eq_cast

-- Porting note:
-- At this point the preferred cast is still `ofInt`,
-- but it will later be `Int.cast`.
-- For now we need to explicitly write `Int.cast` so the lemmas are in terms of the
-- eventually preferred coercion.
@[simp, norm_cast]
theorem coe_int_num (n : ℤ) : (Int.cast n : ℚ).num = n :=
  rfl
#align rat.coe_int_num Rat.coe_int_num

@[simp, norm_cast]
theorem coe_int_den (n : ℤ) : (Int.cast n : ℚ).den = 1 :=
  rfl
#align rat.coe_int_denom Rat.coe_int_den

instance : Zero ℚ :=
  ⟨(0 : ℤ)⟩

instance : One ℚ :=
  ⟨(1 : ℤ)⟩

instance : Inhabited ℚ :=
  ⟨0⟩

#noalign rat.mk_pnat

-- Porting note: TODO Should this be namspaced?
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

private theorem gcd_abs_dvd_left {a b} : (Nat.gcd (Int.natAbs a) b : ℤ) ∣ a :=
  Int.dvd_natAbs.1 <| Int.coe_nat_dvd.2 <| Nat.gcd_dvd_left (Int.natAbs a) b
-- Porting note: no #align here as the declaration is private.

@[simp]
theorem divInt_eq_zero {a b : ℤ} (b0 : b ≠ 0) : a /. b = 0 ↔ a = 0 := by
  rw [←zero_divInt b, divInt_eq_iff b0 b0, zero_mul, mul_eq_zero, or_iff_left b0]

#align rat.mk_eq_zero Rat.divInt_eq_zero

theorem divInt_ne_zero {a b : ℤ} (b0 : b ≠ 0) : a /. b ≠ 0 ↔ a ≠ 0 :=
  (divInt_eq_zero b0).not
#align rat.mk_ne_zero Rat.divInt_ne_zero

-- Porting note: this can move to Std4
theorem normalize_eq_normalize_iff
    (a : Int) (b : Nat) (hb : b ≠ 0) (c : Int) (d : Nat) (hd : d ≠ 0) :
    normalize a b hb = normalize c d hd ↔ a * ↑d = c * ↑b := by
  simp only [normalize, maybeNormalize_eq, mk'.injEq]
  constructor
  · rintro ⟨h₁, h₂⟩
    have h₂ := congrArg (fun x : Nat => (x : Int)) h₂
    simp only [Int.ofNat_div] at h₂
    have h₂ := congrArg (c * · * ↑(Nat.gcd (Int.natAbs a) b)) h₂
    dsimp only at h₂
    rw [←Int.mul_div_assoc _ (Nat.coe_nat_dvd (Nat.gcd_dvd_right _ _)),
      Int.div_mul_cancel ((Nat.coe_nat_dvd (Nat.gcd_dvd_right _ _)).trans (Int.dvd_mul_left _ _)),
      ←Int.mul_div_assoc _ (Nat.coe_nat_dvd (Nat.gcd_dvd_right _ _)), Int.mul_comm c ↑d,
      Int.mul_div_assoc _ (Int.ofNat_dvd_of_dvd_natAbs (Nat.gcd_dvd_left _ _)), ←h₁, Int.mul_assoc,
      Int.div_mul_cancel (Int.ofNat_dvd_of_dvd_natAbs (Nat.gcd_dvd_left _ _)),
      Int.mul_comm ↑d] at h₂
    exact h₂.symm
  · intro h
    have hb' : 0 < b := Nat.pos_of_ne_zero hb
    have hd' : 0 < d := Nat.pos_of_ne_zero hd
    suffices ∀ a c, a * d = c * b → a / a.gcd b = c / c.gcd d ∧ b / a.gcd b = d / c.gcd d by
      cases' this a.natAbs c.natAbs (by simpa [Int.natAbs_mul] using congr_arg Int.natAbs h) with
        h₁ h₂
      have hs := congr_arg Int.sign h
      simp [Int.sign_eq_one_of_pos (Int.ofNat_lt.2 hb'),
        Int.sign_eq_one_of_pos (Int.ofNat_lt.2 hd')] at hs
      -- Porting note:
      -- `conv in a => rw [← Int.sign_mul_natAbs a]`
      -- rewrites all the `a`s, not just the first one.
      -- Fixed in https://github.com/leanprover/lean4/pull/1956
      conv => enter [1, 1, 1]; rw [← Int.sign_mul_natAbs a]
      conv => enter [1, 2, 1]; rw [← Int.sign_mul_natAbs c]
      rw [Int.mul_div_assoc, Int.mul_div_assoc]
      exact ⟨congr (congr_arg (· * ·) hs) (congr_arg (fun x : ℕ => (x : ℤ)) h₁), h₂⟩
      all_goals exact Int.coe_nat_dvd.2 (Nat.gcd_dvd_left _ _)
    intro a c h
    suffices bd : b / a.gcd b = d / c.gcd d
    · refine' ⟨_, bd⟩
      apply Nat.eq_of_mul_eq_mul_left hb'
      rw [← Nat.mul_div_assoc _ (Nat.gcd_dvd_left _ _), mul_comm,
        Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _), bd, ←
        Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _), h, mul_comm,
        Nat.mul_div_assoc _ (Nat.gcd_dvd_left _ _)]
    suffices ∀ {a c : ℕ}, ∀ b > 0, ∀ d > 0, a * d = c * b → b / a.gcd b ≤ d / c.gcd d by
      exact le_antisymm (this _ hb' _ hd' h) (this _ hd' _ hb' h.symm)
    intro a c b hb d hd h
    have gb0 := Nat.gcd_pos_of_pos_right a hb
    have gd0 := Nat.gcd_pos_of_pos_right c hd
    apply Nat.le_of_dvd
    apply (Nat.le_div_iff_mul_le gd0).2
    change 1 * _ ≤ _
    rw [Nat.one_mul]
    apply Nat.le_of_dvd hd (Nat.gcd_dvd_right _ _)
    apply (Nat.coprime_div_gcd_div_gcd gb0).symm.dvd_of_dvd_mul_left
    refine' ⟨c / c.gcd d, _⟩
    rw [← Nat.mul_div_assoc _ (Nat.gcd_dvd_left _ _), ← Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _)]
    apply congr_arg (· / c.gcd d)
    rw [mul_comm, ← Nat.mul_div_assoc _ (Nat.gcd_dvd_left _ _), mul_comm, h,
      Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _), mul_comm]


#align rat.mk_eq Rat.divInt_eq_iff

@[simp]
theorem div_divInt_div_cancel_left {a b c : ℤ} (c0 : c ≠ 0) : a * c /. (b * c) = a /. b := by
  by_cases b0 : b = 0;
  · subst b0
    simp
  apply (divInt_eq_iff (mul_ne_zero b0 c0) b0).2
  rw [mul_right_comm, ←mul_assoc]
#align rat.div_mk_div_cancel_left Rat.div_divInt_div_cancel_left

-- Porting note: this can move to Std4
theorem normalize_eq_mk' (n : Int) (d : Nat) (h : d ≠ 0) (c : Nat.gcd (Int.natAbs n) d = 1) :
    normalize n d h = mk' n d h c := by
  simp [normalize, c, maybeNormalize]

@[simp]
theorem num_den : ∀ {a : ℚ}, a.num /. a.den = a
  | ⟨n, d, h, (c : _ = 1)⟩ => show mkRat n d = _ by simp [mkRat, h, c, normalize_eq_mk']
#align rat.num_denom Rat.num_den

theorem num_den' {n d h c} : (⟨n, d, h, c⟩ : ℚ) = n /. d :=
  num_den.symm
#align rat.num_denom' Rat.num_den'

-- Porting note: we explicitly write `Int.cast` here,
-- as that will later be the preferred coercion (but at this point is not).
theorem coe_int_eq_divInt (z : ℤ) : Int.cast z = z /. 1 :=
  num_den'
#align rat.coe_int_eq_mk Rat.coe_int_eq_divInt

/-- Define a (dependent) function or prove `∀ r : ℚ, p r` by dealing with rational
numbers of the form `n /. d` with `0 < d` and coprime `n`, `d`. -/
@[elab_as_elim]
def numDenCasesOn.{u} {C : ℚ → Sort u} :
    ∀ (a : ℚ) (_ : ∀ n d, 0 < d → (Int.natAbs n).coprime d → C (n /. d)), C a
  | ⟨n, d, h, c⟩, H => by rw [num_den'] ; exact H n d (Nat.pos_of_ne_zero h) c
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
  have d₁0 := ne_of_gt (Int.ofNat_lt.2 $ Nat.pos_of_ne_zero h₁)
  have d₂0 := ne_of_gt (Int.ofNat_lt.2 $ Nat.pos_of_ne_zero h₂)
  exact (divInt_eq_iff (f0 d₁0 d₂0) (f0 b0 d0)).2 (H ((divInt_eq_iff b0 d₁0).1 ha) ((divInt_eq_iff d0 d₂0).1 hc))
#align rat.lift_binop_eq Rat.lift_binop_eq

@[simp]
theorem add_def'' {a b c d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) :
    a /. b + c /. d = (a * d + c * b) /. (b * d) := by
  rw [add_def, eq_comm]
  rw [divInt_eq_iff (mul_ne_zero b0 d0)]
  · rw [add_mul]
    rw [add_mul]
    congr 1
    · rw [mul_comm _ (b*d), mul_comm a d, mul_comm b d, mul_assoc, mul_assoc]
      congr 1
      rw [← mul_assoc, ← mul_assoc]
      congr 1
      rw [mul_comm b, ← divInt_eq b0, num_den]
      apply Nat.cast_injective.ne
      apply Rat.den_nz
    · rw [mul_comm, mul_comm b, ← mul_assoc, ← mul_assoc]
      congr 1
      rw [mul_comm (c /. d).num, mul_assoc, mul_assoc]
      congr 1
      rw [mul_comm, ← divInt_eq d0, num_den]
      apply Nat.cast_injective.ne
      apply Rat.den_nz
  · apply Nat.cast_injective.ne
    exact mul_ne_zero (a /. b).den_nz (c /. d).den_nz

#align rat.add_def Rat.add_def

#align rat.neg Rat.neg

-- Porting note: there's already an instance for `Neg ℚ` is in Std.

-- Porting note: Std has explicit arguments here
@[simp]
theorem neg_def {a b : ℤ} : -(a /. b) = -a /. b := neg_divInt a b
#align rat.neg_def Rat.neg_def

@[simp]
theorem divInt_neg_den (n d : ℤ) : n /. -d = -n /. d := by
  by_cases hd : d = 0 <;> simp [Rat.divInt_eq_iff, hd]
#align rat.mk_neg_denom Rat.divInt_neg_den

-- Porting note: since `Sub ℚ` is defined in Std, we need to prove this here.
-- Presumably we will copy the proof from `add_def`.
@[simp]
theorem sub_def'' {a b c d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) :
    a /. b - c /. d = (a * d - c * b) /. (b * d) := by
  rw [sub_def]
  sorry
#align rat.sub_def Rat.sub_def''

#align rat.mul Rat.mul

-- Porting note: there's already an instance for `Mul ℚ` in Std.
@[simp]
theorem mul_def' {a b c d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) : a /. b * (c /. d) = a * c /. (b * d) := by
  rw [mul_def]
#align rat.mul_def Rat.mul_def'

#align rat.inv Rat.inv

instance : Inv ℚ :=
  ⟨Rat.inv⟩

-- Porting note: there's already an instance for `Div ℚ` is in Std.

@[simp]
theorem inv_def' {a b : ℤ} : (a /. b)⁻¹ = b /. a := by
  by_cases a0 : a = 0
  · subst a0
    simp
  by_cases b0 : b = 0
  · subst b0
    simp
  generalize ha : a /. b = x
  cases' x with n d h c
  rw [num_den'] at ha
  refine' Eq.trans (_ : Rat.inv ⟨n, d, h, c⟩ = d /. n) _
  · cases' n with n <;> [cases' n with n, skip]
    · simp
    · unfold Rat.inv
      simp only [Int.ofNat_eq_coe, Nat.cast_succ, Int.succ_ofNat_pos, dite_true]
      erw [dif_neg, num_den', Int.natAbs_cast]; rfl
      exact of_decide_eq_true rfl
    · unfold Rat.inv
      simp only [Int.natAbs_negSucc, Int.negSucc_not_pos, dite_false]
      rw [dif_pos (Int.negSucc_lt_zero _), num_den', ←neg_def, Int.negSucc_coe, divInt_neg_den,
        ←neg_def]
  have n0 : n ≠ 0 := by
    rintro rfl
    rw [Rat.zero_divInt, divInt_eq_zero b0] at ha
    exact a0 ha
  have d0 := ne_of_gt (Int.ofNat_lt.2 (Nat.pos_of_ne_zero h))
  have ha := (divInt_eq_iff b0 d0).1 ha
  apply (divInt_eq_iff n0 a0).2
  -- Porting note: this was by `cc`
  rw [mul_comm, ha, mul_comm]
#align rat.inv_def Rat.inv_def'

variable (a b c : ℚ)

protected theorem add_zero : a + 0 = a :=
  numDenCasesOn' a fun n d h => by rw [← zero_divInt d] ; simp [h, -zero_divInt]
#align rat.add_zero Rat.add_zero

protected theorem zero_add : 0 + a = a :=
  numDenCasesOn' a fun n d h => by rw [← zero_divInt d] ; simp [h, -zero_divInt]
#align rat.zero_add Rat.zero_add

protected theorem add_comm : a + b = b + a :=
  numDenCasesOn' a fun n₁ d₁ h₁ => numDenCasesOn' b fun n₂ d₂ h₂ => by
    simp [h₁, h₂, add_comm, mul_comm]
#align rat.add_comm Rat.add_comm

protected theorem add_assoc : a + b + c = a + (b + c) :=
  numDenCasesOn' a fun n₁ d₁ h₁ =>
    numDenCasesOn' b fun n₂ d₂ h₂ =>
      numDenCasesOn' c fun n₃ d₃ h₃ => by
        simp [h₁, h₂, h₃]
        rw [mul_assoc, add_mul, add_mul, mul_assoc, add_assoc]
        congr 2
        ac_rfl
#align rat.add_assoc Rat.add_assoc

protected theorem add_left_neg : -a + a = 0 :=
  numDenCasesOn' a fun n d h => by simp [h]
#align rat.add_left_neg Rat.add_left_neg

@[simp]
theorem divInt_zero_one : 0 /. 1 = 0 :=
  show divInt _ _ = _ by
    rw [divInt]
    simp
#align rat.mk_zero_one Rat.divInt_zero_one

@[simp]
theorem divInt_one_one : 1 /. 1 = 1 :=
  show divInt _ _ = _ by
    rw [divInt]
    simp
    rfl
#align rat.mk_one_one Rat.divInt_one_one

@[simp]
theorem divInt_neg_one_one : -1 /. 1 = -1 :=
  show divInt _ _ = _ by
    rw [divInt]
    simp
    rfl
#align rat.mk_neg_one_one Rat.divInt_neg_one_one

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
        simp [h₁, h₂, h₃, mul_ne_zero]
        rw [←  div_divInt_div_cancel_left (Int.coe_nat_ne_zero.2 h₃), add_mul, add_mul]
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
    have n0 : n ≠ 0 :=
      mt
        (by
          rintro rfl
          simp)
        a0
    simpa [h, n0, mul_comm] using @div_divInt_div_cancel_left 1 1 _ n0
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
  /- Important: We do not set `nat_cast := λ n, ((n : ℤ) : ℚ)` (even though it's defeq) as that
    makes `int.cast_coe_nat` and `coe_coe` loop in `simp`. -/
  natCast n := ofInt n
  natCast_zero := rfl
  natCast_succ n := by
    simp only [of_int_eq_cast, coe_int_eq_divInt, add_def'' one_ne_zero one_ne_zero, ← divInt_one_one,
      Nat.cast_add, Nat.cast_one, mul_one]

instance : CommGroupWithZero ℚ :=
  { Rat.commRing with
    zero := 0
    one := 1
    mul := (· * ·)
    inv := Inv.inv
    div := (· / ·)
    exists_pair_ne := ⟨0, 1, Rat.zero_ne_one⟩
    inv_zero := rfl
    mul_inv_cancel := Rat.mul_inv_cancel
    mul_zero := mul_zero
    zero_mul := zero_mul }

instance : IsDomain ℚ :=
  NoZeroDivisors.toIsDomain _

-- Extra instances to short-circuit type class resolution
-- TODO(Mario): this instance slows down data.real.basic
instance : Nontrivial ℚ := by infer_instance

--instance : ring ℚ             := by apply_instance
instance : CommSemiring ℚ := by infer_instance

instance : Semiring ℚ := by infer_instance

instance : AddCommGroup ℚ := by infer_instance

instance : AddGroup ℚ := by infer_instance

instance : AddCommMonoid ℚ := by infer_instance

instance : AddMonoid ℚ := by infer_instance

instance : AddLeftCancelSemigroup ℚ := by infer_instance

instance : AddRightCancelSemigroup ℚ := by infer_instance

instance : AddCommSemigroup ℚ := by infer_instance

instance : AddSemigroup ℚ := by infer_instance

instance : CommMonoid ℚ := by infer_instance

instance : Monoid ℚ := by infer_instance

instance : CommSemigroup ℚ := by infer_instance

instance : Semigroup ℚ := by infer_instance

theorem den_ne_zero (q : ℚ) : q.den ≠ 0 :=
  ne_of_gt (Nat.pos_of_ne_zero q.den_nz)
#align rat.denom_ne_zero Rat.den_ne_zero

theorem eq_iff_mul_eq_mul {p q : ℚ} : p = q ↔ p.num * q.den = q.num * p.den := by
  conv =>
    lhs
    rw [← @num_den p, ← @num_den q]
  apply Rat.divInt_eq_iff <;>
    · rw [← Nat.cast_zero, Ne, Int.ofNat_inj]
      apply den_ne_zero
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
  have hq' : (↑q.den : ℤ) ≠ 0 := by have := den_ne_zero q; simpa
  have hr' : (↑r.den : ℤ) ≠ 0 := by have := den_ne_zero r; simpa
  suffices q.num /. ↑q.den * (r.num /. ↑r.den) = q.num * r.num /. ↑(q.den * r.den) by
    simpa using this
  simp [mul_def' hq' hr', -num_den]
#align rat.mul_num_denom Rat.mul_num_den

theorem div_num_den (q r : ℚ) : q / r = q.num * r.den /. (q.den * r.num) :=
  if hr : r.num = 0 then by
    have hr' : r = 0 := zero_of_num_zero hr
    simp [*]
  else
    calc
      q / r = q * r⁻¹ := div_eq_mul_inv q r
      _ = q.num /. q.den * (r.num /. r.den)⁻¹ := by simp
      _ = q.num /. q.den * (r.den /. r.num) := by rw [inv_def']
      _ = q.num * r.den /. (q.den * r.num) := mul_def' (by simpa using den_ne_zero q) hr

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
  rw [mul_def' hx hd, mul_comm x, div_divInt_div_cancel_left hx]
#align rat.mk_mul_mk_cancel Rat.divInt_mul_divInt_cancel

theorem divInt_div_divInt_cancel_left {x : ℤ} (hx : x ≠ 0) (n d : ℤ) :
    n /. x / (d /. x) = n /. d := by
  rw [div_eq_mul_inv, inv_def', divInt_mul_divInt_cancel hx]
#align rat.mk_div_mk_cancel_left Rat.divInt_div_divInt_cancel_left

theorem divInt_div_divInt_cancel_right {x : ℤ} (hx : x ≠ 0) (n d : ℤ) :
    x /. n / (x /. d) = d /. n := by
  rw [div_eq_mul_inv, inv_def', mul_comm, divInt_mul_divInt_cancel hx]
#align rat.mk_div_mk_cancel_right Rat.divInt_div_divInt_cancel_right

theorem coe_int_div_eq_divInt {n d : ℤ} : (Int.cast n : ℚ) / (Int.cast d) = n /. d := by
  repeat' rw [coe_int_eq_divInt]
  exact divInt_div_divInt_cancel_left one_ne_zero n d
#align rat.coe_int_div_eq_mk Rat.coe_int_div_eq_divInt

@[simp]
theorem num_div_den (r : ℚ) : (r.num / r.den : ℚ) = r := by
  rw [← Int.cast_ofNat]
  erw [← divInt_eq_div, num_den]
#align rat.num_div_denom Rat.num_div_den

theorem coe_int_num_of_den_eq_one {q : ℚ} (hq : q.den = 1) : (Int.cast q.num : ℚ) = q := by
  conv_rhs => rw [← @num_den q, hq]
  rw [coe_int_eq_divInt]
  rfl
#align rat.coe_int_num_of_denom_eq_one Rat.coe_int_num_of_den_eq_one

theorem den_eq_one_iff (r : ℚ) : r.den = 1 ↔ ↑r.num = r :=
  ⟨Rat.coe_int_num_of_den_eq_one, fun h => h ▸ Rat.coe_int_den r.num⟩
#align rat.denom_eq_one_iff Rat.den_eq_one_iff

-- Porting note:
-- Waiting on port of the `lift` tactic.
-- instance canLift : CanLift ℚ ℤ coe fun q => q.denom = 1 :=
--   ⟨fun q hq => ⟨q.num, coe_int_num_of_denom_eq_one hq⟩⟩
-- #align rat.can_lift Rat.canLift

theorem coe_nat_eq_divInt (n : ℕ) : ↑n = n /. 1 := by rw [← Int.cast_ofNat, coe_int_eq_divInt]
#align rat.coe_nat_eq_mk Rat.coe_nat_eq_divInt

@[simp, norm_cast]
theorem coe_nat_num (n : ℕ) : (n : ℚ).num = n := by rw [← Int.cast_ofNat, coe_int_num]
#align rat.coe_nat_num Rat.coe_nat_num

@[simp, norm_cast]
theorem coe_nat_den (n : ℕ) : (n : ℚ).den = 1 := by rw [← Int.cast_ofNat, coe_int_den]
#align rat.coe_nat_denom Rat.coe_nat_den

-- Will be subsumed by `Int.coe_inj` after we have defined
-- `LinearOrderedField ℚ` (which implies characteristic zero).
theorem coe_int_inj (m n : ℤ) : (m : ℚ) = n ↔ m = n :=
  ⟨congr_arg num, congr_arg _⟩
#align rat.coe_int_inj Rat.coe_int_inj

end Casts

end Rat

-- Porting note: `assert_not_exists` is not implemented yet.
-- Guard against import creep.
-- assert_not_exists field
