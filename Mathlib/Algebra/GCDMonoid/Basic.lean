/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Ring.Associated

/-!
# Monoids with normalization functions, `gcd`, and `lcm`

This file defines extra structures on `CommMonoidWithZero`s.

## Main Definitions

* `NormalizationMonoid`
* `StrongNormalizationMonoid`
* `GCDMonoid`
* `IsGCDMonoid`
* `NormalizedGCDMonoid`
* `StrongNormalizedGCDMonoid`
* `gcdMonoidOfGCD`, `gcdMonoidOfExistsGCD`, `normalizedGCDMonoidOfGCD`,
  `normalizedGCDMonoidOfExistsGCD`
* `gcdMonoidOfLCM`, `gcdMonoidOfExistsLCM`, `normalizedGCDMonoidOfLCM`,
  `normalizedGCDMonoidOfExistsLCM`

For the `NormalizedGCDMonoid` instances on `ℕ` and `ℤ`, see `Mathlib/Algebra/GCDMonoid/Nat.lean`.

## Implementation Notes

* `NormalizationMonoid` is defined by assigning to each element a `normUnit` such that multiplying
  by that unit normalizes the monoid, and `normalize` is an idempotent function. This
  definition as currently implemented does casework on `0`.

* `StrongNormalizationMonoid` further requires `normalize` to be a monoid homomorphism.

* `GCDMonoid` contains the definitions of `gcd` and `lcm` with the usual properties. They are
  both determined up to a unit.

* `IsGCDMonoid` is the predicate for the existence of a `GCDMonoid` structure.

* `NormalizedGCDMonoid` extends `NormalizationMonoid`, so the `gcd` and `lcm` are always
  normalized. This makes `gcd`s of polynomials easier to work with, but excludes Euclidean domains,
  and monoids without zero.

* `StrongNormalizedGCDMonoid` similarly extends `StrongNormalizationMonoid`.

* `gcdMonoidOfGCD` and `normalizedGCDMonoidOfGCD` noncomputably construct a `GCDMonoid`
  (resp. `NormalizedGCDMonoid`) structure just from the `gcd` and its properties.

* `gcdMonoidOfExistsGCD` and `normalizedGCDMonoidOfExistsGCD` noncomputably construct a
  `GCDMonoid` (resp. `NormalizedGCDMonoid`) structure just from a proof that any two elements
  have a (not necessarily normalized) `gcd`.

* `gcdMonoidOfLCM` and `normalizedGCDMonoidOfLCM` noncomputably construct a `GCDMonoid`
  (resp. `NormalizedGCDMonoid`) structure just from the `lcm` and its properties.

* `gcdMonoidOfExistsLCM` and `normalizedGCDMonoidOfExistsLCM` noncomputably construct a
  `GCDMonoid` (resp. `NormalizedGCDMonoid`) structure just from a proof that any two elements
  have a (not necessarily normalized) `lcm`.

## TODO

* Port GCD facts about nats, definition of coprime
* Generalize normalization monoids to commutative (cancellative) monoids with or without zero

## Tags

divisibility, gcd, lcm, normalize
-/

@[expose] public section


variable {α : Type*}

/-- Normalization monoid: multiplying with `normUnit` gives a normal form for associated
elements. -/
class NormalizationMonoid (α : Type*) [MonoidWithZero α] where
  /-- `normUnit` assigns to each element of the monoid a unit of the monoid. -/
  normUnit : α → αˣ
  normUnit_zero : normUnit 0 = 1
  normUnit_one : normUnit 1 = 1
  /-- The condition that ensures associated elements are normalized to the same element. -/
  normUnit_mul_units {a : α} (u : αˣ) : a ≠ 0 → normUnit (a * u) = u⁻¹ * normUnit a

/-- Construct a `NormalizationMonoid` from a right inverse of `Associates.mk`. -/
noncomputable abbrev NormalizationMonoid.ofRightInverse {α : Type*} [MonoidWithZero α]
    [IsLeftCancelMulZero α] (out : Associates α → α)
    (mk_out : ∀ a, Associates.mk (out a) = a) (out_one : out 1 = 1) :
    NormalizationMonoid α :=
  have assoc a := (Associates.mk_eq_mk_iff_associated.mp <| mk_out (.mk a)).symm
  let := Classical.dec
  { normUnit a := if a = 0 then 1 else (assoc a).choose
    normUnit_zero := if_pos rfl
    normUnit_one := by
      nontriviality α; rw [← Units.val_inj]; convert ← (assoc 1).choose_spec <;> simp [out_one]
    normUnit_mul_units {a} u ha := by
      simp_rw [Units.mul_left_eq_zero, if_neg ha, eq_inv_mul_iff_mul_eq, ← Units.val_inj]
      rw [Units.val_mul, ← (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero ha).eq_iff,
        (assoc a).choose_spec, ← mul_assoc, (assoc _).choose_spec,
        Associates.mk_eq_mk_iff_associated.mpr (associated_mul_unit_right a u u.isUnit)] }

/-- A cancellative monoid with zero always admits a `NormalizationMonoid` structure. -/
instance (α) [MonoidWithZero α] [IsLeftCancelMulZero α] :
    Nonempty (NormalizationMonoid α) := .intro <| by
  exact .ofRightInverse
    (fun a ↦ by classical exact if a = 1 then 1 else a.out)
    (fun _ ↦ by split_ifs with h <;> simp [h]) (by simp)

/-- Strong normalization monoid: multiplying with `normUnit` gives a normal form for associated
elements. It is stronger in that it ensures the normalization map is a monoid homomorphism. -/
class StrongNormalizationMonoid (α) [CommMonoidWithZero α] extends NormalizationMonoid α where
  /-- The proposition that `normUnit` respects multiplication of non-zero elements. -/
  normUnit_mul : ∀ {a b}, a ≠ 0 → b ≠ 0 → normUnit (a * b) = normUnit a * normUnit b
  /-- The proposition that `normUnit` maps units to their inverses. -/
  normUnit_coe_units : ∀ u : αˣ, normUnit u = u⁻¹
  normUnit_one := normUnit_coe_units 1
  normUnit_mul_units {a} u ha :=
    (by nontriviality α; simp [normUnit_mul, ha, normUnit_coe_units, mul_comm])

export NormalizationMonoid (normUnit normUnit_zero normUnit_one normUnit_mul_units)
export StrongNormalizationMonoid (normUnit_mul)

attribute [simp] normUnit_zero normUnit_mul normUnit_one

section NormalizationMonoid

variable [MonoidWithZero α] [NormalizationMonoid α]

@[simp] theorem normUnit_coe_units (u : αˣ) : normUnit u.1 = u⁻¹ := by
  nontriviality α; convert normUnit_mul_units u one_ne_zero using 1 <;> simp

/-- Chooses an element of each associate class, by multiplying by `normUnit` -/
def normalize (x : α) : α := x * normUnit x

theorem associated_normalize (x : α) : Associated x (normalize x) :=
  ⟨_, rfl⟩

theorem normalize_associated (x : α) : Associated (normalize x) x :=
  (associated_normalize _).symm

theorem associated_normalize_iff {x y : α} : Associated x (normalize y) ↔ Associated x y :=
  ⟨fun h => h.trans (normalize_associated y), fun h => h.trans (associated_normalize y)⟩

theorem normalize_associated_iff {x y : α} : Associated (normalize x) y ↔ Associated x y :=
  ⟨fun h => (associated_normalize _).trans h, fun h => (normalize_associated _).trans h⟩

theorem Associates.mk_normalize (x : α) : Associates.mk (normalize x) = Associates.mk x :=
  Associates.mk_eq_mk_iff_associated.2 (normalize_associated _)

theorem normalize_apply (x : α) : normalize x = x * normUnit x :=
  rfl

@[simp] theorem normalize_zero : normalize (0 : α) = 0 := by simp [normalize]

@[simp] theorem normalize_one : normalize (1 : α) = 1 := by simp [normalize]

theorem normalize_coe_units (u : αˣ) : normalize (u : α) = 1 := by simp [normalize]

@[simp]
theorem normalize_eq_zero {x : α} : normalize x = 0 ↔ x = 0 :=
  ⟨fun hx => (associated_zero_iff_eq_zero x).1 <| hx ▸ associated_normalize _, by
    rintro rfl; exact normalize_zero⟩

theorem normalize_eq_one {x : α} : normalize x = 1 ↔ IsUnit x where
  mp hx := Units.eq_inv_of_mul_eq_one_right hx ▸ Units.isUnit _
  mpr := fun ⟨u, hu⟩ ↦ hu ▸ normalize_coe_units u

@[simp]
theorem normUnit_mul_normUnit (a : α) : normUnit (a * normUnit a) = 1 := by
  nontriviality α using Subsingleton.elim a 0
  obtain rfl | h := eq_or_ne a 0
  · rw [normUnit_zero, zero_mul, normUnit_zero]
  · simp [normUnit_mul_units _ h]

@[simp]
theorem normalize_idem (x : α) : normalize (normalize x) = normalize x := by simp [normalize_apply]

theorem normalize_eq_normalize_iff_associated {a b : α} :
    normalize a = normalize b ↔ Associated a b where
  mp h := (associated_normalize a).trans <| .trans (.of_eq h) (associated_normalize b).symm
  mpr := by
    rintro ⟨u, rfl⟩
    nontriviality α
    refine by_cases (by rintro rfl; simp only [zero_mul]) fun ha : a ≠ 0 ↦ ?_
    simp [normalize, normUnit_mul_units _ ha, mul_assoc]

theorem Associated.eq_of_normalized
    {a b : α} (h : Associated a b) (ha : normalize a = a) (hb : normalize b = b) :
    a = b := by
  rw [← ha, normalize_eq_normalize_iff_associated.mpr h, hb]

@[simp]
theorem dvd_normalize_iff {a b : α} : a ∣ normalize b ↔ a ∣ b :=
  Units.dvd_mul_right

@[simp]
theorem normalize_dvd_iff {a b : α} : normalize a ∣ b ↔ a ∣ b :=
  Units.mul_right_dvd

section

variable [IsLeftCancelMulZero α]

theorem normalize_eq_normalize {a b : α} (hab : a ∣ b) (hba : b ∣ a) :
    normalize a = normalize b :=
  normalize_eq_normalize_iff_associated.mpr (associated_of_dvd_dvd hab hba)

theorem normalize_eq_normalize_iff {x y : α} : normalize x = normalize y ↔ x ∣ y ∧ y ∣ x := by
  rw [normalize_eq_normalize_iff_associated, dvd_dvd_iff_associated]

theorem dvd_antisymm_of_normalize_eq {a b : α} (ha : normalize a = a) (hb : normalize b = b)
    (hab : a ∣ b) (hba : b ∣ a) : a = b :=
  ha ▸ hb ▸ normalize_eq_normalize hab hba

end

end NormalizationMonoid

namespace Associates

variable [MonoidWithZero α] [NormalizationMonoid α]

/-- Maps an element of `Associates` back to the normalized element of its associate class -/
protected def out : Associates α → α :=
  (Quotient.lift (normalize : α → α)) fun _ _ ⟨_, hu⟩ =>
    hu ▸ normalize_eq_normalize_iff_associated.mpr ⟨_, rfl⟩

@[simp]
theorem out_mk (a : α) : (Associates.mk a).out = normalize a :=
  rfl

@[simp]
theorem out_one : (1 : Associates α).out = 1 :=
  normalize_one

@[simp]
theorem out_top : (⊤ : Associates α).out = 0 :=
  normalize_zero

@[simp]
theorem normalize_out (a : Associates α) : normalize a.out = a.out :=
  Quotient.inductionOn a normalize_idem

@[simp]
theorem mk_out (a : Associates α) : Associates.mk a.out = a :=
  Quotient.inductionOn a mk_normalize

theorem out_injective : Function.Injective (Associates.out : _ → α) :=
  Function.LeftInverse.injective mk_out

@[simp]
theorem out_eq_zero_iff {a : Associates α} : a.out = 0 ↔ a = 0 :=
  Quotient.inductionOn a (by simp)

theorem out_zero : (0 : Associates α).out = 0 := by
  simp

variable {α : Type*} [CommMonoidWithZero α] [NormalizationMonoid α]

theorem out_mul' (a b : Associates α) : Associated (a * b).out (a.out * b.out) :=
  Quotient.inductionOn₂ a b fun _ _ ↦ normalize_associated_iff.mpr <|
    .mul_mul (associated_normalize _) (associated_normalize _)

theorem dvd_out_iff (a : α) (b : Associates α) : a ∣ b.out ↔ Associates.mk a ≤ b :=
  Quotient.inductionOn b <| by
    simp [Associates.out_mk, Associates.quotient_mk_eq_mk, mk_le_mk_iff_dvd]

theorem out_dvd_iff (a : α) (b : Associates α) : b.out ∣ a ↔ b ≤ Associates.mk a :=
  Quotient.inductionOn b <| by
    simp [Associates.out_mk, Associates.quotient_mk_eq_mk, mk_le_mk_iff_dvd]

end Associates

section StrongNormalizationMonoid

variable [CommMonoidWithZero α] [StrongNormalizationMonoid α]

@[simp] theorem normalize_mul (x y : α) : normalize (x * y) = normalize x * normalize y := by
  obtain rfl | hx := eq_or_ne x 0; · simp
  obtain rfl | hy := eq_or_ne y 0; · simp
  simp_rw [normalize, normUnit_mul hx hy]
  ac_rfl

/-- `normalize` in a `StrongNormalizationMonoid` as a `MonoidWithZeroHom`. -/
def normalizeHom : α →*₀ α where
  toFun := normalize
  map_zero' := normalize_zero
  map_one' := normalize_one
  map_mul' := normalize_mul

theorem coe_normalizeHom : normalizeHom (α := α) = normalize (α := α) :=
  rfl

theorem Associates.out_mul (a b : Associates α) : (a * b).out = a.out * b.out :=
  Quotient.inductionOn₂ a b fun _ _ => by
    simp only [Associates.quotient_mk_eq_mk, out_mk, mk_mul_mk, normalize_mul]

end StrongNormalizationMonoid

/-- GCD monoid: a cancellative `CommMonoidWithZero` with `gcd` (greatest common divisor) and
`lcm` (least common multiple) operations, determined up to a unit. The type class focuses on `gcd`
and we derive the corresponding `lcm` facts from `gcd`.
-/
class GCDMonoid (α : Type*) [CommMonoidWithZero α] extends IsCancelMulZero α where
  /-- The greatest common divisor between two elements. -/
  gcd : α → α → α
  /-- The least common multiple between two elements. -/
  lcm : α → α → α
  /-- The GCD is a divisor of the first element. -/
  gcd_dvd_left : ∀ a b, gcd a b ∣ a
  /-- The GCD is a divisor of the second element. -/
  gcd_dvd_right : ∀ a b, gcd a b ∣ b
  /-- Any common divisor of both elements is a divisor of the GCD. -/
  dvd_gcd : ∀ {a b c}, a ∣ c → a ∣ b → a ∣ gcd c b
  /-- The product of two elements is `Associated` with the product of their GCD and LCM. -/
  gcd_mul_lcm : ∀ a b, Associated (gcd a b * lcm a b) (a * b)
  /-- `0` is left-absorbing. -/
  lcm_zero_left : ∀ a, lcm 0 a = 0
  /-- `0` is right-absorbing. -/
  lcm_zero_right : ∀ a, lcm a 0 = 0

/-- Existence of a `GCDMonoid` structure on a `CommMonoidWithZero`. -/
class inductive IsGCDMonoid (α : Type*) [CommMonoidWithZero α] : Prop
  | intro : GCDMonoid α → IsGCDMonoid α

attribute [instance 100] GCDMonoid.toIsCancelMulZero

/-- Normalized GCD monoid: a cancellative `CommMonoidWithZero` with normalization and `gcd`
(greatest common divisor) and `lcm` (least common multiple) operations. In this setting `gcd` and
`lcm` form a bounded lattice on the associated elements where `gcd` is the infimum, `lcm` is the
supremum, `1` is bottom, and `0` is top. The type class focuses on `gcd` and we derive the
corresponding `lcm` facts from `gcd`. -/
class NormalizedGCDMonoid (α : Type*) [CommMonoidWithZero α] extends NormalizationMonoid α,
  GCDMonoid α where
  /-- The GCD is normalized to itself. -/
  normalize_gcd : ∀ a b, normalize (gcd a b) = gcd a b
  /-- The LCM is normalized to itself. -/
  normalize_lcm : ∀ a b, normalize (lcm a b) = lcm a b

/-- Strong normalized GCD monoid: a `NormalizedGCDMonoid` whose `normalize` function is a
monoid homomorphism. -/
class StrongNormalizedGCDMonoid (α : Type*) [CommMonoidWithZero α] extends
  StrongNormalizationMonoid α, GCDMonoid α where
  /-- The GCD is normalized to itself. -/
  normalize_gcd : ∀ a b, normalize (gcd a b) = gcd a b
  /-- The LCM is normalized to itself. -/
  normalize_lcm : ∀ a b, normalize (lcm a b) = lcm a b

export GCDMonoid (gcd lcm gcd_dvd_left gcd_dvd_right dvd_gcd
  gcd_mul_lcm lcm_zero_left lcm_zero_right)

attribute [simp] lcm_zero_left lcm_zero_right

instance (α) [CommMonoidWithZero α] [StrongNormalizedGCDMonoid α] : NormalizedGCDMonoid α where
  normalize_gcd := StrongNormalizedGCDMonoid.normalize_gcd
  normalize_lcm := StrongNormalizedGCDMonoid.normalize_lcm

section GCDMonoid

variable [CommMonoidWithZero α]

instance [NormalizationMonoid α] : Nonempty (NormalizationMonoid α) := ⟨‹_›⟩
instance [StrongNormalizationMonoid α] : Nonempty (StrongNormalizationMonoid α) := ⟨‹_›⟩

instance (priority := 100) [GCDMonoid α] : IsGCDMonoid α := ⟨‹_›⟩

variable (α) in
-- This is not an instance due to performance reasons.
theorem IsGCDMonoid.isCancelMulZero [h : IsGCDMonoid α] : IsCancelMulZero α :=
  h.rec fun _ ↦ inferInstance

theorem gcd_isUnit_iff_isRelPrime [GCDMonoid α] {a b : α} :
    IsUnit (gcd a b) ↔ IsRelPrime a b :=
  ⟨fun h _ ha hb ↦ isUnit_of_dvd_unit (dvd_gcd ha hb) h, (· (gcd_dvd_left a b) (gcd_dvd_right a b))⟩

@[simp]
theorem normalize_gcd [NormalizedGCDMonoid α] : ∀ a b : α, normalize (gcd a b) = gcd a b :=
  NormalizedGCDMonoid.normalize_gcd

section GCD

theorem dvd_gcd_iff [GCDMonoid α] (a b c : α) : a ∣ gcd b c ↔ a ∣ b ∧ a ∣ c :=
  Iff.intro (fun h => ⟨h.trans (gcd_dvd_left _ _), h.trans (gcd_dvd_right _ _)⟩) fun ⟨hab, hac⟩ =>
    dvd_gcd hab hac

theorem gcd_comm [NormalizedGCDMonoid α] (a b : α) : gcd a b = gcd b a :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _)
    (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))
    (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))

theorem gcd_comm' [GCDMonoid α] (a b : α) : Associated (gcd a b) (gcd b a) :=
  associated_of_dvd_dvd (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))
    (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))

theorem gcd_assoc [NormalizedGCDMonoid α] (m n k : α) : gcd (gcd m n) k = gcd m (gcd n k) :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _)
    (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_left m n))
      (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_right m n)) (gcd_dvd_right (gcd m n) k)))
    (dvd_gcd
      (dvd_gcd (gcd_dvd_left m (gcd n k)) ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_left n k)))
      ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_right n k)))

theorem gcd_assoc' [GCDMonoid α] (m n k : α) : Associated (gcd (gcd m n) k) (gcd m (gcd n k)) :=
  associated_of_dvd_dvd
    (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_left m n))
      (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_right m n)) (gcd_dvd_right (gcd m n) k)))
    (dvd_gcd
      (dvd_gcd (gcd_dvd_left m (gcd n k)) ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_left n k)))
      ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_right n k)))

instance [NormalizedGCDMonoid α] : Std.Commutative (α := α) gcd where
  comm := gcd_comm

instance [NormalizedGCDMonoid α] : Std.Associative (α := α) gcd where
  assoc := gcd_assoc

theorem gcd_eq_normalize [NormalizedGCDMonoid α] {a b c : α} (habc : gcd a b ∣ c)
    (hcab : c ∣ gcd a b) : gcd a b = normalize c :=
  normalize_gcd a b ▸ normalize_eq_normalize habc hcab

@[simp]
theorem gcd_zero_left [NormalizedGCDMonoid α] (a : α) : gcd 0 a = normalize a :=
  gcd_eq_normalize (gcd_dvd_right 0 a) (dvd_gcd (dvd_zero _) (dvd_refl a))

theorem gcd_zero_left' [GCDMonoid α] (a : α) : Associated (gcd 0 a) a :=
  associated_of_dvd_dvd (gcd_dvd_right 0 a) (dvd_gcd (dvd_zero _) (dvd_refl a))

@[simp]
theorem gcd_zero_right [NormalizedGCDMonoid α] (a : α) : gcd a 0 = normalize a :=
  gcd_eq_normalize (gcd_dvd_left a 0) (dvd_gcd (dvd_refl a) (dvd_zero _))

theorem gcd_zero_right' [GCDMonoid α] (a : α) : Associated (gcd a 0) a :=
  associated_of_dvd_dvd (gcd_dvd_left a 0) (dvd_gcd (dvd_refl a) (dvd_zero _))

@[simp]
theorem gcd_eq_zero_iff [GCDMonoid α] (a b : α) : gcd a b = 0 ↔ a = 0 ∧ b = 0 :=
  Iff.intro
    (fun h => by
      let ⟨ca, ha⟩ := gcd_dvd_left a b
      let ⟨cb, hb⟩ := gcd_dvd_right a b
      rw [h, zero_mul] at ha hb
      exact ⟨ha, hb⟩)
    fun ⟨ha, hb⟩ => by
    rw [ha, hb, ← zero_dvd_iff]
    apply dvd_gcd <;> rfl

theorem gcd_ne_zero_of_left [GCDMonoid α] {a b : α} (ha : a ≠ 0) : gcd a b ≠ 0 := by
  simp_all

theorem gcd_ne_zero_of_right [GCDMonoid α] {a b : α} (hb : b ≠ 0) : gcd a b ≠ 0 := by
  simp_all

@[simp]
theorem gcd_one_left [NormalizedGCDMonoid α] (a : α) : gcd 1 a = 1 :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) normalize_one (gcd_dvd_left _ _) (one_dvd _)

@[simp]
theorem isUnit_gcd_one_left [GCDMonoid α] (a : α) : IsUnit (gcd 1 a) :=
  isUnit_of_dvd_one (gcd_dvd_left _ _)

theorem gcd_one_left' [GCDMonoid α] (a : α) : Associated (gcd 1 a) 1 := by simp

@[simp]
theorem gcd_one_right [NormalizedGCDMonoid α] (a : α) : gcd a 1 = 1 :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) normalize_one (gcd_dvd_right _ _) (one_dvd _)

@[simp]
theorem isUnit_gcd_one_right [GCDMonoid α] (a : α) : IsUnit (gcd a 1) :=
  isUnit_of_dvd_one (gcd_dvd_right _ _)

theorem gcd_one_right' [GCDMonoid α] (a : α) : Associated (gcd a 1) 1 := by simp

@[gcongr]
theorem gcd_dvd_gcd [GCDMonoid α] {a b c d : α} (hab : a ∣ b) (hcd : c ∣ d) : gcd a c ∣ gcd b d :=
  dvd_gcd ((gcd_dvd_left _ _).trans hab) ((gcd_dvd_right _ _).trans hcd)

protected theorem Associated.gcd [GCDMonoid α]
    {a₁ a₂ b₁ b₂ : α} (ha : Associated a₁ a₂) (hb : Associated b₁ b₂) :
    Associated (gcd a₁ b₁) (gcd a₂ b₂) :=
  associated_of_dvd_dvd (gcd_dvd_gcd ha.dvd hb.dvd) (gcd_dvd_gcd ha.dvd' hb.dvd')

@[simp]
theorem gcd_same [NormalizedGCDMonoid α] (a : α) : gcd a a = normalize a :=
  gcd_eq_normalize (gcd_dvd_left _ _) (dvd_gcd (dvd_refl a) (dvd_refl a))

@[simp]
theorem gcd_mul_left [StrongNormalizedGCDMonoid α] (a b c : α) :
    gcd (a * b) (a * c) = normalize a * gcd b c :=
  (by_cases (by rintro rfl; simp))
    fun ha : a ≠ 0 =>
    suffices gcd (a * b) (a * c) = normalize (a * gcd b c) by simpa
    let ⟨d, eq⟩ := dvd_gcd (dvd_mul_right a b) (dvd_mul_right a c)
    gcd_eq_normalize
      (eq.symm ▸ mul_dvd_mul_left a
        (show d ∣ gcd b c from
          dvd_gcd ((mul_dvd_mul_iff_left ha).1 <| eq ▸ gcd_dvd_left _ _)
            ((mul_dvd_mul_iff_left ha).1 <| eq ▸ gcd_dvd_right _ _)))
      (dvd_gcd (mul_dvd_mul_left a <| gcd_dvd_left _ _) (mul_dvd_mul_left a <| gcd_dvd_right _ _))

theorem gcd_mul_left' [GCDMonoid α] (a b c : α) :
    Associated (gcd (a * b) (a * c)) (a * gcd b c) := by
  obtain rfl | ha := eq_or_ne a 0
  · simp only [zero_mul, gcd_zero_left']
  obtain ⟨d, eq⟩ := dvd_gcd (dvd_mul_right a b) (dvd_mul_right a c)
  apply associated_of_dvd_dvd
  · rw [eq]
    gcongr
    exact
      dvd_gcd ((mul_dvd_mul_iff_left ha).1 <| eq ▸ gcd_dvd_left _ _)
        ((mul_dvd_mul_iff_left ha).1 <| eq ▸ gcd_dvd_right _ _)
  · exact dvd_gcd (mul_dvd_mul_left a <| gcd_dvd_left _ _) (mul_dvd_mul_left a <| gcd_dvd_right _ _)

@[simp]
theorem gcd_mul_right [StrongNormalizedGCDMonoid α] (a b c : α) :
    gcd (b * a) (c * a) = gcd b c * normalize a := by simp only [mul_comm, gcd_mul_left]

@[simp]
theorem gcd_mul_right' [GCDMonoid α] (a b c : α) :
    Associated (gcd (b * a) (c * a)) (gcd b c * a) := by
  simp only [mul_comm, gcd_mul_left']

theorem gcd_eq_left_iff [NormalizedGCDMonoid α] (a b : α) (h : normalize a = a) :
    gcd a b = a ↔ a ∣ b :=
  (Iff.intro fun eq => eq ▸ gcd_dvd_right _ _) fun hab =>
    dvd_antisymm_of_normalize_eq (normalize_gcd _ _) h (gcd_dvd_left _ _) (dvd_gcd (dvd_refl a) hab)

theorem gcd_eq_right_iff [NormalizedGCDMonoid α] (a b : α) (h : normalize b = b) :
    gcd a b = b ↔ b ∣ a := by simpa only [gcd_comm a b] using gcd_eq_left_iff b a h

theorem gcd_dvd_gcd_mul_left [GCDMonoid α] (m n k : α) : gcd m n ∣ gcd (k * m) n := by
  grw [← dvd_mul_left]

theorem gcd_dvd_gcd_mul_right [GCDMonoid α] (m n k : α) : gcd m n ∣ gcd (m * k) n := by
  grw [← dvd_mul_right]

theorem gcd_dvd_gcd_mul_left_right [GCDMonoid α] (m n k : α) : gcd m n ∣ gcd m (k * n) := by
  grw [← dvd_mul_left]

theorem gcd_dvd_gcd_mul_right_right [GCDMonoid α] (m n k : α) : gcd m n ∣ gcd m (n * k) := by
  grw [← dvd_mul_right]

theorem Associated.gcd_eq_left [NormalizedGCDMonoid α] {m n : α} (h : Associated m n) (k : α) :
    gcd m k = gcd n k :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) (gcd_dvd_gcd h.dvd dvd_rfl)
    (gcd_dvd_gcd h.symm.dvd dvd_rfl)

theorem Associated.gcd_eq_right [NormalizedGCDMonoid α] {m n : α} (h : Associated m n) (k : α) :
    gcd k m = gcd k n :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) (gcd_dvd_gcd dvd_rfl h.dvd)
    (gcd_dvd_gcd dvd_rfl h.symm.dvd)

theorem dvd_gcd_mul_of_dvd_mul [GCDMonoid α] {m n k : α} (H : k ∣ m * n) : k ∣ gcd k m * n :=
  (dvd_gcd (dvd_mul_right _ n) H).trans (gcd_mul_right' n k m).dvd

theorem dvd_gcd_mul_iff_dvd_mul [GCDMonoid α] {m n k : α} : k ∣ gcd k m * n ↔ k ∣ m * n :=
  ⟨fun h => h.trans (mul_dvd_mul (gcd_dvd_right k m) dvd_rfl), dvd_gcd_mul_of_dvd_mul⟩

theorem dvd_mul_gcd_of_dvd_mul [GCDMonoid α] {m n k : α} (H : k ∣ m * n) : k ∣ m * gcd k n := by
  rw [mul_comm] at H ⊢
  exact dvd_gcd_mul_of_dvd_mul H

theorem dvd_mul_gcd_iff_dvd_mul [GCDMonoid α] {m n k : α} : k ∣ m * gcd k n ↔ k ∣ m * n :=
  ⟨fun h => h.trans (mul_dvd_mul dvd_rfl (gcd_dvd_right k n)), dvd_mul_gcd_of_dvd_mul⟩

/-- Represent a divisor of `m * n` as a product of a divisor of `m` and a divisor of `n`.

Note: In general, this representation is highly non-unique.

See `Nat.dvdProdDvdOfDvdProd` for a constructive version on `ℕ`. -/
instance [h : IsGCDMonoid α] : DecompositionMonoid α where
  primal k m n H := by
    cases h
    by_cases h0 : gcd k m = 0
    · rw [gcd_eq_zero_iff] at h0
      rcases h0 with ⟨rfl, rfl⟩
      exact ⟨0, n, dvd_refl 0, dvd_refl n, by simp⟩
    · obtain ⟨a, ha⟩ := gcd_dvd_left k m
      refine ⟨gcd k m, a, gcd_dvd_right _ _, ?_, ha⟩
      rw [← mul_dvd_mul_iff_left h0, ← ha]
      exact dvd_gcd_mul_of_dvd_mul H

theorem gcd_mul_dvd_mul_gcd [GCDMonoid α] (k m n : α) : gcd k (m * n) ∣ gcd k m * gcd k n := by
  obtain ⟨m', n', hm', hn', h⟩ := exists_dvd_and_dvd_of_dvd_mul (gcd_dvd_right k (m * n))
  replace h : gcd k (m * n) = m' * n' := h
  rw [h]
  have hm'n' : m' * n' ∣ k := h ▸ gcd_dvd_left _ _
  apply mul_dvd_mul
  · have hm'k : m' ∣ k := (dvd_mul_right m' n').trans hm'n'
    exact dvd_gcd hm'k hm'
  · have hn'k : n' ∣ k := (dvd_mul_left n' m').trans hm'n'
    exact dvd_gcd hn'k hn'

theorem gcd_pow_right_dvd_pow_gcd [GCDMonoid α] {a b : α} {k : ℕ} :
    gcd a (b ^ k) ∣ gcd a b ^ k := by
  by_cases hg : gcd a b = 0
  · rw [gcd_eq_zero_iff] at hg
    rcases hg with ⟨rfl, rfl⟩
    exact
      (gcd_zero_left' (0 ^ k : α)).dvd.trans
        (pow_dvd_pow_of_dvd (gcd_zero_left' (0 : α)).symm.dvd _)
  · induction k with
    | zero => rw [pow_zero, pow_zero]; exact (gcd_one_right' a).dvd
    | succ k hk =>
      rw [pow_succ', pow_succ']
      trans gcd a b * gcd a (b ^ k)
      · exact gcd_mul_dvd_mul_gcd a b (b ^ k)
      · exact (mul_dvd_mul_iff_left hg).mpr hk

theorem gcd_pow_left_dvd_pow_gcd [GCDMonoid α] {a b : α} {k : ℕ} : gcd (a ^ k) b ∣ gcd a b ^ k :=
  calc
    gcd (a ^ k) b ∣ gcd b (a ^ k) := (gcd_comm' _ _).dvd
    _ ∣ gcd b a ^ k := gcd_pow_right_dvd_pow_gcd
    _ ∣ gcd a b ^ k := pow_dvd_pow_of_dvd (gcd_comm' _ _).dvd _

theorem pow_dvd_of_mul_eq_pow [GCDMonoid α] {a b c d₁ d₂ : α} (ha : a ≠ 0) (hab : IsUnit (gcd a b))
    {k : ℕ} (h : a * b = c ^ k) (hc : c = d₁ * d₂) (hd₁ : d₁ ∣ a) : d₁ ^ k ≠ 0 ∧ d₁ ^ k ∣ a := by
  have h1 : IsUnit (gcd (d₁ ^ k) b) := by
    apply isUnit_of_dvd_one
    trans gcd d₁ b ^ k
    · exact gcd_pow_left_dvd_pow_gcd
    · apply IsUnit.dvd
      apply IsUnit.pow
      apply isUnit_of_dvd_one
      grw [hd₁, hab.dvd]
  have h2 : d₁ ^ k ∣ a * b := by
    use d₂ ^ k
    rw [h, hc]
    exact mul_pow d₁ d₂ k
  rw [mul_comm] at h2
  have h3 : d₁ ^ k ∣ a := by
    apply (dvd_gcd_mul_of_dvd_mul h2).trans
    rw [h1.mul_left_dvd]
  have h4 : d₁ ^ k ≠ 0 := by
    intro hdk
    rw [hdk] at h3
    apply absurd (zero_dvd_iff.mp h3) ha
  exact ⟨h4, h3⟩

theorem exists_associated_pow_of_mul_eq_pow [GCDMonoid α] {a b c : α} (hab : IsUnit (gcd a b))
    {k : ℕ} (h : a * b = c ^ k) : ∃ d : α, Associated (d ^ k) a := by
  cases subsingleton_or_nontrivial α
  · use 0
    rw [Subsingleton.elim a (0 ^ k)]
  by_cases ha : a = 0
  · use 0
    obtain rfl | hk := eq_or_ne k 0
    · simp [ha] at h
    · rw [ha, zero_pow hk]
  by_cases hb : b = 0
  · use 1
    rw [one_pow]
    apply (associated_one_iff_isUnit.mpr hab).symm.trans
    rw [hb]
    exact gcd_zero_right' a
  obtain rfl | hk := k.eq_zero_or_pos
  · use 1
    rw [pow_zero] at h ⊢
    use Units.mkOfMulEqOne _ _ h
    rw [Units.val_mkOfMulEqOne, one_mul]
  have hc : c ∣ a * b := by
    rw [h]
    exact dvd_pow_self _ hk.ne'
  obtain ⟨d₁, d₂, hd₁, hd₂, hc⟩ := exists_dvd_and_dvd_of_dvd_mul hc
  use d₁
  obtain ⟨h0₁, ⟨a', ha'⟩⟩ := pow_dvd_of_mul_eq_pow ha hab h hc hd₁
  rw [mul_comm] at h hc
  rw [(gcd_comm' a b).isUnit_iff] at hab
  obtain ⟨h0₂, ⟨b', hb'⟩⟩ := pow_dvd_of_mul_eq_pow hb hab h hc hd₂
  rw [ha', hb', hc, mul_pow] at h
  have h' : a' * b' = 1 := by
    apply (mul_right_inj' h0₁).mp
    rw [mul_one]
    apply (mul_right_inj' h0₂).mp
    rw [← h]
    rw [mul_assoc, mul_comm a', ← mul_assoc _ b', ← mul_assoc b', mul_comm b']
  use Units.mkOfMulEqOne _ _ h'
  rw [Units.val_mkOfMulEqOne, ha']

theorem exists_eq_pow_of_mul_eq_pow [GCDMonoid α] [Subsingleton αˣ]
    {a b c : α} (hab : IsUnit (gcd a b)) {k : ℕ} (h : a * b = c ^ k) : ∃ d : α, a = d ^ k :=
  let ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow hab h
  ⟨d, (associated_iff_eq.mp hd).symm⟩

theorem gcd_greatest {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α] {a b d : α}
    (hda : d ∣ a) (hdb : d ∣ b) (hd : ∀ e : α, e ∣ a → e ∣ b → e ∣ d) :
    gcd a b = normalize d :=
  haveI h := hd _ (gcd_dvd_left a b) (gcd_dvd_right a b)
  gcd_eq_normalize h (GCDMonoid.dvd_gcd hda hdb)

theorem gcd_greatest_associated {α : Type*} [CommMonoidWithZero α] [GCDMonoid α] {a b d : α}
    (hda : d ∣ a) (hdb : d ∣ b) (hd : ∀ e : α, e ∣ a → e ∣ b → e ∣ d) :
    Associated d (gcd a b) :=
  haveI h := hd _ (gcd_dvd_left a b) (gcd_dvd_right a b)
  associated_of_dvd_dvd (GCDMonoid.dvd_gcd hda hdb) h

theorem isUnit_gcd_of_eq_mul_gcd {α : Type*} [CommMonoidWithZero α] [GCDMonoid α]
    {x y x' y' : α} (ex : x = gcd x y * x') (ey : y = gcd x y * y') (h : gcd x y ≠ 0) :
    IsUnit (gcd x' y') := by
  rw [← associated_one_iff_isUnit]
  refine Associated.of_mul_left ?_ (Associated.refl <| gcd x y) h
  convert (gcd_mul_left' (gcd x y) x' y').symm
  rw [← ex, ← ey, mul_one]

theorem extract_gcd {α : Type*} [CommMonoidWithZero α] [GCDMonoid α] (x y : α) :
    ∃ x' y', x = gcd x y * x' ∧ y = gcd x y * y' ∧ IsUnit (gcd x' y') := by
  by_cases h : gcd x y = 0
  · obtain ⟨rfl, rfl⟩ := (gcd_eq_zero_iff x y).1 h
    simp_rw [← associated_one_iff_isUnit]
    exact ⟨1, 1, by rw [h, zero_mul], by rw [h, zero_mul], gcd_one_left' 1⟩
  obtain ⟨x', ex⟩ := gcd_dvd_left x y
  obtain ⟨y', ey⟩ := gcd_dvd_right x y
  exact ⟨x', y', ex, ey, isUnit_gcd_of_eq_mul_gcd ex ey h⟩

theorem associated_gcd_left_iff [GCDMonoid α] {x y : α} : Associated x (gcd x y) ↔ x ∣ y :=
  ⟨fun hx => hx.dvd.trans (gcd_dvd_right x y),
    fun hxy => associated_of_dvd_dvd (dvd_gcd dvd_rfl hxy) (gcd_dvd_left x y)⟩

theorem associated_gcd_right_iff [GCDMonoid α] {x y : α} : Associated y (gcd x y) ↔ y ∣ x :=
  ⟨fun hx => hx.dvd.trans (gcd_dvd_left x y),
    fun hxy => associated_of_dvd_dvd (dvd_gcd hxy dvd_rfl) (gcd_dvd_right x y)⟩

theorem Irreducible.isUnit_gcd_iff [GCDMonoid α] {x y : α} (hx : Irreducible x) :
    IsUnit (gcd x y) ↔ ¬(x ∣ y) := by
  rw [hx.isUnit_iff_not_associated_of_dvd (gcd_dvd_left x y), not_iff_not, associated_gcd_left_iff]

theorem Irreducible.gcd_eq_one_iff [NormalizedGCDMonoid α] {x y : α} (hx : Irreducible x) :
    gcd x y = 1 ↔ ¬(x ∣ y) := by
  rw [← hx.isUnit_gcd_iff, ← normalize_eq_one, NormalizedGCDMonoid.normalize_gcd]

section Neg

variable [HasDistribNeg α]

lemma gcd_neg' [GCDMonoid α] {a b : α} : Associated (gcd a (-b)) (gcd a b) :=
  Associated.gcd .rfl (.neg_left .rfl)

lemma gcd_neg [NormalizedGCDMonoid α] {a b : α} : gcd a (-b) = gcd a b :=
  gcd_neg'.eq_of_normalized (normalize_gcd _ _) (normalize_gcd _ _)

lemma neg_gcd' [GCDMonoid α] {a b : α} : Associated (gcd (-a) b) (gcd a b) :=
  Associated.gcd (.neg_left .rfl) .rfl

lemma neg_gcd [NormalizedGCDMonoid α] {a b : α} : gcd (-a) b = gcd a b :=
  neg_gcd'.eq_of_normalized (normalize_gcd _ _) (normalize_gcd _ _)

end Neg

end GCD

section LCM

theorem lcm_dvd_iff [GCDMonoid α] {a b c : α} : lcm a b ∣ c ↔ a ∣ c ∧ b ∣ c := by
  by_cases h : a = 0 ∨ b = 0
  · rcases h with (rfl | rfl) <;>
      simp +contextual only [iff_def, lcm_zero_left, lcm_zero_right,
        zero_dvd_iff, dvd_zero, and_true, imp_true_iff]
  · obtain ⟨h1, h2⟩ := not_or.1 h
    have h : gcd a b ≠ 0 := fun H => h1 ((gcd_eq_zero_iff _ _).1 H).1
    rw [← mul_dvd_mul_iff_left h, (gcd_mul_lcm a b).dvd_iff_dvd_left, ←
      (gcd_mul_right' c a b).dvd_iff_dvd_right, dvd_gcd_iff, mul_comm b c, mul_dvd_mul_iff_left h1,
      mul_dvd_mul_iff_right h2, and_comm]

theorem dvd_lcm_left [GCDMonoid α] (a b : α) : a ∣ lcm a b :=
  (lcm_dvd_iff.1 (dvd_refl (lcm a b))).1

theorem dvd_lcm_right [GCDMonoid α] (a b : α) : b ∣ lcm a b :=
  (lcm_dvd_iff.1 (dvd_refl (lcm a b))).2

theorem lcm_dvd [GCDMonoid α] {a b c : α} (hab : a ∣ b) (hcb : c ∣ b) : lcm a c ∣ b :=
  lcm_dvd_iff.2 ⟨hab, hcb⟩

@[simp]
theorem lcm_eq_zero_iff [GCDMonoid α] (a b : α) : lcm a b = 0 ↔ a = 0 ∨ b = 0 :=
  Iff.intro
    (fun h : lcm a b = 0 => by
      have : Associated (a * b) 0 := (gcd_mul_lcm a b).symm.trans <| by rw [h, mul_zero]
      rwa [← mul_eq_zero, ← associated_zero_iff_eq_zero])
    (by rintro (rfl | rfl) <;> [apply lcm_zero_left; apply lcm_zero_right])

theorem lcm_ne_zero_iff [GCDMonoid α] {a b : α} : lcm a b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 := by
  simp

@[simp]
theorem normalize_lcm [NormalizedGCDMonoid α] (a b : α) : normalize (lcm a b) = lcm a b :=
  NormalizedGCDMonoid.normalize_lcm a b

theorem lcm_comm [NormalizedGCDMonoid α] (a b : α) : lcm a b = lcm b a :=
  dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _)
    (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))
    (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))

theorem lcm_comm' [GCDMonoid α] (a b : α) : Associated (lcm a b) (lcm b a) :=
  associated_of_dvd_dvd (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))
    (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))

theorem lcm_assoc [NormalizedGCDMonoid α] (m n k : α) : lcm (lcm m n) k = lcm m (lcm n k) :=
  dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _)
    (lcm_dvd (lcm_dvd (dvd_lcm_left _ _) ((dvd_lcm_left _ _).trans (dvd_lcm_right _ _)))
      ((dvd_lcm_right _ _).trans (dvd_lcm_right _ _)))
    (lcm_dvd ((dvd_lcm_left _ _).trans (dvd_lcm_left _ _))
      (lcm_dvd ((dvd_lcm_right _ _).trans (dvd_lcm_left _ _)) (dvd_lcm_right _ _)))

theorem lcm_assoc' [GCDMonoid α] (m n k : α) : Associated (lcm (lcm m n) k) (lcm m (lcm n k)) :=
  associated_of_dvd_dvd
    (lcm_dvd (lcm_dvd (dvd_lcm_left _ _) ((dvd_lcm_left _ _).trans (dvd_lcm_right _ _)))
      ((dvd_lcm_right _ _).trans (dvd_lcm_right _ _)))
    (lcm_dvd ((dvd_lcm_left _ _).trans (dvd_lcm_left _ _))
      (lcm_dvd ((dvd_lcm_right _ _).trans (dvd_lcm_left _ _)) (dvd_lcm_right _ _)))

instance [NormalizedGCDMonoid α] : Std.Commutative (α := α) lcm where
  comm := lcm_comm

instance [NormalizedGCDMonoid α] : Std.Associative (α := α) lcm where
  assoc := lcm_assoc

theorem lcm_eq_normalize [NormalizedGCDMonoid α] {a b c : α} (habc : lcm a b ∣ c)
    (hcab : c ∣ lcm a b) : lcm a b = normalize c :=
  normalize_lcm a b ▸ normalize_eq_normalize habc hcab

theorem lcm_dvd_lcm [GCDMonoid α] {a b c d : α} (hab : a ∣ b) (hcd : c ∣ d) : lcm a c ∣ lcm b d :=
  lcm_dvd (hab.trans (dvd_lcm_left _ _)) (hcd.trans (dvd_lcm_right _ _))

protected theorem Associated.lcm [GCDMonoid α]
    {a₁ a₂ b₁ b₂ : α} (ha : Associated a₁ a₂) (hb : Associated b₁ b₂) :
    Associated (lcm a₁ b₁) (lcm a₂ b₂) :=
  associated_of_dvd_dvd (lcm_dvd_lcm ha.dvd hb.dvd) (lcm_dvd_lcm ha.dvd' hb.dvd')

@[simp]
theorem lcm_units_coe_left [NormalizedGCDMonoid α] (u : αˣ) (a : α) : lcm (↑u) a = normalize a :=
  lcm_eq_normalize (lcm_dvd Units.coe_dvd dvd_rfl) (dvd_lcm_right _ _)

@[simp]
theorem lcm_units_coe_right [NormalizedGCDMonoid α] (a : α) (u : αˣ) : lcm a ↑u = normalize a :=
  (lcm_comm a u).trans <| lcm_units_coe_left _ _

@[simp]
theorem lcm_one_left [NormalizedGCDMonoid α] (a : α) : lcm 1 a = normalize a :=
  lcm_units_coe_left 1 a

@[simp]
theorem lcm_one_right [NormalizedGCDMonoid α] (a : α) : lcm a 1 = normalize a :=
  lcm_units_coe_right a 1

@[simp]
theorem lcm_same [NormalizedGCDMonoid α] (a : α) : lcm a a = normalize a :=
  lcm_eq_normalize (lcm_dvd dvd_rfl dvd_rfl) (dvd_lcm_left _ _)

@[simp]
theorem lcm_eq_one_iff [NormalizedGCDMonoid α] (a b : α) : lcm a b = 1 ↔ a ∣ 1 ∧ b ∣ 1 :=
  Iff.intro (fun eq => eq ▸ ⟨dvd_lcm_left _ _, dvd_lcm_right _ _⟩) fun ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ =>
    show lcm (Units.mkOfMulEqOne a c hc.symm : α) (Units.mkOfMulEqOne b d hd.symm) = 1 by
      rw [lcm_units_coe_left, normalize_coe_units]

@[simp]
theorem lcm_mul_left [StrongNormalizedGCDMonoid α] (a b c : α) :
    lcm (a * b) (a * c) = normalize a * lcm b c :=
  (by_cases (by rintro rfl; simp))
    fun ha : a ≠ 0 =>
    suffices lcm (a * b) (a * c) = normalize (a * lcm b c) by simpa
    have : a ∣ lcm (a * b) (a * c) := (dvd_mul_right _ _).trans (dvd_lcm_left _ _)
    let ⟨_, eq⟩ := this
    lcm_eq_normalize
      (lcm_dvd (mul_dvd_mul_left a (dvd_lcm_left _ _)) (mul_dvd_mul_left a (dvd_lcm_right _ _)))
      (eq.symm ▸
        (mul_dvd_mul_left a <|
          lcm_dvd ((mul_dvd_mul_iff_left ha).1 <| eq ▸ dvd_lcm_left _ _)
            ((mul_dvd_mul_iff_left ha).1 <| eq ▸ dvd_lcm_right _ _)))

@[simp]
theorem lcm_mul_right [StrongNormalizedGCDMonoid α] (a b c : α) :
    lcm (b * a) (c * a) = lcm b c * normalize a := by simp only [mul_comm, lcm_mul_left]

theorem lcm_eq_left_iff [NormalizedGCDMonoid α] (a b : α) (h : normalize a = a) :
    lcm a b = a ↔ b ∣ a :=
  (Iff.intro fun eq => eq ▸ dvd_lcm_right _ _) fun hab =>
    dvd_antisymm_of_normalize_eq (normalize_lcm _ _) h (lcm_dvd (dvd_refl a) hab) (dvd_lcm_left _ _)

theorem lcm_eq_right_iff [NormalizedGCDMonoid α] (a b : α) (h : normalize b = b) :
    lcm a b = b ↔ a ∣ b := by simpa only [lcm_comm b a] using lcm_eq_left_iff b a h

theorem lcm_dvd_lcm_mul_left [GCDMonoid α] (m n k : α) : lcm m n ∣ lcm (k * m) n :=
  lcm_dvd_lcm (dvd_mul_left _ _) dvd_rfl

theorem lcm_dvd_lcm_mul_right [GCDMonoid α] (m n k : α) : lcm m n ∣ lcm (m * k) n :=
  lcm_dvd_lcm (dvd_mul_right _ _) dvd_rfl

theorem lcm_dvd_lcm_mul_left_right [GCDMonoid α] (m n k : α) : lcm m n ∣ lcm m (k * n) :=
  lcm_dvd_lcm dvd_rfl (dvd_mul_left _ _)

theorem lcm_dvd_lcm_mul_right_right [GCDMonoid α] (m n k : α) : lcm m n ∣ lcm m (n * k) :=
  lcm_dvd_lcm dvd_rfl (dvd_mul_right _ _)

theorem lcm_eq_of_associated_left [NormalizedGCDMonoid α] {m n : α} (h : Associated m n) (k : α) :
    lcm m k = lcm n k :=
  dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _) (lcm_dvd_lcm h.dvd dvd_rfl)
    (lcm_dvd_lcm h.symm.dvd dvd_rfl)

theorem lcm_eq_of_associated_right [NormalizedGCDMonoid α] {m n : α} (h : Associated m n) (k : α) :
    lcm k m = lcm k n :=
  dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _) (lcm_dvd_lcm dvd_rfl h.dvd)
    (lcm_dvd_lcm dvd_rfl h.symm.dvd)

section Divisibility

variable [GCDMonoid α] {m n a b c : α}

variable (m n) in
@[simp] theorem lcm_dvd_mul : lcm m n ∣ m * n :=
  lcm_dvd (by simp) (by simp)

theorem dvd_lcm_of_dvd_left (h : a ∣ b) (c : α) : a ∣ lcm b c :=
  h.trans (dvd_lcm_left b c)

alias Dvd.dvd.lcm_right := dvd_lcm_of_dvd_left

theorem dvd_of_lcm_right_dvd (h : lcm a b ∣ c) : a ∣ c :=
  (dvd_lcm_left a b).trans h

theorem dvd_lcm_of_dvd_right (h : a ∣ b) (c : α) : a ∣ lcm c b :=
  h.trans (dvd_lcm_right c b)

alias Dvd.dvd.lcm_left := dvd_lcm_of_dvd_right

theorem dvd_of_lcm_left_dvd (h : lcm a b ∣ c) : b ∣ c :=
  (dvd_lcm_right a b).trans h

namespace Prime
variable {p : α} (hp : Prime p)

include hp

theorem dvd_or_dvd_of_dvd_lcm (h : p ∣ lcm a b) : p ∣ a ∨ p ∣ b :=
  dvd_or_dvd hp (h.trans (lcm_dvd_mul a b))

theorem dvd_lcm : p ∣ lcm a b ↔ p ∣ a ∨ p ∣ b :=
  ⟨hp.dvd_or_dvd_of_dvd_lcm, (Or.elim · (dvd_lcm_of_dvd_left · _) (dvd_lcm_of_dvd_right · _))⟩

theorem not_dvd_lcm (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) : ¬ p ∣ lcm a b :=
  hp.dvd_lcm.not.mpr <| not_or.mpr ⟨ha, hb⟩

end Prime

end Divisibility

end LCM

end GCDMonoid

section UniqueUnit

variable [CommMonoidWithZero α] [Subsingleton αˣ]

-- see Note [lower instance priority]
instance (priority := 100) : StrongNormalizationMonoid α where
  normUnit _ := 1
  normUnit_zero := rfl
  normUnit_mul _ _ := (mul_one 1).symm
  normUnit_coe_units _ := Subsingleton.elim _ _

@[deprecated (since := "2026-07-08")]
alias NormalizationMonoid.ofUniqueUnits := instStrongNormalizationMonoid

instance : Unique (NormalizationMonoid α) where
  default := inferInstance
  uniq := by rintro ⟨⟩; congr; apply Subsingleton.elim

instance : Unique (StrongNormalizationMonoid α) where
  default := inferInstance
  uniq := by rintro ⟨⟩; congr; apply Subsingleton.elim

instance subsingleton_gcdMonoid_of_unique_units : Subsingleton (GCDMonoid α) :=
  ⟨fun g₁ g₂ => by
    have hgcd : g₁.gcd = g₂.gcd := by
      ext a b
      refine associated_iff_eq.mp (associated_of_dvd_dvd ?_ ?_) <;>
      apply_rules +allowSynthFailures [dvd_gcd, gcd_dvd_left, gcd_dvd_right]
    have hlcm : g₁.lcm = g₂.lcm := by
      ext a b
      refine associated_iff_eq.mp (associated_of_dvd_dvd ?_ ?_) <;>
      apply_rules +allowSynthFailures [lcm_dvd, dvd_lcm_left, dvd_lcm_right]
    cases g₁
    cases g₂
    dsimp only at hgcd hlcm
    simp only [hgcd, hlcm]⟩

instance subsingleton_normalizedGCDMonoid_of_unique_units : Subsingleton (NormalizedGCDMonoid α) :=
  ⟨by
    rintro @⟨a_norm, a_gcd, _⟩ @⟨b_norm, b_gcd, _⟩
    cases Subsingleton.elim a_gcd b_gcd
    cases Subsingleton.elim a_norm b_norm
    rfl⟩

instance : Subsingleton (StrongNormalizedGCDMonoid α) where
  allEq := by
    rintro @⟨a_norm, a_gcd, _⟩ @⟨b_norm, b_gcd, _⟩
    cases Subsingleton.elim a_gcd b_gcd
    cases Subsingleton.elim a_norm b_norm
    rfl

@[simp]
theorem normUnit_eq_one (x : α) : normUnit x = 1 :=
  rfl

@[simp]
theorem normalize_eq (x : α) : normalize x = x :=
  mul_one x

/-- If a monoid's only unit is `1`, then it is isomorphic to its associates. -/
@[simps]
def associatesEquivOfUniqueUnits : Associates α ≃* α where
  toFun := Associates.out
  invFun := Associates.mk
  left_inv := Associates.mk_out
  right_inv _ := (Associates.out_mk _).trans <| normalize_eq _
  map_mul' := Associates.out_mul

end UniqueUnit

section IsDomain

variable [CommRing α] [NormalizedGCDMonoid α]

theorem gcd_eq_of_dvd_sub_right {a b c : α} (h : a ∣ b - c) : gcd a b = gcd a c := by
  apply dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) <;>
    rw [dvd_gcd_iff] <;>
    refine ⟨gcd_dvd_left _ _, ?_⟩
  · rcases h with ⟨d, hd⟩
    rcases gcd_dvd_right a b with ⟨e, he⟩
    rcases gcd_dvd_left a b with ⟨f, hf⟩
    use e - f * d
    rw [mul_sub, ← he, ← mul_assoc, ← hf, ← hd, sub_sub_cancel]
  · rcases h with ⟨d, hd⟩
    rcases gcd_dvd_right a c with ⟨e, he⟩
    rcases gcd_dvd_left a c with ⟨f, hf⟩
    use e + f * d
    rw [mul_add, ← he, ← mul_assoc, ← hf, ← hd, ← add_sub_assoc, add_comm c b, add_sub_cancel_right]

theorem gcd_eq_of_dvd_sub_left {a b c : α} (h : a ∣ b - c) : gcd b a = gcd c a := by
  rw [gcd_comm _ a, gcd_comm _ a, gcd_eq_of_dvd_sub_right h]

end IsDomain

noncomputable section Constructors

open Associates

variable [CommMonoidWithZero α]

private theorem map_mk_unit_aux {f : Associates α →* α}
    (hinv : Function.RightInverse f Associates.mk) (a : α) :
    a * ↑(Classical.choose (associated_map_mk hinv a)) = f (Associates.mk a) :=
  Classical.choose_spec (associated_map_mk hinv a)

variable [IsCancelMulZero α]

/-- Define `NormalizationMonoid` on a structure from a `MonoidHom` inverse to `Associates.mk`. -/
@[instance_reducible]
def strongNormalizationMonoidOfMonoidHomRightInverse [DecidableEq α] (f : Associates α →* α)
    (hinv : Function.RightInverse f Associates.mk) :
    StrongNormalizationMonoid α where
  normUnit a :=
    if a = 0 then 1
    else Classical.choose (Associates.mk_eq_mk_iff_associated.1 (hinv (Associates.mk a)).symm)
  normUnit_zero := if_pos rfl
  normUnit_mul {a b} ha hb := by
    simp_rw [if_neg (mul_ne_zero ha hb), if_neg ha, if_neg hb, Units.ext_iff, Units.val_mul]
    suffices a * b * ↑(Classical.choose (associated_map_mk hinv (a * b))) =
        a * ↑(Classical.choose (associated_map_mk hinv a)) *
        (b * ↑(Classical.choose (associated_map_mk hinv b))) by
      apply mul_left_cancel₀ (mul_ne_zero ha hb) _
      simpa only [mul_assoc, mul_comm, mul_left_comm] using this
    rw [map_mk_unit_aux hinv a, map_mk_unit_aux hinv (a * b), map_mk_unit_aux hinv b, ←
      map_mul, Associates.mk_mul_mk]
  normUnit_coe_units u := by
    nontriviality α
    simp_rw [if_neg (Units.ne_zero u), Units.ext_iff]
    apply mul_left_cancel₀ (Units.ne_zero u)
    rw [Units.mul_inv, map_mk_unit_aux hinv u,
      Associates.mk_eq_mk_iff_associated.2 (associated_one_iff_isUnit.2 ⟨u, rfl⟩),
      Associates.mk_one, map_one]

@[deprecated (since := "2026-07-08")]
noncomputable alias normalizationMonoidOfMonoidHomRightInverse :=
  strongNormalizationMonoidOfMonoidHomRightInverse

/-- Define `GCDMonoid` on a structure just from the `gcd` and its properties. -/
@[instance_reducible]
noncomputable def gcdMonoidOfGCD [DecidableEq α] (gcd : α → α → α)
    (gcd_dvd_left : ∀ a b, gcd a b ∣ a) (gcd_dvd_right : ∀ a b, gcd a b ∣ b)
    (dvd_gcd : ∀ {a b c}, a ∣ c → a ∣ b → a ∣ gcd c b) : GCDMonoid α :=
  { gcd
    gcd_dvd_left
    gcd_dvd_right
    dvd_gcd := fun {_ _ _} => dvd_gcd
    lcm := fun a b =>
      if a = 0 then 0 else Classical.choose ((gcd_dvd_left a b).trans (Dvd.intro b rfl))
    gcd_mul_lcm := fun a b => by
      split_ifs with a0
      · rw [mul_zero, a0, zero_mul]
      · rw [← Classical.choose_spec ((gcd_dvd_left a b).trans (Dvd.intro b rfl))]
    lcm_zero_left := fun _ => if_pos rfl
    lcm_zero_right := fun a => by
      split_ifs with a0
      · rfl
      have h := (Classical.choose_spec ((gcd_dvd_left a 0).trans (Dvd.intro 0 rfl))).symm
      have a0' : gcd a 0 ≠ 0 := by
        contrapose a0
        rw [← associated_zero_iff_eq_zero, ← a0]
        exact associated_of_dvd_dvd (dvd_gcd (dvd_refl a) (dvd_zero a)) (gcd_dvd_left _ _)
      apply Or.resolve_left (mul_eq_zero.1 _) a0'
      rw [h, mul_zero] }

/-- Define `NormalizedGCDMonoid` on a structure just from the `gcd` and its properties. -/
@[instance_reducible]
noncomputable def normalizedGCDMonoidOfGCD [NormalizationMonoid α] [DecidableEq α] (gcd : α → α → α)
    (gcd_dvd_left : ∀ a b, gcd a b ∣ a) (gcd_dvd_right : ∀ a b, gcd a b ∣ b)
    (dvd_gcd : ∀ {a b c}, a ∣ c → a ∣ b → a ∣ gcd c b)
    (normalize_gcd : ∀ a b, normalize (gcd a b) = gcd a b) : NormalizedGCDMonoid α :=
  { (inferInstance : NormalizationMonoid α) with
    gcd
    gcd_dvd_left
    gcd_dvd_right
    dvd_gcd
    normalize_gcd
    lcm a b :=
      if a = 0 then 0
      else normalize (Classical.choose ((gcd_dvd_left a b).trans (Dvd.intro b rfl)))
    normalize_lcm a b := by split_ifs <;> simp
    gcd_mul_lcm a b := by
      split_ifs with a0
      · rw [mul_zero, a0, zero_mul]
      · exact .trans ((normalize_associated _).mul_left _)
          (.of_eq (Classical.choose_spec (_ : _ ∣ a * b)).symm)
    lcm_zero_left _ := if_pos rfl
    lcm_zero_right a := by
      split_ifs with a0
      · rfl
      let := gcdMonoidOfGCD gcd gcd_dvd_left gcd_dvd_right dvd_gcd
      simpa [gcd_ne_zero_of_left a0] using show GCDMonoid.gcd .. * _ = _
        from (Classical.choose_spec ((gcd_dvd_left a 0).trans (.intro 0 rfl))).symm }

/-- Define `GCDMonoid` on a structure just from the `lcm` and its properties. -/
@[instance_reducible]
noncomputable def gcdMonoidOfLCM [DecidableEq α] (lcm : α → α → α)
    (dvd_lcm_left : ∀ a b, a ∣ lcm a b) (dvd_lcm_right : ∀ a b, b ∣ lcm a b)
    (lcm_dvd : ∀ {a b c}, c ∣ a → b ∣ a → lcm c b ∣ a) : GCDMonoid α :=
  let exists_gcd a b := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
  { lcm
    gcd := fun a b => if a = 0 then b else if b = 0 then a else Classical.choose (exists_gcd a b)
    gcd_mul_lcm := fun a b => by
      split_ifs with h h_1
      · rw [h, eq_zero_of_zero_dvd (dvd_lcm_left _ _), mul_zero, zero_mul]
      · rw [h_1, eq_zero_of_zero_dvd (dvd_lcm_right _ _)]
      rw [mul_comm, ← Classical.choose_spec (exists_gcd a b)]
    lcm_zero_left := fun _ => eq_zero_of_zero_dvd (dvd_lcm_left _ _)
    lcm_zero_right := fun _ => eq_zero_of_zero_dvd (dvd_lcm_right _ _)
    gcd_dvd_left := fun a b => by
      split_ifs with h h_1
      · rw [h]
        apply dvd_zero
      · exact dvd_rfl
      have h0 : lcm a b ≠ 0 := by
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
        rw [con, zero_dvd_iff, mul_eq_zero] at h
        cases h
        · exact absurd ‹a = 0› h
        · exact absurd ‹b = 0› h_1
      rw [← mul_dvd_mul_iff_left h0, ← Classical.choose_spec (exists_gcd a b), mul_comm,
        mul_dvd_mul_iff_right h]
      apply dvd_lcm_right
    gcd_dvd_right := fun a b => by
      split_ifs with h h_1
      · exact dvd_rfl
      · rw [h_1]
        apply dvd_zero
      have h0 : lcm a b ≠ 0 := by
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
        rw [con, zero_dvd_iff, mul_eq_zero] at h
        cases h
        · exact absurd ‹a = 0› h
        · exact absurd ‹b = 0› h_1
      rw [← mul_dvd_mul_iff_left h0, ← Classical.choose_spec (exists_gcd a b),
        mul_dvd_mul_iff_right h_1]
      apply dvd_lcm_left
    dvd_gcd := fun {a b c} ac ab => by
      split_ifs with h h_1
      · exact ab
      · exact ac
      have h0 : lcm c b ≠ 0 := by
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left c rfl)
        rw [con, zero_dvd_iff, mul_eq_zero] at h
        cases h
        · exact absurd ‹c = 0› h
        · exact absurd ‹b = 0› h_1
      rw [← mul_dvd_mul_iff_left h0, ← Classical.choose_spec (exists_gcd c b)]
      rcases ab with ⟨d, rfl⟩
      rw [mul_eq_zero] at ‹a * d ≠ 0›
      push Not at h_1
      rw [mul_comm a, ← mul_assoc, mul_dvd_mul_iff_right h_1.1]
      apply lcm_dvd (Dvd.intro d rfl)
      rw [mul_comm, mul_dvd_mul_iff_right h_1.2]
      apply ac }

/-- Define `NormalizedGCDMonoid` on a structure just from the `lcm` and its properties. -/
@[instance_reducible]
noncomputable def normalizedGCDMonoidOfLCM [NormalizationMonoid α] [DecidableEq α] (lcm : α → α → α)
    (dvd_lcm_left : ∀ a b, a ∣ lcm a b) (dvd_lcm_right : ∀ a b, b ∣ lcm a b)
    (lcm_dvd : ∀ {a b c}, c ∣ a → b ∣ a → lcm c b ∣ a)
    (normalize_lcm : ∀ a b, normalize (lcm a b) = lcm a b) : NormalizedGCDMonoid α :=
  let exists_gcd a b := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
  let := gcdMonoidOfLCM lcm dvd_lcm_left dvd_lcm_right lcm_dvd
  { (inferInstance : NormalizationMonoid α) with
    lcm
    gcd a b := normalize <|
      if a = 0 then b
      else if b = 0 then a else Classical.choose (exists_gcd a b)
    gcd_mul_lcm a b := by
      split_ifs with h h_1
      · rw [h, eq_zero_of_zero_dvd (dvd_lcm_left _ _), mul_zero, zero_mul]
      · rw [h_1, eq_zero_of_zero_dvd (dvd_lcm_right _ _), mul_zero, mul_zero]
      rw [mul_comm]
      exact ((normalize_associated _).mul_left _).trans
        (.of_eq (Classical.choose_spec (exists_gcd a b)).symm)
    normalize_lcm
    normalize_gcd a b := normalize_idem _
    lcm_zero_left _ := eq_zero_of_zero_dvd (dvd_lcm_left _ _)
    lcm_zero_right _ := eq_zero_of_zero_dvd (dvd_lcm_right _ _)
    gcd_dvd_left a b := by
      split_ifs with h h_1
      · rw [h]
        apply dvd_zero
      · exact (normalize_associated _).dvd
      have h0 : lcm a b ≠ 0 := lcm_ne_zero_iff.mpr ⟨h, h_1⟩
      rw [normalize_dvd_iff, ← mul_dvd_mul_iff_left h0, ← Classical.choose_spec (exists_gcd a b),
        mul_comm, mul_dvd_mul_iff_right h]
      apply dvd_lcm_right
    gcd_dvd_right a b := by
      split_ifs with h h_1
      · exact (normalize_associated _).dvd
      · rw [h_1]
        apply dvd_zero
      have h0 : lcm a b ≠ 0 := lcm_ne_zero_iff.mpr ⟨h, h_1⟩
      rw [normalize_dvd_iff, ← mul_dvd_mul_iff_left h0, ← Classical.choose_spec (exists_gcd a b),
        mul_dvd_mul_iff_right h_1]
      apply dvd_lcm_left
    dvd_gcd {a b c} ac ab := by
      split_ifs with h h_1
      · apply dvd_normalize_iff.2 ab
      · apply dvd_normalize_iff.2 ac
      have h0 : lcm c b ≠ 0 := lcm_ne_zero_iff.mpr ⟨h, h_1⟩
      rw [dvd_normalize_iff, ← mul_dvd_mul_iff_left h0, ← Classical.choose_spec (exists_gcd c b)]
      rcases ab with ⟨d, rfl⟩
      rw [mul_eq_zero] at h_1
      push Not at h_1
      rw [mul_comm a, ← mul_assoc, mul_dvd_mul_iff_right h_1.1]
      apply lcm_dvd (Dvd.intro d rfl)
      rw [mul_comm, mul_dvd_mul_iff_right h_1.2]
      apply ac }

/-- Define a `GCDMonoid` structure on a monoid just from the existence of a `gcd`. -/
@[instance_reducible]
noncomputable def gcdMonoidOfExistsGCD [DecidableEq α]
    (h : ∀ a b : α, ∃ c : α, ∀ d : α, d ∣ a ∧ d ∣ b ↔ d ∣ c) : GCDMonoid α :=
  gcdMonoidOfGCD (fun a b => Classical.choose (h a b))
    (fun a b => ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).1)
    (fun a b => ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).2)
    fun {a b c} ac ab => (Classical.choose_spec (h c b) a).1 ⟨ac, ab⟩

/-- Define a `NormalizedGCDMonoid` structure on a monoid just from the existence of a `gcd`. -/
@[instance_reducible]
noncomputable def normalizedGCDMonoidOfExistsGCD [NormalizationMonoid α] [DecidableEq α]
    (h : ∀ a b : α, ∃ c : α, ∀ d : α, d ∣ a ∧ d ∣ b ↔ d ∣ c) : NormalizedGCDMonoid α :=
  normalizedGCDMonoidOfGCD (fun a b => normalize (Classical.choose (h a b)))
    (fun a b =>
      normalize_dvd_iff.2 ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).1)
    (fun a b =>
      normalize_dvd_iff.2 ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).2)
    (fun {a b c} ac ab => dvd_normalize_iff.2 ((Classical.choose_spec (h c b) a).1 ⟨ac, ab⟩))
    fun _ _ => normalize_idem _

/-- Define a `StrongNormalizedGCDMonoid` structure on a monoid just from
the existence of a `gcd`. -/
abbrev strongNormalizedGCDMonoidOfExistsGCD [StrongNormalizationMonoid α] [DecidableEq α]
    (h : ∀ a b : α, ∃ c : α, ∀ d : α, d ∣ a ∧ d ∣ b ↔ d ∣ c) : StrongNormalizedGCDMonoid α where
  __ := normalizedGCDMonoidOfExistsGCD h
  __ := ‹StrongNormalizationMonoid α›

theorem nonempty_normalizedGCDMonoid_iff_isGCDMonoid {α} [CommMonoidWithZero α] :
    Nonempty (NormalizedGCDMonoid α) ↔ IsGCDMonoid α where
  mp := fun ⟨_⟩ ↦ inferInstance
  mpr := fun ⟨_⟩ ↦ by
    have := Classical.arbitrary (NormalizationMonoid α)
    classical exact ⟨normalizedGCDMonoidOfExistsGCD fun _ _ ↦ ⟨_, fun _ ↦ (dvd_gcd_iff ..).symm⟩⟩

instance (α) [CommMonoidWithZero α] [IsGCDMonoid α] : Nonempty (NormalizedGCDMonoid α) :=
  nonempty_normalizedGCDMonoid_iff_isGCDMonoid.mpr ‹_›

theorem nonempty_strongNormalizedGCDMonoid_iff {α} [CommMonoidWithZero α] :
    Nonempty (StrongNormalizedGCDMonoid α) ↔
    IsGCDMonoid α ∧ Nonempty (StrongNormalizationMonoid α) :=
  ⟨fun ⟨_⟩ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨⟨_⟩, ⟨_⟩⟩ ↦ by classical exact
    ⟨strongNormalizedGCDMonoidOfExistsGCD fun _ _ ↦ ⟨_, fun _ ↦ (dvd_gcd_iff ..).symm⟩⟩⟩

/-- Define a `GCDMonoid` structure on a monoid just from the existence of an `lcm`. -/
@[instance_reducible]
noncomputable def gcdMonoidOfExistsLCM [DecidableEq α]
    (h : ∀ a b : α, ∃ c : α, ∀ d : α, a ∣ d ∧ b ∣ d ↔ c ∣ d) : GCDMonoid α :=
  gcdMonoidOfLCM (fun a b => Classical.choose (h a b))
    (fun a b => ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).1)
    (fun a b => ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).2)
    fun {a b c} ac ab => (Classical.choose_spec (h c b) a).1 ⟨ac, ab⟩

/-- Define a `NormalizedGCDMonoid` structure on a monoid just from the existence of an `lcm`. -/
@[instance_reducible]
noncomputable def normalizedGCDMonoidOfExistsLCM [NormalizationMonoid α] [DecidableEq α]
    (h : ∀ a b : α, ∃ c : α, ∀ d : α, a ∣ d ∧ b ∣ d ↔ c ∣ d) : NormalizedGCDMonoid α :=
  normalizedGCDMonoidOfLCM (fun a b => normalize (Classical.choose (h a b)))
    (fun a b =>
      dvd_normalize_iff.2 ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).1)
    (fun a b =>
      dvd_normalize_iff.2 ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).2)
    (fun {a b c} ac ab => normalize_dvd_iff.2 ((Classical.choose_spec (h c b) a).1 ⟨ac, ab⟩))
    fun _ _ => normalize_idem _

/-- Define a `StrongNormalizedGCDMonoid` structure on a monoid just from
the existence of a `lcm`. -/
abbrev strongNormalizedGCDMonoidOfExistsLCM [StrongNormalizationMonoid α] [DecidableEq α]
    (h : ∀ a b : α, ∃ c : α, ∀ d : α, a ∣ d ∧ b ∣ d ↔ c ∣ d) : StrongNormalizedGCDMonoid α where
  __ := normalizedGCDMonoidOfExistsLCM h
  __ := ‹StrongNormalizationMonoid α›

theorem isGCDMonoid_iff_exists_gcd {α} [CommMonoidWithZero α] :
    IsGCDMonoid α ↔ IsCancelMulZero α ∧ ∀ a b : α, ∃ c : α, ∀ d : α, d ∣ a ∧ d ∣ b ↔ d ∣ c where
  mp := fun ⟨_⟩ ↦ ⟨inferInstance, fun _ _ ↦ ⟨_, fun _ ↦ (dvd_gcd_iff ..).symm⟩⟩
  mpr := fun ⟨_, h⟩ ↦ by classical exact ⟨gcdMonoidOfExistsGCD h⟩

theorem isGCDMonoid_iff_exists_lcm {α} [CommMonoidWithZero α] :
    IsGCDMonoid α ↔ IsCancelMulZero α ∧ ∀ a b : α, ∃ c : α, ∀ d : α, a ∣ d ∧ b ∣ d ↔ c ∣ d where
  mp := fun ⟨_⟩ ↦ ⟨inferInstance, fun _ _ ↦ ⟨_, fun _ ↦ (lcm_dvd_iff ..).symm⟩⟩
  mpr := fun ⟨_, h⟩ ↦ by classical exact ⟨gcdMonoidOfExistsLCM h⟩

end Constructors

namespace CommGroupWithZero

variable (G₀ : Type*) [CommGroupWithZero G₀] [DecidableEq G₀]

-- see Note [lower instance priority]
instance (priority := 100) : StrongNormalizedGCDMonoid G₀ where
  normUnit x := if h : x = 0 then 1 else (Units.mk0 x h)⁻¹
  normUnit_zero := dif_pos rfl
  normUnit_mul {x y} x0 y0 := Units.ext <| by simp [x0, y0, mul_comm]
  normUnit_coe_units u := by simp
  gcd a b := if a = 0 ∧ b = 0 then 0 else 1
  lcm a b := if a = 0 ∨ b = 0 then 0 else 1
  gcd_dvd_left a b := by simp +contextual
  gcd_dvd_right a b := by simp +contextual
  dvd_gcd {a b c} hac hab := by simp_all
  gcd_mul_lcm a b := by
    split_ifs <;> simp_all [Associated.comm]
  lcm_zero_left _ := if_pos (Or.inl rfl)
  lcm_zero_right _ := if_pos (Or.inr rfl)
  -- `split_ifs` wants to split `normalize`, so handle the cases manually
  normalize_gcd a b := if h : a = 0 ∧ b = 0 then by simp [if_pos h] else by simp [if_neg h]
  normalize_lcm a b := if h : a = 0 ∨ b = 0 then by simp [if_pos h] else by simp [if_neg h]

@[simp]
theorem coe_normUnit {a : G₀} (h0 : a ≠ 0) : (↑(normUnit a) : G₀) = a⁻¹ := by
  simp [normUnit, h0]

theorem normalize_eq_one {a : G₀} (h0 : a ≠ 0) : normalize a = 1 := by simp [normalize_apply, h0]

end CommGroupWithZero

namespace Associates

variable [CommMonoidWithZero α] [GCDMonoid α]

instance instGCDMonoid : GCDMonoid (Associates α) where
  gcd := Quotient.map₂ gcd fun _ _ (ha : Associated _ _) _ _ (hb : Associated _ _) => ha.gcd hb
  lcm := Quotient.map₂ lcm fun _ _ (ha : Associated _ _) _ _ (hb : Associated _ _) => ha.lcm hb
  gcd_dvd_left := by rintro ⟨a⟩ ⟨b⟩; exact mk_le_mk_of_dvd (gcd_dvd_left _ _)
  gcd_dvd_right := by rintro ⟨a⟩ ⟨b⟩; exact mk_le_mk_of_dvd (gcd_dvd_right _ _)
  dvd_gcd := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ hac hbc
    exact mk_le_mk_of_dvd (dvd_gcd (dvd_of_mk_le_mk hac) (dvd_of_mk_le_mk hbc))
  gcd_mul_lcm := by
    rintro ⟨a⟩ ⟨b⟩
    rw [associated_iff_eq]
    exact Quotient.sound <| gcd_mul_lcm _ _
  lcm_zero_left := by rintro ⟨a⟩; exact congr_arg Associates.mk <| lcm_zero_left _
  lcm_zero_right := by rintro ⟨a⟩; exact congr_arg Associates.mk <| lcm_zero_right _

theorem gcd_mk_mk {a b : α} : gcd (Associates.mk a) (Associates.mk b) = Associates.mk (gcd a b) :=
  rfl
theorem lcm_mk_mk {a b : α} : lcm (Associates.mk a) (Associates.mk b) = Associates.mk (lcm a b) :=
  rfl

end Associates
