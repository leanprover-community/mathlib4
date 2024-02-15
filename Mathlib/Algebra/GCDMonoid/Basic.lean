/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker
-/
import Mathlib.Algebra.Associated
import Mathlib.Algebra.Ring.Regular
import Mathlib.Tactic.Common

#align_import algebra.gcd_monoid.basic from "leanprover-community/mathlib"@"550b58538991c8977703fdeb7c9d51a5aa27df11"

/-!
# Monoids with normalization functions, `gcd`, and `lcm`

This file defines extra structures on `CancelCommMonoidWithZero`s, including `IsDomain`s.

## Main Definitions

* `NormalizationMonoid`
* `GCDMonoid`
* `NormalizedGCDMonoid`
* `gcdMonoid_of_gcd`, `gcdMonoid_of_exists_gcd`, `normalizedGCDMonoid_of_gcd`,
  `normalizedGCDMonoid_of_exists_gcd`
* `gcdMonoid_of_lcm`, `gcdMonoid_of_exists_lcm`, `normalizedGCDMonoid_of_lcm`,
  `normalizedGCDMonoid_of_exists_lcm`

For the `NormalizedGCDMonoid` instances on `ℕ` and `ℤ`, see `RingTheory.Int.Basic`.

## Implementation Notes

* `NormalizationMonoid` is defined by assigning to each element a `normUnit` such that multiplying
by that unit normalizes the monoid, and `normalize` is an idempotent monoid homomorphism. This
definition as currently implemented does casework on `0`.

* `GCDMonoid` contains the definitions of `gcd` and `lcm` with the usual properties. They are
  both determined up to a unit.

* `NormalizedGCDMonoid` extends `NormalizationMonoid`, so the `gcd` and `lcm` are always
  normalized. This makes `gcd`s of polynomials easier to work with, but excludes Euclidean domains,
  and monoids without zero.

* `gcdMonoid_of_gcd` and `normalizedGCDMonoid_of_gcd` noncomputably construct a `GCDMonoid`
  (resp. `NormalizedGCDMonoid`) structure just from the `gcd` and its properties.

* `gcdMonoid_of_exists_gcd` and `normalizedGCDMonoid_of_exists_gcd` noncomputably construct a
  `GCDMonoid` (resp. `NormalizedGCDMonoid`) structure just from a proof that any two elements
  have a (not necessarily normalized) `gcd`.

* `gcdMonoid_of_lcm` and `normalizedGCDMonoid_of_lcm` noncomputably construct a `GCDMonoid`
  (resp. `NormalizedGCDMonoid`) structure just from the `lcm` and its properties.

* `gcdMonoid_of_exists_lcm` and `normalizedGCDMonoid_of_exists_lcm` noncomputably construct a
  `GCDMonoid` (resp. `NormalizedGCDMonoid`) structure just from a proof that any two elements
  have a (not necessarily normalized) `lcm`.

## TODO

* Port GCD facts about nats, definition of coprime
* Generalize normalization monoids to commutative (cancellative) monoids with or without zero

## Tags

divisibility, gcd, lcm, normalize
-/


variable {α : Type*}

-- Porting note: mathlib3 had a `@[protect_proj]` here, but adding `protected` to all the fields
-- adds unnecessary clutter to later code
/-- Normalization monoid: multiplying with `normUnit` gives a normal form for associated
elements. -/
class NormalizationMonoid (α : Type*) [CancelCommMonoidWithZero α] where
  /-- `normUnit` assigns to each element of the monoid a unit of the monoid. -/
  normUnit : α → αˣ
  /-- The proposition that `normUnit` maps `0` to the identity. -/
  normUnit_zero : normUnit 0 = 1
  /-- The proposition that `normUnit` respects multiplication of non-zero elements. -/
  normUnit_mul : ∀ {a b}, a ≠ 0 → b ≠ 0 → normUnit (a * b) = normUnit a * normUnit b
  /-- The proposition that `normUnit` maps units to their inverses. -/
  normUnit_coe_units : ∀ u : αˣ, normUnit u = u⁻¹
#align normalization_monoid NormalizationMonoid

export NormalizationMonoid (normUnit normUnit_zero normUnit_mul normUnit_coe_units)

attribute [simp] normUnit_coe_units normUnit_zero normUnit_mul

section NormalizationMonoid

variable [CancelCommMonoidWithZero α] [NormalizationMonoid α]

@[simp]
theorem normUnit_one : normUnit (1 : α) = 1 :=
  normUnit_coe_units 1
#align norm_unit_one normUnit_one

-- Porting note: quite slow. Improve performance?
/-- Chooses an element of each associate class, by multiplying by `normUnit` -/
def normalize : α →*₀ α where
  toFun x := x * normUnit x
  map_zero' := by
    simp only [normUnit_zero]
    exact mul_one (0:α)
  map_one' := by dsimp only; rw [normUnit_one, one_mul]; rfl
  map_mul' x y :=
    (by_cases fun hx : x = 0 => by dsimp only; rw [hx, zero_mul, zero_mul, zero_mul]) fun hx =>
      (by_cases fun hy : y = 0 => by dsimp only; rw [hy, mul_zero, zero_mul, mul_zero]) fun hy => by
        simp only [normUnit_mul hx hy, Units.val_mul]; simp only [mul_assoc, mul_left_comm y]
#align normalize normalize

theorem associated_normalize (x : α) : Associated x (normalize x) :=
  ⟨_, rfl⟩
#align associated_normalize associated_normalize

theorem normalize_associated (x : α) : Associated (normalize x) x :=
  (associated_normalize _).symm
#align normalize_associated normalize_associated

theorem associated_normalize_iff {x y : α} : Associated x (normalize y) ↔ Associated x y :=
  ⟨fun h => h.trans (normalize_associated y), fun h => h.trans (associated_normalize y)⟩
#align associated_normalize_iff associated_normalize_iff

theorem normalize_associated_iff {x y : α} : Associated (normalize x) y ↔ Associated x y :=
  ⟨fun h => (associated_normalize _).trans h, fun h => (normalize_associated _).trans h⟩
#align normalize_associated_iff normalize_associated_iff

theorem Associates.mk_normalize (x : α) : Associates.mk (normalize x) = Associates.mk x :=
  Associates.mk_eq_mk_iff_associated.2 (normalize_associated _)
#align associates.mk_normalize Associates.mk_normalize

@[simp]
theorem normalize_apply (x : α) : normalize x = x * normUnit x :=
  rfl
#align normalize_apply normalize_apply

-- Porting note: `simp` can prove this
-- @[simp]
theorem normalize_zero : normalize (0 : α) = 0 :=
  normalize.map_zero
#align normalize_zero normalize_zero

-- Porting note: `simp` can prove this
-- @[simp]
theorem normalize_one : normalize (1 : α) = 1 :=
  normalize.map_one
#align normalize_one normalize_one

theorem normalize_coe_units (u : αˣ) : normalize (u : α) = 1 := by simp
#align normalize_coe_units normalize_coe_units

theorem normalize_eq_zero {x : α} : normalize x = 0 ↔ x = 0 :=
  ⟨fun hx => (associated_zero_iff_eq_zero x).1 <| hx ▸ associated_normalize _, by
    rintro rfl; exact normalize_zero⟩
#align normalize_eq_zero normalize_eq_zero

theorem normalize_eq_one {x : α} : normalize x = 1 ↔ IsUnit x :=
  ⟨fun hx => isUnit_iff_exists_inv.2 ⟨_, hx⟩, fun ⟨u, hu⟩ => hu ▸ normalize_coe_units u⟩
#align normalize_eq_one normalize_eq_one

-- Porting note: quite slow. Improve performance?
@[simp]
theorem normUnit_mul_normUnit (a : α) : normUnit (a * normUnit a) = 1 := by
  nontriviality α using Subsingleton.elim a 0
  obtain rfl | h := eq_or_ne a 0
  · rw [normUnit_zero, zero_mul, normUnit_zero]
  · rw [normUnit_mul h (Units.ne_zero _), normUnit_coe_units, mul_inv_eq_one]
#align norm_unit_mul_norm_unit normUnit_mul_normUnit

theorem normalize_idem (x : α) : normalize (normalize x) = normalize x := by simp
#align normalize_idem normalize_idem

theorem normalize_eq_normalize {a b : α} (hab : a ∣ b) (hba : b ∣ a) :
    normalize a = normalize b := by
  nontriviality α
  rcases associated_of_dvd_dvd hab hba with ⟨u, rfl⟩
  refine' by_cases (by rintro rfl; simp only [zero_mul]) fun ha : a ≠ 0 => _
  suffices a * ↑(normUnit a) = a * ↑u * ↑(normUnit a) * ↑u⁻¹ by
    simpa only [normalize_apply, mul_assoc, normUnit_mul ha u.ne_zero, normUnit_coe_units]
  calc
    a * ↑(normUnit a) = a * ↑(normUnit a) * ↑u * ↑u⁻¹ := (Units.mul_inv_cancel_right _ _).symm
    _ = a * ↑u * ↑(normUnit a) * ↑u⁻¹ := by rw [mul_right_comm a]
#align normalize_eq_normalize normalize_eq_normalize

theorem normalize_eq_normalize_iff {x y : α} : normalize x = normalize y ↔ x ∣ y ∧ y ∣ x :=
  ⟨fun h => ⟨Units.dvd_mul_right.1 ⟨_, h.symm⟩, Units.dvd_mul_right.1 ⟨_, h⟩⟩, fun ⟨hxy, hyx⟩ =>
    normalize_eq_normalize hxy hyx⟩
#align normalize_eq_normalize_iff normalize_eq_normalize_iff

theorem dvd_antisymm_of_normalize_eq {a b : α} (ha : normalize a = a) (hb : normalize b = b)
    (hab : a ∣ b) (hba : b ∣ a) : a = b :=
  ha ▸ hb ▸ normalize_eq_normalize hab hba
#align dvd_antisymm_of_normalize_eq dvd_antisymm_of_normalize_eq

--can be proven by simp
theorem dvd_normalize_iff {a b : α} : a ∣ normalize b ↔ a ∣ b :=
  Units.dvd_mul_right
#align dvd_normalize_iff dvd_normalize_iff

--can be proven by simp
theorem normalize_dvd_iff {a b : α} : normalize a ∣ b ↔ a ∣ b :=
  Units.mul_right_dvd
#align normalize_dvd_iff normalize_dvd_iff

end NormalizationMonoid

namespace Associates

variable [CancelCommMonoidWithZero α] [NormalizationMonoid α]

attribute [local instance] Associated.setoid

/-- Maps an element of `Associates` back to the normalized element of its associate class -/
protected def out : Associates α → α :=
  (Quotient.lift (normalize : α → α)) fun a _ ⟨_, hu⟩ =>
    hu ▸ normalize_eq_normalize ⟨_, rfl⟩ (Units.mul_right_dvd.2 <| dvd_refl a)
#align associates.out Associates.out

@[simp]
theorem out_mk (a : α) : (Associates.mk a).out = normalize a :=
  rfl
#align associates.out_mk Associates.out_mk

@[simp]
theorem out_one : (1 : Associates α).out = 1 :=
  normalize_one
#align associates.out_one Associates.out_one

theorem out_mul (a b : Associates α) : (a * b).out = a.out * b.out :=
  Quotient.inductionOn₂ a b fun _ _ => by
    simp only [Associates.quotient_mk_eq_mk, out_mk, mk_mul_mk, normalize.map_mul]
#align associates.out_mul Associates.out_mul

theorem dvd_out_iff (a : α) (b : Associates α) : a ∣ b.out ↔ Associates.mk a ≤ b :=
  Quotient.inductionOn b <| by
    simp [Associates.out_mk, Associates.quotient_mk_eq_mk, mk_le_mk_iff_dvd_iff]
#align associates.dvd_out_iff Associates.dvd_out_iff

theorem out_dvd_iff (a : α) (b : Associates α) : b.out ∣ a ↔ b ≤ Associates.mk a :=
  Quotient.inductionOn b <| by
    simp [Associates.out_mk, Associates.quotient_mk_eq_mk, mk_le_mk_iff_dvd_iff]
#align associates.out_dvd_iff Associates.out_dvd_iff

@[simp]
theorem out_top : (⊤ : Associates α).out = 0 :=
  normalize_zero
#align associates.out_top Associates.out_top

-- Porting note: lower priority to avoid linter complaints about simp-normal form
@[simp 1100]
theorem normalize_out (a : Associates α) : normalize a.out = a.out :=
  Quotient.inductionOn a normalize_idem
#align associates.normalize_out Associates.normalize_out

@[simp]
theorem mk_out (a : Associates α) : Associates.mk a.out = a :=
  Quotient.inductionOn a mk_normalize
#align associates.mk_out Associates.mk_out

theorem out_injective : Function.Injective (Associates.out : _ → α) :=
  Function.LeftInverse.injective mk_out
#align associates.out_injective Associates.out_injective

end Associates

-- Porting note: mathlib3 had a `@[protect_proj]` here, but adding `protected` to all the fields
-- adds unnecessary clutter to later code
/-- GCD monoid: a `CancelCommMonoidWithZero` with `gcd` (greatest common divisor) and
`lcm` (least common multiple) operations, determined up to a unit. The type class focuses on `gcd`
and we derive the corresponding `lcm` facts from `gcd`.
-/
class GCDMonoid (α : Type*) [CancelCommMonoidWithZero α] where
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
#align gcd_monoid GCDMonoid

/-- Normalized GCD monoid: a `CancelCommMonoidWithZero` with normalization and `gcd`
(greatest common divisor) and `lcm` (least common multiple) operations. In this setting `gcd` and
`lcm` form a bounded lattice on the associated elements where `gcd` is the infimum, `lcm` is the
supremum, `1` is bottom, and `0` is top. The type class focuses on `gcd` and we derive the
corresponding `lcm` facts from `gcd`.
-/
class NormalizedGCDMonoid (α : Type*) [CancelCommMonoidWithZero α] extends NormalizationMonoid α,
  GCDMonoid α where
  /-- The GCD is normalized to itself. -/
  normalize_gcd : ∀ a b, normalize (gcd a b) = gcd a b
  /-- The LCM is normalized to itself. -/
  normalize_lcm : ∀ a b, normalize (lcm a b) = lcm a b
#align normalized_gcd_monoid NormalizedGCDMonoid

export GCDMonoid (gcd lcm gcd_dvd_left gcd_dvd_right dvd_gcd lcm_zero_left lcm_zero_right)

attribute [simp] lcm_zero_left lcm_zero_right

section GCDMonoid

variable [CancelCommMonoidWithZero α]

instance [NormalizationMonoid α] : Nonempty (NormalizationMonoid α) := ⟨‹_›⟩
instance [GCDMonoid α] : Nonempty (GCDMonoid α) := ⟨‹_›⟩
instance [NormalizedGCDMonoid α] : Nonempty (NormalizedGCDMonoid α) := ⟨‹_›⟩
instance [h : Nonempty (NormalizedGCDMonoid α)] : Nonempty (NormalizationMonoid α) :=
  h.elim fun _ ↦ inferInstance
instance [h : Nonempty (NormalizedGCDMonoid α)] : Nonempty (GCDMonoid α) :=
  h.elim fun _ ↦ inferInstance

theorem gcd_isUnit_iff_isRelPrime [GCDMonoid α] {a b : α} :
    IsUnit (gcd a b) ↔ IsRelPrime a b :=
  ⟨fun h _ ha hb ↦ isUnit_of_dvd_unit (dvd_gcd ha hb) h, (· (gcd_dvd_left a b) (gcd_dvd_right a b))⟩

-- Porting note: lower priority to avoid linter complaints about simp-normal form
@[simp 1100]
theorem normalize_gcd [NormalizedGCDMonoid α] : ∀ a b : α, normalize (gcd a b) = gcd a b :=
  NormalizedGCDMonoid.normalize_gcd
#align normalize_gcd normalize_gcd

theorem gcd_mul_lcm [GCDMonoid α] : ∀ a b : α, Associated (gcd a b * lcm a b) (a * b) :=
  GCDMonoid.gcd_mul_lcm
#align gcd_mul_lcm gcd_mul_lcm

section GCD

theorem dvd_gcd_iff [GCDMonoid α] (a b c : α) : a ∣ gcd b c ↔ a ∣ b ∧ a ∣ c :=
  Iff.intro (fun h => ⟨h.trans (gcd_dvd_left _ _), h.trans (gcd_dvd_right _ _)⟩) fun ⟨hab, hac⟩ =>
    dvd_gcd hab hac
#align dvd_gcd_iff dvd_gcd_iff

theorem gcd_comm [NormalizedGCDMonoid α] (a b : α) : gcd a b = gcd b a :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _)
    (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))
    (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))
#align gcd_comm gcd_comm

theorem gcd_comm' [GCDMonoid α] (a b : α) : Associated (gcd a b) (gcd b a) :=
  associated_of_dvd_dvd (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))
    (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))
#align gcd_comm' gcd_comm'

theorem gcd_assoc [NormalizedGCDMonoid α] (m n k : α) : gcd (gcd m n) k = gcd m (gcd n k) :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _)
    (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_left m n))
      (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_right m n)) (gcd_dvd_right (gcd m n) k)))
    (dvd_gcd
      (dvd_gcd (gcd_dvd_left m (gcd n k)) ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_left n k)))
      ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_right n k)))
#align gcd_assoc gcd_assoc

theorem gcd_assoc' [GCDMonoid α] (m n k : α) : Associated (gcd (gcd m n) k) (gcd m (gcd n k)) :=
  associated_of_dvd_dvd
    (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_left m n))
      (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_right m n)) (gcd_dvd_right (gcd m n) k)))
    (dvd_gcd
      (dvd_gcd (gcd_dvd_left m (gcd n k)) ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_left n k)))
      ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_right n k)))
#align gcd_assoc' gcd_assoc'

instance [NormalizedGCDMonoid α] : Std.Commutative (α := α) gcd where
  comm := gcd_comm

instance [NormalizedGCDMonoid α] : Std.Associative (α := α) gcd where
  assoc := gcd_assoc

theorem gcd_eq_normalize [NormalizedGCDMonoid α] {a b c : α} (habc : gcd a b ∣ c)
    (hcab : c ∣ gcd a b) : gcd a b = normalize c :=
  normalize_gcd a b ▸ normalize_eq_normalize habc hcab
#align gcd_eq_normalize gcd_eq_normalize

@[simp]
theorem gcd_zero_left [NormalizedGCDMonoid α] (a : α) : gcd 0 a = normalize a :=
  gcd_eq_normalize (gcd_dvd_right 0 a) (dvd_gcd (dvd_zero _) (dvd_refl a))
#align gcd_zero_left gcd_zero_left

theorem gcd_zero_left' [GCDMonoid α] (a : α) : Associated (gcd 0 a) a :=
  associated_of_dvd_dvd (gcd_dvd_right 0 a) (dvd_gcd (dvd_zero _) (dvd_refl a))
#align gcd_zero_left' gcd_zero_left'

@[simp]
theorem gcd_zero_right [NormalizedGCDMonoid α] (a : α) : gcd a 0 = normalize a :=
  gcd_eq_normalize (gcd_dvd_left a 0) (dvd_gcd (dvd_refl a) (dvd_zero _))
#align gcd_zero_right gcd_zero_right

theorem gcd_zero_right' [GCDMonoid α] (a : α) : Associated (gcd a 0) a :=
  associated_of_dvd_dvd (gcd_dvd_left a 0) (dvd_gcd (dvd_refl a) (dvd_zero _))
#align gcd_zero_right' gcd_zero_right'

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
#align gcd_eq_zero_iff gcd_eq_zero_iff

@[simp]
theorem gcd_one_left [NormalizedGCDMonoid α] (a : α) : gcd 1 a = 1 :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) normalize_one (gcd_dvd_left _ _) (one_dvd _)
#align gcd_one_left gcd_one_left

@[simp]
theorem gcd_one_left' [GCDMonoid α] (a : α) : Associated (gcd 1 a) 1 :=
  associated_of_dvd_dvd (gcd_dvd_left _ _) (one_dvd _)
#align gcd_one_left' gcd_one_left'

@[simp]
theorem gcd_one_right [NormalizedGCDMonoid α] (a : α) : gcd a 1 = 1 :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) normalize_one (gcd_dvd_right _ _) (one_dvd _)
#align gcd_one_right gcd_one_right

@[simp]
theorem gcd_one_right' [GCDMonoid α] (a : α) : Associated (gcd a 1) 1 :=
  associated_of_dvd_dvd (gcd_dvd_right _ _) (one_dvd _)
#align gcd_one_right' gcd_one_right'

theorem gcd_dvd_gcd [GCDMonoid α] {a b c d : α} (hab : a ∣ b) (hcd : c ∣ d) : gcd a c ∣ gcd b d :=
  dvd_gcd ((gcd_dvd_left _ _).trans hab) ((gcd_dvd_right _ _).trans hcd)
#align gcd_dvd_gcd gcd_dvd_gcd

@[simp]
theorem gcd_same [NormalizedGCDMonoid α] (a : α) : gcd a a = normalize a :=
  gcd_eq_normalize (gcd_dvd_left _ _) (dvd_gcd (dvd_refl a) (dvd_refl a))
#align gcd_same gcd_same

@[simp]
theorem gcd_mul_left [NormalizedGCDMonoid α] (a b c : α) :
    gcd (a * b) (a * c) = normalize a * gcd b c :=
  (by_cases (by rintro rfl; simp only [zero_mul, gcd_zero_left, normalize_zero]))
    fun ha : a ≠ 0 =>
    suffices gcd (a * b) (a * c) = normalize (a * gcd b c) by simpa
    let ⟨d, eq⟩ := dvd_gcd (dvd_mul_right a b) (dvd_mul_right a c)
    gcd_eq_normalize
      (eq.symm ▸ mul_dvd_mul_left a
        (show d ∣ gcd b c from
          dvd_gcd ((mul_dvd_mul_iff_left ha).1 <| eq ▸ gcd_dvd_left _ _)
            ((mul_dvd_mul_iff_left ha).1 <| eq ▸ gcd_dvd_right _ _)))
      (dvd_gcd (mul_dvd_mul_left a <| gcd_dvd_left _ _) (mul_dvd_mul_left a <| gcd_dvd_right _ _))
#align gcd_mul_left gcd_mul_left

theorem gcd_mul_left' [GCDMonoid α] (a b c : α) :
    Associated (gcd (a * b) (a * c)) (a * gcd b c) := by
  obtain rfl | ha := eq_or_ne a 0
  · simp only [zero_mul, gcd_zero_left']
  obtain ⟨d, eq⟩ := dvd_gcd (dvd_mul_right a b) (dvd_mul_right a c)
  apply associated_of_dvd_dvd
  · rw [eq]
    apply mul_dvd_mul_left
    exact
      dvd_gcd ((mul_dvd_mul_iff_left ha).1 <| eq ▸ gcd_dvd_left _ _)
        ((mul_dvd_mul_iff_left ha).1 <| eq ▸ gcd_dvd_right _ _)
  · exact dvd_gcd (mul_dvd_mul_left a <| gcd_dvd_left _ _) (mul_dvd_mul_left a <| gcd_dvd_right _ _)
#align gcd_mul_left' gcd_mul_left'

@[simp]
theorem gcd_mul_right [NormalizedGCDMonoid α] (a b c : α) :
    gcd (b * a) (c * a) = gcd b c * normalize a := by simp only [mul_comm, gcd_mul_left]
#align gcd_mul_right gcd_mul_right

@[simp]
theorem gcd_mul_right' [GCDMonoid α] (a b c : α) : Associated (gcd (b * a) (c * a)) (gcd b c * a) :=
  by simp only [mul_comm, gcd_mul_left']
#align gcd_mul_right' gcd_mul_right'

theorem gcd_eq_left_iff [NormalizedGCDMonoid α] (a b : α) (h : normalize a = a) :
    gcd a b = a ↔ a ∣ b :=
  (Iff.intro fun eq => eq ▸ gcd_dvd_right _ _) fun hab =>
    dvd_antisymm_of_normalize_eq (normalize_gcd _ _) h (gcd_dvd_left _ _) (dvd_gcd (dvd_refl a) hab)
#align gcd_eq_left_iff gcd_eq_left_iff

theorem gcd_eq_right_iff [NormalizedGCDMonoid α] (a b : α) (h : normalize b = b) :
    gcd a b = b ↔ b ∣ a := by simpa only [gcd_comm a b] using gcd_eq_left_iff b a h
#align gcd_eq_right_iff gcd_eq_right_iff

theorem gcd_dvd_gcd_mul_left [GCDMonoid α] (m n k : α) : gcd m n ∣ gcd (k * m) n :=
  gcd_dvd_gcd (dvd_mul_left _ _) dvd_rfl
#align gcd_dvd_gcd_mul_left gcd_dvd_gcd_mul_left

theorem gcd_dvd_gcd_mul_right [GCDMonoid α] (m n k : α) : gcd m n ∣ gcd (m * k) n :=
  gcd_dvd_gcd (dvd_mul_right _ _) dvd_rfl
#align gcd_dvd_gcd_mul_right gcd_dvd_gcd_mul_right

theorem gcd_dvd_gcd_mul_left_right [GCDMonoid α] (m n k : α) : gcd m n ∣ gcd m (k * n) :=
  gcd_dvd_gcd dvd_rfl (dvd_mul_left _ _)
#align gcd_dvd_gcd_mul_left_right gcd_dvd_gcd_mul_left_right

theorem gcd_dvd_gcd_mul_right_right [GCDMonoid α] (m n k : α) : gcd m n ∣ gcd m (n * k) :=
  gcd_dvd_gcd dvd_rfl (dvd_mul_right _ _)
#align gcd_dvd_gcd_mul_right_right gcd_dvd_gcd_mul_right_right

theorem Associated.gcd_eq_left [NormalizedGCDMonoid α] {m n : α} (h : Associated m n) (k : α) :
    gcd m k = gcd n k :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) (gcd_dvd_gcd h.dvd dvd_rfl)
    (gcd_dvd_gcd h.symm.dvd dvd_rfl)
#align associated.gcd_eq_left Associated.gcd_eq_left

theorem Associated.gcd_eq_right [NormalizedGCDMonoid α] {m n : α} (h : Associated m n) (k : α) :
    gcd k m = gcd k n :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) (gcd_dvd_gcd dvd_rfl h.dvd)
    (gcd_dvd_gcd dvd_rfl h.symm.dvd)
#align associated.gcd_eq_right Associated.gcd_eq_right

theorem dvd_gcd_mul_of_dvd_mul [GCDMonoid α] {m n k : α} (H : k ∣ m * n) : k ∣ gcd k m * n :=
  (dvd_gcd (dvd_mul_right _ n) H).trans (gcd_mul_right' n k m).dvd
#align dvd_gcd_mul_of_dvd_mul dvd_gcd_mul_of_dvd_mul

theorem dvd_gcd_mul_iff_dvd_mul [GCDMonoid α] {m n k : α} : k ∣ gcd k m * n ↔ k ∣ m * n :=
  ⟨fun h => h.trans (mul_dvd_mul (gcd_dvd_right k m) dvd_rfl), dvd_gcd_mul_of_dvd_mul⟩

theorem dvd_mul_gcd_of_dvd_mul [GCDMonoid α] {m n k : α} (H : k ∣ m * n) : k ∣ m * gcd k n := by
  rw [mul_comm] at H ⊢
  exact dvd_gcd_mul_of_dvd_mul H
#align dvd_mul_gcd_of_dvd_mul dvd_mul_gcd_of_dvd_mul

theorem dvd_mul_gcd_iff_dvd_mul [GCDMonoid α] {m n k : α} : k ∣ m * gcd k n ↔ k ∣ m * n :=
  ⟨fun h => h.trans (mul_dvd_mul dvd_rfl (gcd_dvd_right k n)), dvd_mul_gcd_of_dvd_mul⟩

/-- Represent a divisor of `m * n` as a product of a divisor of `m` and a divisor of `n`.

Note: In general, this representation is highly non-unique.

See `Nat.prodDvdAndDvdOfDvdProd` for a constructive version on `ℕ`.  -/
instance [h : Nonempty (GCDMonoid α)] : DecompositionMonoid α where
  primal k m n H := by
    cases h
    by_cases h0 : gcd k m = 0
    · rw [gcd_eq_zero_iff] at h0
      rcases h0 with ⟨rfl, rfl⟩
      refine' ⟨0, n, dvd_refl 0, dvd_refl n, _⟩
      simp
    · obtain ⟨a, ha⟩ := gcd_dvd_left k m
      refine' ⟨gcd k m, a, gcd_dvd_right _ _, _, ha⟩
      suffices h : gcd k m * a ∣ gcd k m * n by
        cases' h with b hb
        use b
        rw [mul_assoc] at hb
        apply mul_left_cancel₀ h0 hb
      rw [← ha]
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
#align gcd_mul_dvd_mul_gcd gcd_mul_dvd_mul_gcd

theorem gcd_pow_right_dvd_pow_gcd [GCDMonoid α] {a b : α} {k : ℕ} :
    gcd a (b ^ k) ∣ gcd a b ^ k := by
  by_cases hg : gcd a b = 0
  · rw [gcd_eq_zero_iff] at hg
    rcases hg with ⟨rfl, rfl⟩
    exact
      (gcd_zero_left' (0 ^ k : α)).dvd.trans
        (pow_dvd_pow_of_dvd (gcd_zero_left' (0 : α)).symm.dvd _)
  · induction' k with k hk
    · rw [pow_zero, pow_zero]
      exact (gcd_one_right' a).dvd
    rw [pow_succ, pow_succ]
    trans gcd a b * gcd a (b ^ k)
    · exact gcd_mul_dvd_mul_gcd a b (b ^ k)
    · exact (mul_dvd_mul_iff_left hg).mpr hk
#align gcd_pow_right_dvd_pow_gcd gcd_pow_right_dvd_pow_gcd

theorem gcd_pow_left_dvd_pow_gcd [GCDMonoid α] {a b : α} {k : ℕ} : gcd (a ^ k) b ∣ gcd a b ^ k :=
  calc
    gcd (a ^ k) b ∣ gcd b (a ^ k) := (gcd_comm' _ _).dvd
    _ ∣ gcd b a ^ k := gcd_pow_right_dvd_pow_gcd
    _ ∣ gcd a b ^ k := pow_dvd_pow_of_dvd (gcd_comm' _ _).dvd _
#align gcd_pow_left_dvd_pow_gcd gcd_pow_left_dvd_pow_gcd

theorem pow_dvd_of_mul_eq_pow [GCDMonoid α] {a b c d₁ d₂ : α} (ha : a ≠ 0) (hab : IsUnit (gcd a b))
    {k : ℕ} (h : a * b = c ^ k) (hc : c = d₁ * d₂) (hd₁ : d₁ ∣ a) : d₁ ^ k ≠ 0 ∧ d₁ ^ k ∣ a := by
  have h1 : IsUnit (gcd (d₁ ^ k) b) := by
    apply isUnit_of_dvd_one
    trans gcd d₁ b ^ k
    · exact gcd_pow_left_dvd_pow_gcd
    · apply IsUnit.dvd
      apply IsUnit.pow
      apply isUnit_of_dvd_one
      apply dvd_trans _ hab.dvd
      apply gcd_dvd_gcd hd₁ (dvd_refl b)
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
#align pow_dvd_of_mul_eq_pow pow_dvd_of_mul_eq_pow

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
#align exists_associated_pow_of_mul_eq_pow exists_associated_pow_of_mul_eq_pow

theorem exists_eq_pow_of_mul_eq_pow [GCDMonoid α] [Unique αˣ] {a b c : α} (hab : IsUnit (gcd a b))
    {k : ℕ} (h : a * b = c ^ k) : ∃ d : α, a = d ^ k :=
  let ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow hab h
  ⟨d, (associated_iff_eq.mp hd).symm⟩
#align exists_eq_pow_of_mul_eq_pow exists_eq_pow_of_mul_eq_pow

theorem gcd_greatest {α : Type*} [CancelCommMonoidWithZero α] [NormalizedGCDMonoid α] {a b d : α}
    (hda : d ∣ a) (hdb : d ∣ b) (hd : ∀ e : α, e ∣ a → e ∣ b → e ∣ d) :
    GCDMonoid.gcd a b = normalize d :=
  haveI h := hd _ (GCDMonoid.gcd_dvd_left a b) (GCDMonoid.gcd_dvd_right a b)
  gcd_eq_normalize h (GCDMonoid.dvd_gcd hda hdb)
#align gcd_greatest gcd_greatest

theorem gcd_greatest_associated {α : Type*} [CancelCommMonoidWithZero α] [GCDMonoid α] {a b d : α}
    (hda : d ∣ a) (hdb : d ∣ b) (hd : ∀ e : α, e ∣ a → e ∣ b → e ∣ d) :
    Associated d (GCDMonoid.gcd a b) :=
  haveI h := hd _ (GCDMonoid.gcd_dvd_left a b) (GCDMonoid.gcd_dvd_right a b)
  associated_of_dvd_dvd (GCDMonoid.dvd_gcd hda hdb) h
#align gcd_greatest_associated gcd_greatest_associated

theorem isUnit_gcd_of_eq_mul_gcd {α : Type*} [CancelCommMonoidWithZero α] [GCDMonoid α]
    {x y x' y' : α} (ex : x = gcd x y * x') (ey : y = gcd x y * y') (h : gcd x y ≠ 0) :
    IsUnit (gcd x' y') := by
  rw [← associated_one_iff_isUnit]
  refine' Associated.of_mul_left _ (Associated.refl <| gcd x y) h
  convert (gcd_mul_left' (gcd x y) x' y').symm using 1
  rw [← ex, ← ey, mul_one]
#align is_unit_gcd_of_eq_mul_gcd isUnit_gcd_of_eq_mul_gcd

theorem extract_gcd {α : Type*} [CancelCommMonoidWithZero α] [GCDMonoid α] (x y : α) :
    ∃ x' y', x = gcd x y * x' ∧ y = gcd x y * y' ∧ IsUnit (gcd x' y') := by
  by_cases h : gcd x y = 0
  · obtain ⟨rfl, rfl⟩ := (gcd_eq_zero_iff x y).1 h
    simp_rw [← associated_one_iff_isUnit]
    exact ⟨1, 1, by rw [h, zero_mul], by rw [h, zero_mul], gcd_one_left' 1⟩
  obtain ⟨x', ex⟩ := gcd_dvd_left x y
  obtain ⟨y', ey⟩ := gcd_dvd_right x y
  exact ⟨x', y', ex, ey, isUnit_gcd_of_eq_mul_gcd ex ey h⟩
#align extract_gcd extract_gcd

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

end GCD

section LCM

theorem lcm_dvd_iff [GCDMonoid α] {a b c : α} : lcm a b ∣ c ↔ a ∣ c ∧ b ∣ c := by
  by_cases h : a = 0 ∨ b = 0
  · rcases h with (rfl | rfl) <;>
      simp (config := { contextual := true }) only [iff_def, lcm_zero_left, lcm_zero_right,
        zero_dvd_iff, dvd_zero, eq_self_iff_true, and_true_iff, imp_true_iff]
  · obtain ⟨h1, h2⟩ := not_or.1 h
    have h : gcd a b ≠ 0 := fun H => h1 ((gcd_eq_zero_iff _ _).1 H).1
    rw [← mul_dvd_mul_iff_left h, (gcd_mul_lcm a b).dvd_iff_dvd_left, ←
      (gcd_mul_right' c a b).dvd_iff_dvd_right, dvd_gcd_iff, mul_comm b c, mul_dvd_mul_iff_left h1,
      mul_dvd_mul_iff_right h2, and_comm]
#align lcm_dvd_iff lcm_dvd_iff

theorem dvd_lcm_left [GCDMonoid α] (a b : α) : a ∣ lcm a b :=
  (lcm_dvd_iff.1 (dvd_refl (lcm a b))).1
#align dvd_lcm_left dvd_lcm_left

theorem dvd_lcm_right [GCDMonoid α] (a b : α) : b ∣ lcm a b :=
  (lcm_dvd_iff.1 (dvd_refl (lcm a b))).2
#align dvd_lcm_right dvd_lcm_right

theorem lcm_dvd [GCDMonoid α] {a b c : α} (hab : a ∣ b) (hcb : c ∣ b) : lcm a c ∣ b :=
  lcm_dvd_iff.2 ⟨hab, hcb⟩
#align lcm_dvd lcm_dvd

@[simp]
theorem lcm_eq_zero_iff [GCDMonoid α] (a b : α) : lcm a b = 0 ↔ a = 0 ∨ b = 0 :=
  Iff.intro
    (fun h : lcm a b = 0 => by
      have : Associated (a * b) 0 := (gcd_mul_lcm a b).symm.trans <| by rw [h, mul_zero]
      rwa [← mul_eq_zero, ← associated_zero_iff_eq_zero])
    (by rintro (rfl | rfl) <;> [apply lcm_zero_left; apply lcm_zero_right])
#align lcm_eq_zero_iff lcm_eq_zero_iff

-- Porting note: lower priority to avoid linter complaints about simp-normal form
@[simp 1100]
theorem normalize_lcm [NormalizedGCDMonoid α] (a b : α) : normalize (lcm a b) = lcm a b :=
  NormalizedGCDMonoid.normalize_lcm a b
#align normalize_lcm normalize_lcm

theorem lcm_comm [NormalizedGCDMonoid α] (a b : α) : lcm a b = lcm b a :=
  dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _)
    (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))
    (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))
#align lcm_comm lcm_comm

theorem lcm_comm' [GCDMonoid α] (a b : α) : Associated (lcm a b) (lcm b a) :=
  associated_of_dvd_dvd (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))
    (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))
#align lcm_comm' lcm_comm'

theorem lcm_assoc [NormalizedGCDMonoid α] (m n k : α) : lcm (lcm m n) k = lcm m (lcm n k) :=
  dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _)
    (lcm_dvd (lcm_dvd (dvd_lcm_left _ _) ((dvd_lcm_left _ _).trans (dvd_lcm_right _ _)))
      ((dvd_lcm_right _ _).trans (dvd_lcm_right _ _)))
    (lcm_dvd ((dvd_lcm_left _ _).trans (dvd_lcm_left _ _))
      (lcm_dvd ((dvd_lcm_right _ _).trans (dvd_lcm_left _ _)) (dvd_lcm_right _ _)))
#align lcm_assoc lcm_assoc

theorem lcm_assoc' [GCDMonoid α] (m n k : α) : Associated (lcm (lcm m n) k) (lcm m (lcm n k)) :=
  associated_of_dvd_dvd
    (lcm_dvd (lcm_dvd (dvd_lcm_left _ _) ((dvd_lcm_left _ _).trans (dvd_lcm_right _ _)))
      ((dvd_lcm_right _ _).trans (dvd_lcm_right _ _)))
    (lcm_dvd ((dvd_lcm_left _ _).trans (dvd_lcm_left _ _))
      (lcm_dvd ((dvd_lcm_right _ _).trans (dvd_lcm_left _ _)) (dvd_lcm_right _ _)))
#align lcm_assoc' lcm_assoc'

instance [NormalizedGCDMonoid α] : Std.Commutative (α := α) lcm where
  comm := lcm_comm

instance [NormalizedGCDMonoid α] : Std.Associative (α := α) lcm where
  assoc := lcm_assoc

theorem lcm_eq_normalize [NormalizedGCDMonoid α] {a b c : α} (habc : lcm a b ∣ c)
    (hcab : c ∣ lcm a b) : lcm a b = normalize c :=
  normalize_lcm a b ▸ normalize_eq_normalize habc hcab
#align lcm_eq_normalize lcm_eq_normalize

theorem lcm_dvd_lcm [GCDMonoid α] {a b c d : α} (hab : a ∣ b) (hcd : c ∣ d) : lcm a c ∣ lcm b d :=
  lcm_dvd (hab.trans (dvd_lcm_left _ _)) (hcd.trans (dvd_lcm_right _ _))
#align lcm_dvd_lcm lcm_dvd_lcm

@[simp]
theorem lcm_units_coe_left [NormalizedGCDMonoid α] (u : αˣ) (a : α) : lcm (↑u) a = normalize a :=
  lcm_eq_normalize (lcm_dvd Units.coe_dvd dvd_rfl) (dvd_lcm_right _ _)
#align lcm_units_coe_left lcm_units_coe_left

@[simp]
theorem lcm_units_coe_right [NormalizedGCDMonoid α] (a : α) (u : αˣ) : lcm a ↑u = normalize a :=
  (lcm_comm a u).trans <| lcm_units_coe_left _ _
#align lcm_units_coe_right lcm_units_coe_right

@[simp]
theorem lcm_one_left [NormalizedGCDMonoid α] (a : α) : lcm 1 a = normalize a :=
  lcm_units_coe_left 1 a
#align lcm_one_left lcm_one_left

@[simp]
theorem lcm_one_right [NormalizedGCDMonoid α] (a : α) : lcm a 1 = normalize a :=
  lcm_units_coe_right a 1
#align lcm_one_right lcm_one_right

@[simp]
theorem lcm_same [NormalizedGCDMonoid α] (a : α) : lcm a a = normalize a :=
  lcm_eq_normalize (lcm_dvd dvd_rfl dvd_rfl) (dvd_lcm_left _ _)
#align lcm_same lcm_same

@[simp]
theorem lcm_eq_one_iff [NormalizedGCDMonoid α] (a b : α) : lcm a b = 1 ↔ a ∣ 1 ∧ b ∣ 1 :=
  Iff.intro (fun eq => eq ▸ ⟨dvd_lcm_left _ _, dvd_lcm_right _ _⟩) fun ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ =>
    show lcm (Units.mkOfMulEqOne a c hc.symm : α) (Units.mkOfMulEqOne b d hd.symm) = 1 by
      rw [lcm_units_coe_left, normalize_coe_units]
#align lcm_eq_one_iff lcm_eq_one_iff

@[simp]
theorem lcm_mul_left [NormalizedGCDMonoid α] (a b c : α) :
    lcm (a * b) (a * c) = normalize a * lcm b c :=
  (by_cases (by rintro rfl; simp only [zero_mul, lcm_zero_left, normalize_zero]))
    fun ha : a ≠ 0 =>
    suffices lcm (a * b) (a * c) = normalize (a * lcm b c) by simpa
    have : a ∣ lcm (a * b) (a * c) := (dvd_mul_right _ _).trans (dvd_lcm_left _ _)
    let ⟨d, eq⟩ := this
    lcm_eq_normalize
      (lcm_dvd (mul_dvd_mul_left a (dvd_lcm_left _ _)) (mul_dvd_mul_left a (dvd_lcm_right _ _)))
      (eq.symm ▸
        (mul_dvd_mul_left a <|
          lcm_dvd ((mul_dvd_mul_iff_left ha).1 <| eq ▸ dvd_lcm_left _ _)
            ((mul_dvd_mul_iff_left ha).1 <| eq ▸ dvd_lcm_right _ _)))
#align lcm_mul_left lcm_mul_left

@[simp]
theorem lcm_mul_right [NormalizedGCDMonoid α] (a b c : α) :
    lcm (b * a) (c * a) = lcm b c * normalize a := by simp only [mul_comm, lcm_mul_left]
#align lcm_mul_right lcm_mul_right

theorem lcm_eq_left_iff [NormalizedGCDMonoid α] (a b : α) (h : normalize a = a) :
    lcm a b = a ↔ b ∣ a :=
  (Iff.intro fun eq => eq ▸ dvd_lcm_right _ _) fun hab =>
    dvd_antisymm_of_normalize_eq (normalize_lcm _ _) h (lcm_dvd (dvd_refl a) hab) (dvd_lcm_left _ _)
#align lcm_eq_left_iff lcm_eq_left_iff

theorem lcm_eq_right_iff [NormalizedGCDMonoid α] (a b : α) (h : normalize b = b) :
    lcm a b = b ↔ a ∣ b := by simpa only [lcm_comm b a] using lcm_eq_left_iff b a h
#align lcm_eq_right_iff lcm_eq_right_iff

theorem lcm_dvd_lcm_mul_left [GCDMonoid α] (m n k : α) : lcm m n ∣ lcm (k * m) n :=
  lcm_dvd_lcm (dvd_mul_left _ _) dvd_rfl
#align lcm_dvd_lcm_mul_left lcm_dvd_lcm_mul_left

theorem lcm_dvd_lcm_mul_right [GCDMonoid α] (m n k : α) : lcm m n ∣ lcm (m * k) n :=
  lcm_dvd_lcm (dvd_mul_right _ _) dvd_rfl
#align lcm_dvd_lcm_mul_right lcm_dvd_lcm_mul_right

theorem lcm_dvd_lcm_mul_left_right [GCDMonoid α] (m n k : α) : lcm m n ∣ lcm m (k * n) :=
  lcm_dvd_lcm dvd_rfl (dvd_mul_left _ _)
#align lcm_dvd_lcm_mul_left_right lcm_dvd_lcm_mul_left_right

theorem lcm_dvd_lcm_mul_right_right [GCDMonoid α] (m n k : α) : lcm m n ∣ lcm m (n * k) :=
  lcm_dvd_lcm dvd_rfl (dvd_mul_right _ _)
#align lcm_dvd_lcm_mul_right_right lcm_dvd_lcm_mul_right_right

theorem lcm_eq_of_associated_left [NormalizedGCDMonoid α] {m n : α} (h : Associated m n) (k : α) :
    lcm m k = lcm n k :=
  dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _) (lcm_dvd_lcm h.dvd dvd_rfl)
    (lcm_dvd_lcm h.symm.dvd dvd_rfl)
#align lcm_eq_of_associated_left lcm_eq_of_associated_left

theorem lcm_eq_of_associated_right [NormalizedGCDMonoid α] {m n : α} (h : Associated m n) (k : α) :
    lcm k m = lcm k n :=
  dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _) (lcm_dvd_lcm dvd_rfl h.dvd)
    (lcm_dvd_lcm dvd_rfl h.symm.dvd)
#align lcm_eq_of_associated_right lcm_eq_of_associated_right

end LCM

@[deprecated] alias GCDMonoid.prime_of_irreducible := Irreducible.prime
#align gcd_monoid.prime_of_irreducible Irreducible.prime
@[deprecated] alias GCDMonoid.irreducible_iff_prime := irreducible_iff_prime
#align gcd_monoid.irreducible_iff_prime irreducible_iff_prime

end GCDMonoid

section UniqueUnit

variable [CancelCommMonoidWithZero α] [Unique αˣ]

-- see Note [lower instance priority]
instance (priority := 100) normalizationMonoidOfUniqueUnits : NormalizationMonoid α where
  normUnit _ := 1
  normUnit_zero := rfl
  normUnit_mul _ _ := (mul_one 1).symm
  normUnit_coe_units _ := Subsingleton.elim _ _
#align normalization_monoid_of_unique_units normalizationMonoidOfUniqueUnits

instance uniqueNormalizationMonoidOfUniqueUnits : Unique (NormalizationMonoid α) where
  default := normalizationMonoidOfUniqueUnits
  uniq := fun ⟨u, _, _, _⟩ => by congr; simp [eq_iff_true_of_subsingleton]
#align unique_normalization_monoid_of_unique_units uniqueNormalizationMonoidOfUniqueUnits

instance subsingleton_gcdMonoid_of_unique_units : Subsingleton (GCDMonoid α) :=
  ⟨fun g₁ g₂ => by
    have hgcd : g₁.gcd = g₂.gcd := by
      ext a b
      refine' associated_iff_eq.mp (associated_of_dvd_dvd _ _)
      -- Porting note: Lean4 seems to need help specifying `g₁` and `g₂`
      · exact dvd_gcd (@gcd_dvd_left _ _ g₁ _ _) (@gcd_dvd_right _ _ g₁ _ _)
      · exact @dvd_gcd _ _ g₁ _ _ _ (@gcd_dvd_left _ _ g₂ _ _) (@gcd_dvd_right _ _ g₂ _ _)
    have hlcm : g₁.lcm = g₂.lcm := by
      ext a b
      -- Porting note: Lean4 seems to need help specifying `g₁` and `g₂`
      refine' associated_iff_eq.mp (associated_of_dvd_dvd _ _)
      · exact (@lcm_dvd_iff _ _ g₁ ..).mpr ⟨@dvd_lcm_left _ _ g₂ _ _, @dvd_lcm_right _ _ g₂ _ _⟩
      · exact lcm_dvd_iff.mpr ⟨@dvd_lcm_left _ _ g₁ _ _, @dvd_lcm_right _ _ g₁ _ _⟩
    cases g₁
    cases g₂
    dsimp only at hgcd hlcm
    simp only [hgcd, hlcm]⟩
#align subsingleton_gcd_monoid_of_unique_units subsingleton_gcdMonoid_of_unique_units

instance subsingleton_normalizedGCDMonoid_of_unique_units : Subsingleton (NormalizedGCDMonoid α) :=
  ⟨by
    intro a b
    cases' a with a_norm a_gcd
    cases' b with b_norm b_gcd
    have := Subsingleton.elim a_gcd b_gcd
    subst this
    have := Subsingleton.elim a_norm b_norm
    subst this
    rfl⟩
#align subsingleton_normalized_gcd_monoid_of_unique_units subsingleton_normalizedGCDMonoid_of_unique_units

@[simp]
theorem normUnit_eq_one (x : α) : normUnit x = 1 :=
  rfl
#align norm_unit_eq_one normUnit_eq_one

-- Porting note: `simp` can prove this
-- @[simp]
theorem normalize_eq (x : α) : normalize x = x :=
  mul_one x
#align normalize_eq normalize_eq

/-- If a monoid's only unit is `1`, then it is isomorphic to its associates. -/
@[simps]
def associatesEquivOfUniqueUnits : Associates α ≃* α where
  toFun := Associates.out
  invFun := Associates.mk
  left_inv := Associates.mk_out
  right_inv _ := (Associates.out_mk _).trans <| normalize_eq _
  map_mul' := Associates.out_mul
#align associates_equiv_of_unique_units associatesEquivOfUniqueUnits
#align associates_equiv_of_unique_units_symm_apply associatesEquivOfUniqueUnits_symm_apply
#align associates_equiv_of_unique_units_apply associatesEquivOfUniqueUnits_apply

end UniqueUnit

section IsDomain

variable [CommRing α] [IsDomain α] [NormalizedGCDMonoid α]

theorem gcd_eq_of_dvd_sub_right {a b c : α} (h : a ∣ b - c) : gcd a b = gcd a c := by
  apply dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) <;>
    rw [dvd_gcd_iff] <;>
    refine' ⟨gcd_dvd_left _ _, _⟩
  · rcases h with ⟨d, hd⟩
    rcases gcd_dvd_right a b with ⟨e, he⟩
    rcases gcd_dvd_left a b with ⟨f, hf⟩
    use e - f * d
    rw [mul_sub, ← he, ← mul_assoc, ← hf, ← hd, sub_sub_cancel]
  · rcases h with ⟨d, hd⟩
    rcases gcd_dvd_right a c with ⟨e, he⟩
    rcases gcd_dvd_left a c with ⟨f, hf⟩
    use e + f * d
    rw [mul_add, ← he, ← mul_assoc, ← hf, ← hd, ← add_sub_assoc, add_comm c b, add_sub_cancel]
#align gcd_eq_of_dvd_sub_right gcd_eq_of_dvd_sub_right

theorem gcd_eq_of_dvd_sub_left {a b c : α} (h : a ∣ b - c) : gcd b a = gcd c a := by
  rw [gcd_comm _ a, gcd_comm _ a, gcd_eq_of_dvd_sub_right h]
#align gcd_eq_of_dvd_sub_left gcd_eq_of_dvd_sub_left

end IsDomain

noncomputable section Constructors

open Associates

variable [CancelCommMonoidWithZero α]

private theorem map_mk_unit_aux [DecidableEq α] {f : Associates α →* α}
    (hinv : Function.RightInverse f Associates.mk) (a : α) :
    a * ↑(Classical.choose (associated_map_mk hinv a)) = f (Associates.mk a) :=
  Classical.choose_spec (associated_map_mk hinv a)

/-- Define `NormalizationMonoid` on a structure from a `MonoidHom` inverse to `Associates.mk`. -/
def normalizationMonoidOfMonoidHomRightInverse [DecidableEq α] (f : Associates α →* α)
    (hinv : Function.RightInverse f Associates.mk) :
    NormalizationMonoid α where
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
      -- Porting note: original `simpa` fails with `unexpected bound variable #1`
      -- simpa only [mul_assoc, mul_comm, mul_left_comm] using this
      rw [this, mul_assoc, ← mul_assoc _ b, mul_comm _ b, ← mul_assoc, ← mul_assoc,
        mul_assoc (a * b)]
    rw [map_mk_unit_aux hinv a, map_mk_unit_aux hinv (a * b), map_mk_unit_aux hinv b, ←
      MonoidHom.map_mul, Associates.mk_mul_mk]
  normUnit_coe_units u := by
    nontriviality α
    simp_rw [if_neg (Units.ne_zero u), Units.ext_iff]
    apply mul_left_cancel₀ (Units.ne_zero u)
    rw [Units.mul_inv, map_mk_unit_aux hinv u,
      Associates.mk_eq_mk_iff_associated.2 (associated_one_iff_isUnit.2 ⟨u, rfl⟩),
      Associates.mk_one, MonoidHom.map_one]
#align normalization_monoid_of_monoid_hom_right_inverse normalizationMonoidOfMonoidHomRightInverse

/-- Define `GCDMonoid` on a structure just from the `gcd` and its properties. -/
noncomputable def gcdMonoidOfGCD [DecidableEq α] (gcd : α → α → α)
    (gcd_dvd_left : ∀ a b, gcd a b ∣ a) (gcd_dvd_right : ∀ a b, gcd a b ∣ b)
    (dvd_gcd : ∀ {a b c}, a ∣ c → a ∣ b → a ∣ gcd c b) : GCDMonoid α :=
  { gcd
    gcd_dvd_left
    gcd_dvd_right
    dvd_gcd := fun {a b c} => dvd_gcd
    lcm := fun a b =>
      if a = 0 then 0 else Classical.choose ((gcd_dvd_left a b).trans (Dvd.intro b rfl))
    gcd_mul_lcm := fun a b => by
      -- Porting note: need `dsimp only` before `split_ifs`
      dsimp only
      split_ifs with a0
      · rw [mul_zero, a0, zero_mul]
      · rw [← Classical.choose_spec ((gcd_dvd_left a b).trans (Dvd.intro b rfl))]
    lcm_zero_left := fun a => if_pos rfl
    lcm_zero_right := fun a => by
      -- Porting note: need `dsimp only` before `split_ifs`
      dsimp only
      split_ifs with a0
      · rfl
      have h := (Classical.choose_spec ((gcd_dvd_left a 0).trans (Dvd.intro 0 rfl))).symm
      have a0' : gcd a 0 ≠ 0 := by
        contrapose! a0
        rw [← associated_zero_iff_eq_zero, ← a0]
        exact associated_of_dvd_dvd (dvd_gcd (dvd_refl a) (dvd_zero a)) (gcd_dvd_left _ _)
      apply Or.resolve_left (mul_eq_zero.1 _) a0'
      rw [h, mul_zero] }
#align gcd_monoid_of_gcd gcdMonoidOfGCD

/-- Define `NormalizedGCDMonoid` on a structure just from the `gcd` and its properties. -/
noncomputable def normalizedGCDMonoidOfGCD [NormalizationMonoid α] [DecidableEq α] (gcd : α → α → α)
    (gcd_dvd_left : ∀ a b, gcd a b ∣ a) (gcd_dvd_right : ∀ a b, gcd a b ∣ b)
    (dvd_gcd : ∀ {a b c}, a ∣ c → a ∣ b → a ∣ gcd c b)
    (normalize_gcd : ∀ a b, normalize (gcd a b) = gcd a b) : NormalizedGCDMonoid α :=
  { (inferInstance : NormalizationMonoid α) with
    gcd
    gcd_dvd_left
    gcd_dvd_right
    dvd_gcd := fun {a b c} => dvd_gcd
    normalize_gcd
    lcm := fun a b =>
      if a = 0 then 0
      else Classical.choose (dvd_normalize_iff.2 ((gcd_dvd_left a b).trans (Dvd.intro b rfl)))
    normalize_lcm := fun a b => by
      dsimp [normalize]
      split_ifs with a0
      · exact @normalize_zero α _ _
      · have := (Classical.choose_spec
          (dvd_normalize_iff.2 ((gcd_dvd_left a b).trans (Dvd.intro b rfl)))).symm
        set l := Classical.choose (dvd_normalize_iff.2 ((gcd_dvd_left a b).trans (Dvd.intro b rfl)))
        obtain rfl | hb := eq_or_ne b 0
        -- Porting note: using `simp only` causes the propositions inside `Classical.choose` to
        -- differ, so `set` is unable to produce `l = 0` inside `this`. See
        -- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/
        -- Classical.2Echoose/near/317491179
        · rw [mul_zero a, normalize_zero, mul_eq_zero] at this
          obtain ha | hl := this
          · apply (a0 _).elim
            rw [← zero_dvd_iff, ← ha]
            exact gcd_dvd_left _ _
          · rw [hl, zero_mul]
        have h1 : gcd a b ≠ 0 := by
          have hab : a * b ≠ 0 := mul_ne_zero a0 hb
          contrapose! hab
          rw [← normalize_eq_zero, ← this, hab, zero_mul]
        have h2 : normalize (gcd a b * l) = gcd a b * l := by rw [this, normalize_idem]
        rw [← normalize_gcd] at this
        rwa [normalize.map_mul, normalize_gcd, mul_right_inj' h1] at h2
    gcd_mul_lcm := fun a b => by
      -- Porting note: need `dsimp only`
      dsimp only
      split_ifs with a0
      · rw [mul_zero, a0, zero_mul]
      · rw [←
          Classical.choose_spec (dvd_normalize_iff.2 ((gcd_dvd_left a b).trans (Dvd.intro b rfl)))]
        exact normalize_associated (a * b)
    lcm_zero_left := fun a => if_pos rfl
    lcm_zero_right := fun a => by
      -- Porting note: need `dsimp only`
      dsimp only
      split_ifs with a0
      · rfl
      rw [← normalize_eq_zero] at a0
      have h :=
        (Classical.choose_spec
            (dvd_normalize_iff.2 ((gcd_dvd_left a 0).trans (Dvd.intro 0 rfl)))).symm
      have gcd0 : gcd a 0 = normalize a := by
        rw [← normalize_gcd]
        exact normalize_eq_normalize (gcd_dvd_left _ _) (dvd_gcd (dvd_refl a) (dvd_zero a))
      rw [← gcd0] at a0
      apply Or.resolve_left (mul_eq_zero.1 _) a0
      rw [h, mul_zero, normalize_zero] }
#align normalized_gcd_monoid_of_gcd normalizedGCDMonoidOfGCD

/-- Define `GCDMonoid` on a structure just from the `lcm` and its properties. -/
noncomputable def gcdMonoidOfLCM [DecidableEq α] (lcm : α → α → α)
    (dvd_lcm_left : ∀ a b, a ∣ lcm a b) (dvd_lcm_right : ∀ a b, b ∣ lcm a b)
    (lcm_dvd : ∀ {a b c}, c ∣ a → b ∣ a → lcm c b ∣ a) : GCDMonoid α :=
  let exists_gcd a b := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
  { lcm
    gcd := fun a b => if a = 0 then b else if b = 0 then a else Classical.choose (exists_gcd a b)
    gcd_mul_lcm := fun a b => by
      -- Porting note: need `dsimp only`
      dsimp only
      split_ifs with h h_1
      · rw [h, eq_zero_of_zero_dvd (dvd_lcm_left _ _), mul_zero, zero_mul]
      · rw [h_1, eq_zero_of_zero_dvd (dvd_lcm_right _ _), mul_zero]
      rw [mul_comm, ← Classical.choose_spec (exists_gcd a b)]
    lcm_zero_left := fun a => eq_zero_of_zero_dvd (dvd_lcm_left _ _)
    lcm_zero_right := fun a => eq_zero_of_zero_dvd (dvd_lcm_right _ _)
    gcd_dvd_left := fun a b => by
      -- Porting note: need `dsimp only`
      dsimp only
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
      -- Porting note: need `dsimp only`
      dsimp only
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
      -- Porting note: need `dsimp only`
      dsimp only
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
      push_neg at h_1
      rw [mul_comm a, ← mul_assoc, mul_dvd_mul_iff_right h_1.1]
      apply lcm_dvd (Dvd.intro d rfl)
      rw [mul_comm, mul_dvd_mul_iff_right h_1.2]
      apply ac }
#align gcd_monoid_of_lcm gcdMonoidOfLCM

-- Porting note: very slow; improve performance?
/-- Define `NormalizedGCDMonoid` on a structure just from the `lcm` and its properties. -/
noncomputable def normalizedGCDMonoidOfLCM [NormalizationMonoid α] [DecidableEq α] (lcm : α → α → α)
    (dvd_lcm_left : ∀ a b, a ∣ lcm a b) (dvd_lcm_right : ∀ a b, b ∣ lcm a b)
    (lcm_dvd : ∀ {a b c}, c ∣ a → b ∣ a → lcm c b ∣ a)
    (normalize_lcm : ∀ a b, normalize (lcm a b) = lcm a b) : NormalizedGCDMonoid α :=
  let exists_gcd a b := dvd_normalize_iff.2 (lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl))
  { (inferInstance : NormalizationMonoid α) with
    lcm
    gcd := fun a b =>
      if a = 0 then normalize b
      else if b = 0 then normalize a else Classical.choose (exists_gcd a b)
    gcd_mul_lcm := fun a b => by
      dsimp only
      split_ifs with h h_1
      · rw [h, eq_zero_of_zero_dvd (dvd_lcm_left _ _), mul_zero, zero_mul]
      · rw [h_1, eq_zero_of_zero_dvd (dvd_lcm_right _ _), mul_zero, mul_zero]
      rw [mul_comm, ← Classical.choose_spec (exists_gcd a b)]
      exact normalize_associated (a * b)
    normalize_lcm
    normalize_gcd := fun a b => by
      dsimp [normalize]
      split_ifs with h h_1
      · apply normalize_idem
      · apply normalize_idem
      have h0 : lcm a b ≠ 0 := by
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
        rw [con, zero_dvd_iff, mul_eq_zero] at h
        cases h
        · exact absurd ‹a = 0› h
        · exact absurd ‹b = 0› h_1
      apply mul_left_cancel₀ h0
      refine' _root_.trans _ (Classical.choose_spec (exists_gcd a b))
      conv_lhs =>
        congr
        rw [← normalize_lcm a b]
      erw [← normalize.map_mul, ← Classical.choose_spec (exists_gcd a b), normalize_idem]
    lcm_zero_left := fun a => eq_zero_of_zero_dvd (dvd_lcm_left _ _)
    lcm_zero_right := fun a => eq_zero_of_zero_dvd (dvd_lcm_right _ _)
    gcd_dvd_left := fun a b => by
      dsimp only
      split_ifs with h h_1
      · rw [h]
        apply dvd_zero
      · exact (normalize_associated _).dvd
      have h0 : lcm a b ≠ 0 := by
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
        rw [con, zero_dvd_iff, mul_eq_zero] at h
        cases h
        · exact absurd ‹a = 0› h
        · exact absurd ‹b = 0› h_1
      rw [← mul_dvd_mul_iff_left h0, ← Classical.choose_spec (exists_gcd a b), normalize_dvd_iff,
        mul_comm, mul_dvd_mul_iff_right h]
      apply dvd_lcm_right
    gcd_dvd_right := fun a b => by
      dsimp only
      split_ifs with h h_1
      · exact (normalize_associated _).dvd
      · rw [h_1]
        apply dvd_zero
      have h0 : lcm a b ≠ 0 := by
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
        rw [con, zero_dvd_iff, mul_eq_zero] at h
        cases h
        · exact absurd ‹a = 0› h
        · exact absurd ‹b = 0› h_1
      rw [← mul_dvd_mul_iff_left h0, ← Classical.choose_spec (exists_gcd a b), normalize_dvd_iff,
        mul_dvd_mul_iff_right h_1]
      apply dvd_lcm_left
    dvd_gcd := fun {a b c} ac ab => by
      dsimp only
      split_ifs with h h_1
      · apply dvd_normalize_iff.2 ab
      · apply dvd_normalize_iff.2 ac
      have h0 : lcm c b ≠ 0 := by
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left c rfl)
        rw [con, zero_dvd_iff, mul_eq_zero] at h
        cases h
        · exact absurd ‹c = 0› h
        · exact absurd ‹b = 0› h_1
      rw [← mul_dvd_mul_iff_left h0, ←
      Classical.choose_spec
        (dvd_normalize_iff.2 (lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left c rfl))),
      dvd_normalize_iff]
      rcases ab with ⟨d, rfl⟩
      rw [mul_eq_zero] at h_1
      push_neg at h_1
      rw [mul_comm a, ← mul_assoc, mul_dvd_mul_iff_right h_1.1]
      apply lcm_dvd (Dvd.intro d rfl)
      rw [mul_comm, mul_dvd_mul_iff_right h_1.2]
      apply ac }
#align normalized_gcd_monoid_of_lcm normalizedGCDMonoidOfLCM

/-- Define a `GCDMonoid` structure on a monoid just from the existence of a `gcd`. -/
noncomputable def gcdMonoidOfExistsGCD [DecidableEq α]
    (h : ∀ a b : α, ∃ c : α, ∀ d : α, d ∣ a ∧ d ∣ b ↔ d ∣ c) : GCDMonoid α :=
  gcdMonoidOfGCD (fun a b => Classical.choose (h a b))
    (fun a b => ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).1)
    (fun a b => ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).2)
    fun {a b c} ac ab => (Classical.choose_spec (h c b) a).1 ⟨ac, ab⟩
#align gcd_monoid_of_exists_gcd gcdMonoidOfExistsGCD

/-- Define a `NormalizedGCDMonoid` structure on a monoid just from the existence of a `gcd`. -/
noncomputable def normalizedGCDMonoidOfExistsGCD [NormalizationMonoid α] [DecidableEq α]
    (h : ∀ a b : α, ∃ c : α, ∀ d : α, d ∣ a ∧ d ∣ b ↔ d ∣ c) : NormalizedGCDMonoid α :=
  normalizedGCDMonoidOfGCD (fun a b => normalize (Classical.choose (h a b)))
    (fun a b =>
      normalize_dvd_iff.2 ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).1)
    (fun a b =>
      normalize_dvd_iff.2 ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).2)
    (fun {a b c} ac ab => dvd_normalize_iff.2 ((Classical.choose_spec (h c b) a).1 ⟨ac, ab⟩))
    fun _ _ => normalize_idem _
#align normalized_gcd_monoid_of_exists_gcd normalizedGCDMonoidOfExistsGCD

/-- Define a `GCDMonoid` structure on a monoid just from the existence of an `lcm`. -/
noncomputable def gcdMonoidOfExistsLCM [DecidableEq α]
    (h : ∀ a b : α, ∃ c : α, ∀ d : α, a ∣ d ∧ b ∣ d ↔ c ∣ d) : GCDMonoid α :=
  gcdMonoidOfLCM (fun a b => Classical.choose (h a b))
    (fun a b => ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).1)
    (fun a b => ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).2)
    fun {a b c} ac ab => (Classical.choose_spec (h c b) a).1 ⟨ac, ab⟩
#align gcd_monoid_of_exists_lcm gcdMonoidOfExistsLCM

/-- Define a `NormalizedGCDMonoid` structure on a monoid just from the existence of an `lcm`. -/
noncomputable def normalizedGCDMonoidOfExistsLCM [NormalizationMonoid α] [DecidableEq α]
    (h : ∀ a b : α, ∃ c : α, ∀ d : α, a ∣ d ∧ b ∣ d ↔ c ∣ d) : NormalizedGCDMonoid α :=
  normalizedGCDMonoidOfLCM (fun a b => normalize (Classical.choose (h a b)))
    (fun a b =>
      dvd_normalize_iff.2 ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).1)
    (fun a b =>
      dvd_normalize_iff.2 ((Classical.choose_spec (h a b) (Classical.choose (h a b))).2 dvd_rfl).2)
    (fun {a b c} ac ab => normalize_dvd_iff.2 ((Classical.choose_spec (h c b) a).1 ⟨ac, ab⟩))
    fun _ _ => normalize_idem _
#align normalized_gcd_monoid_of_exists_lcm normalizedGCDMonoidOfExistsLCM

end Constructors

namespace CommGroupWithZero

variable (G₀ : Type*) [CommGroupWithZero G₀] [DecidableEq G₀]

-- Porting note: very slow; improve performance?
-- see Note [lower instance priority]
instance (priority := 100) : NormalizedGCDMonoid G₀ where
  normUnit x := if h : x = 0 then 1 else (Units.mk0 x h)⁻¹
  normUnit_zero := dif_pos rfl
  normUnit_mul := fun {x y} x0 y0 => Units.eq_iff.1 (by
    -- Porting note: need `dsimp only`, also `simp` reaches maximum heartbeat
    -- by Units.eq_iff.mp (by simp only [x0, y0, mul_comm])
    dsimp only
    split_ifs with h
    · rw [mul_eq_zero] at h
      cases h
      · exact absurd ‹x = 0› x0
      · exact absurd ‹y = 0› y0
    · rw [Units.mk0_mul, mul_inv_rev, mul_comm] )
  normUnit_coe_units u := by
    -- Porting note: need `dsimp only`
    dsimp only
    rw [dif_neg (Units.ne_zero _), Units.mk0_val]
  gcd a b := if a = 0 ∧ b = 0 then 0 else 1
  lcm a b := if a = 0 ∨ b = 0 then 0 else 1
  gcd_dvd_left a b := by
    -- Porting note: need `dsimp only`
    dsimp only
    split_ifs with h
    · rw [h.1]
    · exact one_dvd _
  gcd_dvd_right a b := by
    -- Porting note: need `dsimp only`
    dsimp only
    split_ifs with h
    · rw [h.2]
    · exact one_dvd _
  dvd_gcd := fun {a b c} hac hab => by
    -- Porting note: need `dsimp only`
    dsimp only
    split_ifs with h
    · apply dvd_zero
    · rw [not_and_or] at h
      cases h
      · refine' isUnit_iff_dvd_one.mp (isUnit_of_dvd_unit _ (IsUnit.mk0 _ ‹c ≠ 0›))
        exact hac
      · refine' isUnit_iff_dvd_one.mp (isUnit_of_dvd_unit _ (IsUnit.mk0 _ ‹b ≠ 0›))
        exact hab
  gcd_mul_lcm a b := by
    by_cases ha : a = 0
    · simp only [ha, true_and, true_or, ite_true, mul_zero, zero_mul]
      exact Associated.refl _
    · by_cases hb : b = 0
      · simp only [hb, and_true, or_true, ite_true, mul_zero]
        exact Associated.refl _
      -- Porting note: need `dsimp only`
      · dsimp only
        rw [if_neg (not_and_of_not_left _ ha), one_mul, if_neg (not_or_of_not ha hb)]
        exact (associated_one_iff_isUnit.mpr ((IsUnit.mk0 _ ha).mul (IsUnit.mk0 _ hb))).symm
  lcm_zero_left b := if_pos (Or.inl rfl)
  lcm_zero_right a := if_pos (Or.inr rfl)
  -- `split_ifs` wants to split `normalize`, so handle the cases manually
  normalize_gcd a b := if h : a = 0 ∧ b = 0 then by simp [if_pos h] else by simp [if_neg h]
  normalize_lcm a b := if h : a = 0 ∨ b = 0 then by simp [if_pos h] else by simp [if_neg h]

@[simp]
theorem coe_normUnit {a : G₀} (h0 : a ≠ 0) : (↑(normUnit a) : G₀) = a⁻¹ := by simp [normUnit, h0]
#align comm_group_with_zero.coe_norm_unit CommGroupWithZero.coe_normUnit

theorem normalize_eq_one {a : G₀} (h0 : a ≠ 0) : normalize a = 1 := by simp [normalize_apply, h0]
#align comm_group_with_zero.normalize_eq_one CommGroupWithZero.normalize_eq_one

end CommGroupWithZero
