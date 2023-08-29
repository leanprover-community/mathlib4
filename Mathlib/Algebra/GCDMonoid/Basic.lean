/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker
-/
import Mathlib.Algebra.Associated
import Mathlib.Algebra.GroupPower.Lemmas
import Mathlib.Algebra.Ring.Regular

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
    -- ⊢ 0 * ↑1 = 0
    exact mul_one (0:α)
    -- 🎉 no goals
  map_one' := by dsimp only; rw [normUnit_one, one_mul]; rfl
                 -- ⊢ 1 * ↑(normUnit 1) = 1
                             -- ⊢ ↑1 = 1
                                                         -- 🎉 no goals
  map_mul' x y :=
    (by_cases fun hx : x = 0 => by dsimp only; rw [hx, zero_mul, zero_mul, zero_mul]) fun hx =>
                                   -- ⊢ x * y * ↑(normUnit (x * y)) = x * ↑(normUnit x) * (y * ↑(normUnit y))
                                               -- 🎉 no goals
      (by_cases fun hy : y = 0 => by dsimp only; rw [hy, mul_zero, zero_mul, mul_zero]) fun hy => by
                                     -- ⊢ x * y * ↑(normUnit (x * y)) = x * ↑(normUnit x) * (y * ↑(normUnit y))
                                                 -- 🎉 no goals
        simp only [normUnit_mul hx hy, Units.val_mul]; simp only [mul_assoc, mul_left_comm y]
        -- ⊢ x * y * (↑(normUnit x) * ↑(normUnit y)) = x * ↑(normUnit x) * (y * ↑(normUni …
                                                       -- 🎉 no goals
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
                                                                   -- 🎉 no goals
#align normalize_coe_units normalize_coe_units

theorem normalize_eq_zero {x : α} : normalize x = 0 ↔ x = 0 :=
  ⟨fun hx => (associated_zero_iff_eq_zero x).1 <| hx ▸ associated_normalize _, by
    rintro rfl; exact normalize_zero⟩
    -- ⊢ ↑normalize 0 = 0
                -- 🎉 no goals
#align normalize_eq_zero normalize_eq_zero

theorem normalize_eq_one {x : α} : normalize x = 1 ↔ IsUnit x :=
  ⟨fun hx => isUnit_iff_exists_inv.2 ⟨_, hx⟩, fun ⟨u, hu⟩ => hu ▸ normalize_coe_units u⟩
#align normalize_eq_one normalize_eq_one

-- Porting note: quite slow. Improve performance?
@[simp]
theorem normUnit_mul_normUnit (a : α) : normUnit (a * normUnit a) = 1 := by
  nontriviality α using Subsingleton.elim a 0
  -- ⊢ normUnit (a * ↑(normUnit a)) = 1
  obtain rfl | h := eq_or_ne a 0
  -- ⊢ normUnit (0 * ↑(normUnit 0)) = 1
  · rw [normUnit_zero, zero_mul, normUnit_zero]
    -- 🎉 no goals
  · rw [normUnit_mul h (Units.ne_zero _), normUnit_coe_units, mul_inv_eq_one]
    -- 🎉 no goals
#align norm_unit_mul_norm_unit normUnit_mul_normUnit

theorem normalize_idem (x : α) : normalize (normalize x) = normalize x := by simp
                                                                             -- 🎉 no goals
#align normalize_idem normalize_idem

theorem normalize_eq_normalize {a b : α} (hab : a ∣ b) (hba : b ∣ a) :
    normalize a = normalize b := by
  nontriviality α
  -- ⊢ ↑normalize a = ↑normalize b
  rcases associated_of_dvd_dvd hab hba with ⟨u, rfl⟩
  -- ⊢ ↑normalize a = ↑normalize (a * ↑u)
  refine' by_cases (by rintro rfl; simp only [zero_mul]) fun ha : a ≠ 0 => _
  -- ⊢ ↑normalize a = ↑normalize (a * ↑u)
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
    -- 🎉 no goals
#align associates.out_mul Associates.out_mul

theorem dvd_out_iff (a : α) (b : Associates α) : a ∣ b.out ↔ Associates.mk a ≤ b :=
  Quotient.inductionOn b <| by
    simp [Associates.out_mk, Associates.quotient_mk_eq_mk, mk_le_mk_iff_dvd_iff]
    -- 🎉 no goals
#align associates.dvd_out_iff Associates.dvd_out_iff

theorem out_dvd_iff (a : α) (b : Associates α) : b.out ∣ a ↔ b ≤ Associates.mk a :=
  Quotient.inductionOn b <| by
    simp [Associates.out_mk, Associates.quotient_mk_eq_mk, mk_le_mk_iff_dvd_iff]
    -- 🎉 no goals
#align associates.out_dvd_iff Associates.out_dvd_iff

@[simp]
theorem out_top : (⊤ : Associates α).out = 0 :=
  normalize_zero
#align associates.out_top Associates.out_top

-- Porting note: lower priority to avoid linter complaints about simp-normal form
@[simp 1100]
theorem normalize_out (a : Associates α) :
  normalize a.out = a.out :=
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

-- Porting note: lower priority to avoid linter complaints about simp-normal form
@[simp 1100]
theorem normalize_gcd [NormalizedGCDMonoid α] :
  ∀ a b : α, normalize (gcd a b) = gcd a b :=
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

instance [NormalizedGCDMonoid α] : IsCommutative α gcd :=
  ⟨gcd_comm⟩

instance [NormalizedGCDMonoid α] : IsAssociative α gcd :=
  ⟨gcd_assoc⟩

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
      -- ⊢ a = 0 ∧ b = 0
      let ⟨cb, hb⟩ := gcd_dvd_right a b
      -- ⊢ a = 0 ∧ b = 0
      rw [h, zero_mul] at ha hb
      -- ⊢ a = 0 ∧ b = 0
      exact ⟨ha, hb⟩)
      -- 🎉 no goals
    fun ⟨ha, hb⟩ => by
    rw [ha, hb, ← zero_dvd_iff]
    -- ⊢ 0 ∣ gcd 0 0
    apply dvd_gcd <;> rfl
    -- ⊢ 0 ∣ 0
                      -- 🎉 no goals
                      -- 🎉 no goals
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
                -- ⊢ gcd (0 * b) (0 * c) = ↑normalize 0 * gcd b c
                            -- 🎉 no goals
    fun ha : a ≠ 0 =>
    suffices gcd (a * b) (a * c) = normalize (a * gcd b c) by simpa
                                                              -- 🎉 no goals
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
  -- ⊢ Associated (gcd (0 * b) (0 * c)) (0 * gcd b c)
  · simp only [zero_mul, gcd_zero_left']
    -- 🎉 no goals
  obtain ⟨d, eq⟩ := dvd_gcd (dvd_mul_right a b) (dvd_mul_right a c)
  -- ⊢ Associated (gcd (a * b) (a * c)) (a * gcd b c)
  apply associated_of_dvd_dvd
  -- ⊢ gcd (a * b) (a * c) ∣ a * gcd b c
  · rw [eq]
    -- ⊢ a * d ∣ a * gcd b c
    apply mul_dvd_mul_left
    -- ⊢ d ∣ gcd b c
    exact
      dvd_gcd ((mul_dvd_mul_iff_left ha).1 <| eq ▸ gcd_dvd_left _ _)
        ((mul_dvd_mul_iff_left ha).1 <| eq ▸ gcd_dvd_right _ _)
  · exact dvd_gcd (mul_dvd_mul_left a <| gcd_dvd_left _ _) (mul_dvd_mul_left a <| gcd_dvd_right _ _)
    -- 🎉 no goals
#align gcd_mul_left' gcd_mul_left'

@[simp]
theorem gcd_mul_right [NormalizedGCDMonoid α] (a b c : α) :
    gcd (b * a) (c * a) = gcd b c * normalize a := by simp only [mul_comm, gcd_mul_left]
                                                      -- 🎉 no goals
#align gcd_mul_right gcd_mul_right

@[simp]
theorem gcd_mul_right' [GCDMonoid α] (a b c : α) : Associated (gcd (b * a) (c * a)) (gcd b c * a) :=
  by simp only [mul_comm, gcd_mul_left']
     -- 🎉 no goals
#align gcd_mul_right' gcd_mul_right'

theorem gcd_eq_left_iff [NormalizedGCDMonoid α] (a b : α) (h : normalize a = a) :
    gcd a b = a ↔ a ∣ b :=
  (Iff.intro fun eq => eq ▸ gcd_dvd_right _ _) fun hab =>
    dvd_antisymm_of_normalize_eq (normalize_gcd _ _) h (gcd_dvd_left _ _) (dvd_gcd (dvd_refl a) hab)
#align gcd_eq_left_iff gcd_eq_left_iff

theorem gcd_eq_right_iff [NormalizedGCDMonoid α] (a b : α) (h : normalize b = b) :
    gcd a b = b ↔ b ∣ a := by simpa only [gcd_comm a b] using gcd_eq_left_iff b a h
                              -- 🎉 no goals
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

theorem dvd_mul_gcd_of_dvd_mul [GCDMonoid α] {m n k : α} (H : k ∣ m * n) : k ∣ m * gcd k n := by
  rw [mul_comm] at H ⊢
  -- ⊢ k ∣ gcd k n * m
  exact dvd_gcd_mul_of_dvd_mul H
  -- 🎉 no goals
#align dvd_mul_gcd_of_dvd_mul dvd_mul_gcd_of_dvd_mul

/-- Represent a divisor of `m * n` as a product of a divisor of `m` and a divisor of `n`.

In other words, the nonzero elements of a `GCDMonoid` form a decomposition monoid
(more widely known as a pre-Schreier domain in the context of rings).

Note: In general, this representation is highly non-unique.

See `Nat.prodDvdAndDvdOfDvdProd` for a constructive version on `ℕ`.  -/
theorem exists_dvd_and_dvd_of_dvd_mul [GCDMonoid α] {m n k : α} (H : k ∣ m * n) :
    ∃ d₁ d₂, d₁ ∣ m ∧ d₂ ∣ n ∧ k = d₁ * d₂ := by
  by_cases h0 : gcd k m = 0
  -- ⊢ ∃ d₁ d₂, d₁ ∣ m ∧ d₂ ∣ n ∧ k = d₁ * d₂
  · rw [gcd_eq_zero_iff] at h0
    -- ⊢ ∃ d₁ d₂, d₁ ∣ m ∧ d₂ ∣ n ∧ k = d₁ * d₂
    rcases h0 with ⟨rfl, rfl⟩
    -- ⊢ ∃ d₁ d₂, d₁ ∣ 0 ∧ d₂ ∣ n ∧ 0 = d₁ * d₂
    refine' ⟨0, n, dvd_refl 0, dvd_refl n, _⟩
    -- ⊢ 0 = 0 * n
    simp
    -- 🎉 no goals
  · obtain ⟨a, ha⟩ := gcd_dvd_left k m
    -- ⊢ ∃ d₁ d₂, d₁ ∣ m ∧ d₂ ∣ n ∧ k = d₁ * d₂
    refine' ⟨gcd k m, a, gcd_dvd_right _ _, _, ha⟩
    -- ⊢ a ∣ n
    suffices h : gcd k m * a ∣ gcd k m * n
    -- ⊢ a ∣ n
    · cases' h with b hb
      -- ⊢ a ∣ n
      use b
      -- ⊢ n = a * b
      rw [mul_assoc] at hb
      -- ⊢ n = a * b
      apply mul_left_cancel₀ h0 hb
      -- 🎉 no goals
    rw [← ha]
    -- ⊢ k ∣ gcd k m * n
    exact dvd_gcd_mul_of_dvd_mul H
    -- 🎉 no goals
#align exists_dvd_and_dvd_of_dvd_mul exists_dvd_and_dvd_of_dvd_mul

theorem dvd_mul [GCDMonoid α] {k m n : α} : k ∣ m * n ↔ ∃ d₁ d₂, d₁ ∣ m ∧ d₂ ∣ n ∧ k = d₁ * d₂ := by
  refine' ⟨exists_dvd_and_dvd_of_dvd_mul, _⟩
  -- ⊢ (∃ d₁ d₂, d₁ ∣ m ∧ d₂ ∣ n ∧ k = d₁ * d₂) → k ∣ m * n
  rintro ⟨d₁, d₂, hy, hz, rfl⟩
  -- ⊢ d₁ * d₂ ∣ m * n
  exact mul_dvd_mul hy hz
  -- 🎉 no goals
#align dvd_mul dvd_mul

theorem gcd_mul_dvd_mul_gcd [GCDMonoid α] (k m n : α) : gcd k (m * n) ∣ gcd k m * gcd k n := by
  obtain ⟨m', n', hm', hn', h⟩ := exists_dvd_and_dvd_of_dvd_mul (gcd_dvd_right k (m * n))
  -- ⊢ gcd k (m * n) ∣ gcd k m * gcd k n
  replace h : gcd k (m * n) = m' * n' := h
  -- ⊢ gcd k (m * n) ∣ gcd k m * gcd k n
  rw [h]
  -- ⊢ m' * n' ∣ gcd k m * gcd k n
  have hm'n' : m' * n' ∣ k := h ▸ gcd_dvd_left _ _
  -- ⊢ m' * n' ∣ gcd k m * gcd k n
  apply mul_dvd_mul
  -- ⊢ m' ∣ gcd k m
  · have hm'k : m' ∣ k := (dvd_mul_right m' n').trans hm'n'
    -- ⊢ m' ∣ gcd k m
    exact dvd_gcd hm'k hm'
    -- 🎉 no goals
  · have hn'k : n' ∣ k := (dvd_mul_left n' m').trans hm'n'
    -- ⊢ n' ∣ gcd k n
    exact dvd_gcd hn'k hn'
    -- 🎉 no goals
#align gcd_mul_dvd_mul_gcd gcd_mul_dvd_mul_gcd

theorem gcd_pow_right_dvd_pow_gcd [GCDMonoid α] {a b : α} {k : ℕ} :
    gcd a (b ^ k) ∣ gcd a b ^ k := by
  by_cases hg : gcd a b = 0
  -- ⊢ gcd a (b ^ k) ∣ gcd a b ^ k
  · rw [gcd_eq_zero_iff] at hg
    -- ⊢ gcd a (b ^ k) ∣ gcd a b ^ k
    rcases hg with ⟨rfl, rfl⟩
    -- ⊢ gcd 0 (0 ^ k) ∣ gcd 0 0 ^ k
    exact
      (gcd_zero_left' (0 ^ k : α)).dvd.trans
        (pow_dvd_pow_of_dvd (gcd_zero_left' (0 : α)).symm.dvd _)
  · induction' k with k hk
    -- ⊢ gcd a (b ^ Nat.zero) ∣ gcd a b ^ Nat.zero
    · rw [pow_zero, pow_zero]
      -- ⊢ gcd a 1 ∣ 1
      exact (gcd_one_right' a).dvd
      -- 🎉 no goals
    rw [pow_succ, pow_succ]
    -- ⊢ gcd a (b * b ^ k) ∣ gcd a b * gcd a b ^ k
    trans gcd a b * gcd a (b ^ k)
    -- ⊢ gcd a (b * b ^ k) ∣ gcd a b * gcd a (b ^ k)
    · exact gcd_mul_dvd_mul_gcd a b (b ^ k)
      -- 🎉 no goals
    · exact (mul_dvd_mul_iff_left hg).mpr hk
      -- 🎉 no goals
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
  -- ⊢ d₁ ^ k ≠ 0 ∧ d₁ ^ k ∣ a
  have h3 : d₁ ^ k ∣ a := by
    apply (dvd_gcd_mul_of_dvd_mul h2).trans
    rw [IsUnit.mul_left_dvd _ _ _ h1]
  have h4 : d₁ ^ k ≠ 0 := by
    intro hdk
    rw [hdk] at h3
    apply absurd (zero_dvd_iff.mp h3) ha
  exact ⟨h4, h3⟩
  -- 🎉 no goals
#align pow_dvd_of_mul_eq_pow pow_dvd_of_mul_eq_pow

theorem exists_associated_pow_of_mul_eq_pow [GCDMonoid α] {a b c : α} (hab : IsUnit (gcd a b))
    {k : ℕ} (h : a * b = c ^ k) : ∃ d : α, Associated (d ^ k) a := by
  cases subsingleton_or_nontrivial α
  -- ⊢ ∃ d, Associated (d ^ k) a
  · use 0
    -- ⊢ Associated (0 ^ k) a
    rw [Subsingleton.elim a (0 ^ k)]
    -- 🎉 no goals
  by_cases ha : a = 0
  -- ⊢ ∃ d, Associated (d ^ k) a
  · use 0
    -- ⊢ Associated (0 ^ k) a
    rw [ha]
    -- ⊢ Associated (0 ^ k) 0
    obtain rfl | hk := k.eq_zero_or_pos
    -- ⊢ Associated (0 ^ 0) 0
    · exfalso
      -- ⊢ False
      revert h
      -- ⊢ a * b = c ^ 0 → False
      rw [ha, zero_mul, pow_zero]
      -- ⊢ 0 = 1 → False
      apply zero_ne_one
      -- 🎉 no goals
    · rw [zero_pow hk]
      -- 🎉 no goals
  by_cases hb : b = 0
  -- ⊢ ∃ d, Associated (d ^ k) a
  · use 1
    -- ⊢ Associated (1 ^ k) a
    rw [one_pow]
    -- ⊢ Associated 1 a
    apply (associated_one_iff_isUnit.mpr hab).symm.trans
    -- ⊢ Associated (gcd a b) a
    rw [hb]
    -- ⊢ Associated (gcd a 0) a
    exact gcd_zero_right' a
    -- 🎉 no goals
  obtain rfl | hk := k.eq_zero_or_pos
  -- ⊢ ∃ d, Associated (d ^ 0) a
  · use 1
    -- ⊢ Associated (1 ^ 0) a
    rw [pow_zero] at h ⊢
    -- ⊢ Associated 1 a
    use Units.mkOfMulEqOne _ _ h
    -- ⊢ 1 * ↑(Units.mkOfMulEqOne a b h) = a
    rw [Units.val_mkOfMulEqOne, one_mul]
    -- 🎉 no goals
  have hc : c ∣ a * b := by
    rw [h]
    exact dvd_pow_self _ hk.ne'
  obtain ⟨d₁, d₂, hd₁, hd₂, hc⟩ := exists_dvd_and_dvd_of_dvd_mul hc
  -- ⊢ ∃ d, Associated (d ^ k) a
  use d₁
  -- ⊢ Associated (d₁ ^ k) a
  obtain ⟨h0₁, ⟨a', ha'⟩⟩ := pow_dvd_of_mul_eq_pow ha hab h hc hd₁
  -- ⊢ Associated (d₁ ^ k) a
  rw [mul_comm] at h hc
  -- ⊢ Associated (d₁ ^ k) a
  rw [(gcd_comm' a b).isUnit_iff] at hab
  -- ⊢ Associated (d₁ ^ k) a
  obtain ⟨h0₂, ⟨b', hb'⟩⟩ := pow_dvd_of_mul_eq_pow hb hab h hc hd₂
  -- ⊢ Associated (d₁ ^ k) a
  rw [ha', hb', hc, mul_pow] at h
  -- ⊢ Associated (d₁ ^ k) a
  have h' : a' * b' = 1 := by
    apply (mul_right_inj' h0₁).mp
    rw [mul_one]
    apply (mul_right_inj' h0₂).mp
    rw [← h]
    rw [mul_assoc, mul_comm a', ← mul_assoc _ b', ← mul_assoc b', mul_comm b']
  use Units.mkOfMulEqOne _ _ h'
  -- ⊢ d₁ ^ k * ↑(Units.mkOfMulEqOne a' b' h') = a
  rw [Units.val_mkOfMulEqOne, ha']
  -- 🎉 no goals
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
  -- ⊢ Associated (gcd x' y') 1
  refine' Associated.of_mul_left _ (Associated.refl <| gcd x y) h
  -- ⊢ Associated (gcd x y * gcd x' y') (gcd x y * 1)
  convert (gcd_mul_left' (gcd x y) x' y').symm using 1
  -- ⊢ gcd x y * 1 = gcd (gcd x y * x') (gcd x y * y')
  rw [← ex, ← ey, mul_one]
  -- 🎉 no goals
#align is_unit_gcd_of_eq_mul_gcd isUnit_gcd_of_eq_mul_gcd

theorem extract_gcd {α : Type*} [CancelCommMonoidWithZero α] [GCDMonoid α] (x y : α) :
    ∃ x' y', x = gcd x y * x' ∧ y = gcd x y * y' ∧ IsUnit (gcd x' y') := by
  by_cases h : gcd x y = 0
  -- ⊢ ∃ x' y', x = gcd x y * x' ∧ y = gcd x y * y' ∧ IsUnit (gcd x' y')
  · obtain ⟨rfl, rfl⟩ := (gcd_eq_zero_iff x y).1 h
    -- ⊢ ∃ x' y', 0 = gcd 0 0 * x' ∧ 0 = gcd 0 0 * y' ∧ IsUnit (gcd x' y')
    simp_rw [← associated_one_iff_isUnit]
    -- ⊢ ∃ x' y', 0 = gcd 0 0 * x' ∧ 0 = gcd 0 0 * y' ∧ Associated (gcd x' y') 1
    exact ⟨1, 1, by rw [h, zero_mul], by rw [h, zero_mul], gcd_one_left' 1⟩
    -- 🎉 no goals
  obtain ⟨x', ex⟩ := gcd_dvd_left x y
  -- ⊢ ∃ x' y', x = gcd x y * x' ∧ y = gcd x y * y' ∧ IsUnit (gcd x' y')
  obtain ⟨y', ey⟩ := gcd_dvd_right x y
  -- ⊢ ∃ x' y', x = gcd x y * x' ∧ y = gcd x y * y' ∧ IsUnit (gcd x' y')
  exact ⟨x', y', ex, ey, isUnit_gcd_of_eq_mul_gcd ex ey h⟩
  -- 🎉 no goals
#align extract_gcd extract_gcd

end GCD

section LCM

theorem lcm_dvd_iff [GCDMonoid α] {a b c : α} : lcm a b ∣ c ↔ a ∣ c ∧ b ∣ c := by
  by_cases h : a = 0 ∨ b = 0
  -- ⊢ lcm a b ∣ c ↔ a ∣ c ∧ b ∣ c
  · rcases h with (rfl | rfl) <;>
    -- ⊢ lcm 0 b ∣ c ↔ 0 ∣ c ∧ b ∣ c
      simp (config := { contextual := true }) only [iff_def, lcm_zero_left, lcm_zero_right,
        zero_dvd_iff, dvd_zero, eq_self_iff_true, and_true_iff, imp_true_iff]
  · obtain ⟨h1, h2⟩ := not_or.1 h
    -- ⊢ lcm a b ∣ c ↔ a ∣ c ∧ b ∣ c
    have h : gcd a b ≠ 0 := fun H => h1 ((gcd_eq_zero_iff _ _).1 H).1
    -- ⊢ lcm a b ∣ c ↔ a ∣ c ∧ b ∣ c
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
      -- ⊢ a = 0 ∨ b = 0
      rwa [← mul_eq_zero, ← associated_zero_iff_eq_zero])
      -- 🎉 no goals
    (by rintro (rfl | rfl) <;> [apply lcm_zero_left; apply lcm_zero_right])
        -- 🎉 no goals
#align lcm_eq_zero_iff lcm_eq_zero_iff

-- Porting note: lower priority to avoid linter complaints about simp-normal form
@[simp 1100]
theorem normalize_lcm [NormalizedGCDMonoid α] (a b : α) :
  normalize (lcm a b) = lcm a b :=
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

instance [NormalizedGCDMonoid α] : IsCommutative α lcm :=
  ⟨lcm_comm⟩

instance [NormalizedGCDMonoid α] : IsAssociative α lcm :=
  ⟨lcm_assoc⟩

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
      -- 🎉 no goals
#align lcm_eq_one_iff lcm_eq_one_iff

@[simp]
theorem lcm_mul_left [NormalizedGCDMonoid α] (a b c : α) :
    lcm (a * b) (a * c) = normalize a * lcm b c :=
  (by_cases (by rintro rfl; simp only [zero_mul, lcm_zero_left, normalize_zero]))
                -- ⊢ lcm (0 * b) (0 * c) = ↑normalize 0 * lcm b c
                            -- 🎉 no goals
    fun ha : a ≠ 0 =>
    suffices lcm (a * b) (a * c) = normalize (a * lcm b c) by simpa
                                                              -- 🎉 no goals
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
                                                      -- 🎉 no goals
#align lcm_mul_right lcm_mul_right

theorem lcm_eq_left_iff [NormalizedGCDMonoid α] (a b : α) (h : normalize a = a) :
    lcm a b = a ↔ b ∣ a :=
  (Iff.intro fun eq => eq ▸ dvd_lcm_right _ _) fun hab =>
    dvd_antisymm_of_normalize_eq (normalize_lcm _ _) h (lcm_dvd (dvd_refl a) hab) (dvd_lcm_left _ _)
#align lcm_eq_left_iff lcm_eq_left_iff

theorem lcm_eq_right_iff [NormalizedGCDMonoid α] (a b : α) (h : normalize b = b) :
    lcm a b = b ↔ a ∣ b := by simpa only [lcm_comm b a] using lcm_eq_left_iff b a h
                              -- 🎉 no goals
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

namespace GCDMonoid

theorem prime_of_irreducible [GCDMonoid α] {x : α} (hi : Irreducible x) : Prime x :=
  ⟨hi.ne_zero,
    ⟨hi.1, fun a b h => by
      cases' gcd_dvd_left x a with y hy
      -- ⊢ x ∣ a ∨ x ∣ b
      cases' hi.isUnit_or_isUnit hy with hu hu
      -- ⊢ x ∣ a ∨ x ∣ b
      · right
        -- ⊢ x ∣ b
        trans gcd (x * b) (a * b)
        -- ⊢ x ∣ gcd (x * b) (a * b)
        apply dvd_gcd (dvd_mul_right x b) h
        -- ⊢ gcd (x * b) (a * b) ∣ b
        rw [(gcd_mul_right' b x a).dvd_iff_dvd_left]
        -- ⊢ gcd x a * b ∣ b
        exact (associated_unit_mul_left _ _ hu).dvd
        -- 🎉 no goals
      · left
        -- ⊢ x ∣ a
        rw [hy]
        -- ⊢ gcd x a * y ∣ a
        exact dvd_trans (associated_mul_unit_left _ _ hu).dvd (gcd_dvd_right x a)⟩⟩
        -- 🎉 no goals
#align gcd_monoid.prime_of_irreducible GCDMonoid.prime_of_irreducible

theorem irreducible_iff_prime [GCDMonoid α] {p : α} : Irreducible p ↔ Prime p :=
  ⟨prime_of_irreducible, Prime.irreducible⟩
#align gcd_monoid.irreducible_iff_prime GCDMonoid.irreducible_iff_prime

end GCDMonoid

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
  uniq := fun ⟨u, _, _, _⟩ => by congr; simp
                                 -- ⊢ u = fun x => 1
                                        -- 🎉 no goals
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
    -- ⊢ { gcd := gcd✝, lcm := lcm✝, gcd_dvd_left := gcd_dvd_left✝, gcd_dvd_right :=  …
    cases g₂
    -- ⊢ { gcd := gcd✝¹, lcm := lcm✝¹, gcd_dvd_left := gcd_dvd_left✝¹, gcd_dvd_right  …
    dsimp only at hgcd hlcm
    -- ⊢ { gcd := gcd✝¹, lcm := lcm✝¹, gcd_dvd_left := gcd_dvd_left✝¹, gcd_dvd_right  …
    simp only [hgcd, hlcm]⟩
    -- 🎉 no goals
#align subsingleton_gcd_monoid_of_unique_units subsingleton_gcdMonoid_of_unique_units

instance subsingleton_normalizedGCDMonoid_of_unique_units : Subsingleton (NormalizedGCDMonoid α) :=
  ⟨by
    intro a b
    -- ⊢ a = b
    cases' a with a_norm a_gcd
    -- ⊢ NormalizedGCDMonoid.mk normalize_gcd✝ normalize_lcm✝ = b
    cases' b with b_norm b_gcd
    -- ⊢ NormalizedGCDMonoid.mk normalize_gcd✝¹ normalize_lcm✝¹ = NormalizedGCDMonoid …
    have := Subsingleton.elim a_gcd b_gcd
    -- ⊢ NormalizedGCDMonoid.mk normalize_gcd✝¹ normalize_lcm✝¹ = NormalizedGCDMonoid …
    subst this
    -- ⊢ NormalizedGCDMonoid.mk normalize_gcd✝¹ normalize_lcm✝¹ = NormalizedGCDMonoid …
    have := Subsingleton.elim a_norm b_norm
    -- ⊢ NormalizedGCDMonoid.mk normalize_gcd✝¹ normalize_lcm✝¹ = NormalizedGCDMonoid …
    subst this
    -- ⊢ NormalizedGCDMonoid.mk normalize_gcd✝¹ normalize_lcm✝¹ = NormalizedGCDMonoid …
    rfl⟩
    -- 🎉 no goals
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
  -- ⊢ gcd a b ∣ gcd a c
    rw [dvd_gcd_iff] <;>
    -- ⊢ gcd a b ∣ a ∧ gcd a b ∣ c
    -- ⊢ gcd a c ∣ a ∧ gcd a c ∣ b
    refine' ⟨gcd_dvd_left _ _, _⟩
    -- ⊢ gcd a b ∣ c
    -- ⊢ gcd a c ∣ b
  · rcases h with ⟨d, hd⟩
    -- ⊢ gcd a b ∣ c
    rcases gcd_dvd_right a b with ⟨e, he⟩
    -- ⊢ gcd a b ∣ c
    rcases gcd_dvd_left a b with ⟨f, hf⟩
    -- ⊢ gcd a b ∣ c
    use e - f * d
    -- ⊢ c = gcd a b * (e - f * d)
    rw [mul_sub, ← he, ← mul_assoc, ← hf, ← hd, sub_sub_cancel]
    -- 🎉 no goals
  · rcases h with ⟨d, hd⟩
    -- ⊢ gcd a c ∣ b
    rcases gcd_dvd_right a c with ⟨e, he⟩
    -- ⊢ gcd a c ∣ b
    rcases gcd_dvd_left a c with ⟨f, hf⟩
    -- ⊢ gcd a c ∣ b
    use e + f * d
    -- ⊢ b = gcd a c * (e + f * d)
    rw [mul_add, ← he, ← mul_assoc, ← hf, ← hd, ← add_sub_assoc, add_comm c b, add_sub_cancel]
    -- 🎉 no goals
#align gcd_eq_of_dvd_sub_right gcd_eq_of_dvd_sub_right

theorem gcd_eq_of_dvd_sub_left {a b c : α} (h : a ∣ b - c) : gcd b a = gcd c a := by
  rw [gcd_comm _ a, gcd_comm _ a, gcd_eq_of_dvd_sub_right h]
  -- 🎉 no goals
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
    -- ⊢ ↑(Classical.choose (_ : Associated (a * b) (↑f (Associates.mk (a * b))))) =  …
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
    -- ⊢ (fun a => if a = 0 then 1 else Classical.choose (_ : Associated a (↑f (Assoc …
    simp_rw [if_neg (Units.ne_zero u), Units.ext_iff]
    -- ⊢ ↑(Classical.choose (_ : Associated (↑u) (↑f (Associates.mk ↑u)))) = ↑u⁻¹
    apply mul_left_cancel₀ (Units.ne_zero u)
    -- ⊢ ↑u * ↑(Classical.choose (_ : Associated (↑u) (↑f (Associates.mk ↑u)))) = ↑u  …
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
      -- ⊢ Associated (gcd a b * if a = 0 then 0 else Classical.choose (_ : gcd a b ∣ a …
      split_ifs with a0
      -- ⊢ Associated (gcd a b * 0) (a * b)
      · rw [mul_zero, a0, zero_mul]
        -- 🎉 no goals
      · rw [← Classical.choose_spec ((gcd_dvd_left a b).trans (Dvd.intro b rfl))]
        -- 🎉 no goals
    lcm_zero_left := fun a => if_pos rfl
    lcm_zero_right := fun a => by
      -- Porting note: need `dsimp only` before `split_ifs`
      dsimp only
      -- ⊢ (if a = 0 then 0 else Classical.choose (_ : gcd a 0 ∣ a * 0)) = 0
      split_ifs with a0
      -- ⊢ 0 = 0
      · rfl
        -- 🎉 no goals
      have h := (Classical.choose_spec ((gcd_dvd_left a 0).trans (Dvd.intro 0 rfl))).symm
      -- ⊢ Classical.choose (_ : gcd a 0 ∣ a * 0) = 0
      have a0' : gcd a 0 ≠ 0 := by
        contrapose! a0
        rw [← associated_zero_iff_eq_zero, ← a0]
        exact associated_of_dvd_dvd (dvd_gcd (dvd_refl a) (dvd_zero a)) (gcd_dvd_left _ _)
      apply Or.resolve_left (mul_eq_zero.1 _) a0'
      -- ⊢ gcd a 0 * Classical.choose (_ : gcd a 0 ∣ a * 0) = 0
      rw [h, mul_zero] }
      -- 🎉 no goals
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
      -- ⊢ (if a = 0 then 0 else Classical.choose (_ : gcd a b ∣ a * b * ↑(normUnit (a  …
      split_ifs with a0
      -- ⊢ 0 * ↑(normUnit 0) = 0
      · exact @normalize_zero α _ _
        -- 🎉 no goals
      · have := (Classical.choose_spec
          (dvd_normalize_iff.2 ((gcd_dvd_left a b).trans (Dvd.intro b rfl)))).symm
        set l := Classical.choose (dvd_normalize_iff.2 ((gcd_dvd_left a b).trans (Dvd.intro b rfl)))
        -- ⊢ l * ↑(normUnit l) = l
        obtain rfl | hb := eq_or_ne b 0
        -- ⊢ l * ↑(normUnit l) = l
        -- Porting note: using `simp only` causes the propositions inside `Classical.choose` to
        -- differ, so `set` is unable to produce `l = 0` inside `this`. See
        -- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/
        -- Classical.2Echoose/near/317491179
        · rw [mul_zero a, normalize_zero, mul_eq_zero] at this
          -- ⊢ l * ↑(normUnit l) = l
          obtain ha | hl := this
          -- ⊢ l * ↑(normUnit l) = l
          · apply (a0 _).elim
            -- ⊢ a = 0
            rw [← zero_dvd_iff, ← ha]
            -- ⊢ gcd a 0 ∣ a
            exact gcd_dvd_left _ _
            -- 🎉 no goals
          · rw [hl, zero_mul]
      -- ⊢ Associated (gcd a b * if a = 0 then 0 else Classical.choose (_ : gcd a b ∣ ↑ …
            -- 🎉 no goals
      -- ⊢ Associated (gcd a b * 0) (a * b)
        have h1 : gcd a b ≠ 0 := by
        -- 🎉 no goals
          have hab : a * b ≠ 0 := mul_ne_zero a0 hb
          contrapose! hab
          rw [← normalize_eq_zero, ← this, hab, zero_mul]
        -- 🎉 no goals
        have h2 : normalize (gcd a b * l) = gcd a b * l := by rw [this, normalize_idem]
        -- ⊢ l * ↑(normUnit l) = l
        rw [← normalize_gcd] at this
        -- ⊢ l * ↑(normUnit l) = l
      -- ⊢ (if a = 0 then 0 else Classical.choose (_ : gcd a 0 ∣ ↑normalize (a * 0))) = 0
        rwa [normalize.map_mul, normalize_gcd, mul_right_inj' h1] at h2
      -- ⊢ 0 = 0
        -- 🎉 no goals
        -- 🎉 no goals
    gcd_mul_lcm := fun a b => by
      -- ⊢ Classical.choose (_ : gcd a 0 ∣ ↑normalize (a * 0)) = 0
      -- Porting note: need `dsimp only`
      dsimp only
      split_ifs with a0
      · rw [mul_zero, a0, zero_mul]
      · rw [←
          Classical.choose_spec (dvd_normalize_iff.2 ((gcd_dvd_left a b).trans (Dvd.intro b rfl)))]
        exact normalize_associated (a * b)
      -- ⊢ Classical.choose (_ : gcd a 0 ∣ ↑normalize (a * 0)) = 0
    lcm_zero_left := fun a => if_pos rfl
      -- ⊢ gcd a 0 * Classical.choose (_ : gcd a 0 ∣ ↑normalize (a * 0)) = 0
    lcm_zero_right := fun a => by
      -- 🎉 no goals
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
      -- ⊢ Associated ((if a = 0 then b else if b = 0 then a else Classical.choose (_ : …
      split_ifs with h h_1
      · rw [h, eq_zero_of_zero_dvd (dvd_lcm_left _ _), mul_zero, zero_mul]
        -- 🎉 no goals
      · rw [h_1, eq_zero_of_zero_dvd (dvd_lcm_right _ _), mul_zero]
        -- 🎉 no goals
      rw [mul_comm, ← Classical.choose_spec (exists_gcd a b)]
      -- 🎉 no goals
    lcm_zero_left := fun a => eq_zero_of_zero_dvd (dvd_lcm_left _ _)
      -- ⊢ (if a = 0 then b else if b = 0 then a else Classical.choose (_ : lcm a b ∣ a …
    lcm_zero_right := fun a => eq_zero_of_zero_dvd (dvd_lcm_right _ _)
    gcd_dvd_left := fun a b => by
        -- ⊢ b ∣ 0
      -- Porting note: need `dsimp only`
        -- 🎉 no goals
      dsimp only
        -- 🎉 no goals
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
      -- 🎉 no goals
        · exact absurd ‹b = 0› h_1
      rw [← mul_dvd_mul_iff_left h0, ← Classical.choose_spec (exists_gcd a b), mul_comm,
        mul_dvd_mul_iff_right h]
      -- ⊢ (if a = 0 then b else if b = 0 then a else Classical.choose (_ : lcm a b ∣ a …
      apply dvd_lcm_right
    gcd_dvd_right := fun a b => by
        -- 🎉 no goals
      -- Porting note: need `dsimp only`
        -- ⊢ a ∣ 0
      dsimp only
        -- 🎉 no goals
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
      -- 🎉 no goals
        · exact absurd ‹b = 0› h_1
      rw [← mul_dvd_mul_iff_left h0, ← Classical.choose_spec (exists_gcd a b),
        mul_dvd_mul_iff_right h_1]
      -- ⊢ a ∣ if c = 0 then b else if b = 0 then c else Classical.choose (_ : lcm c b  …
      apply dvd_lcm_left
    dvd_gcd := fun {a b c} ac ab => by
        -- 🎉 no goals
      -- Porting note: need `dsimp only`
        -- 🎉 no goals
      dsimp only
      split_ifs with h h_1
      · exact ab
      · exact ac
      have h0 : lcm c b ≠ 0 := by
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left c rfl)
        rw [con, zero_dvd_iff, mul_eq_zero] at h
      -- ⊢ lcm c b * a ∣ c * b
        cases h
      -- ⊢ lcm c (a * d) * a ∣ c * (a * d)
        · exact absurd ‹c = 0› h
      -- ⊢ lcm c (a * d) * a ∣ c * (a * d)
        · exact absurd ‹b = 0› h_1
      -- ⊢ lcm c (a * d) * a ∣ c * (a * d)
      rw [← mul_dvd_mul_iff_left h0, ← Classical.choose_spec (exists_gcd c b)]
      -- ⊢ lcm c (d * a) ∣ c * d
      rcases ab with ⟨d, rfl⟩
      -- ⊢ d * a ∣ c * d
      rw [mul_eq_zero] at ‹a * d ≠ 0›
      -- ⊢ a ∣ c
      push_neg at h_1
      -- 🎉 no goals
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
      -- ⊢ Associated ((if a = 0 then ↑normalize b else if b = 0 then ↑normalize a else …
      split_ifs with h h_1
      · rw [h, eq_zero_of_zero_dvd (dvd_lcm_left _ _), mul_zero, zero_mul]
        -- 🎉 no goals
      · rw [h_1, eq_zero_of_zero_dvd (dvd_lcm_right _ _), mul_zero, mul_zero]
        -- 🎉 no goals
      rw [mul_comm, ← Classical.choose_spec (exists_gcd a b)]
      -- ⊢ Associated (↑normalize (a * b)) (a * b)
      exact normalize_associated (a * b)
      -- 🎉 no goals
    normalize_lcm
    normalize_gcd := fun a b => by
      dsimp [normalize]
      -- ⊢ (if a = 0 then b * ↑(normUnit b) else if b = 0 then a * ↑(normUnit a) else C …
      split_ifs with h h_1
      · apply normalize_idem
        -- 🎉 no goals
      · apply normalize_idem
        -- 🎉 no goals
      have h0 : lcm a b ≠ 0 := by
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
        rw [con, zero_dvd_iff, mul_eq_zero] at h
        cases h
        · exact absurd ‹a = 0› h
        · exact absurd ‹b = 0› h_1
      apply mul_left_cancel₀ h0
      -- ⊢ lcm a b * (Classical.choose (_ : lcm a b ∣ a * b * ↑(normUnit (a * b))) * ↑( …
      -- ⊢ (if a = 0 then ↑normalize b else if b = 0 then ↑normalize a else Classical.c …
      refine' _root_.trans _ (Classical.choose_spec (exists_gcd a b))
      -- ⊢ lcm a b * (Classical.choose (_ : lcm a b ∣ a * b * ↑(normUnit (a * b))) * ↑( …
        -- ⊢ ↑normalize b ∣ 0
      conv_lhs =>
        -- 🎉 no goals
        congr
        -- 🎉 no goals
        rw [← normalize_lcm a b]
      erw [← normalize.map_mul, ← Classical.choose_spec (exists_gcd a b), normalize_idem]
      -- 🎉 no goals
    lcm_zero_left := fun a => eq_zero_of_zero_dvd (dvd_lcm_left _ _)
    lcm_zero_right := fun a => eq_zero_of_zero_dvd (dvd_lcm_right _ _)
    gcd_dvd_left := fun a b => by
      dsimp only
      split_ifs with h h_1
      · rw [h]
        apply dvd_zero
      -- 🎉 no goals
      · exact (normalize_associated _).dvd
      have h0 : lcm a b ≠ 0 := by
      -- ⊢ (if a = 0 then ↑normalize b else if b = 0 then ↑normalize a else Classical.c …
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
        -- 🎉 no goals
        rw [con, zero_dvd_iff, mul_eq_zero] at h
        -- ⊢ ↑normalize a ∣ 0
        cases h
        -- 🎉 no goals
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
      -- 🎉 no goals
        apply dvd_zero
      have h0 : lcm a b ≠ 0 := by
      -- ⊢ a ∣ if c = 0 then ↑normalize b else if b = 0 then ↑normalize c else Classica …
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
        -- 🎉 no goals
        rw [con, zero_dvd_iff, mul_eq_zero] at h
        -- 🎉 no goals
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
      -- ⊢ lcm c (a * d) * a ∣ c * (a * d)
        intro con
      -- ⊢ lcm c (a * d) * a ∣ c * (a * d)
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left c rfl)
      -- ⊢ lcm c (a * d) * a ∣ c * (a * d)
        rw [con, zero_dvd_iff, mul_eq_zero] at h
      -- ⊢ lcm c (d * a) ∣ c * d
        cases h
      -- ⊢ d * a ∣ c * d
        · exact absurd ‹c = 0› h
      -- ⊢ a ∣ c
        · exact absurd ‹b = 0› h_1
      -- 🎉 no goals
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
    -- ⊢ ↑(if h : x * y = 0 then 1 else (Units.mk0 (x * y) h)⁻¹) = ↑((if h : x = 0 th …
    split_ifs with h
    -- ⊢ ↑1 = ↑((Units.mk0 x x0)⁻¹ * (Units.mk0 y y0)⁻¹)
    · rw [mul_eq_zero] at h
      -- ⊢ ↑1 = ↑((Units.mk0 x x0)⁻¹ * (Units.mk0 y y0)⁻¹)
      cases h
      -- ⊢ ↑1 = ↑((Units.mk0 x x0)⁻¹ * (Units.mk0 y y0)⁻¹)
      · exact absurd ‹x = 0› x0
        -- 🎉 no goals
      · exact absurd ‹y = 0› y0
        -- 🎉 no goals
    · rw [Units.mk0_mul, mul_inv_rev, mul_comm] )
      -- 🎉 no goals
  normUnit_coe_units u := by
    -- Porting note: need `dsimp only`
    dsimp only
    -- ⊢ (if h : ↑u = 0 then 1 else (Units.mk0 (↑u) h)⁻¹) = u⁻¹
    rw [dif_neg (Units.ne_zero _), Units.mk0_val]
    -- 🎉 no goals
  gcd a b := if a = 0 ∧ b = 0 then 0 else 1
  lcm a b := if a = 0 ∨ b = 0 then 0 else 1
  gcd_dvd_left a b := by
    -- Porting note: need `dsimp only`
    dsimp only
    -- ⊢ (if a = 0 ∧ b = 0 then 0 else 1) ∣ a
    split_ifs with h
    -- ⊢ 0 ∣ a
    · rw [h.1]
      -- 🎉 no goals
    · exact one_dvd _
      -- 🎉 no goals
  gcd_dvd_right a b := by
    -- Porting note: need `dsimp only`
    dsimp only
    -- ⊢ (if a = 0 ∧ b = 0 then 0 else 1) ∣ b
    split_ifs with h
    -- ⊢ 0 ∣ b
    · rw [h.2]
      -- 🎉 no goals
    · exact one_dvd _
      -- 🎉 no goals
  dvd_gcd := fun {a b c} hac hab => by
    -- Porting note: need `dsimp only`
    dsimp only
    -- ⊢ a ∣ if c = 0 ∧ b = 0 then 0 else 1
    split_ifs with h
    -- ⊢ a ∣ 0
    · apply dvd_zero
      -- 🎉 no goals
    · rw [not_and_or] at h
      -- ⊢ a ∣ 1
      cases h
      -- ⊢ a ∣ 1
      · refine' isUnit_iff_dvd_one.mp (isUnit_of_dvd_unit _ (IsUnit.mk0 _ ‹c ≠ 0›))
        -- ⊢ a ∣ c
        exact hac
        -- 🎉 no goals
      · refine' isUnit_iff_dvd_one.mp (isUnit_of_dvd_unit _ (IsUnit.mk0 _ ‹b ≠ 0›))
        -- ⊢ a ∣ b
        exact hab
        -- 🎉 no goals
  gcd_mul_lcm a b := by
    by_cases ha : a = 0
    -- ⊢ Associated ((fun a b => if a = 0 ∧ b = 0 then 0 else 1) a b * (fun a b => if …
    · simp only [ha, true_and, true_or, ite_true, mul_zero, zero_mul]
      -- ⊢ Associated 0 0
      exact Associated.refl _
      -- 🎉 no goals
    · by_cases hb : b = 0
      -- ⊢ Associated ((fun a b => if a = 0 ∧ b = 0 then 0 else 1) a b * (fun a b => if …
      · simp only [hb, and_true, or_true, ite_true, mul_zero]
        -- ⊢ Associated 0 0
        exact Associated.refl _
        -- 🎉 no goals
      -- Porting note: need `dsimp only`
      · dsimp only
        -- ⊢ Associated ((if a = 0 ∧ b = 0 then 0 else 1) * if a = 0 ∨ b = 0 then 0 else  …
        rw [if_neg (not_and_of_not_left _ ha), one_mul, if_neg (not_or_of_not ha hb)]
        -- ⊢ Associated 1 (a * b)
        exact (associated_one_iff_isUnit.mpr ((IsUnit.mk0 _ ha).mul (IsUnit.mk0 _ hb))).symm
        -- 🎉 no goals
  lcm_zero_left b := if_pos (Or.inl rfl)
  lcm_zero_right a := if_pos (Or.inr rfl)
  -- `split_ifs` wants to split `normalize`, so handle the cases manually
  normalize_gcd a b := if h : a = 0 ∧ b = 0 then by simp [if_pos h] else by simp [if_neg h]
                                                    -- 🎉 no goals
                                                                            -- 🎉 no goals
  normalize_lcm a b := if h : a = 0 ∨ b = 0 then by simp [if_pos h] else by simp [if_neg h]
                                                    -- 🎉 no goals
                                                                            -- 🎉 no goals

@[simp]
theorem coe_normUnit {a : G₀} (h0 : a ≠ 0) : (↑(normUnit a) : G₀) = a⁻¹ := by simp [normUnit, h0]
                                                                              -- 🎉 no goals
#align comm_group_with_zero.coe_norm_unit CommGroupWithZero.coe_normUnit

theorem normalize_eq_one {a : G₀} (h0 : a ≠ 0) : normalize a = 1 := by simp [normalize_apply, h0]
                                                                       -- 🎉 no goals
#align comm_group_with_zero.normalize_eq_one CommGroupWithZero.normalize_eq_one

end CommGroupWithZero
