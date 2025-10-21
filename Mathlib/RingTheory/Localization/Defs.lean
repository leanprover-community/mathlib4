/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Regular.Basic
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.Data.Fintype.Prod
import Mathlib.GroupTheory.MonoidLocalization.MonoidWithZero
import Mathlib.RingTheory.OreLocalization.Ring
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.Ring

/-!
# Localizations of commutative rings

We characterize the localization of a commutative ring `R` at a submonoid `M` up to
isomorphism; that is, a commutative ring `S` is the localization of `R` at `M` iff we can find a
ring homomorphism `f : R →+* S` satisfying 3 properties:
1. For all `y ∈ M`, `f y` is a unit;
2. For all `z : S`, there exists `(x, y) : R × M` such that `z * f y = f x`;
3. For all `x, y : R` such that `f x = f y`, there exists `c ∈ M` such that `x * c = y * c`.
   (The converse is a consequence of 1.)

In the following, let `R, P` be commutative rings, `S, Q` be `R`- and `P`-algebras
and `M, T` be submonoids of `R` and `P` respectively, e.g.:
```
variable (R S P Q : Type*) [CommRing R] [CommRing S] [CommRing P] [CommRing Q]
variable [Algebra R S] [Algebra P Q] (M : Submonoid R) (T : Submonoid P)
```

## Main definitions

* `IsLocalization (M : Submonoid R) (S : Type*)` is a typeclass expressing that `S` is a
  localization of `R` at `M`, i.e. the canonical map `algebraMap R S : R →+* S` is a
  localization map (satisfying the above properties).
* `IsLocalization.mk' S` is a surjection sending `(x, y) : R × M` to `f x * (f y)⁻¹`
* `IsLocalization.lift` is the ring homomorphism from `S` induced by a homomorphism from `R`
  which maps elements of `M` to invertible elements of the codomain.
* `IsLocalization.map S Q` is the ring homomorphism from `S` to `Q` which maps elements
  of `M` to elements of `T`
* `IsLocalization.ringEquivOfRingEquiv`: if `R` and `P` are isomorphic by an isomorphism
  sending `M` to `T`, then `S` and `Q` are isomorphic

## Main results

* `Localization M S`, a construction of the localization as a quotient type, defined in
  `GroupTheory.MonoidLocalization`, has `CommRing`, `Algebra R` and `IsLocalization M`
  instances if `R` is a ring. `Localization.Away`, `Localization.AtPrime` and `FractionRing`
  are abbreviations for `Localization`s and have their corresponding `IsLocalization` instances

## Implementation notes

In maths it is natural to reason up to isomorphism, but in Lean we cannot naturally `rewrite` one
structure with an isomorphic one; one way around this is to isolate a predicate characterizing
a structure up to isomorphism, and reason about things that satisfy the predicate.

A previous version of this file used a fully bundled type of ring localization maps,
then used a type synonym `f.codomain` for `f : LocalizationMap M S` to instantiate the
`R`-algebra structure on `S`. This results in defining ad-hoc copies for everything already
defined on `S`. By making `IsLocalization` a predicate on the `algebraMap R S`,
we can ensure the localization map commutes nicely with other `algebraMap`s.

To prove most lemmas about a localization map `algebraMap R S` in this file we invoke the
corresponding proof for the underlying `CommMonoid` localization map
`IsLocalization.toLocalizationMap M S`, which can be found in `GroupTheory.MonoidLocalization`
and the namespace `Submonoid.LocalizationMap`.

To reason about the localization as a quotient type, use `mk_eq_of_mk'` and associated lemmas.
These show the quotient map `mk : R → M → Localization M` equals the surjection
`LocalizationMap.mk'` induced by the map `algebraMap : R →+* Localization M`.
The lemma `mk_eq_of_mk'` hence gives you access to the results in the rest of the file,
which are about the `LocalizationMap.mk'` induced by any localization map.

The proof that "a `CommRing` `K` which is the localization of an integral domain `R` at `R \ {0}`
is a field" is a `def` rather than an `instance`, so if you want to reason about a field of
fractions `K`, assume `[Field K]` instead of just `[CommRing K]`.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

assert_not_exists AlgHom Ideal

open Function

section CommSemiring

variable {R : Type*} [CommSemiring R] (M : Submonoid R) (S : Type*) [CommSemiring S]
variable [Algebra R S] {P : Type*} [CommSemiring P]

/-- The typeclass `IsLocalization (M : Submonoid R) S` where `S` is an `R`-algebra
expresses that `S` is isomorphic to the localization of `R` at `M`. -/
@[mk_iff]
class IsLocalization (M : Submonoid R) (S : Type*) [CommSemiring S] [Algebra R S] : Prop where
  /-- Everything in the image of `algebraMap` is a unit -/
  map_units (S) : ∀ y : M, IsUnit (algebraMap R S y)
  /-- The `algebraMap` is surjective -/
  surj (M) : ∀ z : S, ∃ x : R × M, z * algebraMap R S x.2 = algebraMap R S x.1
  /-- The kernel of `algebraMap` is contained in the annihilator of `M`;
      it is then equal to the annihilator by `map_units'` -/
  exists_of_eq : ∀ {x y}, algebraMap R S x = algebraMap R S y → ∃ c : M, ↑c * x = ↑c * y

variable {M}

namespace IsLocalization

section IsLocalization

variable [IsLocalization M S]

section

@[deprecated (since := "2025-09-04")] alias map_units' := IsLocalization.map_units
@[deprecated (since := "2025-09-04")] alias surj' := IsLocalization.surj

variable (M) {S}

variable (S) in
@[inherit_doc IsLocalization.exists_of_eq]
theorem eq_iff_exists {x y} : algebraMap R S x = algebraMap R S y ↔ ∃ c : M, ↑c * x = ↑c * y :=
  Iff.intro IsLocalization.exists_of_eq fun ⟨c, h⟩ ↦ by
    apply_fun algebraMap R S at h
    rw [map_mul, map_mul] at h
    exact (IsLocalization.map_units S c).mul_right_inj.mp h

theorem injective_iff_isRegular : Injective (algebraMap R S) ↔ ∀ c : M, IsRegular (c : R) := by
  simp_rw [Commute.isRegular_iff (Commute.all _), IsLeftRegular,
    Injective, eq_iff_exists M, exists_imp, forall_comm (α := M)]

theorem of_le (N : Submonoid R) (h₁ : M ≤ N) (h₂ : ∀ r ∈ N, IsUnit (algebraMap R S r)) :
    IsLocalization N S where
  map_units r := h₂ r r.2
  surj s :=
    have ⟨⟨x, y, hy⟩, H⟩ := IsLocalization.surj M s
    ⟨⟨x, y, h₁ hy⟩, H⟩
  exists_of_eq {x y} := by
    rw [IsLocalization.eq_iff_exists M]
    rintro ⟨c, hc⟩
    exact ⟨⟨c, h₁ c.2⟩, hc⟩

theorem of_le_of_exists_dvd (N : Submonoid R) (h₁ : M ≤ N) (h₂ : ∀ n ∈ N, ∃ m ∈ M, n ∣ m) :
    IsLocalization N S :=
  of_le M N h₁ fun n hn ↦ have ⟨m, hm, dvd⟩ := h₂ n hn
    isUnit_of_dvd_unit (map_dvd _ dvd) (map_units S ⟨m, hm⟩)

theorem algebraMap_isUnit_iff {x : R} : IsUnit (algebraMap R S x) ↔ ∃ m ∈ M, x ∣ m := by
  refine ⟨fun h ↦ ?_, fun ⟨m, hm, dvd⟩ ↦ isUnit_of_dvd_unit (map_dvd _ dvd) (map_units S ⟨m, hm⟩)⟩
  have ⟨s, hxs⟩ := isUnit_iff_dvd_one.mp h
  have ⟨⟨r, m⟩, hrm⟩ := surj M s
  apply_fun (algebraMap R S x * ·) at hrm
  rw [← mul_assoc, ← hxs, one_mul, ← map_mul] at hrm
  have ⟨m', eq⟩ := exists_of_eq (M := M) hrm
  exact ⟨m' * m, mul_mem m'.2 m.2, _, mul_left_comm _ x _ ▸ eq⟩

variable (S)

/-- `IsLocalization.toLocalizationMap M S` shows `S` is the monoid localization of `R` at `M`. -/
abbrev toLocalizationMap : M.LocalizationMap S where
  __ := algebraMap R S
  toFun := algebraMap R S
  map_units' := IsLocalization.map_units _
  surj' := IsLocalization.surj _
  exists_of_eq _ _ := IsLocalization.exists_of_eq

@[deprecated (since := "2025-08-01")] alias toLocalizationWithZeroMap := toLocalizationMap

@[simp]
lemma toLocalizationMap_toMonoidHom :
    (toLocalizationMap M S).toMonoidHom = (algebraMap R S : R →*₀ S) := rfl

@[deprecated (since := "2025-08-13")] alias toLocalizationMap_toMap := toLocalizationMap_toMonoidHom

@[simp] lemma coe_toLocalizationMap : ⇑(toLocalizationMap M S) = algebraMap R S := rfl

@[deprecated (since := "2025-08-13")] alias toLocalizationMap_toMap_apply := coe_toLocalizationMap

lemma toLocalizationMap_apply (x) : toLocalizationMap M S x = algebraMap R S x := rfl

theorem surj₂ : ∀ z w : S, ∃ z' w' : R, ∃ d : M,
    (z * algebraMap R S d = algebraMap R S z') ∧ (w * algebraMap R S d = algebraMap R S w') :=
  (toLocalizationMap M S).surj₂

end

variable (M) {S}

/-- Given a localization map `f : M →* N`, a section function sending `z : N` to some
`(x, y) : M × S` such that `f x * (f y)⁻¹ = z`. -/
noncomputable def sec (z : S) : R × M :=
  Classical.choose <| IsLocalization.surj _ z

@[simp]
theorem toLocalizationMap_sec : (toLocalizationMap M S).sec = sec M :=
  rfl

/-- Given `z : S`, `IsLocalization.sec M z` is defined to be a pair `(x, y) : R × M` such
that `z * f y = f x` (so this lemma is true by definition). -/
theorem sec_spec (z : S) :
    z * algebraMap R S (IsLocalization.sec M z).2 = algebraMap R S (IsLocalization.sec M z).1 :=
  Classical.choose_spec <| IsLocalization.surj _ z

/-- Given `z : S`, `IsLocalization.sec M z` is defined to be a pair `(x, y) : R × M` such
that `z * f y = f x`, so this lemma is just an application of `S`'s commutativity. -/
theorem sec_spec' (z : S) :
    algebraMap R S (IsLocalization.sec M z).1 = algebraMap R S (IsLocalization.sec M z).2 * z := by
  rw [mul_comm, sec_spec]

variable {M}

/-- If `M` contains `0` then the localization at `M` is trivial. -/
theorem subsingleton (h : 0 ∈ M) : Subsingleton S := (toLocalizationMap M S).subsingleton h

protected theorem subsingleton_iff : Subsingleton S ↔ 0 ∈ M :=
  (toLocalizationMap M S).subsingleton_iff

theorem map_right_cancel {x y} {c : M} (h : algebraMap R S (c * x) = algebraMap R S (c * y)) :
    algebraMap R S x = algebraMap R S y :=
  (toLocalizationMap M S).map_right_cancel h

theorem map_left_cancel {x y} {c : M} (h : algebraMap R S (x * c) = algebraMap R S (y * c)) :
    algebraMap R S x = algebraMap R S y :=
  (toLocalizationMap M S).map_left_cancel h

theorem eq_zero_of_fst_eq_zero {z x} {y : M} (h : z * algebraMap R S y = algebraMap R S x)
    (hx : x = 0) : z = 0 := by
  rw [hx, (algebraMap R S).map_zero] at h
  exact (IsUnit.mul_left_eq_zero (IsLocalization.map_units S y)).1 h

variable (M S)

theorem map_eq_zero_iff (r : R) : algebraMap R S r = 0 ↔ ∃ m : M, ↑m * r = 0 :=
  (toLocalizationMap M S).map_eq_zero_iff

variable {M}

/-- `IsLocalization.mk' S` is the surjection sending `(x, y) : R × M` to
`f x * (f y)⁻¹`. -/
noncomputable def mk' (x : R) (y : M) : S :=
  (toLocalizationMap M S).mk' x y

@[simp]
theorem mk'_sec (z : S) : mk' S (IsLocalization.sec M z).1 (IsLocalization.sec M z).2 = z :=
  (toLocalizationMap M S).mk'_sec _

theorem mk'_mul (x₁ x₂ : R) (y₁ y₂ : M) : mk' S (x₁ * x₂) (y₁ * y₂) = mk' S x₁ y₁ * mk' S x₂ y₂ :=
  (toLocalizationMap M S).mk'_mul _ _ _ _

theorem mk'_one (x) : mk' S x (1 : M) = algebraMap R S x :=
  (toLocalizationMap M S).mk'_one _

@[simp]
theorem mk'_spec (x) (y : M) : mk' S x y * algebraMap R S y = algebraMap R S x :=
  (toLocalizationMap M S).mk'_spec _ _

@[simp]
theorem mk'_spec' (x) (y : M) : algebraMap R S y * mk' S x y = algebraMap R S x :=
  (toLocalizationMap M S).mk'_spec' _ _

@[simp]
theorem mk'_spec_mk (x) (y : R) (hy : y ∈ M) :
    mk' S x ⟨y, hy⟩ * algebraMap R S y = algebraMap R S x :=
  mk'_spec S x ⟨y, hy⟩

@[simp]
theorem mk'_spec'_mk (x) (y : R) (hy : y ∈ M) :
    algebraMap R S y * mk' S x ⟨y, hy⟩ = algebraMap R S x :=
  mk'_spec' S x ⟨y, hy⟩

variable {S}

theorem eq_mk'_iff_mul_eq {x} {y : M} {z} :
    z = mk' S x y ↔ z * algebraMap R S y = algebraMap R S x :=
  (toLocalizationMap M S).eq_mk'_iff_mul_eq

theorem eq_mk'_of_mul_eq {x : R} {y : M} {z : R} (h : z * y = x) : (algebraMap R S) z = mk' S x y :=
  eq_mk'_iff_mul_eq.mpr (by rw [← h, map_mul])

theorem mk'_eq_iff_eq_mul {x} {y : M} {z} :
    mk' S x y = z ↔ algebraMap R S x = z * algebraMap R S y :=
  (toLocalizationMap M S).mk'_eq_iff_eq_mul

theorem mk'_add_eq_iff_add_mul_eq_mul {x} {y : M} {z₁ z₂} :
    mk' S x y + z₁ = z₂ ↔ algebraMap R S x + z₁ * algebraMap R S y = z₂ * algebraMap R S y := by
  rw [← mk'_spec S x y, ← IsUnit.mul_left_inj (IsLocalization.map_units S y), right_distrib]

theorem mk'_pow (x : R) (y : M) (n : ℕ) : mk' S (x ^ n) (y ^ n) = mk' S x y ^ n := by
  simp_rw [IsLocalization.mk'_eq_iff_eq_mul, SubmonoidClass.coe_pow, map_pow, ← mul_pow]
  simp

variable (M)

theorem mk'_surjective (z : S) : ∃ (x : _) (y : M), mk' S x y = z :=
  let ⟨r, hr⟩ := IsLocalization.surj _ z
  ⟨r.1, r.2, (eq_mk'_iff_mul_eq.2 hr).symm⟩

variable (S)

/-- The localization of a `Fintype` is a `Fintype`. Cannot be an instance. -/
noncomputable def fintype' [Fintype R] : Fintype S :=
  have := Classical.propDecidable
  Fintype.ofSurjective (Function.uncurry <| IsLocalization.mk' S) fun a =>
    Prod.exists'.mpr <| IsLocalization.mk'_surjective M a

variable {M S}

/-- Localizing at a submonoid with 0 inside it leads to the trivial ring. -/
def uniqueOfZeroMem (h : (0 : R) ∈ M) : Unique S :=
  uniqueOfZeroEqOne <| by simpa using IsLocalization.map_units S ⟨0, h⟩

theorem mk'_eq_iff_eq {x₁ x₂} {y₁ y₂ : M} :
    mk' S x₁ y₁ = mk' S x₂ y₂ ↔ algebraMap R S (y₂ * x₁) = algebraMap R S (y₁ * x₂) :=
  (toLocalizationMap M S).mk'_eq_iff_eq

theorem mk'_eq_iff_eq' {x₁ x₂} {y₁ y₂ : M} :
    mk' S x₁ y₁ = mk' S x₂ y₂ ↔ algebraMap R S (x₁ * y₂) = algebraMap R S (x₂ * y₁) :=
  (toLocalizationMap M S).mk'_eq_iff_eq'

protected theorem eq {a₁ b₁} {a₂ b₂ : M} :
    mk' S a₁ a₂ = mk' S b₁ b₂ ↔ ∃ c : M, ↑c * (↑b₂ * a₁) = c * (a₂ * b₁) :=
  (toLocalizationMap M S).eq

theorem mk'_eq_zero_iff (x : R) (s : M) : mk' S x s = 0 ↔ ∃ m : M, ↑m * x = 0 :=
  (toLocalizationMap M S).mk'_eq_zero_iff x s

@[simp]
theorem mk'_zero (s : M) : IsLocalization.mk' S 0 s = 0 :=
  (toLocalizationMap M S).mk'_zero s

theorem ne_zero_of_mk'_ne_zero {x : R} {y : M} (hxy : IsLocalization.mk' S x y ≠ 0) : x ≠ 0 := by
  rintro rfl
  exact hxy (IsLocalization.mk'_zero _)

include M in
variable (M) in
/-- Any localization of a commutative semiring without zero-divisors also has no zero-divisors. -/
theorem noZeroDivisors [NoZeroDivisors R] : NoZeroDivisors S :=
  (toLocalizationMap M S).noZeroDivisors

theorem sec_fst_ne_zero {x : S} (hx : x ≠ 0) : (sec M x).fst ≠ 0 :=
  mt (fun h ↦ by rw [← mk'_sec (M := M) S x, h, mk'_zero]) hx

section Ext

theorem eq_iff_eq [Algebra R P] [IsLocalization M P] {x y} :
    algebraMap R S x = algebraMap R S y ↔ algebraMap R P x = algebraMap R P y :=
  (toLocalizationMap M S).eq_iff_eq (toLocalizationMap M P)

theorem mk'_eq_iff_mk'_eq [Algebra R P] [IsLocalization M P] {x₁ x₂} {y₁ y₂ : M} :
    mk' S x₁ y₁ = mk' S x₂ y₂ ↔ mk' P x₁ y₁ = mk' P x₂ y₂ :=
  (toLocalizationMap M S).mk'_eq_iff_mk'_eq (toLocalizationMap M P)

theorem mk'_eq_of_eq {a₁ b₁ : R} {a₂ b₂ : M} (H : ↑a₂ * b₁ = ↑b₂ * a₁) :
    mk' S a₁ a₂ = mk' S b₁ b₂ :=
  (toLocalizationMap M S).mk'_eq_of_eq H

theorem mk'_eq_of_eq' {a₁ b₁ : R} {a₂ b₂ : M} (H : b₁ * ↑a₂ = a₁ * ↑b₂) :
    mk' S a₁ a₂ = mk' S b₁ b₂ :=
  (toLocalizationMap M S).mk'_eq_of_eq' H

theorem mk'_cancel (a : R) (b c : M) :
    mk' S (a * c) (b * c) = mk' S a b := (toLocalizationMap M S).mk'_cancel _ _ _

variable (S)

@[simp]
theorem mk'_self {x : R} (hx : x ∈ M) : mk' S x ⟨x, hx⟩ = 1 :=
  (toLocalizationMap M S).mk'_self _ hx

@[simp]
theorem mk'_self' {x : M} : mk' S (x : R) x = 1 :=
  (toLocalizationMap M S).mk'_self' _

theorem mk'_self'' {x : M} : mk' S x.1 x = 1 :=
  mk'_self' _

end Ext

theorem mul_mk'_eq_mk'_of_mul (x y : R) (z : M) :
    (algebraMap R S) x * mk' S y z = mk' S (x * y) z :=
  (toLocalizationMap M S).mul_mk'_eq_mk'_of_mul _ _ _

theorem mk'_eq_mul_mk'_one (x : R) (y : M) : mk' S x y = (algebraMap R S) x * mk' S 1 y :=
  ((toLocalizationMap M S).mul_mk'_one_eq_mk' _ _).symm

@[simp]
theorem mk'_mul_cancel_left (x : R) (y : M) : mk' S (y * x : R) y = (algebraMap R S) x :=
  (toLocalizationMap M S).mk'_mul_cancel_left _ _

theorem mk'_mul_cancel_right (x : R) (y : M) : mk' S (x * y) y = (algebraMap R S) x :=
  (toLocalizationMap M S).mk'_mul_cancel_right _ _

@[simp]
theorem mk'_mul_mk'_eq_one (x y : M) : mk' S (x : R) y * mk' S (y : R) x = 1 := by
  rw [← mk'_mul, mul_comm]; exact mk'_self _ _

theorem mk'_mul_mk'_eq_one' (x : R) (y : M) (h : x ∈ M) : mk' S x y * mk' S (y : R) ⟨x, h⟩ = 1 :=
  mk'_mul_mk'_eq_one ⟨x, h⟩ _

theorem smul_mk' (x y : R) (m : M) : x • mk' S y m = mk' S (x * y) m := by
  nth_rw 2 [← one_mul m]
  rw [mk'_mul, mk'_one, Algebra.smul_def]

@[simp] theorem smul_mk'_one (x : R) (m : M) : x • mk' S 1 m = mk' S x m := by
  rw [smul_mk', mul_one]

@[simp] lemma smul_mk'_self {m : M} {r : R} :
    (m : R) • mk' S r m = algebraMap R S r := by
  rw [smul_mk', mk'_mul_cancel_left]

@[simps]
noncomputable instance invertible_mk'_one (s : M) :
    Invertible (IsLocalization.mk' S (1 : R) s) where
  invOf := algebraMap R S s
  invOf_mul_self := by simp
  mul_invOf_self := by simp

section

variable (M)

theorem isUnit_comp (j : S →+* P) (y : M) : IsUnit (j.comp (algebraMap R S) y) :=
  (toLocalizationMap M S).isUnit_comp j.toMonoidHom _

end

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `CommSemiring`s
`g : R →+* P` such that `g(M) ⊆ Units P`, `f x = f y → g x = g y` for all `x y : R`. -/
theorem eq_of_eq {g : R →+* P} (hg : ∀ y : M, IsUnit (g y)) {x y}
    (h : (algebraMap R S) x = (algebraMap R S) y) : g x = g y :=
  Submonoid.LocalizationMap.eq_of_eq (toLocalizationMap M S) (g := g.toMonoidHom) hg h

theorem mk'_add (x₁ x₂ : R) (y₁ y₂ : M) :
    mk' S (x₁ * y₂ + x₂ * y₁) (y₁ * y₂) = mk' S x₁ y₁ + mk' S x₂ y₂ :=
  mk'_eq_iff_eq_mul.2 <|
    Eq.symm
      (by
        rw [mul_comm (_ + _), mul_add, mul_mk'_eq_mk'_of_mul, mk'_add_eq_iff_add_mul_eq_mul,
          mul_comm (_ * _), ← mul_assoc, add_comm, ← map_mul, mul_mk'_eq_mk'_of_mul,
          mk'_add_eq_iff_add_mul_eq_mul]
        simp only [map_add, Submonoid.coe_mul, map_mul]
        ring)

theorem mul_add_inv_left {g : R →+* P} (h : ∀ y : M, IsUnit (g y)) (y : M) (w z₁ z₂ : P) :
    w * ↑(IsUnit.liftRight (g.toMonoidHom.restrict M) h y)⁻¹ + z₁ =
    z₂ ↔ w + g y * z₁ = g y * z₂ := by
  rw [mul_comm, ← one_mul z₁, ← Units.inv_mul (IsUnit.liftRight (g.toMonoidHom.restrict M) h y),
    mul_assoc, ← mul_add, Units.inv_mul_eq_iff_eq_mul, Units.inv_mul_cancel_left,
    IsUnit.coe_liftRight]
  simp [RingHom.toMonoidHom_eq_coe, MonoidHom.restrict_apply]

theorem lift_spec_mul_add {g : R →+* P} (hg : ∀ y : M, IsUnit (g y)) (z w w' v) :
    ((toLocalizationMap M S).lift hg) z * w + w' = v ↔
      g ((toLocalizationMap M S).sec z).1 * w + g ((toLocalizationMap M S).sec z).2 * w' =
        g ((toLocalizationMap M S).sec z).2 * v := by
  rw [mul_comm, Submonoid.LocalizationMap.lift_apply, ← mul_assoc, mul_add_inv_left hg,
    mul_comm]
  rfl

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `CommSemiring`s
`g : R →+* P` such that `g y` is invertible for all `y : M`, the homomorphism induced from
`S` to `P` sending `z : S` to `g x * (g y)⁻¹`, where `(x, y) : R × M` are such that
`z = f x * (f y)⁻¹`. -/
noncomputable def lift {g : R →+* P} (hg : ∀ y : M, IsUnit (g y)) : S →+* P :=
  { (toLocalizationMap M S).lift₀ g.toMonoidWithZeroHom hg with
    map_add' := by
      intro x y
      dsimp
      rw [(toLocalizationMap M S).lift₀_def, (toLocalizationMap M S).lift_spec,
        mul_add, mul_comm, eq_comm, lift_spec_mul_add, add_comm, mul_comm, mul_assoc, mul_comm,
        mul_assoc, lift_spec_mul_add]
      simp_rw [← mul_assoc]
      change g _ * g _ * g _ + g _ * g _ * g _ = g _ * g _ * g _
      simp_rw [← map_mul g, ← map_add g]
      apply eq_of_eq (S := S) hg
      simp only [sec_spec', toLocalizationMap_sec, map_add, map_mul]
      ring }

variable {g : R →+* P} (hg : ∀ y : M, IsUnit (g y))

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `CommSemiring`s
`g : R →* P` such that `g y` is invertible for all `y : M`, the homomorphism induced from
`S` to `P` maps `f x * (f y)⁻¹` to `g x * (g y)⁻¹` for all `x : R, y ∈ M`. -/
theorem lift_mk' (x y) :
    lift hg (mk' S x y) = g x * ↑(IsUnit.liftRight (g.toMonoidHom.restrict M) hg y)⁻¹ :=
  (toLocalizationMap M S).lift_mk' _ _ _

theorem lift_mk'_spec (x v) (y : M) : lift hg (mk' S x y) = v ↔ g x = g y * v :=
  (toLocalizationMap M S).lift_mk'_spec _ _ _ _

@[simp]
theorem lift_eq (x : R) : lift hg ((algebraMap R S) x) = g x :=
  (toLocalizationMap M S).lift_eq _ _

theorem lift_eq_iff {x y : R × M} :
    lift hg (mk' S x.1 x.2) = lift hg (mk' S y.1 y.2) ↔ g (x.1 * y.2) = g (y.1 * x.2) :=
  (toLocalizationMap M S).lift_eq_iff _

@[simp]
theorem lift_comp : (lift hg).comp (algebraMap R S) = g :=
  RingHom.ext <| (DFunLike.ext_iff (F := MonoidHom _ _)).1 <| (toLocalizationMap M S).lift_comp _

@[simp]
theorem lift_of_comp (j : S →+* P) : lift (isUnit_comp M j) = j :=
  RingHom.ext <| (DFunLike.ext_iff (F := MonoidHom _ _)).1 <|
    (toLocalizationMap M S).lift_of_comp j.toMonoidHom

variable (M)

section
include M

/-- See note [partially-applied ext lemmas] -/
theorem monoidHom_ext {P : Type*} [Monoid P] ⦃j k : S →* P⦄
    (h : j.comp (algebraMap R S : R →* S) = k.comp (algebraMap R S)) : j = k :=
  (toLocalizationMap M S).epic_of_localizationMap h

/-- See note [partially-applied ext lemmas] -/
theorem ringHom_ext {P : Type*} [Semiring P] ⦃j k : S →+* P⦄
    (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) :
    j = k :=
  RingHom.coe_monoidHom_injective <| monoidHom_ext M <| MonoidHom.ext <| RingHom.congr_fun h

/-- To show `j` and `k` agree on the whole localization, it suffices to show they agree
on the image of the base ring, if they preserve `1` and `*`. -/
protected theorem ext {P : Type*} [Monoid P] (j k : S → P) (hj1 : j 1 = 1) (hk1 : k 1 = 1)
    (hjm : ∀ a b, j (a * b) = j a * j b) (hkm : ∀ a b, k (a * b) = k a * k b)
    (h : ∀ a, j (algebraMap R S a) = k (algebraMap R S a)) : j = k :=
  let j' : MonoidHom S P :=
    { toFun := j, map_one' := hj1, map_mul' := hjm }
  let k' : MonoidHom S P :=
    { toFun := k, map_one' := hk1, map_mul' := hkm }
  have : j' = k' := monoidHom_ext M (MonoidHom.ext h)
  show j'.toFun = k'.toFun by rw [this]
end

variable {M}

theorem lift_unique {j : S →+* P} (hj : ∀ x, j ((algebraMap R S) x) = g x) : lift hg = j :=
  RingHom.ext <|
    (DFunLike.ext_iff (F := MonoidHom _ _)).1 <|
      Submonoid.LocalizationMap.lift_unique (toLocalizationMap M S) (g := g.toMonoidHom) hg
        (j := j.toMonoidHom) hj

@[simp]
theorem lift_id (x) : lift (map_units S : ∀ _ : M, IsUnit _) x = x :=
  (toLocalizationMap M S).lift_id _

theorem lift_surjective_iff :
    Surjective (lift hg : S → P) ↔ ∀ v : P, ∃ x : R × M, v * g x.2 = g x.1 :=
  (toLocalizationMap M S).lift_surjective_iff hg

theorem lift_injective_iff :
    Injective (lift hg : S → P) ↔ ∀ x y, algebraMap R S x = algebraMap R S y ↔ g x = g y :=
  (toLocalizationMap M S).lift_injective_iff hg

variable (M) in
include M in
lemma injective_iff_map_algebraMap_eq {T} [CommSemiring T] (f : S →+* T) :
    Function.Injective f ↔ ∀ x y,
      algebraMap R S x = algebraMap R S y ↔ f (algebraMap R S x) = f (algebraMap R S y) := by
  rw [← IsLocalization.lift_of_comp (M := M) f, IsLocalization.lift_injective_iff]
  simp

section Map

variable {T : Submonoid P} {Q : Type*} [CommSemiring Q]
variable [Algebra P Q] [IsLocalization T Q]

section

variable (Q)

/-- Map a homomorphism `g : R →+* P` to `S →+* Q`, where `S` and `Q` are
localizations of `R` and `P` at `M` and `T` respectively,
such that `g(M) ⊆ T`.

We send `z : S` to `algebraMap P Q (g x) * (algebraMap P Q (g y))⁻¹`, where
`(x, y) : R × M` are such that `z = f x * (f y)⁻¹`. -/
noncomputable def map (g : R →+* P) (hy : M ≤ T.comap g) : S →+* Q :=
  lift (M := M) (g := (algebraMap P Q).comp g) fun y => map_units _ ⟨g y, hy y.2⟩

end

section
variable (hy : M ≤ T.comap g)
include hy

@[simp]
theorem map_eq (x) : map Q g hy ((algebraMap R S) x) = algebraMap P Q (g x) :=
  lift_eq (fun y => map_units _ ⟨g y, hy y.2⟩) x

@[simp]
theorem map_comp : (map Q g hy).comp (algebraMap R S) = (algebraMap P Q).comp g :=
  lift_comp fun y => map_units _ ⟨g y, hy y.2⟩

theorem map_mk' (x) (y : M) : map Q g hy (mk' S x y) = mk' Q (g x) ⟨g y, hy y.2⟩ :=
  Submonoid.LocalizationMap.map_mk' (toLocalizationMap M S) (g := g.toMonoidHom)
    (fun y => hy y.2) (k := toLocalizationMap T Q) ..

theorem map_unique (j : S →+* Q) (hj : ∀ x : R, j (algebraMap R S x) = algebraMap P Q (g x)) :
    map Q g hy = j :=
  lift_unique (fun y => map_units _ ⟨g y, hy y.2⟩) hj

/-- If `CommSemiring` homs `g : R →+* P, l : P →+* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
theorem map_comp_map {A : Type*} [CommSemiring A] {U : Submonoid A} {W} [CommSemiring W]
    [Algebra A W] [IsLocalization U W] {l : P →+* A} (hl : T ≤ U.comap l) :
    (map W l hl).comp (map Q g hy : S →+* _) = map W (l.comp g) fun _ hx => hl (hy hx) :=
  RingHom.ext fun x =>
    Submonoid.LocalizationMap.map_map (P := P) (toLocalizationMap M S) (fun y => hy y.2)
      (toLocalizationMap U W) (fun w => hl w.2) x

/-- If `CommSemiring` homs `g : R →+* P, l : P →+* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
theorem map_map {A : Type*} [CommSemiring A] {U : Submonoid A} {W} [CommSemiring W] [Algebra A W]
    [IsLocalization U W] {l : P →+* A} (hl : T ≤ U.comap l) (x : S) :
    map W l hl (map Q g hy x) = map W (l.comp g) (fun _ hx => hl (hy hx)) x := by
  rw [← map_comp_map (Q := Q) hy hl]; rfl

protected theorem map_smul (x : S) (z : R) : map Q g hy (z • x : S) = g z • map Q g hy x := by
  rw [Algebra.smul_def, Algebra.smul_def, RingHom.map_mul, map_eq]

end

@[simp]
theorem map_id_mk' {Q : Type*} [CommSemiring Q] [Algebra R Q] [IsLocalization M Q] (x) (y : M) :
    map Q (RingHom.id R) (le_refl M) (mk' S x y) = mk' Q x y :=
  map_mk' ..

@[simp]
theorem map_id (z : S) (h : M ≤ M.comap (RingHom.id R) := le_refl M) :
    map S (RingHom.id _) h z = z :=
  lift_id _

section

variable (S Q)

/-- If `S`, `Q` are localizations of `R` and `P` at submonoids `M, T` respectively, an
isomorphism `j : R ≃+* P` such that `j(M) = T` induces an isomorphism of localizations
`S ≃+* Q`. -/
@[simps]
noncomputable def ringEquivOfRingEquiv (h : R ≃+* P) (H : M.map h.toMonoidHom = T) : S ≃+* Q :=
  have H' : T.map h.symm.toMonoidHom = M := by
    rw [← M.map_id, ← H, Submonoid.map_map]
    congr
    ext
    apply h.symm_apply_apply
  { map Q (h : R →+* P) (M.le_comap_of_map_le (le_of_eq H)) with
    toFun := map Q (h : R →+* P) (M.le_comap_of_map_le (le_of_eq H))
    invFun := map S (h.symm : P →+* R) (T.le_comap_of_map_le (le_of_eq H'))
    left_inv := fun x => by
      rw [map_map, map_unique _ (RingHom.id _), RingHom.id_apply]
      simp
    right_inv := fun x => by
      rw [map_map, map_unique _ (RingHom.id _), RingHom.id_apply]
      simp }

end

theorem ringEquivOfRingEquiv_eq_map {j : R ≃+* P} (H : M.map j.toMonoidHom = T) :
    (ringEquivOfRingEquiv S Q j H : S →+* Q) =
      map Q (j : R →+* P) (M.le_comap_of_map_le (le_of_eq H)) :=
  rfl

theorem ringEquivOfRingEquiv_eq {j : R ≃+* P} (H : M.map j.toMonoidHom = T) (x) :
    ringEquivOfRingEquiv S Q j H ((algebraMap R S) x) = algebraMap P Q (j x) := by
  simp

theorem ringEquivOfRingEquiv_mk' {j : R ≃+* P} (H : M.map j.toMonoidHom = T) (x : R) (y : M) :
    ringEquivOfRingEquiv S Q j H (mk' S x y) =
      mk' Q (j x) ⟨j y, show j y ∈ T from H ▸ Set.mem_image_of_mem j y.2⟩ := by
  simp [map_mk']

@[simp]
theorem ringEquivOfRingEquiv_symm {j : R ≃+* P} (H : M.map j = T) :
    (ringEquivOfRingEquiv S Q j H).symm =
      ringEquivOfRingEquiv Q S j.symm (show T.map (j : R ≃* P).symm = M by
        rw [← H, ← Submonoid.comap_equiv_eq_map_symm, ← Submonoid.map_coe_toMulEquiv,
          Submonoid.comap_map_eq_of_injective (j : R ≃* P).injective]) := rfl

end Map

section at_units
lemma at_units (S : Submonoid R)
    (hS : S ≤ IsUnit.submonoid R) : IsLocalization S R where
  map_units y := hS y.prop
  surj := fun s ↦ ⟨⟨s, 1⟩, by simp⟩
  exists_of_eq := fun {x y} (e : x = y) ↦ ⟨1, e ▸ rfl⟩

end at_units

section

variable (M S) (Q : Type*) [CommSemiring Q] [Algebra P Q]

/-- Injectivity of a map descends to the map induced on localizations. -/
theorem map_injective_of_injective (h : Function.Injective g) [IsLocalization (M.map g) Q] :
    Function.Injective (map Q g M.le_comap_map : S → Q) :=
  (toLocalizationMap M S).map_injective_of_injective h (toLocalizationMap (M.map g) Q)

/-- Surjectivity of a map descends to the map induced on localizations. -/
theorem map_surjective_of_surjective (h : Function.Surjective g) [IsLocalization (M.map g) Q] :
    Function.Surjective (map Q g M.le_comap_map : S → Q) :=
  (toLocalizationMap M S).map_surjective_of_surjective h (toLocalizationMap (M.map g) Q)

end

end IsLocalization

section

variable (M)

theorem isLocalization_of_base_ringEquiv [IsLocalization M S] (h : R ≃+* P) :
    haveI := ((algebraMap R S).comp h.symm.toRingHom).toAlgebra
    IsLocalization (M.map h) S := by
  letI : Algebra P S := ((algebraMap R S).comp h.symm.toRingHom).toAlgebra
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩⟩
    convert IsLocalization.map_units S ⟨y, hy⟩
    dsimp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
    exact congr_arg _ (h.symm_apply_apply _)
  · intro y
    obtain ⟨⟨x, s⟩, e⟩ := IsLocalization.surj M y
    refine ⟨⟨h x, _, _, s.prop, rfl⟩, ?_⟩
    dsimp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply] at e ⊢
    convert e <;> exact h.symm_apply_apply _
  · intro x y
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, RingHom.comp_apply,
      IsLocalization.eq_iff_exists M S]
    simp [← h.toEquiv.apply_eq_iff_eq]

theorem isLocalization_iff_of_base_ringEquiv (h : R ≃+* P) :
    IsLocalization M S ↔
      haveI := ((algebraMap R S).comp h.symm.toRingHom).toAlgebra
      IsLocalization (M.map h) S := by
  letI : Algebra P S := ((algebraMap R S).comp h.symm.toRingHom).toAlgebra
  refine ⟨fun _ => isLocalization_of_base_ringEquiv M S h, ?_⟩
  intro (H : IsLocalization (Submonoid.map (h : R ≃* P) M) S)
  convert isLocalization_of_base_ringEquiv (Submonoid.map (h : R ≃* P) M) S h.symm
  · rw [← Submonoid.map_coe_toMulEquiv, RingEquiv.coe_toMulEquiv_symm, ←
      Submonoid.comap_equiv_eq_map_symm, Submonoid.comap_map_eq_of_injective]
    exact h.toEquiv.injective
  rw [RingHom.algebraMap_toAlgebra, RingHom.comp_assoc]
  simp only [RingHom.comp_id, RingEquiv.symm_symm, RingEquiv.symm_toRingHom_comp_toRingHom]
  apply Algebra.algebra_ext
  intro r
  rw [RingHom.algebraMap_toAlgebra]

end

variable (M)

theorem nonZeroDivisors_le_comap [IsLocalization M S] :
    nonZeroDivisors R ≤ (nonZeroDivisors S).comap (algebraMap R S) :=
  (toLocalizationMap M S).nonZeroDivisors_le_comap

theorem map_nonZeroDivisors_le [IsLocalization M S] :
    (nonZeroDivisors R).map (algebraMap R S) ≤ nonZeroDivisors S :=
  (toLocalizationMap M S).map_nonZeroDivisors_le

end IsLocalization

namespace Localization

open IsLocalization

/-! ### Constructing a localization at a given submonoid -/

section

instance instUniqueLocalization [Subsingleton R] : Unique (Localization M) where
  uniq a := by
    with_unfolding_all change a = mk 1 1
    exact Localization.induction_on a fun _ => by
      congr <;> apply Subsingleton.elim

theorem add_mk (a b c d) : (mk a b : Localization M) + mk c d =
    mk ((b : R) * c + (d : R) * a) (b * d) := by
  rw [add_comm (b * c) (d * a), mul_comm b d]
  exact OreLocalization.oreDiv_add_oreDiv

theorem add_mk_self (a b c) : (mk a b : Localization M) + mk c b = mk (a + c) b := by
  rw [add_mk, mk_eq_mk_iff, r_eq_r']
  refine (r' M).symm ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul]
  ring

/-- For any given denominator `b : M`, the map `a ↦ a / b` is an `AddMonoidHom` from `R` to
  `Localization M`. -/
@[simps]
def mkAddMonoidHom (b : M) : R →+ Localization M where
  toFun a := mk a b
  map_zero' := mk_zero _
  map_add' _ _ := (add_mk_self _ _ _).symm

theorem mk_sum {ι : Type*} (f : ι → R) (s : Finset ι) (b : M) :
    mk (∑ i ∈ s, f i) b = ∑ i ∈ s, mk (f i) b :=
  map_sum (mkAddMonoidHom b) f s

theorem mk_list_sum (l : List R) (b : M) : mk l.sum b = (l.map fun a => mk a b).sum :=
  map_list_sum (mkAddMonoidHom b) l

theorem mk_multiset_sum (l : Multiset R) (b : M) : mk l.sum b = (l.map fun a => mk a b).sum :=
  (mkAddMonoidHom b).map_multiset_sum l

instance isLocalization : IsLocalization M (Localization M) where
  map_units := (Localization.monoidOf M).map_units
  surj := (Localization.monoidOf M).surj
  exists_of_eq := (Localization.monoidOf M).eq_iff_exists.mp

instance [NoZeroDivisors R] : NoZeroDivisors (Localization M) := IsLocalization.noZeroDivisors M

end

@[simp]
theorem toLocalizationMap_eq_monoidOf : toLocalizationMap M (Localization M) = monoidOf M :=
  rfl

theorem monoidOf_eq_algebraMap (x) : monoidOf M x = algebraMap R (Localization M) x :=
  rfl

theorem mk_one_eq_algebraMap (x) : mk x 1 = algebraMap R (Localization M) x :=
  rfl

theorem mk_eq_mk'_apply (x y) : mk x y = IsLocalization.mk' (Localization M) x y := by
  rw [mk_eq_monoidOf_mk'_apply, mk', toLocalizationMap_eq_monoidOf]

theorem mk_eq_mk' : (mk : R → M → Localization M) = IsLocalization.mk' (Localization M) :=
  mk_eq_monoidOf_mk'

theorem mk_algebraMap {A : Type*} [CommSemiring A] [Algebra A R] (m : A) :
    mk (algebraMap A R m) 1 = algebraMap A (Localization M) m := by
  rw [mk_eq_mk', mk'_eq_iff_eq_mul, Submonoid.coe_one, map_one, mul_one]; rfl

end Localization

namespace IsLocalization

variable [IsLocalization M S]

theorem to_map_eq_zero_iff {x : R} (hM : M ≤ nonZeroDivisors R) : algebraMap R S x = 0 ↔ x = 0 := by
  constructor <;> intro h
  · obtain ⟨c, hc⟩ := (map_eq_zero_iff M _ _).mp h
    exact (hM c.2).1 x hc
  · rw [h, map_zero]

protected theorem injectiveₛ (hM : ∀ m ∈ M, IsRegular m) : Injective (algebraMap R S) :=
  (toLocalizationMap M S).injective_iff.mpr hM

protected theorem to_map_ne_zero_of_mem_nonZeroDivisors [Nontrivial R] (hM : M ≤ nonZeroDivisors R)
    {x : R} (hx : x ∈ nonZeroDivisors R) : algebraMap R S x ≠ 0 := by
  rw [Ne, to_map_eq_zero_iff S hM]
  exact nonZeroDivisors.ne_zero hx

variable {S}

theorem sec_snd_ne_zero [Nontrivial R] (hM : M ≤ nonZeroDivisors R) (x : S) :
    ((sec M x).snd : R) ≠ 0 :=
  nonZeroDivisors.coe_ne_zero ⟨(sec M x).snd.val, hM (sec M x).snd.property⟩

variable [IsDomain R]

variable (S) in
/-- A `CommRing` `S` which is the localization of an integral domain `R` at a subset of
non-zero elements is an integral domain. -/
theorem isDomain_of_le_nonZeroDivisors (hM : M ≤ nonZeroDivisors R) : IsDomain S where
  __ : IsCancelMulZero S := (toLocalizationMap M S).isCancelMulZero
  __ : Nontrivial S := (toLocalizationMap M S).nontrivial fun h ↦ zero_notMem_nonZeroDivisors (hM h)

/-- The localization of an integral domain to a set of non-zero elements is an integral domain. -/
theorem isDomain_localization {M : Submonoid R} (hM : M ≤ nonZeroDivisors R) :
    IsDomain (Localization M) :=
  isDomain_of_le_nonZeroDivisors _ hM

end IsLocalization

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] {M : Submonoid R} (S : Type*) [CommRing S]
variable [Algebra R S] {P : Type*} [CommRing P]

namespace Localization

theorem neg_mk (a b) : -(mk a b : Localization M) = mk (-a) b := OreLocalization.neg_def _ _

theorem sub_mk (a c) (b d) : (mk a b : Localization M) - mk c d =
    mk ((d : R) * a - b * c) (b * d) := by
  rw [sub_eq_add_neg, neg_mk, add_mk, add_comm, mul_neg, ← sub_eq_add_neg]

end Localization

namespace IsLocalization

variable [IsLocalization M S]

theorem mk'_neg (x : R) (y : M) :
    mk' S (-x) y = - mk' S x y := by
  rw [eq_comm, eq_mk'_iff_mul_eq, neg_mul, map_neg, mk'_spec]

theorem mk'_sub (x₁ x₂ : R) (y₁ y₂ : M) :
    mk' S (x₁ * y₂ - x₂ * y₁) (y₁ * y₂) = mk' S x₁ y₁ - mk' S x₂ y₂ := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ← mk'_neg, ← mk'_add, neg_mul]

include M in
lemma injective_of_map_algebraMap_zero {T} [CommRing T] (f : S →+* T)
    (h : ∀ x, f (algebraMap R S x) = 0 → algebraMap R S x = 0) :
    Function.Injective f := by
  rw [IsLocalization.injective_iff_map_algebraMap_eq M]
  refine fun x y ↦ ⟨fun hz ↦ hz ▸ rfl, fun hz ↦ ?_⟩
  rw [← sub_eq_zero, ← map_sub, ← map_sub] at hz
  apply h at hz
  rwa [map_sub, sub_eq_zero] at hz

protected theorem injective (hM : M ≤ nonZeroDivisors R) : Injective (algebraMap R S) :=
  IsLocalization.injectiveₛ S fun _x hx ↦ isRegular_iff_mem_nonZeroDivisors.mpr (hM hx)

end IsLocalization

end CommRing
