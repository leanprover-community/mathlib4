/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Ring.Equiv
import Mathlib.GroupTheory.MonoidLocalization
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.NonZeroDivisors
import Mathlib.Tactic.Ring

#align_import ring_theory.localization.basic from "leanprover-community/mathlib"@"b69c9a770ecf37eb21f7b8cf4fa00de3b62694ec"

/-!
# Localizations of commutative rings

We characterize the localization of a commutative ring `R` at a submonoid `M` up to
isomorphism; that is, a commutative ring `S` is the localization of `R` at `M` iff we can find a
ring homomorphism `f : R →+* S` satisfying 3 properties:
1. For all `y ∈ M`, `f y` is a unit;
2. For all `z : S`, there exists `(x, y) : R × M` such that `z * f y = f x`;
3. For all `x, y : R`, `f x = f y` iff there exists `c ∈ M` such that `x * c = y * c`.

In the following, let `R, P` be commutative rings, `S, Q` be `R`- and `P`-algebras
and `M, T` be submonoids of `R` and `P` respectively, e.g.:
```
variables (R S P Q : Type*) [CommRing R] [CommRing S] [CommRing P] [CommRing Q]
variables [Algebra R S] [Algebra P Q] (M : Submonoid R) (T : Submonoid P)
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
 * `IsLocalization.algEquiv`: if `Q` is another localization of `R` at `M`, then `S` and `Q`
   are isomorphic as `R`-algebras

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


open Function

open BigOperators

section CommSemiring

variable {R : Type*} [CommSemiring R] (M : Submonoid R) (S : Type*) [CommSemiring S]

variable [Algebra R S] {P : Type*} [CommSemiring P]

/-- The typeclass `IsLocalization (M : Submodule R) S` where `S` is an `R`-algebra
expresses that `S` is isomorphic to the localization of `R` at `M`. -/
class IsLocalization : Prop where
  --Porting note: add ' to fields, and made new versions of these with either `S` or `M` explicit.
  /-- Everything in the image of `algebraMap` is a unit -/
  map_units' : ∀ y : M, IsUnit (algebraMap R S y)
  /-- the `algebraMap` is surjective -/
  surj' : ∀ z : S, ∃ x : R × M, z * algebraMap R S x.2 = algebraMap R S x.1
  /-- The kernel of `algebraMap` is the annihilator of `M` -/
  eq_iff_exists' : ∀ {x y}, algebraMap R S x = algebraMap R S y ↔ ∃ c : M, ↑c * x = ↑c * y
#align is_localization IsLocalization

variable {M}

namespace IsLocalization

section IsLocalization

variable [IsLocalization M S]

section

@[inherit_doc IsLocalization.map_units']
theorem map_units : ∀ y : M, IsUnit (algebraMap R S y) :=
  IsLocalization.map_units'

variable (M) {S}
@[inherit_doc IsLocalization.surj']
theorem surj : ∀ z : S, ∃ x : R × M, z * algebraMap R S x.2 = algebraMap R S x.1 :=
  IsLocalization.surj'

variable (S)
@[inherit_doc IsLocalization.eq_iff_exists']
theorem eq_iff_exists {x y} : algebraMap R S x = algebraMap R S y ↔ ∃ c : M, ↑c * x = ↑c * y :=
  IsLocalization.eq_iff_exists'

variable {S}
theorem of_le (N : Submonoid R) (h₁ : M ≤ N) (h₂ : ∀ r ∈ N, IsUnit (algebraMap R S r)) :
    IsLocalization N S :=
  { map_units' := fun r => h₂ r r.2
    surj' := fun s => by
      obtain ⟨⟨x, y, hy⟩, H⟩ := IsLocalization.surj M s
      -- ⊢ ∃ x, s * ↑(algebraMap R S) ↑x.snd = ↑(algebraMap R S) x.fst
      exact ⟨⟨x, y, h₁ hy⟩, H⟩
      -- 🎉 no goals
    eq_iff_exists' := @fun x y => by
      constructor
      -- ⊢ ↑(algebraMap R S) x = ↑(algebraMap R S) y → ∃ c, ↑c * x = ↑c * y
      · rw [IsLocalization.eq_iff_exists M]
        -- ⊢ (∃ c, ↑c * x = ↑c * y) → ∃ c, ↑c * x = ↑c * y
        rintro ⟨c, hc⟩
        -- ⊢ ∃ c, ↑c * x = ↑c * y
        exact ⟨⟨c, h₁ c.2⟩, hc⟩
        -- 🎉 no goals
      · rintro ⟨c, h⟩
        -- ⊢ ↑(algebraMap R S) x = ↑(algebraMap R S) y
        simpa only [map_mul, (h₂ c c.2).mul_right_inj] using
          congr_arg (algebraMap R S) h }
#align is_localization.of_le IsLocalization.of_le

variable (S)

/-- `IsLocalization.toLocalizationWithZeroMap M S` shows `S` is the monoid localization of
`R` at `M`. -/
@[simps]
def toLocalizationWithZeroMap : Submonoid.LocalizationWithZeroMap M S :=
  { algebraMap R S with
    toFun := algebraMap R S
    map_units' := IsLocalization.map_units _
    surj' := IsLocalization.surj _
    eq_iff_exists' := fun _ _ => IsLocalization.eq_iff_exists _ _ }
#align is_localization.to_localization_with_zero_map IsLocalization.toLocalizationWithZeroMap

/-- `IsLocalization.toLocalizationMap M S` shows `S` is the monoid localization of `R` at `M`. -/
abbrev toLocalizationMap : Submonoid.LocalizationMap M S :=
  (toLocalizationWithZeroMap M S).toLocalizationMap
#align is_localization.to_localization_map IsLocalization.toLocalizationMap

@[simp]
theorem toLocalizationMap_toMap : (toLocalizationMap M S).toMap = (algebraMap R S : R →*₀ S) :=
  rfl
#align is_localization.to_localization_map_to_map IsLocalization.toLocalizationMap_toMap

theorem toLocalizationMap_toMap_apply (x) : (toLocalizationMap M S).toMap x = algebraMap R S x :=
  rfl
#align is_localization.to_localization_map_to_map_apply IsLocalization.toLocalizationMap_toMap_apply

end

variable (M) {S}

/-- Given a localization map `f : M →* N`, a section function sending `z : N` to some
`(x, y) : M × S` such that `f x * (f y)⁻¹ = z`. -/
noncomputable def sec (z : S) : R × M :=
  Classical.choose <| IsLocalization.surj _ z
#align is_localization.sec IsLocalization.sec

@[simp]
theorem toLocalizationMap_sec : (toLocalizationMap M S).sec = sec M :=
  rfl
#align is_localization.to_localization_map_sec IsLocalization.toLocalizationMap_sec

/-- Given `z : S`, `IsLocalization.sec M z` is defined to be a pair `(x, y) : R × M` such
that `z * f y = f x` (so this lemma is true by definition). -/
theorem sec_spec (z : S) :
    z * algebraMap R S (IsLocalization.sec M z).2 = algebraMap R S (IsLocalization.sec M z).1 :=
  Classical.choose_spec <| IsLocalization.surj _ z
#align is_localization.sec_spec IsLocalization.sec_spec

/-- Given `z : S`, `IsLocalization.sec M z` is defined to be a pair `(x, y) : R × M` such
that `z * f y = f x`, so this lemma is just an application of `S`'s commutativity. -/
theorem sec_spec' (z : S) :
    algebraMap R S (IsLocalization.sec M z).1 = algebraMap R S (IsLocalization.sec M z).2 * z := by
  rw [mul_comm, sec_spec]
  -- 🎉 no goals
#align is_localization.sec_spec' IsLocalization.sec_spec'

variable {M}

theorem map_right_cancel {x y} {c : M} (h : algebraMap R S (c * x) = algebraMap R S (c * y)) :
    algebraMap R S x = algebraMap R S y :=
  (toLocalizationMap M S).map_right_cancel h
#align is_localization.map_right_cancel IsLocalization.map_right_cancel

theorem map_left_cancel {x y} {c : M} (h : algebraMap R S (x * c) = algebraMap R S (y * c)) :
    algebraMap R S x = algebraMap R S y :=
  (toLocalizationMap M S).map_left_cancel h
#align is_localization.map_left_cancel IsLocalization.map_left_cancel

theorem eq_zero_of_fst_eq_zero {z x} {y : M} (h : z * algebraMap R S y = algebraMap R S x)
    (hx : x = 0) : z = 0 := by
  rw [hx, (algebraMap R S).map_zero] at h
  -- ⊢ z = 0
  exact (IsUnit.mul_left_eq_zero (IsLocalization.map_units S y)).1 h
  -- 🎉 no goals
#align is_localization.eq_zero_of_fst_eq_zero IsLocalization.eq_zero_of_fst_eq_zero

variable (M S)

theorem map_eq_zero_iff (r : R) : algebraMap R S r = 0 ↔ ∃ m : M, ↑m * r = 0 := by
  constructor
  -- ⊢ ↑(algebraMap R S) r = 0 → ∃ m, ↑m * r = 0
  intro h
  -- ⊢ ∃ m, ↑m * r = 0
  · obtain ⟨m, hm⟩ := (IsLocalization.eq_iff_exists M S).mp ((algebraMap R S).map_zero.trans h.symm)
    -- ⊢ ∃ m, ↑m * r = 0
    exact ⟨m, by simpa using hm.symm⟩
    -- 🎉 no goals
  · rintro ⟨m, hm⟩
    -- ⊢ ↑(algebraMap R S) r = 0
    rw [← (IsLocalization.map_units S m).mul_right_inj, mul_zero, ← RingHom.map_mul, hm,
      RingHom.map_zero]
#align is_localization.map_eq_zero_iff IsLocalization.map_eq_zero_iff

variable {M}

/-- `IsLocalization.mk' S` is the surjection sending `(x, y) : R × M` to
`f x * (f y)⁻¹`. -/
noncomputable def mk' (x : R) (y : M) : S :=
  (toLocalizationMap M S).mk' x y
#align is_localization.mk' IsLocalization.mk'

@[simp]
theorem mk'_sec (z : S) : mk' S (IsLocalization.sec M z).1 (IsLocalization.sec M z).2 = z :=
  (toLocalizationMap M S).mk'_sec _
#align is_localization.mk'_sec IsLocalization.mk'_sec

theorem mk'_mul (x₁ x₂ : R) (y₁ y₂ : M) : mk' S (x₁ * x₂) (y₁ * y₂) = mk' S x₁ y₁ * mk' S x₂ y₂ :=
  (toLocalizationMap M S).mk'_mul _ _ _ _
#align is_localization.mk'_mul IsLocalization.mk'_mul

theorem mk'_one (x) : mk' S x (1 : M) = algebraMap R S x :=
  (toLocalizationMap M S).mk'_one _
#align is_localization.mk'_one IsLocalization.mk'_one

@[simp]
theorem mk'_spec (x) (y : M) : mk' S x y * algebraMap R S y = algebraMap R S x :=
  (toLocalizationMap M S).mk'_spec _ _
#align is_localization.mk'_spec IsLocalization.mk'_spec

@[simp]
theorem mk'_spec' (x) (y : M) : algebraMap R S y * mk' S x y = algebraMap R S x :=
  (toLocalizationMap M S).mk'_spec' _ _
#align is_localization.mk'_spec' IsLocalization.mk'_spec'

@[simp]
theorem mk'_spec_mk (x) (y : R) (hy : y ∈ M) :
    mk' S x ⟨y, hy⟩ * algebraMap R S y = algebraMap R S x :=
  mk'_spec S x ⟨y, hy⟩
#align is_localization.mk'_spec_mk IsLocalization.mk'_spec_mk

@[simp]
theorem mk'_spec'_mk (x) (y : R) (hy : y ∈ M) :
    algebraMap R S y * mk' S x ⟨y, hy⟩ = algebraMap R S x :=
  mk'_spec' S x ⟨y, hy⟩
#align is_localization.mk'_spec'_mk IsLocalization.mk'_spec'_mk

variable {S}

theorem eq_mk'_iff_mul_eq {x} {y : M} {z} :
    z = mk' S x y ↔ z * algebraMap R S y = algebraMap R S x :=
  (toLocalizationMap M S).eq_mk'_iff_mul_eq
#align is_localization.eq_mk'_iff_mul_eq IsLocalization.eq_mk'_iff_mul_eq

theorem mk'_eq_iff_eq_mul {x} {y : M} {z} :
    mk' S x y = z ↔ algebraMap R S x = z * algebraMap R S y :=
  (toLocalizationMap M S).mk'_eq_iff_eq_mul
#align is_localization.mk'_eq_iff_eq_mul IsLocalization.mk'_eq_iff_eq_mul

theorem mk'_add_eq_iff_add_mul_eq_mul {x} {y : M} {z₁ z₂} :
    mk' S x y + z₁ = z₂ ↔ algebraMap R S x + z₁ * algebraMap R S y = z₂ * algebraMap R S y := by
  rw [← mk'_spec S x y, ← IsUnit.mul_left_inj (IsLocalization.map_units S y), right_distrib]
  -- 🎉 no goals
#align is_localization.mk'_add_eq_iff_add_mul_eq_mul IsLocalization.mk'_add_eq_iff_add_mul_eq_mul

variable (M)

theorem mk'_surjective (z : S) : ∃ (x : _) (y : M), mk' S x y = z :=
  let ⟨r, hr⟩ := IsLocalization.surj _ z
  ⟨r.1, r.2, (eq_mk'_iff_mul_eq.2 hr).symm⟩
#align is_localization.mk'_surjective IsLocalization.mk'_surjective

variable (S)

/-- The localization of a `Fintype` is a `Fintype`. Cannot be an instance. -/
noncomputable def fintype' [Fintype R] : Fintype S :=
  have := Classical.propDecidable
  Fintype.ofSurjective (Function.uncurry <| IsLocalization.mk' S) fun a =>
    Prod.exists'.mpr <| IsLocalization.mk'_surjective M a
#align is_localization.fintype' IsLocalization.fintype'

variable {M S}

/-- Localizing at a submonoid with 0 inside it leads to the trivial ring. -/
def uniqueOfZeroMem (h : (0 : R) ∈ M) : Unique S :=
  uniqueOfZeroEqOne <| by simpa using IsLocalization.map_units S ⟨0, h⟩
                          -- 🎉 no goals
#align is_localization.unique_of_zero_mem IsLocalization.uniqueOfZeroMem

theorem mk'_eq_iff_eq {x₁ x₂} {y₁ y₂ : M} :
    mk' S x₁ y₁ = mk' S x₂ y₂ ↔ algebraMap R S (y₂ * x₁) = algebraMap R S (y₁ * x₂) :=
  (toLocalizationMap M S).mk'_eq_iff_eq
#align is_localization.mk'_eq_iff_eq IsLocalization.mk'_eq_iff_eq

theorem mk'_eq_iff_eq' {x₁ x₂} {y₁ y₂ : M} :
    mk' S x₁ y₁ = mk' S x₂ y₂ ↔ algebraMap R S (x₁ * y₂) = algebraMap R S (x₂ * y₁) :=
  (toLocalizationMap M S).mk'_eq_iff_eq'
#align is_localization.mk'_eq_iff_eq' IsLocalization.mk'_eq_iff_eq'

theorem mk'_mem_iff {x} {y : M} {I : Ideal S} : mk' S x y ∈ I ↔ algebraMap R S x ∈ I := by
  constructor <;> intro h
  -- ⊢ mk' S x y ∈ I → ↑(algebraMap R S) x ∈ I
                  -- ⊢ ↑(algebraMap R S) x ∈ I
                  -- ⊢ mk' S x y ∈ I
  · rw [← mk'_spec S x y, mul_comm]
    -- ⊢ ↑(algebraMap R S) ↑y * mk' S x y ∈ I
    exact I.mul_mem_left ((algebraMap R S) y) h
    -- 🎉 no goals
  · rw [← mk'_spec S x y] at h
    -- ⊢ mk' S x y ∈ I
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 (map_units S y)
    -- ⊢ mk' S x y ∈ I
    have := I.mul_mem_left b h
    -- ⊢ mk' S x y ∈ I
    rwa [mul_comm, mul_assoc, hb, mul_one] at this
    -- 🎉 no goals
#align is_localization.mk'_mem_iff IsLocalization.mk'_mem_iff

protected theorem eq {a₁ b₁} {a₂ b₂ : M} :
    mk' S a₁ a₂ = mk' S b₁ b₂ ↔ ∃ c : M, ↑c * (↑b₂ * a₁) = c * (a₂ * b₁) :=
  (toLocalizationMap M S).eq
#align is_localization.eq IsLocalization.eq

theorem mk'_eq_zero_iff (x : R) (s : M) : mk' S x s = 0 ↔ ∃ m : M, ↑m * x = 0 := by
  rw [← (map_units S s).mul_left_inj, mk'_spec, zero_mul, map_eq_zero_iff M]
  -- 🎉 no goals
#align is_localization.mk'_eq_zero_iff IsLocalization.mk'_eq_zero_iff

@[simp]
theorem mk'_zero (s : M) : IsLocalization.mk' S 0 s = 0 := by
  rw [eq_comm, IsLocalization.eq_mk'_iff_mul_eq, zero_mul, map_zero]
  -- 🎉 no goals
#align is_localization.mk'_zero IsLocalization.mk'_zero

theorem ne_zero_of_mk'_ne_zero {x : R} {y : M} (hxy : IsLocalization.mk' S x y ≠ 0) : x ≠ 0 := by
  rintro rfl
  -- ⊢ False
  exact hxy (IsLocalization.mk'_zero _)
  -- 🎉 no goals
#align is_localization.ne_zero_of_mk'_ne_zero IsLocalization.ne_zero_of_mk'_ne_zero

section Ext

variable [Algebra R P] [IsLocalization M P]

theorem eq_iff_eq {x y} :
    algebraMap R S x = algebraMap R S y ↔ algebraMap R P x = algebraMap R P y :=
  (toLocalizationMap M S).eq_iff_eq (toLocalizationMap M P)
#align is_localization.eq_iff_eq IsLocalization.eq_iff_eq

theorem mk'_eq_iff_mk'_eq {x₁ x₂} {y₁ y₂ : M} :
    mk' S x₁ y₁ = mk' S x₂ y₂ ↔ mk' P x₁ y₁ = mk' P x₂ y₂ :=
  (toLocalizationMap M S).mk'_eq_iff_mk'_eq (toLocalizationMap M P)
#align is_localization.mk'_eq_iff_mk'_eq IsLocalization.mk'_eq_iff_mk'_eq

theorem mk'_eq_of_eq {a₁ b₁ : R} {a₂ b₂ : M} (H : ↑a₂ * b₁ = ↑b₂ * a₁) :
    mk' S a₁ a₂ = mk' S b₁ b₂ :=
  (toLocalizationMap M S).mk'_eq_of_eq H
#align is_localization.mk'_eq_of_eq IsLocalization.mk'_eq_of_eq

theorem mk'_eq_of_eq' {a₁ b₁ : R} {a₂ b₂ : M} (H : b₁ * ↑a₂ = a₁ * ↑b₂) :
    mk' S a₁ a₂ = mk' S b₁ b₂ :=
  (toLocalizationMap M S).mk'_eq_of_eq' H
#align is_localization.mk'_eq_of_eq' IsLocalization.mk'_eq_of_eq'

variable (S)

@[simp]
theorem mk'_self {x : R} (hx : x ∈ M) : mk' S x ⟨x, hx⟩ = 1 :=
  (toLocalizationMap M S).mk'_self _ hx
#align is_localization.mk'_self IsLocalization.mk'_self

@[simp]
theorem mk'_self' {x : M} : mk' S (x : R) x = 1 :=
  (toLocalizationMap M S).mk'_self' _
#align is_localization.mk'_self' IsLocalization.mk'_self'

theorem mk'_self'' {x : M} : mk' S x.1 x = 1 :=
  mk'_self' _
#align is_localization.mk'_self'' IsLocalization.mk'_self''

end Ext

theorem mul_mk'_eq_mk'_of_mul (x y : R) (z : M) :
    (algebraMap R S) x * mk' S y z = mk' S (x * y) z :=
  (toLocalizationMap M S).mul_mk'_eq_mk'_of_mul _ _ _
#align is_localization.mul_mk'_eq_mk'_of_mul IsLocalization.mul_mk'_eq_mk'_of_mul

theorem mk'_eq_mul_mk'_one (x : R) (y : M) : mk' S x y = (algebraMap R S) x * mk' S 1 y :=
  ((toLocalizationMap M S).mul_mk'_one_eq_mk' _ _).symm
#align is_localization.mk'_eq_mul_mk'_one IsLocalization.mk'_eq_mul_mk'_one

@[simp]
theorem mk'_mul_cancel_left (x : R) (y : M) : mk' S (y * x : R) y = (algebraMap R S) x :=
  (toLocalizationMap M S).mk'_mul_cancel_left _ _
#align is_localization.mk'_mul_cancel_left IsLocalization.mk'_mul_cancel_left

theorem mk'_mul_cancel_right (x : R) (y : M) : mk' S (x * y) y = (algebraMap R S) x :=
  (toLocalizationMap M S).mk'_mul_cancel_right _ _
#align is_localization.mk'_mul_cancel_right IsLocalization.mk'_mul_cancel_right

@[simp]
theorem mk'_mul_mk'_eq_one (x y : M) : mk' S (x : R) y * mk' S (y : R) x = 1 := by
  rw [← mk'_mul, mul_comm]; exact mk'_self _ _
  -- ⊢ mk' S (↑y * ↑x) (y * x) = 1
                            -- 🎉 no goals
#align is_localization.mk'_mul_mk'_eq_one IsLocalization.mk'_mul_mk'_eq_one

theorem mk'_mul_mk'_eq_one' (x : R) (y : M) (h : x ∈ M) : mk' S x y * mk' S (y : R) ⟨x, h⟩ = 1 :=
  mk'_mul_mk'_eq_one ⟨x, h⟩ _
#align is_localization.mk'_mul_mk'_eq_one' IsLocalization.mk'_mul_mk'_eq_one'

theorem smul_mk' (x y : R) (m : M) : x • mk' S y m = mk' S (x * y) m  := by
  nth_rw 2 [← one_mul m]
  -- ⊢ x • mk' S y m = mk' S (x * y) (1 * m)
  rw [mk'_mul, mk'_one, Algebra.smul_def]
  -- 🎉 no goals

@[simp] theorem smul_mk'_one (x : R) (m : M) : x • mk' S 1 m = mk' S x m := by
  rw [smul_mk', mul_one]
  -- 🎉 no goals

@[simp] lemma smul_mk'_self {m : M} {r : R} :
    (m : R) • mk' S r m = algebraMap R S r := by
  rw [smul_mk', mk'_mul_cancel_left]
  -- 🎉 no goals

section

variable (M)

theorem isUnit_comp (j : S →+* P) (y : M) : IsUnit (j.comp (algebraMap R S) y) :=
  (toLocalizationMap M S).isUnit_comp j.toMonoidHom _
#align is_localization.is_unit_comp IsLocalization.isUnit_comp

end

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `CommSemiring`s
`g : R →+* P` such that `g(M) ⊆ Units P`, `f x = f y → g x = g y` for all `x y : R`. -/
theorem eq_of_eq {g : R →+* P} (hg : ∀ y : M, IsUnit (g y)) {x y}
    (h : (algebraMap R S) x = (algebraMap R S) y) : g x = g y :=
  @Submonoid.LocalizationMap.eq_of_eq _ _ _ _ _ _ _ (toLocalizationMap M S) g.toMonoidHom hg _ _ h
#align is_localization.eq_of_eq IsLocalization.eq_of_eq

theorem mk'_add (x₁ x₂ : R) (y₁ y₂ : M) :
    mk' S (x₁ * y₂ + x₂ * y₁) (y₁ * y₂) = mk' S x₁ y₁ + mk' S x₂ y₂ :=
  mk'_eq_iff_eq_mul.2 <|
    Eq.symm
      (by
        rw [mul_comm (_ + _), mul_add, mul_mk'_eq_mk'_of_mul, mk'_add_eq_iff_add_mul_eq_mul,
          mul_comm (_ * _), ← mul_assoc, add_comm, ← map_mul, mul_mk'_eq_mk'_of_mul,
          add_comm _ (mk' _ _ _), mk'_add_eq_iff_add_mul_eq_mul]
        simp only [map_add, Submonoid.coe_mul, map_mul]
        -- ⊢ ↑(algebraMap R S) ↑y₁ * (↑(algebraMap R S) ↑y₁ * ↑(algebraMap R S) ↑y₂) * ↑( …
        ring)
        -- 🎉 no goals
#align is_localization.mk'_add IsLocalization.mk'_add

theorem mul_add_inv_left {g : R →+* P} (h : ∀ y : M, IsUnit (g y)) (y : M) (w z₁ z₂ : P) :
    w * ↑(IsUnit.liftRight (g.toMonoidHom.restrict M) h y)⁻¹ + z₁ =
    z₂ ↔ w + g y * z₁ = g y * z₂ := by
  rw [mul_comm, ← one_mul z₁, ← Units.inv_mul (IsUnit.liftRight (g.toMonoidHom.restrict M) h y),
    mul_assoc, ← mul_add, Units.inv_mul_eq_iff_eq_mul, Units.inv_mul_cancel_left,
    IsUnit.coe_liftRight]
  simp [RingHom.toMonoidHom_eq_coe, MonoidHom.restrict_apply]
  -- 🎉 no goals
#align is_localization.mul_add_inv_left IsLocalization.mul_add_inv_left

theorem lift_spec_mul_add {g : R →+* P} (hg : ∀ y : M, IsUnit (g y)) (z w w' v) :
    ((toLocalizationWithZeroMap M S).lift g.toMonoidWithZeroHom hg) z * w + w' = v ↔
      g ((toLocalizationMap M S).sec z).1 * w + g ((toLocalizationMap M S).sec z).2 * w' =
        g ((toLocalizationMap M S).sec z).2 * v := by
  erw [mul_comm, ← mul_assoc, mul_add_inv_left hg, mul_comm]
  -- ⊢ ↑↑(RingHom.toMonoidWithZeroHom g) (Submonoid.LocalizationMap.sec (toLocaliza …
  rfl
  -- 🎉 no goals
#align is_localization.lift_spec_mul_add IsLocalization.lift_spec_mul_add

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `CommSemiring`s
`g : R →+* P` such that `g y` is invertible for all `y : M`, the homomorphism induced from
`S` to `P` sending `z : S` to `g x * (g y)⁻¹`, where `(x, y) : R × M` are such that
`z = f x * (f y)⁻¹`. -/
noncomputable def lift {g : R →+* P} (hg : ∀ y : M, IsUnit (g y)) : S →+* P :=
  {
    @Submonoid.LocalizationWithZeroMap.lift _ _ _ _ _ _ _ (toLocalizationWithZeroMap M S)
      g.toMonoidWithZeroHom hg with
    map_add' := by
      intro x y
      -- ⊢ OneHom.toFun (↑{ toOneHom := { toFun := src✝.toFun, map_one' := (_ : ZeroHom …
      erw [(toLocalizationMap M S).lift_spec, mul_add, mul_comm, eq_comm, lift_spec_mul_add,
        add_comm, mul_comm, mul_assoc, mul_comm, mul_assoc, lift_spec_mul_add]
      simp_rw [← mul_assoc]
      -- ⊢ ↑g (Submonoid.LocalizationMap.sec (toLocalizationMap M S) y).fst * ↑g ↑(Subm …
      show g _ * g _ * g _ + g _ * g _ * g _ = g _ * g _ * g _
      -- ⊢ ↑g (Submonoid.LocalizationMap.sec (toLocalizationMap M S) y).fst * ↑g ↑(Subm …
      simp_rw [← map_mul g, ← map_add g]
      -- ⊢ ↑g ((Submonoid.LocalizationMap.sec (toLocalizationMap M S) y).fst * ↑(Submon …
      apply @eq_of_eq _ _ _ S _ _ _ _ _ g hg
      -- ⊢ ↑(algebraMap R S) ((Submonoid.LocalizationMap.sec (toLocalizationMap M S) y) …
      simp only [sec_spec', toLocalizationMap_sec, map_add, map_mul]
      -- ⊢ ↑(algebraMap R S) ↑(sec M y).snd * y * ↑(algebraMap R S) ↑(sec M x).snd * ↑( …
      ring }
      -- 🎉 no goals
#align is_localization.lift IsLocalization.lift

variable {g : R →+* P} (hg : ∀ y : M, IsUnit (g y))

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `CommSemiring`s
`g : R →* P` such that `g y` is invertible for all `y : M`, the homomorphism induced from
`S` to `P` maps `f x * (f y)⁻¹` to `g x * (g y)⁻¹` for all `x : R, y ∈ M`. -/
theorem lift_mk' (x y) :
    lift hg (mk' S x y) = g x * ↑(IsUnit.liftRight (g.toMonoidHom.restrict M) hg y)⁻¹ :=
  (toLocalizationMap M S).lift_mk' _ _ _
#align is_localization.lift_mk' IsLocalization.lift_mk'

theorem lift_mk'_spec (x v) (y : M) : lift hg (mk' S x y) = v ↔ g x = g y * v :=
  (toLocalizationMap M S).lift_mk'_spec _ _ _ _
#align is_localization.lift_mk'_spec IsLocalization.lift_mk'_spec

@[simp]
theorem lift_eq (x : R) : lift hg ((algebraMap R S) x) = g x :=
  (toLocalizationMap M S).lift_eq _ _
#align is_localization.lift_eq IsLocalization.lift_eq

theorem lift_eq_iff {x y : R × M} :
    lift hg (mk' S x.1 x.2) = lift hg (mk' S y.1 y.2) ↔ g (x.1 * y.2) = g (y.1 * x.2) :=
  (toLocalizationMap M S).lift_eq_iff _
#align is_localization.lift_eq_iff IsLocalization.lift_eq_iff

@[simp]
theorem lift_comp : (lift hg).comp (algebraMap R S) = g :=
  RingHom.ext <| (FunLike.ext_iff (F := MonoidHom _ _)).1 <| (toLocalizationMap M S).lift_comp _
#align is_localization.lift_comp IsLocalization.lift_comp

@[simp]
theorem lift_of_comp (j : S →+* P) : lift (isUnit_comp M j) = j :=
  RingHom.ext <| (FunLike.ext_iff (F := MonoidHom _ _)).1 <|
    (toLocalizationMap M S).lift_of_comp j.toMonoidHom
#align is_localization.lift_of_comp IsLocalization.lift_of_comp

variable (M)

/-- See note [partially-applied ext lemmas] -/
theorem monoidHom_ext ⦃j k : S →* P⦄
    (h : j.comp (algebraMap R S : R →* S) = k.comp (algebraMap R S)) : j = k :=
  Submonoid.LocalizationMap.epic_of_localizationMap (toLocalizationMap M S) <| FunLike.congr_fun h
#align is_localization.monoid_hom_ext IsLocalization.monoidHom_ext

/-- See note [partially-applied ext lemmas] -/
theorem ringHom_ext ⦃j k : S →+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) :
    j = k :=
  RingHom.coe_monoidHom_injective <| monoidHom_ext M <| MonoidHom.ext <| RingHom.congr_fun h
#align is_localization.ring_hom_ext IsLocalization.ringHom_ext

/- This is not an instance because the submonoid `M` would become a metavariable
  in typeclass search. -/
theorem algHom_subsingleton [Algebra R P] : Subsingleton (S →ₐ[R] P) :=
  ⟨fun f g =>
    AlgHom.coe_ringHom_injective <|
      IsLocalization.ringHom_ext M <| by rw [f.comp_algebraMap, g.comp_algebraMap]⟩
                                         -- 🎉 no goals
#align is_localization.alg_hom_subsingleton IsLocalization.algHom_subsingleton

/-- To show `j` and `k` agree on the whole localization, it suffices to show they agree
on the image of the base ring, if they preserve `1` and `*`. -/
protected theorem ext (j k : S → P) (hj1 : j 1 = 1) (hk1 : k 1 = 1)
    (hjm : ∀ a b, j (a * b) = j a * j b) (hkm : ∀ a b, k (a * b) = k a * k b)
    (h : ∀ a, j (algebraMap R S a) = k (algebraMap R S a)) : j = k :=
  let j' : MonoidHom S P :=
    { toFun := j, map_one' := hj1, map_mul' := hjm }
  let k' : MonoidHom S P :=
    { toFun := k, map_one' := hk1, map_mul' := hkm }
  have : j' = k' := monoidHom_ext M (MonoidHom.ext h)
  show j'.toFun = k'.toFun by rw [this]
                              -- 🎉 no goals
#align is_localization.ext IsLocalization.ext

variable {M}

theorem lift_unique {j : S →+* P} (hj : ∀ x, j ((algebraMap R S) x) = g x) : lift hg = j :=
  RingHom.ext <|
    (FunLike.ext_iff (F := MonoidHom _ _)).1 <|
      @Submonoid.LocalizationMap.lift_unique _ _ _ _ _ _ _ (toLocalizationMap M S) g.toMonoidHom hg
        j.toMonoidHom hj
#align is_localization.lift_unique IsLocalization.lift_unique

@[simp]
theorem lift_id (x) : lift (map_units S : ∀ _ : M, IsUnit _) x = x :=
  (toLocalizationMap M S).lift_id _
#align is_localization.lift_id IsLocalization.lift_id

theorem lift_surjective_iff :
    Surjective (lift hg : S → P) ↔ ∀ v : P, ∃ x : R × M, v * g x.2 = g x.1 :=
  (toLocalizationMap M S).lift_surjective_iff hg
#align is_localization.lift_surjective_iff IsLocalization.lift_surjective_iff

theorem lift_injective_iff :
    Injective (lift hg : S → P) ↔ ∀ x y, algebraMap R S x = algebraMap R S y ↔ g x = g y :=
  (toLocalizationMap M S).lift_injective_iff hg
#align is_localization.lift_injective_iff IsLocalization.lift_injective_iff

section Map

variable {T : Submonoid P} {Q : Type*} [CommSemiring Q] (hy : M ≤ T.comap g)

variable [Algebra P Q] [IsLocalization T Q]

section

variable (Q)

/-- Map a homomorphism `g : R →+* P` to `S →+* Q`, where `S` and `Q` are
localizations of `R` and `P` at `M` and `T` respectively,
such that `g(M) ⊆ T`.

We send `z : S` to `algebraMap P Q (g x) * (algebraMap P Q (g y))⁻¹`, where
`(x, y) : R × M` are such that `z = f x * (f y)⁻¹`. -/
noncomputable def map (g : R →+* P) (hy : M ≤ T.comap g) : S →+* Q :=
  @lift R _ M _ _ _ _ _ _ ((algebraMap P Q).comp g) fun y => map_units _ ⟨g y, hy y.2⟩
#align is_localization.map IsLocalization.map

end

--Porting note: added `simp` attribute, since it proves very similar lemmas marked `simp`
@[simp]
theorem map_eq (x) : map Q g hy ((algebraMap R S) x) = algebraMap P Q (g x) :=
  lift_eq (fun y => map_units _ ⟨g y, hy y.2⟩) x
#align is_localization.map_eq IsLocalization.map_eq

@[simp]
theorem map_comp : (map Q g hy).comp (algebraMap R S) = (algebraMap P Q).comp g :=
  lift_comp fun y => map_units _ ⟨g y, hy y.2⟩
#align is_localization.map_comp IsLocalization.map_comp

theorem map_mk' (x) (y : M) : map Q g hy (mk' S x y) = mk' Q (g x) ⟨g y, hy y.2⟩ :=
  @Submonoid.LocalizationMap.map_mk' _ _ _ _ _ _ _ (toLocalizationMap M S) g.toMonoidHom _
    (fun y => hy y.2) _ _ (toLocalizationMap T Q) _ _
#align is_localization.map_mk' IsLocalization.map_mk'

--Porting note: new theorem
@[simp]
theorem map_id_mk' {Q : Type*} [CommSemiring Q] [Algebra R Q] [IsLocalization M Q] (x) (y : M) :
    map Q (RingHom.id R) (le_refl M) (mk' S x y) = mk' Q x y :=
  map_mk' _ _ _

@[simp]
theorem map_id (z : S) (h : M ≤ M.comap (RingHom.id R) := le_refl M) :
    map S (RingHom.id _) h z = z :=
  lift_id _
#align is_localization.map_id IsLocalization.map_id

theorem map_unique (j : S →+* Q) (hj : ∀ x : R, j (algebraMap R S x) = algebraMap P Q (g x)) :
    map Q g hy = j :=
  lift_unique (fun y => map_units _ ⟨g y, hy y.2⟩) hj
#align is_localization.map_unique IsLocalization.map_unique

/-- If `CommSemiring` homs `g : R →+* P, l : P →+* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
theorem map_comp_map {A : Type*} [CommSemiring A] {U : Submonoid A} {W} [CommSemiring W]
    [Algebra A W] [IsLocalization U W] {l : P →+* A} (hl : T ≤ U.comap l) :
    (map W l hl).comp (map Q g hy : S →+* _) = map W (l.comp g) fun _ hx => hl (hy hx) :=
  RingHom.ext fun x =>
    @Submonoid.LocalizationMap.map_map _ _ _ _ _ P _ (toLocalizationMap M S) g _ (fun y => hy y.2)
      _ _ _ _ _ _ _ _ (toLocalizationMap U W) l (fun w => hl w.2) x
#align is_localization.map_comp_map IsLocalization.map_comp_map

/-- If `CommSemiring` homs `g : R →+* P, l : P →+* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
theorem map_map {A : Type*} [CommSemiring A] {U : Submonoid A} {W} [CommSemiring W] [Algebra A W]
    [IsLocalization U W] {l : P →+* A} (hl : T ≤ U.comap l) (x : S) :
    map W l hl (map Q g hy x) = map W (l.comp g) (fun x hx => hl (hy hx)) x := by
  rw [← map_comp_map (Q := Q) hy hl]; rfl
  -- ⊢ ↑(map W l hl) (↑(map Q g hy) x) = ↑(RingHom.comp (map W l hl) (map Q g hy)) x
                                      -- 🎉 no goals
#align is_localization.map_map IsLocalization.map_map

theorem map_smul (x : S) (z : R) : map Q g hy (z • x : S) = g z • map Q g hy x := by
  rw [Algebra.smul_def, Algebra.smul_def, RingHom.map_mul, map_eq]
  -- 🎉 no goals
#align is_localization.map_smul IsLocalization.map_smul

section

variable (S Q)

/-- If `S`, `Q` are localizations of `R` and `P` at submonoids `M, T` respectively, an
isomorphism `j : R ≃+* P` such that `j(M) = T` induces an isomorphism of localizations
`S ≃+* Q`. -/
@[simps]
noncomputable def ringEquivOfRingEquiv (h : R ≃+* P) (H : M.map h.toMonoidHom = T) : S ≃+* Q :=
  have H' : T.map h.symm.toMonoidHom = M := by
    rw [← M.map_id, ← H, Submonoid.map_map]
    -- ⊢ Submonoid.map (MonoidHom.comp (RingEquiv.toMonoidHom (RingEquiv.symm h)) (Ri …
    congr
    -- ⊢ MonoidHom.comp (RingEquiv.toMonoidHom (RingEquiv.symm h)) (RingEquiv.toMonoi …
    ext
    -- ⊢ ↑(MonoidHom.comp (RingEquiv.toMonoidHom (RingEquiv.symm h)) (RingEquiv.toMon …
    apply h.symm_apply_apply
    -- 🎉 no goals
  {
    map Q (h : R →+* P) (M.le_comap_of_map_le (le_of_eq H)) with
    toFun := map Q (h : R →+* P) (M.le_comap_of_map_le (le_of_eq H))
    invFun := map S (h.symm : P →+* R) (T.le_comap_of_map_le (le_of_eq H'))
    left_inv := fun x => by
      rw [map_map, map_unique _ (RingHom.id _), RingHom.id_apply]
      -- ⊢ ∀ (x : R), ↑(RingHom.id S) (↑(algebraMap R S) x) = ↑(algebraMap R S) (↑(Ring …
      simp
      -- 🎉 no goals
    right_inv := fun x => by
      rw [map_map, map_unique _ (RingHom.id _), RingHom.id_apply]
      -- ⊢ ∀ (x : P), ↑(RingHom.id Q) (↑(algebraMap P Q) x) = ↑(algebraMap P Q) (↑(Ring …
      simp }
      -- 🎉 no goals
#align is_localization.ring_equiv_of_ring_equiv IsLocalization.ringEquivOfRingEquiv

end

theorem ringEquivOfRingEquiv_eq_map {j : R ≃+* P} (H : M.map j.toMonoidHom = T) :
    (ringEquivOfRingEquiv S Q j H : S →+* Q) =
      map Q (j : R →+* P) (M.le_comap_of_map_le (le_of_eq H)) :=
  rfl
#align is_localization.ring_equiv_of_ring_equiv_eq_map IsLocalization.ringEquivOfRingEquiv_eq_map

--Porting note: removed `simp`, `simp` can prove it
theorem ringEquivOfRingEquiv_eq {j : R ≃+* P} (H : M.map j.toMonoidHom = T) (x) :
    ringEquivOfRingEquiv S Q j H ((algebraMap R S) x) = algebraMap P Q (j x) := by
  simp
  -- 🎉 no goals
#align is_localization.ring_equiv_of_ring_equiv_eq IsLocalization.ringEquivOfRingEquiv_eq

theorem ringEquivOfRingEquiv_mk' {j : R ≃+* P} (H : M.map j.toMonoidHom = T) (x : R) (y : M) :
    ringEquivOfRingEquiv S Q j H (mk' S x y) =
      mk' Q (j x) ⟨j y, show j y ∈ T from H ▸ Set.mem_image_of_mem j y.2⟩ := by
  simp [map_mk']
  -- 🎉 no goals
#align is_localization.ring_equiv_of_ring_equiv_mk' IsLocalization.ringEquivOfRingEquiv_mk'

end Map

section AlgEquiv

variable {Q : Type*} [CommSemiring Q] [Algebra R Q] [IsLocalization M Q]

section

variable (M S Q)

/-- If `S`, `Q` are localizations of `R` at the submonoid `M` respectively,
there is an isomorphism of localizations `S ≃ₐ[R] Q`. -/
@[simps!]
noncomputable def algEquiv : S ≃ₐ[R] Q :=
  { ringEquivOfRingEquiv S Q (RingEquiv.refl R) M.map_id with
    commutes' := ringEquivOfRingEquiv_eq _ }
#align is_localization.alg_equiv IsLocalization.algEquiv

end

--Porting note: removed `simp`, `simp` can prove it
theorem algEquiv_mk' (x : R) (y : M) : algEquiv M S Q (mk' S x y) = mk' Q x y :=
  by simp
     -- 🎉 no goals
#align is_localization.alg_equiv_mk' IsLocalization.algEquiv_mk'

--Porting note: removed `simp`, `simp` can prove it
theorem algEquiv_symm_mk' (x : R) (y : M) : (algEquiv M S Q).symm (mk' Q x y) = mk' S x y := by simp
                                                                                                -- 🎉 no goals
#align is_localization.alg_equiv_symm_mk' IsLocalization.algEquiv_symm_mk'

end AlgEquiv

end IsLocalization

section

variable (M) {S}

theorem isLocalization_of_algEquiv [Algebra R P] [IsLocalization M S] (h : S ≃ₐ[R] P) :
    IsLocalization M P := by
  constructor
  · intro y
    -- ⊢ IsUnit (↑(algebraMap R P) ↑y)
    convert (IsLocalization.map_units S y).map h.toAlgHom.toRingHom.toMonoidHom
    -- ⊢ ↑(algebraMap R P) ↑y = ↑↑↑↑h (↑(algebraMap R S) ↑y)
    exact (h.commutes y).symm
    -- 🎉 no goals
  · intro y
    -- ⊢ ∃ x, y * ↑(algebraMap R P) ↑x.snd = ↑(algebraMap R P) x.fst
    obtain ⟨⟨x, s⟩, e⟩ := IsLocalization.surj M (h.symm y)
    -- ⊢ ∃ x, y * ↑(algebraMap R P) ↑x.snd = ↑(algebraMap R P) x.fst
    apply_fun (show S → P from h) at e
    -- ⊢ ∃ x, y * ↑(algebraMap R P) ↑x.snd = ↑(algebraMap R P) x.fst
    simp only [h.map_mul, h.apply_symm_apply, h.commutes] at e
    -- ⊢ ∃ x, y * ↑(algebraMap R P) ↑x.snd = ↑(algebraMap R P) x.fst
    exact ⟨⟨x, s⟩, e⟩
    -- 🎉 no goals
  · intro x y
    -- ⊢ ↑(algebraMap R P) x = ↑(algebraMap R P) y ↔ ∃ c, ↑c * x = ↑c * y
    rw [← h.symm.toEquiv.injective.eq_iff, ← IsLocalization.eq_iff_exists M S, ← h.symm.commutes, ←
      h.symm.commutes]
    rfl
    -- 🎉 no goals
#align is_localization.is_localization_of_alg_equiv IsLocalization.isLocalization_of_algEquiv

theorem isLocalization_iff_of_algEquiv [Algebra R P] (h : S ≃ₐ[R] P) :
    IsLocalization M S ↔ IsLocalization M P :=
  ⟨fun _ => isLocalization_of_algEquiv M h, fun _ => isLocalization_of_algEquiv M h.symm⟩
#align is_localization.is_localization_iff_of_alg_equiv IsLocalization.isLocalization_iff_of_algEquiv

theorem isLocalization_iff_of_ringEquiv (h : S ≃+* P) :
    IsLocalization M S ↔ @IsLocalization _ _ M P _ (h.toRingHom.comp <| algebraMap R S).toAlgebra :=
  letI := (h.toRingHom.comp <| algebraMap R S).toAlgebra
  isLocalization_iff_of_algEquiv M { h with commutes' := fun _ => rfl }
#align is_localization.is_localization_iff_of_ring_equiv IsLocalization.isLocalization_iff_of_ringEquiv

variable (S)

theorem isLocalization_of_base_ringEquiv [IsLocalization M S] (h : R ≃+* P) :
    @IsLocalization _ _ (M.map h.toMonoidHom) S _
      ((algebraMap R S).comp h.symm.toRingHom).toAlgebra := by
  letI : Algebra P S := ((algebraMap R S).comp h.symm.toRingHom).toAlgebra
  -- ⊢ IsLocalization (Submonoid.map (RingEquiv.toMonoidHom h) M) S
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩⟩
    -- ⊢ IsUnit (↑(algebraMap P S) ↑{ val := ↑(RingEquiv.toMonoidHom h) y, property : …
    convert IsLocalization.map_units S ⟨y, hy⟩
    -- ⊢ ↑(algebraMap P S) ↑{ val := ↑(RingEquiv.toMonoidHom h) y, property := (_ : ∃ …
    dsimp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
    -- ⊢ ↑(algebraMap R S) (↑(RingEquiv.toRingHom (RingEquiv.symm h)) (↑(RingEquiv.to …
    exact congr_arg _ (h.symm_apply_apply _)
    -- 🎉 no goals
  · intro y
    -- ⊢ ∃ x, y * ↑(algebraMap P S) ↑x.snd = ↑(algebraMap P S) x.fst
    obtain ⟨⟨x, s⟩, e⟩ := IsLocalization.surj M y
    -- ⊢ ∃ x, y * ↑(algebraMap P S) ↑x.snd = ↑(algebraMap P S) x.fst
    refine' ⟨⟨h x, _, _, s.prop, rfl⟩, _⟩
    -- ⊢ y * ↑(algebraMap P S) ↑(↑h x, { val := ↑(RingEquiv.toMonoidHom h) ↑s, proper …
    dsimp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply] at e ⊢
    -- ⊢ y * ↑(algebraMap R S) (↑(RingEquiv.toRingHom (RingEquiv.symm h)) (↑(RingEqui …
    convert e <;> exact h.symm_apply_apply _
    -- ⊢ ↑(RingEquiv.toRingHom (RingEquiv.symm h)) (↑(RingEquiv.toMonoidHom h) ↑s) = ↑s
                  -- 🎉 no goals
                  -- 🎉 no goals
  · intro x y
    -- ⊢ ↑(algebraMap P S) x = ↑(algebraMap P S) y ↔ ∃ c, ↑c * x = ↑c * y
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, RingHom.comp_apply,
      IsLocalization.eq_iff_exists M S]
    simp_rw [← h.toEquiv.apply_eq_iff_eq]
    -- ⊢ (∃ c, ↑h.toEquiv (↑c * ↑(RingEquiv.toRingHom (RingEquiv.symm h)) x) = ↑h.toE …
    change (∃ c : M, h (c * h.symm x) = h (c * h.symm y)) ↔ _
    -- ⊢ (∃ c, ↑h (↑c * ↑(RingEquiv.symm h) x) = ↑h (↑c * ↑(RingEquiv.symm h) y)) ↔ ∃ …
    simp only [RingEquiv.apply_symm_apply, RingEquiv.map_mul]
    -- ⊢ (∃ c, ↑h ↑c * x = ↑h ↑c * y) ↔ ∃ c, ↑c * x = ↑c * y
    exact
      ⟨fun ⟨c, e⟩ => ⟨⟨_, _, c.prop, rfl⟩, e⟩, fun ⟨⟨_, c, h, e₁⟩, e₂⟩ => ⟨⟨_, h⟩, e₁.symm ▸ e₂⟩⟩
#align is_localization.is_localization_of_base_ring_equiv IsLocalization.isLocalization_of_base_ringEquiv

theorem isLocalization_iff_of_base_ringEquiv (h : R ≃+* P) :
    IsLocalization M S ↔
      @IsLocalization _ _ (M.map h.toMonoidHom) S _
        ((algebraMap R S).comp h.symm.toRingHom).toAlgebra := by
  letI : Algebra P S := ((algebraMap R S).comp h.symm.toRingHom).toAlgebra
  -- ⊢ IsLocalization M S ↔ IsLocalization (Submonoid.map (RingEquiv.toMonoidHom h) …
  refine' ⟨fun _ => isLocalization_of_base_ringEquiv M S h, _⟩
  -- ⊢ IsLocalization (Submonoid.map (RingEquiv.toMonoidHom h) M) S → IsLocalizatio …
  intro H
  -- ⊢ IsLocalization M S
  convert isLocalization_of_base_ringEquiv (Submonoid.map (RingEquiv.toMonoidHom h) M) S h.symm
  -- ⊢ M = Submonoid.map (RingEquiv.toMonoidHom (RingEquiv.symm h)) (Submonoid.map  …
  · erw [Submonoid.map_equiv_eq_comap_symm, Submonoid.comap_map_eq_of_injective]
    -- ⊢ Injective ↑(MulEquiv.toMonoidHom (MulEquiv.symm (RingEquiv.toMulEquiv (RingE …
    exact h.toEquiv.injective
    -- 🎉 no goals
  rw [RingHom.algebraMap_toAlgebra, RingHom.comp_assoc]
  -- ⊢ inst✝¹ = RingHom.toAlgebra (RingHom.comp (algebraMap R S) (RingHom.comp (Rin …
  simp only [RingHom.comp_id, RingEquiv.symm_symm, RingEquiv.symm_toRingHom_comp_toRingHom]
  -- ⊢ inst✝¹ = RingHom.toAlgebra (algebraMap R S)
  apply Algebra.algebra_ext
  -- ⊢ ∀ (r : R), ↑(algebraMap R S) r = ↑(algebraMap R S) r
  intro r
  -- ⊢ ↑(algebraMap R S) r = ↑(algebraMap R S) r
  rw [RingHom.algebraMap_toAlgebra]
  -- 🎉 no goals
#align is_localization.is_localization_iff_of_base_ring_equiv IsLocalization.isLocalization_iff_of_base_ringEquiv

end

variable (M)

theorem nonZeroDivisors_le_comap [IsLocalization M S] :
    nonZeroDivisors R ≤ (nonZeroDivisors S).comap (algebraMap R S) := by
  rintro a ha b (e : b * algebraMap R S a = 0)
  -- ⊢ b = 0
  obtain ⟨x, s, rfl⟩ := mk'_surjective M b
  -- ⊢ mk' S x s = 0
  rw [← @mk'_one R _ M, ← mk'_mul, ← (algebraMap R S).map_zero, ← @mk'_one R _ M,
    IsLocalization.eq] at e
  obtain ⟨c, e⟩ := e
  -- ⊢ mk' S x s = 0
  rw [mul_zero, mul_zero, Submonoid.coe_one, one_mul, ← mul_assoc] at e
  -- ⊢ mk' S x s = 0
  rw [mk'_eq_zero_iff]
  -- ⊢ ∃ m, ↑m * x = 0
  exact ⟨c, ha _ e⟩
  -- 🎉 no goals
#align is_localization.non_zero_divisors_le_comap IsLocalization.nonZeroDivisors_le_comap

theorem map_nonZeroDivisors_le [IsLocalization M S] :
    (nonZeroDivisors R).map (algebraMap R S) ≤ nonZeroDivisors S :=
  Submonoid.map_le_iff_le_comap.mpr (nonZeroDivisors_le_comap M S)
#align is_localization.map_non_zero_divisors_le IsLocalization.map_nonZeroDivisors_le

end IsLocalization

namespace Localization

open IsLocalization

/-! ### Constructing a localization at a given submonoid -/

section

instance instUniqueLocalization [Subsingleton R] : Unique (Localization M) where
  uniq a := show a = mk 1 1 from
    Localization.induction_on a fun _ => by
      congr <;> apply Subsingleton.elim
      -- ⊢ x✝.fst = 1
                -- 🎉 no goals
                -- 🎉 no goals

/-- Addition in a ring localization is defined as `⟨a, b⟩ + ⟨c, d⟩ = ⟨b * c + d * a, b * d⟩`.

Should not be confused with `AddLocalization.add`, which is defined as
`⟨a, b⟩ + ⟨c, d⟩ = ⟨a + c, b + d⟩`.
-/
protected irreducible_def add (z w : Localization M) : Localization M :=
  Localization.liftOn₂ z w (fun a b c d => mk ((b : R) * c + d * a) (b * d))
    @fun a a' b b' c c' d d' h1 h2 =>
    mk_eq_mk_iff.2
      (by
        rw [r_eq_r'] at h1 h2 ⊢
        -- ⊢ ↑(r' M) (↑b * c + ↑d * a, b * d) (↑b' * c' + ↑d' * a', b' * d')
        cases' h1 with t₅ ht₅
        -- ⊢ ↑(r' M) (↑b * c + ↑d * a, b * d) (↑b' * c' + ↑d' * a', b' * d')
        cases' h2 with t₆ ht₆
        -- ⊢ ↑(r' M) (↑b * c + ↑d * a, b * d) (↑b' * c' + ↑d' * a', b' * d')
        use t₅ * t₆
        -- ⊢ ↑(t₅ * t₆) * (↑(↑b' * c' + ↑d' * a', b' * d').snd * (↑b * c + ↑d * a, b * d) …
        dsimp only
        -- ⊢ ↑(t₅ * t₆) * (↑(b' * d') * (↑b * c + ↑d * a)) = ↑(t₅ * t₆) * (↑(b * d) * (↑b …
        calc
          ↑t₅ * ↑t₆ * (↑b' * ↑d' * ((b : R) * c + d * a)) =
              t₆ * (d' * c) * (t₅ * (b' * b)) + t₅ * (b' * a) * (t₆ * (d' * d)) :=
            by ring
          _ = t₅ * t₆ * (b * d * (b' * c' + d' * a')) := by rw [ht₆, ht₅]; ring
          )
#align localization.add Localization.add

instance : Add (Localization M) :=
  ⟨Localization.add⟩

theorem add_mk (a b c d) : (mk a b : Localization M) + mk c d =
    mk ((b : R) * c + (d : R) * a) (b * d) := by
  show Localization.add (mk a b) (mk c d) = mk _ _
  -- ⊢ Localization.add (mk a b) (mk c d) = mk (↑b * c + ↑d * a) (b * d)
  simp [Localization.add_def]
  -- 🎉 no goals
#align localization.add_mk Localization.add_mk

theorem add_mk_self (a b c) : (mk a b : Localization M) + mk c b = mk (a + c) b := by
  rw [add_mk, mk_eq_mk_iff, r_eq_r']
  -- ⊢ ↑(r' M) (↑b * c + ↑b * a, b * b) (a + c, b)
  refine' (r' M).symm ⟨1, _⟩
  -- ⊢ ↑1 * (↑(↑b * c + ↑b * a, b * b).snd * (a + c, b).fst) = ↑1 * (↑(a + c, b).sn …
  simp only [Submonoid.coe_one, Submonoid.coe_mul]
  -- ⊢ 1 * (↑b * ↑b * (a + c)) = 1 * (↑b * (↑b * c + ↑b * a))
  ring
  -- 🎉 no goals
#align localization.add_mk_self Localization.add_mk_self

local macro "localization_tac" : tactic =>
  `(tactic|
   { intros
     simp only [add_mk, Localization.mk_mul, ← Localization.mk_zero 1]
     refine mk_eq_mk_iff.mpr (r_of_eq ?_)
     simp only [Submonoid.coe_mul]
     ring })

instance : CommSemiring (Localization M) :=
  { (show CommMonoidWithZero (Localization M) by infer_instance) with
                                                 -- 🎉 no goals
    add := (· + ·)
    nsmul := (· • ·)
    nsmul_zero := fun x =>
      Localization.induction_on x fun x => by simp only [smul_mk, zero_nsmul, mk_zero]
                                              -- 🎉 no goals
    nsmul_succ := fun n x =>
      Localization.induction_on x fun x => by simp only [smul_mk, succ_nsmul, add_mk_self]
                                              -- 🎉 no goals
    add_assoc := fun m n k =>
            -- 🎉 no goals
      Localization.induction_on₃ m n k
        (by localization_tac)
    zero_add := fun y =>
            -- 🎉 no goals
      Localization.induction_on y
        (by localization_tac)
    add_zero := fun y =>
            -- 🎉 no goals
      Localization.induction_on y
        (by localization_tac)
    add_comm := fun y z =>
      Localization.induction_on₂ z y
        (by localization_tac)
            -- 🎉 no goals
    left_distrib := fun m n k =>
      Localization.induction_on₃ m n k
        (by localization_tac)
            -- 🎉 no goals
    right_distrib := fun m n k =>
      Localization.induction_on₃ m n k
        (by localization_tac) }
            -- 🎉 no goals

/-- For any given denominator `b : M`, the map `a ↦ a / b` is an `AddMonoidHom` from `R` to
  `Localization M`-/
@[simps]
def mkAddMonoidHom (b : M) : R →+ Localization M
    where
  toFun a := mk a b
  map_zero' := mk_zero _
  map_add' _ _ := (add_mk_self _ _ _).symm
#align localization.mk_add_monoid_hom Localization.mkAddMonoidHom

theorem mk_sum {ι : Type*} (f : ι → R) (s : Finset ι) (b : M) :
    mk (∑ i in s, f i) b = ∑ i in s, mk (f i) b :=
  (mkAddMonoidHom b).map_sum f s
#align localization.mk_sum Localization.mk_sum

theorem mk_list_sum (l : List R) (b : M) : mk l.sum b = (l.map fun a => mk a b).sum :=
  (mkAddMonoidHom b).map_list_sum l
#align localization.mk_list_sum Localization.mk_list_sum

theorem mk_multiset_sum (l : Multiset R) (b : M) : mk l.sum b = (l.map fun a => mk a b).sum :=
  (mkAddMonoidHom b).map_multiset_sum l
#align localization.mk_multiset_sum Localization.mk_multiset_sum

instance {S : Type*} [Monoid S] [DistribMulAction S R] [IsScalarTower S R R] :
    DistribMulAction S (Localization M)
    where
  smul_zero s := by simp only [← Localization.mk_zero 1, Localization.smul_mk, smul_zero]
                    -- 🎉 no goals
  smul_add s x y :=
    Localization.induction_on₂ x y <|
      Prod.rec fun r₁ x₁ =>
        Prod.rec fun r₂ x₂ => by
          simp only [Localization.smul_mk, Localization.add_mk, smul_add, mul_comm _ (s • _),
            mul_comm _ r₁, mul_comm _ r₂, smul_mul_assoc]

instance {S : Type*} [Semiring S] [MulSemiringAction S R] [IsScalarTower S R R] :
    MulSemiringAction S (Localization M) :=
  { inferInstanceAs (MulDistribMulAction S (Localization M)),
    inferInstanceAs (DistribMulAction S (Localization M)) with }

instance {S : Type*} [Semiring S] [Module S R] [IsScalarTower S R R] : Module S (Localization M) :=
  { inferInstanceAs (DistribMulAction S (Localization M)) with
    zero_smul :=
      Localization.ind <|
        Prod.rec <| by
          intros
          -- ⊢ 0 • mk (fst✝, snd✝).fst (fst✝, snd✝).snd = 0
          simp only [Localization.smul_mk, zero_smul, mk_zero]
          -- 🎉 no goals
    add_smul := fun s₁ s₂ =>
      Localization.ind <|
          -- ⊢ (s₁ + s₂) • mk (fst✝, snd✝).fst (fst✝, snd✝).snd = s₁ • mk (fst✝, snd✝).fst  …
        Prod.rec <| by
          -- 🎉 no goals
          intros
          simp only [Localization.smul_mk, add_smul, add_mk_self] }

instance algebra {S : Type*} [CommSemiring S] [Algebra S R] : Algebra S (Localization M)
    where
  toRingHom :=
    RingHom.comp
      { Localization.monoidOf M with
        toFun := (monoidOf M).toMap
        map_zero' := by rw [← mk_zero (1 : M), mk_one_eq_monoidOf_mk]
                        -- 🎉 no goals
        map_add' := fun x y => by
          simp only [← mk_one_eq_monoidOf_mk, add_mk, Submonoid.coe_one, one_mul, add_comm] }
          -- 🎉 no goals
      (algebraMap S R)
  smul_def' s :=
    Localization.ind <|
      Prod.rec <| by
        intro r x
        -- ⊢ s • mk (r, x).fst (r, x).snd =
        dsimp
        -- ⊢ s • mk r x = ↑(Submonoid.LocalizationMap.toMap (monoidOf M)) (↑(algebraMap S …
        simp only [← mk_one_eq_monoidOf_mk, mk_mul, Localization.smul_mk, one_mul,
          Algebra.smul_def]
  commutes' s :=
    Localization.ind <|
        -- ⊢ ↑(RingHom.comp
      Prod.rec <| by
        -- ⊢ ↑(Submonoid.LocalizationMap.toMap (monoidOf M)) (↑(algebraMap S R) s) * mk r …
        intro r x
        dsimp
        simp only [← mk_one_eq_monoidOf_mk, mk_mul, Localization.smul_mk, one_mul, mul_one,
          Algebra.commutes]

instance isLocalization : IsLocalization M (Localization M) where
  map_units' := (Localization.monoidOf M).map_units
  surj' := (Localization.monoidOf M).surj
  eq_iff_exists' := (Localization.monoidOf M).eq_iff_exists

end

@[simp]
theorem toLocalizationMap_eq_monoidOf : toLocalizationMap M (Localization M) = monoidOf M :=
  rfl
#align localization.to_localization_map_eq_monoid_of Localization.toLocalizationMap_eq_monoidOf

theorem monoidOf_eq_algebraMap (x) : (monoidOf M).toMap x = algebraMap R (Localization M) x :=
  rfl
#align localization.monoid_of_eq_algebra_map Localization.monoidOf_eq_algebraMap

theorem mk_one_eq_algebraMap (x) : mk x 1 = algebraMap R (Localization M) x :=
  rfl
#align localization.mk_one_eq_algebra_map Localization.mk_one_eq_algebraMap

theorem mk_eq_mk'_apply (x y) : mk x y = IsLocalization.mk' (Localization M) x y := by
  rw [mk_eq_monoidOf_mk'_apply, mk', toLocalizationMap_eq_monoidOf]
  -- 🎉 no goals
#align localization.mk_eq_mk'_apply Localization.mk_eq_mk'_apply

--Porting note: removed `simp`. Left hand side can be simplified; not clear what normal form should
--be.
theorem mk_eq_mk' : (mk : R → M → Localization M) = IsLocalization.mk' (Localization M) :=
  mk_eq_monoidOf_mk'
#align localization.mk_eq_mk' Localization.mk_eq_mk'

theorem mk_algebraMap {A : Type*} [CommSemiring A] [Algebra A R] (m : A) :
    mk (algebraMap A R m) 1 = algebraMap A (Localization M) m := by
  rw [mk_eq_mk', mk'_eq_iff_eq_mul, Submonoid.coe_one, map_one, mul_one]; rfl
  -- ⊢ ↑(algebraMap ((fun x => R) m) (Localization M)) (↑(algebraMap A R) m) = ↑(al …
                                                                          -- 🎉 no goals
#align localization.mk_algebra_map Localization.mk_algebraMap

theorem mk_nat_cast (m : ℕ) : (mk m 1 : Localization M) = m := by
  simpa using @mk_algebraMap R _ M ℕ _ _ m
  -- 🎉 no goals
#align localization.mk_nat_cast Localization.mk_nat_cast

variable [IsLocalization M S]

section

variable (M)

/-- The localization of `R` at `M` as a quotient type is isomorphic to any other localization. -/
@[simps!]
noncomputable def algEquiv : Localization M ≃ₐ[R] S :=
  IsLocalization.algEquiv M _ _
#align localization.alg_equiv Localization.algEquiv

/-- The localization of a singleton is a singleton. Cannot be an instance due to metavariables. -/
noncomputable def _root_.IsLocalization.unique (R Rₘ) [CommSemiring R] [CommSemiring Rₘ]
    (M : Submonoid R) [Subsingleton R] [Algebra R Rₘ] [IsLocalization M Rₘ] : Unique Rₘ :=
  have : Inhabited Rₘ := ⟨1⟩
  (algEquiv M Rₘ).symm.injective.unique
#align is_localization.unique IsLocalization.unique

end

--Porting note: removed `simp`, `simp` can prove it
nonrec theorem algEquiv_mk' (x : R) (y : M) : algEquiv M S (mk' (Localization M) x y) = mk' S x y :=
  algEquiv_mk' _ _
#align localization.alg_equiv_mk' Localization.algEquiv_mk'

--Porting note: removed `simp`, `simp` can prove it
nonrec theorem algEquiv_symm_mk' (x : R) (y : M) :
    (algEquiv M S).symm (mk' S x y) = mk' (Localization M) x y :=
  algEquiv_symm_mk' _ _
#align localization.alg_equiv_symm_mk' Localization.algEquiv_symm_mk'

theorem algEquiv_mk (x y) : algEquiv M S (mk x y) = mk' S x y := by rw [mk_eq_mk', algEquiv_mk']
                                                                    -- 🎉 no goals
#align localization.alg_equiv_mk Localization.algEquiv_mk

theorem algEquiv_symm_mk (x : R) (y : M) : (algEquiv M S).symm (mk' S x y) = mk x y := by
  rw [mk_eq_mk', algEquiv_symm_mk']
  -- 🎉 no goals
#align localization.alg_equiv_symm_mk Localization.algEquiv_symm_mk

end Localization

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] {M : Submonoid R} (S : Type*) [CommRing S]

variable [Algebra R S] {P : Type*} [CommRing P]

namespace Localization

/-- Negation in a ring localization is defined as `-⟨a, b⟩ = ⟨-a, b⟩`. -/
protected irreducible_def neg (z : Localization M) : Localization M :=
  Localization.liftOn z (fun a b => mk (-a) b) @fun a b c d h =>
    mk_eq_mk_iff.2
      (by
        rw [r_eq_r'] at h ⊢
        -- ⊢ ↑(r' M) (-a, c) (-b, d)
        cases' h with t ht
        -- ⊢ ↑(r' M) (-a, c) (-b, d)
        use t
        -- ⊢ ↑t * (↑(-b, d).snd * (-a, c).fst) = ↑t * (↑(-a, c).snd * (-b, d).fst)
        rw [mul_neg, mul_neg, ht]
        -- ⊢ -(↑t * (↑(a, c).snd * (b, d).fst)) = ↑t * (↑(-a, c).snd * (-b, d).fst)
        ring_nf)
        -- 🎉 no goals
#align localization.neg Localization.neg

instance : Neg (Localization M) :=
  ⟨Localization.neg⟩

theorem neg_mk (a b) : -(mk a b : Localization M) = mk (-a) b := by
  show Localization.neg (mk a b) = mk (-a) b
  -- ⊢ Localization.neg (mk a b) = mk (-a) b
  rw [Localization.neg_def]
  -- ⊢ liftOn (mk a b) (fun a b => mk (-a) b) (_ : ∀ (a b : R) (c d : { x // x ∈ M  …
  apply liftOn_mk
  -- 🎉 no goals
#align localization.neg_mk Localization.neg_mk

instance : CommRing (Localization M) :=
  { inferInstanceAs (CommSemiring (Localization M)) with
    zsmul := (· • ·)
    zsmul_zero' := fun x =>
      Localization.induction_on x fun x => by simp only [smul_mk, zero_zsmul, mk_zero]
                                              -- 🎉 no goals
    zsmul_succ' := fun n x =>
      Localization.induction_on x fun x => by
        simp [smul_mk, add_mk_self, -mk_eq_monoidOf_mk', add_comm (n : ℤ) 1, add_smul]
        -- 🎉 no goals
    zsmul_neg' := fun n x =>
      Localization.induction_on x fun x => by
        dsimp only
        -- ⊢ Int.negSucc n • mk x.fst x.snd = -(↑(Nat.succ n) • mk x.fst x.snd)
        rw [smul_mk, smul_mk, neg_mk, ← neg_smul]
        -- ⊢ mk (Int.negSucc n • x.fst) x.snd = mk (-↑(Nat.succ n) • x.fst) x.snd
        rfl
        -- 🎉 no goals
    neg := Neg.neg
    sub := fun x y => x + -y
    sub_eq_add_neg := fun x y => rfl
    add_left_neg := fun y =>
      Localization.induction_on y
        (by
          intros
          -- ⊢ -mk y✝.fst y✝.snd + mk y✝.fst y✝.snd = 0
          simp only [add_mk, Localization.mk_mul, neg_mk, ← mk_zero 1]
          -- ⊢ mk (↑y✝.snd * y✝.fst + ↑y✝.snd * -y✝.fst) (y✝.snd * y✝.snd) = mk 0 1
          refine' mk_eq_mk_iff.mpr (r_of_eq _)
          -- ⊢ ↑(0, 1).snd * (↑y✝.snd * y✝.fst + ↑y✝.snd * -y✝.fst, y✝.snd * y✝.snd).fst =  …
          simp only [Submonoid.coe_mul]
          -- ⊢ ↑1 * (↑y✝.snd * y✝.fst + ↑y✝.snd * -y✝.fst) = ↑y✝.snd * ↑y✝.snd * 0
          ring) }
          -- 🎉 no goals

theorem sub_mk (a c) (b d) : (mk a b : Localization M) - mk c d =
    mk ((d : R) * a - b * c) (b * d) :=
  calc
    mk a b - mk c d = mk a b + -mk c d := sub_eq_add_neg _ _
    _ = mk a b + mk (-c) d := by rw [neg_mk]
                                 -- 🎉 no goals
    _ = mk (b * -c + d * a) (b * d) := (add_mk _ _ _ _)
    _ = mk (d * a - b * c) (b * d) := by congr; ring
                                         -- ⊢ ↑b * -c + ↑d * a = ↑d * a - ↑b * c
                                                -- 🎉 no goals
#align localization.sub_mk Localization.sub_mk

theorem mk_int_cast (m : ℤ) : (mk m 1 : Localization M) = m := by
  simpa using @mk_algebraMap R _ M ℤ _ _ m
  -- 🎉 no goals
#align localization.mk_int_cast Localization.mk_int_cast

end Localization

namespace IsLocalization

variable {K : Type*} [IsLocalization M S]

theorem to_map_eq_zero_iff {x : R} (hM : M ≤ nonZeroDivisors R) : algebraMap R S x = 0 ↔ x = 0 := by
  rw [← (algebraMap R S).map_zero]
  -- ⊢ ↑(algebraMap R S) x = ↑(algebraMap R S) 0 ↔ x = 0
  constructor <;> intro h
  -- ⊢ ↑(algebraMap R S) x = ↑(algebraMap R S) 0 → x = 0
                  -- ⊢ x = 0
                  -- ⊢ ↑(algebraMap R S) x = ↑(algebraMap R S) 0
  · cases' (eq_iff_exists M S).mp h with c hc
    -- ⊢ x = 0
    rw [mul_zero, mul_comm] at hc
    -- ⊢ x = 0
    exact hM c.2 x hc
    -- 🎉 no goals
  · rw [h]
    -- 🎉 no goals
#align is_localization.to_map_eq_zero_iff IsLocalization.to_map_eq_zero_iff

protected theorem injective (hM : M ≤ nonZeroDivisors R) : Injective (algebraMap R S) := by
  rw [injective_iff_map_eq_zero (algebraMap R S)]
  -- ⊢ ∀ (a : R), ↑(algebraMap R S) a = 0 → a = 0
  intro a ha
  -- ⊢ a = 0
  rwa [to_map_eq_zero_iff S hM] at ha
  -- 🎉 no goals
#align is_localization.injective IsLocalization.injective

protected theorem to_map_ne_zero_of_mem_nonZeroDivisors [Nontrivial R] (hM : M ≤ nonZeroDivisors R)
    {x : R} (hx : x ∈ nonZeroDivisors R) : algebraMap R S x ≠ 0 :=
  show (algebraMap R S).toMonoidWithZeroHom x ≠ 0 from
    map_ne_zero_of_mem_nonZeroDivisors (algebraMap R S) (IsLocalization.injective S hM) hx
#align is_localization.to_map_ne_zero_of_mem_non_zero_divisors IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors

variable {S}

theorem sec_snd_ne_zero [Nontrivial R] (hM : M ≤ nonZeroDivisors R) (x : S) :
    ((sec M x).snd : R) ≠ 0 :=
  nonZeroDivisors.coe_ne_zero ⟨(sec M x).snd.val, hM (sec M x).snd.property⟩
#align is_localization.sec_snd_ne_zero IsLocalization.sec_snd_ne_zero

theorem sec_fst_ne_zero [Nontrivial R] [NoZeroDivisors S] (hM : M ≤ nonZeroDivisors R) {x : S}
    (hx : x ≠ 0) : (sec M x).fst ≠ 0 := by
  have hsec := sec_spec M x
  -- ⊢ (sec M x).fst ≠ 0
  intro hfst
  -- ⊢ False
  rw [hfst, map_zero, mul_eq_zero, _root_.map_eq_zero_iff] at hsec
  -- ⊢ False
  · exact Or.elim hsec hx (sec_snd_ne_zero hM x)
    -- 🎉 no goals
  · exact IsLocalization.injective S hM
    -- 🎉 no goals
#align is_localization.sec_fst_ne_zero IsLocalization.sec_fst_ne_zero

variable (S M) (Q : Type*) [CommRing Q] {g : R →+* P} [Algebra P Q]

/-- Injectivity of a map descends to the map induced on localizations. -/
theorem map_injective_of_injective (hg : Function.Injective g)
    [i : IsLocalization (M.map g : Submonoid P) Q] :
    --Porting note: Why does `i` need to be given explicitly?
    Function.Injective (@map _ _ _ _ _ _ _ _ _ _ Q _ _ i g (Submonoid.le_comap_map M) : S → Q) := by
  rw [injective_iff_map_eq_zero]
  -- ⊢ ∀ (a : S), ↑(map Q g (_ : M ≤ Submonoid.comap g (Submonoid.map g M))) a = 0  …
  intro z hz
  -- ⊢ z = 0
  obtain ⟨a, b, rfl⟩ := mk'_surjective M z
  -- ⊢ mk' S a b = 0
  rw [map_mk', mk'_eq_zero_iff] at hz
  -- ⊢ mk' S a b = 0
  obtain ⟨⟨m', hm'⟩, hm⟩ := hz
  -- ⊢ mk' S a b = 0
  rw [Submonoid.mem_map] at hm'
  -- ⊢ mk' S a b = 0
  obtain ⟨n, hn, hnm⟩ := hm'
  -- ⊢ mk' S a b = 0
  rw [Subtype.coe_mk, ← hnm, ← map_mul, ← map_zero g] at hm
  -- ⊢ mk' S a b = 0
  rw [mk'_eq_zero_iff]
  -- ⊢ ∃ m, ↑m * a = 0
  exact ⟨⟨n, hn⟩, hg hm⟩
  -- 🎉 no goals
#align is_localization.map_injective_of_injective IsLocalization.map_injective_of_injective

variable {S Q M}

variable (A : Type*) [CommRing A] [IsDomain A]

/-- A `CommRing` `S` which is the localization of a ring `R` without zero divisors at a subset of
non-zero elements does not have zero divisors.
See note [reducible non-instances]. -/
@[reducible]
theorem noZeroDivisors_of_le_nonZeroDivisors [Algebra A S] {M : Submonoid A} [IsLocalization M S]
    (hM : M ≤ nonZeroDivisors A) : NoZeroDivisors S :=
  {
    eq_zero_or_eq_zero_of_mul_eq_zero := by
      intro z w h
      -- ⊢ z = 0 ∨ w = 0
      cases' surj M z with x hx
      -- ⊢ z = 0 ∨ w = 0
      cases' surj M w with y hy
      -- ⊢ z = 0 ∨ w = 0
      have :
        z * w * algebraMap A S y.2 * algebraMap A S x.2 = algebraMap A S x.1 * algebraMap A S y.1 :=
        by rw [mul_assoc z, hy, ← hx]; ring
      rw [h, zero_mul, zero_mul, ← (algebraMap A S).map_mul] at this
      -- ⊢ z = 0 ∨ w = 0
      cases' eq_zero_or_eq_zero_of_mul_eq_zero ((to_map_eq_zero_iff S hM).mp this.symm) with H H
      -- ⊢ z = 0 ∨ w = 0
      · exact Or.inl (eq_zero_of_fst_eq_zero hx H)
        -- 🎉 no goals
      · exact Or.inr (eq_zero_of_fst_eq_zero hy H) }
        -- 🎉 no goals
#align is_localization.no_zero_divisors_of_le_non_zero_divisors IsLocalization.noZeroDivisors_of_le_nonZeroDivisors

/-- A `CommRing` `S` which is the localization of an integral domain `R` at a subset of
non-zero elements is an integral domain.
See note [reducible non-instances]. -/
@[reducible]
theorem isDomain_of_le_nonZeroDivisors [Algebra A S] {M : Submonoid A} [IsLocalization M S]
    (hM : M ≤ nonZeroDivisors A) : IsDomain S := by
  apply @NoZeroDivisors.to_isDomain _ _ (id _) (id _)
  -- ⊢ Nontrivial S
  · exact
      ⟨⟨(algebraMap A S) 0, (algebraMap A S) 1, fun h =>
          zero_ne_one (IsLocalization.injective S hM h)⟩⟩
  · exact noZeroDivisors_of_le_nonZeroDivisors _ hM
    -- 🎉 no goals
#align is_localization.is_domain_of_le_non_zero_divisors IsLocalization.isDomain_of_le_nonZeroDivisors

variable {A}

/-- The localization of an integral domain to a set of non-zero elements is an integral domain.
See note [reducible non-instances]. -/
@[reducible]
theorem isDomain_localization {M : Submonoid A} (hM : M ≤ nonZeroDivisors A) :
    IsDomain (Localization M) :=
  isDomain_of_le_nonZeroDivisors _ hM
#align is_localization.is_domain_localization IsLocalization.isDomain_localization

end IsLocalization

open IsLocalization

/-- If `R` is a field, then localizing at a submonoid not containing `0` adds no new elements. -/
theorem IsField.localization_map_bijective {R Rₘ : Type*} [CommRing R] [CommRing Rₘ]
    {M : Submonoid R} (hM : (0 : R) ∉ M) (hR : IsField R) [Algebra R Rₘ] [IsLocalization M Rₘ] :
    Function.Bijective (algebraMap R Rₘ) := by
  letI := hR.toField
  -- ⊢ Bijective ↑(algebraMap R Rₘ)
  replace hM := le_nonZeroDivisors_of_noZeroDivisors hM
  -- ⊢ Bijective ↑(algebraMap R Rₘ)
  refine' ⟨IsLocalization.injective _ hM, fun x => _⟩
  -- ⊢ ∃ a, ↑(algebraMap R Rₘ) a = x
  obtain ⟨r, ⟨m, hm⟩, rfl⟩ := mk'_surjective M x
  -- ⊢ ∃ a, ↑(algebraMap R Rₘ) a = mk' Rₘ r { val := m, property := hm }
  obtain ⟨n, hn⟩ := hR.mul_inv_cancel (nonZeroDivisors.ne_zero <| hM hm)
  -- ⊢ ∃ a, ↑(algebraMap R Rₘ) a = mk' Rₘ r { val := m, property := hm }
  exact ⟨r * n, by erw [eq_mk'_iff_mul_eq, ← map_mul, mul_assoc, _root_.mul_comm n, hn, mul_one]⟩
  -- 🎉 no goals
#align is_field.localization_map_bijective IsField.localization_map_bijective

/-- If `R` is a field, then localizing at a submonoid not containing `0` adds no new elements. -/
theorem Field.localization_map_bijective {K Kₘ : Type*} [Field K] [CommRing Kₘ] {M : Submonoid K}
    (hM : (0 : K) ∉ M) [Algebra K Kₘ] [IsLocalization M Kₘ] :
    Function.Bijective (algebraMap K Kₘ) :=
  (Field.toIsField K).localization_map_bijective hM
#align field.localization_map_bijective Field.localization_map_bijective

-- this looks weird due to the `letI` inside the above lemma, but trying to do it the other
-- way round causes issues with defeq of instances, so this is actually easier.
section Algebra

variable {S} {Rₘ Sₘ : Type*} [CommRing Rₘ] [CommRing Sₘ]

variable [Algebra R Rₘ] [IsLocalization M Rₘ]

variable [Algebra S Sₘ] [i : IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]

section

variable (S M)

/-- Definition of the natural algebra induced by the localization of an algebra.
Given an algebra `R → S`, a submonoid `R` of `M`, and a localization `Rₘ` for `M`,
let `Sₘ` be the localization of `S` to the image of `M` under `algebraMap R S`.
Then this is the natural algebra structure on `Rₘ → Sₘ`, such that the entire square commutes,
where `localization_map.map_comp` gives the commutativity of the underlying maps.

This instance can be helpful if you define `Sₘ := Localization (Algebra.algebraMapSubmonoid S M)`,
however we will instead use the hypotheses `[Algebra Rₘ Sₘ] [IsScalarTower R Rₘ Sₘ]` in lemmas
since the algebra structure may arise in different ways.
-/
noncomputable def localizationAlgebra : Algebra Rₘ Sₘ :=
  (map Sₘ (algebraMap R S)
        (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :
      Rₘ →+* Sₘ).toAlgebra
#align localization_algebra localizationAlgebra

end

section

variable [Algebra Rₘ Sₘ] [Algebra R Sₘ] [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]

variable (S Rₘ Sₘ)

theorem IsLocalization.map_units_map_submonoid (y : M) : IsUnit (algebraMap R Sₘ y) := by
  rw [IsScalarTower.algebraMap_apply _ S]
  -- ⊢ IsUnit (↑(algebraMap S Sₘ) (↑(algebraMap R S) ↑y))
  exact IsLocalization.map_units Sₘ ⟨algebraMap R S y, Algebra.mem_algebraMapSubmonoid_of_mem y⟩
  -- 🎉 no goals
#align is_localization.map_units_map_submonoid IsLocalization.map_units_map_submonoid

@[simp]
theorem IsLocalization.algebraMap_mk' (x : R) (y : M) :
    algebraMap Rₘ Sₘ (IsLocalization.mk' Rₘ x y) =
      IsLocalization.mk' Sₘ (algebraMap R S x)
        ⟨algebraMap R S y, Algebra.mem_algebraMapSubmonoid_of_mem y⟩ := by
  rw [IsLocalization.eq_mk'_iff_mul_eq, Subtype.coe_mk, ← IsScalarTower.algebraMap_apply, ←
    IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R Rₘ Sₘ,
    IsScalarTower.algebraMap_apply R Rₘ Sₘ, ← _root_.map_mul, mul_comm,
    IsLocalization.mul_mk'_eq_mk'_of_mul]
  exact congr_arg (algebraMap Rₘ Sₘ) (IsLocalization.mk'_mul_cancel_left x y)
  -- 🎉 no goals
#align is_localization.algebra_map_mk' IsLocalization.algebraMap_mk'

variable (M)

/-- If the square below commutes, the bottom map is uniquely specified:
```
R  →  S
↓     ↓
Rₘ → Sₘ
```
-/
theorem IsLocalization.algebraMap_eq_map_map_submonoid :
    algebraMap Rₘ Sₘ =
      map Sₘ (algebraMap R S)
        (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :=
  Eq.symm <|
    IsLocalization.map_unique _ (algebraMap Rₘ Sₘ) fun x => by
      rw [← IsScalarTower.algebraMap_apply R S Sₘ, ← IsScalarTower.algebraMap_apply R Rₘ Sₘ]
      -- 🎉 no goals
#align is_localization.algebra_map_eq_map_map_submonoid IsLocalization.algebraMap_eq_map_map_submonoid

/-- If the square below commutes, the bottom map is uniquely specified:
```
R  →  S
↓     ↓
Rₘ → Sₘ
```
-/
theorem IsLocalization.algebraMap_apply_eq_map_map_submonoid (x) :
    algebraMap Rₘ Sₘ x =
      map Sₘ (algebraMap R S)
        (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) x :=
  FunLike.congr_fun (IsLocalization.algebraMap_eq_map_map_submonoid _ _ _ _) x
#align is_localization.algebra_map_apply_eq_map_map_submonoid IsLocalization.algebraMap_apply_eq_map_map_submonoid

theorem IsLocalization.lift_algebraMap_eq_algebraMap :
    @IsLocalization.lift R _ M Rₘ _ _ Sₘ _ _ (algebraMap R Sₘ)
        (IsLocalization.map_units_map_submonoid S Sₘ) =
      algebraMap Rₘ Sₘ :=
  IsLocalization.lift_unique _ fun _ => (IsScalarTower.algebraMap_apply _ _ _ _).symm
#align is_localization.lift_algebra_map_eq_algebra_map IsLocalization.lift_algebraMap_eq_algebraMap

end

variable (Rₘ Sₘ)

/-- Injectivity of the underlying `algebraMap` descends to the algebra induced by localization. -/
theorem localizationAlgebra_injective (hRS : Function.Injective (algebraMap R S)) :
    Function.Injective (@algebraMap Rₘ Sₘ _ _ (localizationAlgebra M S)) :=
  --Porting note: I don't understand why `i` needs to be explicit or why writing `(i := i)`
  --doesn't work.
  @IsLocalization.map_injective_of_injective _ _ M Rₘ _ _ _ _ _ Sₘ _ _ _ hRS i
#align localization_algebra_injective localizationAlgebra_injective

end Algebra

end CommRing
