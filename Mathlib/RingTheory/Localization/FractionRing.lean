/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.Localization.Basic

#align_import ring_theory.localization.fraction_ring from "leanprover-community/mathlib"@"831c494092374cfe9f50591ed0ac81a25efc5b86"

/-!
# Fraction ring / fraction field Frac(R) as localization

## Main definitions

 * `IsFractionRing R K` expresses that `K` is a field of fractions of `R`, as an abbreviation of
   `IsLocalization (NonZeroDivisors R) K`

## Main results

 * `IsFractionRing.field`: a definition (not an instance) stating the localization of an integral
   domain `R` at `R \ {0}` is a field
 * `Rat.isFractionRing` is an instance stating `ℚ` is the field of fractions of `ℤ`

## Implementation notes

See `RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


variable (R : Type*) [CommRing R] {M : Submonoid R} (S : Type*) [CommRing S]

variable [Algebra R S] {P : Type*} [CommRing P]

variable {A : Type*} [CommRing A] [IsDomain A] (K : Type*)

-- TODO: should this extend `Algebra` instead of assuming it?
/-- `IsFractionRing R K` states `K` is the field of fractions of an integral domain `R`. -/
abbrev IsFractionRing [CommRing K] [Algebra R K] :=
  IsLocalization (nonZeroDivisors R) K
#align is_fraction_ring IsFractionRing

/-- The cast from `Int` to `Rat` as a `FractionRing`. -/
instance Rat.isFractionRing : IsFractionRing ℤ ℚ where
  map_units' := by
    rintro ⟨x, hx⟩
    -- ⊢ IsUnit (↑(algebraMap ℤ ℚ) ↑{ val := x, property := hx })
    rw [mem_nonZeroDivisors_iff_ne_zero] at hx
    -- ⊢ IsUnit (↑(algebraMap ℤ ℚ) ↑{ val := x, property := hx✝ })
    simpa only [eq_intCast, isUnit_iff_ne_zero, Int.cast_eq_zero, Ne.def, Subtype.coe_mk] using hx
    -- 🎉 no goals
  surj' := by
    rintro ⟨n, d, hd, h⟩
    -- ⊢ ∃ x, mk' n d * ↑(algebraMap ℤ ℚ) ↑x.snd = ↑(algebraMap ℤ ℚ) x.fst
    refine' ⟨⟨n, ⟨d, _⟩⟩, Rat.mul_den_eq_num⟩
    -- ⊢ ↑d ∈ nonZeroDivisors ℤ
    rw [mem_nonZeroDivisors_iff_ne_zero, Int.coe_nat_ne_zero_iff_pos]
    -- ⊢ 0 < d
    exact Nat.zero_lt_of_ne_zero hd
    -- 🎉 no goals
  eq_iff_exists' := by
    intro x y
    -- ⊢ ↑(algebraMap ℤ ℚ) x = ↑(algebraMap ℤ ℚ) y ↔ ∃ c, ↑c * x = ↑c * y
    rw [eq_intCast, eq_intCast, Int.cast_inj]
    -- ⊢ x = y ↔ ∃ c, ↑c * x = ↑c * y
    apply Iff.intro
    -- ⊢ x = y → ∃ c, ↑c * x = ↑c * y
    · rintro rfl
      -- ⊢ ∃ c, ↑c * x = ↑c * x
      use 1
      -- 🎉 no goals
    · rintro ⟨⟨c, hc⟩, h⟩
      -- ⊢ x = y
      apply mul_left_cancel₀ _ h
      -- ⊢ ↑{ val := c, property := hc } ≠ 0
      rwa [mem_nonZeroDivisors_iff_ne_zero] at hc
      -- 🎉 no goals
#align rat.is_fraction_ring Rat.isFractionRing

namespace IsFractionRing

open IsLocalization

variable {R K}

section CommRing

variable [CommRing K] [Algebra R K] [IsFractionRing R K] [Algebra A K] [IsFractionRing A K]

theorem to_map_eq_zero_iff {x : R} : algebraMap R K x = 0 ↔ x = 0 :=
  IsLocalization.to_map_eq_zero_iff _ le_rfl
#align is_fraction_ring.to_map_eq_zero_iff IsFractionRing.to_map_eq_zero_iff

variable (R K)

protected theorem injective : Function.Injective (algebraMap R K) :=
  IsLocalization.injective _ (le_of_eq rfl)
#align is_fraction_ring.injective IsFractionRing.injective

variable {R K}

@[norm_cast, simp]
-- Porting note: using `↑` didn't work, so I needed to explicitly put in the cast myself
theorem coe_inj {a b : R} : (Algebra.cast a : K) = Algebra.cast b ↔ a = b :=
  (IsFractionRing.injective R K).eq_iff
#align is_fraction_ring.coe_inj IsFractionRing.coe_inj

instance (priority := 100) [NoZeroDivisors K] : NoZeroSMulDivisors R K :=
  NoZeroSMulDivisors.of_algebraMap_injective <| IsFractionRing.injective R K

protected theorem to_map_ne_zero_of_mem_nonZeroDivisors [Nontrivial R] {x : R}
    (hx : x ∈ nonZeroDivisors R) : algebraMap R K x ≠ 0 :=
  IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _ le_rfl hx
#align is_fraction_ring.to_map_ne_zero_of_mem_non_zero_divisors IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors

variable (A)

/-- A `CommRing` `K` which is the localization of an integral domain `R` at `R - {0}` is an
integral domain. -/
protected theorem isDomain : IsDomain K :=
  isDomain_of_le_nonZeroDivisors _ (le_refl (nonZeroDivisors A))
#align is_fraction_ring.is_domain IsFractionRing.isDomain

/-- The inverse of an element in the field of fractions of an integral domain. -/
protected noncomputable irreducible_def inv (z : K) : K := open Classical in
  if h : z = 0 then 0
  else
    mk' K ↑(sec (nonZeroDivisors A) z).2
      ⟨(sec _ z).1,
        mem_nonZeroDivisors_iff_ne_zero.2 fun h0 =>
          h <| eq_zero_of_fst_eq_zero (sec_spec (nonZeroDivisors A) z) h0⟩
#align is_fraction_ring.inv IsFractionRing.inv

protected theorem mul_inv_cancel (x : K) (hx : x ≠ 0) : x * IsFractionRing.inv A x = 1 := by
  rw [IsFractionRing.inv, dif_neg hx, ←
    IsUnit.mul_left_inj
      (map_units K
        ⟨(sec _ x).1,
          mem_nonZeroDivisors_iff_ne_zero.2 fun h0 =>
            hx <| eq_zero_of_fst_eq_zero (sec_spec (nonZeroDivisors A) x) h0⟩),
    one_mul, mul_assoc]
  rw [mk'_spec, ← eq_mk'_iff_mul_eq]
  -- ⊢ x = mk' ((fun x => K) ↑{ val := (sec (nonZeroDivisors A) x).fst, property := …
  exact (mk'_sec _ x).symm
  -- 🎉 no goals
#align is_fraction_ring.mul_inv_cancel IsFractionRing.mul_inv_cancel

/-- A `CommRing` `K` which is the localization of an integral domain `R` at `R - {0}` is a field.
See note [reducible non-instances]. -/
@[reducible]
noncomputable def toField : Field K :=
  { IsFractionRing.isDomain A, inferInstanceAs (CommRing K) with
    inv := IsFractionRing.inv A
    mul_inv_cancel := IsFractionRing.mul_inv_cancel A
    inv_zero := by
      change IsFractionRing.inv A (0 : K) = 0
      -- ⊢ IsFractionRing.inv A 0 = 0
      rw [IsFractionRing.inv]
      -- ⊢ (if h : 0 = 0 then 0 else mk' K ↑(sec (nonZeroDivisors A) 0).snd { val := (s …
      exact dif_pos rfl }
      -- 🎉 no goals
#align is_fraction_ring.to_field IsFractionRing.toField

end CommRing

variable {B : Type*} [CommRing B] [IsDomain B] [Field K] {L : Type*} [Field L] [Algebra A K]
  [IsFractionRing A K] {g : A →+* L}

theorem mk'_mk_eq_div {r s} (hs : s ∈ nonZeroDivisors A) :
    mk' K r ⟨s, hs⟩ = algebraMap A K r / algebraMap A K s :=
  mk'_eq_iff_eq_mul.2 <|
    (div_mul_cancel (algebraMap A K r)
        (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs)).symm
#align is_fraction_ring.mk'_mk_eq_div IsFractionRing.mk'_mk_eq_div

@[simp]
theorem mk'_eq_div {r} (s : nonZeroDivisors A) : mk' K r s = algebraMap A K r / algebraMap A K s :=
  mk'_mk_eq_div s.2
#align is_fraction_ring.mk'_eq_div IsFractionRing.mk'_eq_div

theorem div_surjective (z : K) :
    ∃ (x y : A) (hy : y ∈ nonZeroDivisors A), algebraMap _ _ x / algebraMap _ _ y = z :=
  let ⟨x, ⟨y, hy⟩, h⟩ := mk'_surjective (nonZeroDivisors A) z
  ⟨x, y, hy, by rwa [mk'_eq_div] at h⟩
                -- 🎉 no goals
#align is_fraction_ring.div_surjective IsFractionRing.div_surjective

theorem isUnit_map_of_injective (hg : Function.Injective g) (y : nonZeroDivisors A) :
    IsUnit (g y) :=
  IsUnit.mk0 (g y) <|
    show g.toMonoidWithZeroHom y ≠ 0 from map_ne_zero_of_mem_nonZeroDivisors g hg y.2
#align is_fraction_ring.is_unit_map_of_injective IsFractionRing.isUnit_map_of_injective

@[simp]
theorem mk'_eq_zero_iff_eq_zero [Algebra R K] [IsFractionRing R K] {x : R} {y : nonZeroDivisors R} :
    mk' K x y = 0 ↔ x = 0 := by
  refine' ⟨fun hxy => _, fun h => by rw [h, mk'_zero]⟩
  -- ⊢ x = 0
  · simp_rw [mk'_eq_zero_iff, mul_left_coe_nonZeroDivisors_eq_zero_iff] at hxy
    -- ⊢ x = 0
    exact (exists_const _).mp hxy
    -- 🎉 no goals
#align is_fraction_ring.mk'_eq_zero_iff_eq_zero IsFractionRing.mk'_eq_zero_iff_eq_zero

theorem mk'_eq_one_iff_eq {x : A} {y : nonZeroDivisors A} : mk' K x y = 1 ↔ x = y := by
  refine' ⟨_, fun hxy => by rw [hxy, mk'_self']⟩
  -- ⊢ mk' K x y = 1 → x = ↑y
  · intro hxy
    -- ⊢ x = ↑y
    have hy : (algebraMap A K) ↑y ≠ (0 : K) :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.property
    rw [IsFractionRing.mk'_eq_div, div_eq_one_iff_eq hy] at hxy
    -- ⊢ x = ↑y
    exact IsFractionRing.injective A K hxy
    -- 🎉 no goals
#align is_fraction_ring.mk'_eq_one_iff_eq IsFractionRing.mk'_eq_one_iff_eq

open Function

/-- Given an integral domain `A` with field of fractions `K`,
and an injective ring hom `g : A →+* L` where `L` is a field, we get a
field hom sending `z : K` to `g x * (g y)⁻¹`, where `(x, y) : A × (NonZeroDivisors A)` are
such that `z = f x * (f y)⁻¹`. -/
noncomputable def lift (hg : Injective g) : K →+* L :=
  IsLocalization.lift fun y : nonZeroDivisors A => isUnit_map_of_injective hg y
#align is_fraction_ring.lift IsFractionRing.lift

/-- Given an integral domain `A` with field of fractions `K`,
and an injective ring hom `g : A →+* L` where `L` is a field,
the field hom induced from `K` to `L` maps `x` to `g x` for all
`x : A`. -/
@[simp]
theorem lift_algebraMap (hg : Injective g) (x) : lift hg (algebraMap A K x) = g x :=
  lift_eq _ _
#align is_fraction_ring.lift_algebra_map IsFractionRing.lift_algebraMap

/-- Given an integral domain `A` with field of fractions `K`,
and an injective ring hom `g : A →+* L` where `L` is a field,
field hom induced from `K` to `L` maps `f x / f y` to `g x / g y` for all
`x : A, y ∈ NonZeroDivisors A`. -/
theorem lift_mk' (hg : Injective g) (x) (y : nonZeroDivisors A) : lift hg (mk' K x y) = g x / g y :=
  by simp only [mk'_eq_div, map_div₀, lift_algebraMap]
     -- 🎉 no goals
#align is_fraction_ring.lift_mk' IsFractionRing.lift_mk'

/-- Given integral domains `A, B` with fields of fractions `K`, `L`
and an injective ring hom `j : A →+* B`, we get a field hom
sending `z : K` to `g (j x) * (g (j y))⁻¹`, where `(x, y) : A × (NonZeroDivisors A)` are
such that `z = f x * (f y)⁻¹`. -/
noncomputable def map {A B K L : Type*} [CommRing A] [CommRing B] [IsDomain B] [CommRing K]
    [Algebra A K] [IsFractionRing A K] [CommRing L] [Algebra B L] [IsFractionRing B L] {j : A →+* B}
    (hj : Injective j) : K →+* L :=
  IsLocalization.map L j
    (show nonZeroDivisors A ≤ (nonZeroDivisors B).comap j from
      nonZeroDivisors_le_comap_nonZeroDivisors_of_injective j hj)
#align is_fraction_ring.map IsFractionRing.map

/-- Given integral domains `A, B` and localization maps to their fields of fractions
`f : A →+* K, g : B →+* L`, an isomorphism `j : A ≃+* B` induces an isomorphism of
fields of fractions `K ≃+* L`. -/
noncomputable def fieldEquivOfRingEquiv [Algebra B L] [IsFractionRing B L] (h : A ≃+* B) :
    K ≃+* L :=
  ringEquivOfRingEquiv K L h
    (by
      ext b
      -- ⊢ b ∈ Submonoid.map (RingEquiv.toMonoidHom h) (?m.392285 h) ↔ b ∈ ?m.392287 h
      show b ∈ h.toEquiv '' _ ↔ _
      -- ⊢ b ∈ ↑h.toEquiv '' ↑(?m.392285 h) ↔ b ∈ ?m.392287 h
      erw [h.toEquiv.image_eq_preimage, Set.preimage, Set.mem_setOf_eq,
        mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero]
      exact h.symm.map_ne_zero_iff)
      -- 🎉 no goals
#align is_fraction_ring.field_equiv_of_ring_equiv IsFractionRing.fieldEquivOfRingEquiv

theorem isFractionRing_iff_of_base_ringEquiv (h : R ≃+* P) :
    IsFractionRing R S ↔
      @IsFractionRing P _ S _ ((algebraMap R S).comp h.symm.toRingHom).toAlgebra := by
  delta IsFractionRing
  -- ⊢ IsLocalization (nonZeroDivisors R) S ↔ IsLocalization (nonZeroDivisors P) S
  convert isLocalization_iff_of_base_ringEquiv (nonZeroDivisors R) S h
  -- ⊢ nonZeroDivisors P = Submonoid.map (RingEquiv.toMonoidHom h) (nonZeroDivisors …
  ext x
  -- ⊢ x ∈ nonZeroDivisors P ↔ x ∈ Submonoid.map (RingEquiv.toMonoidHom h) (nonZero …
  erw [Submonoid.map_equiv_eq_comap_symm]
  -- ⊢ x ∈ nonZeroDivisors P ↔ x ∈ Submonoid.comap (MulEquiv.toMonoidHom (MulEquiv. …
  simp only [MulEquiv.coe_toMonoidHom, RingEquiv.toMulEquiv_eq_coe, Submonoid.mem_comap]
  -- ⊢ x ∈ nonZeroDivisors P ↔ ↑(MulEquiv.symm ↑h) x ∈ nonZeroDivisors R
  constructor
  -- ⊢ x ∈ nonZeroDivisors P → ↑(MulEquiv.symm ↑h) x ∈ nonZeroDivisors R
  · rintro hx z (hz : z * h.symm x = 0)
    -- ⊢ z = 0
    rw [← h.map_eq_zero_iff]
    -- ⊢ ↑h z = 0
    apply hx
    -- ⊢ ↑h z * x = 0
    simpa only [h.map_zero, h.apply_symm_apply, h.map_mul] using congr_arg h hz
    -- 🎉 no goals
  · rintro (hx : h.symm x ∈ _) z hz
    -- ⊢ z = 0
    rw [← h.symm.map_eq_zero_iff]
    -- ⊢ ↑(RingEquiv.symm h) z = 0
    apply hx
    -- ⊢ ↑(RingEquiv.symm h) z * ↑(RingEquiv.symm h) x = 0
    rw [← h.symm.map_mul, hz, h.symm.map_zero]
    -- 🎉 no goals
#align is_fraction_ring.is_fraction_ring_iff_of_base_ring_equiv IsFractionRing.isFractionRing_iff_of_base_ringEquiv

protected theorem nontrivial (R S : Type*) [CommRing R] [Nontrivial R] [CommRing S] [Algebra R S]
    [IsFractionRing R S] : Nontrivial S := by
  apply nontrivial_of_ne
  intro h
  apply @zero_ne_one R
  exact
    IsLocalization.injective S (le_of_eq rfl)
      (((algebraMap R S).map_zero.trans h).trans (algebraMap R S).map_one.symm)
#align is_fraction_ring.nontrivial IsFractionRing.nontrivial

end IsFractionRing

variable (A)

/-- The fraction ring of a commutative ring `R` as a quotient type.

We instantiate this definition as generally as possible, and assume that the
commutative ring `R` is an integral domain only when this is needed for proving.

In this generality, this construction is also known as the *total fraction ring* of `R`.
-/
@[reducible]
def FractionRing :=
  Localization (nonZeroDivisors R)
#align fraction_ring FractionRing

namespace FractionRing

instance unique [Subsingleton R] : Unique (FractionRing R) :=
  Localization.instUniqueLocalization
#align fraction_ring.unique FractionRing.unique

instance [Nontrivial R] : Nontrivial (FractionRing R) :=
  ⟨⟨(algebraMap R _) 0, (algebraMap _ _) 1, fun H =>
      zero_ne_one (IsLocalization.injective _ le_rfl H)⟩⟩

/-- Porting note: if the fields of this instance are explicitly defined as they were
in mathlib3, the last instance in this file suffers a TC timeout -/
noncomputable instance field : Field (FractionRing A) := IsFractionRing.toField A

@[simp]
theorem mk_eq_div {r s} :
    (Localization.mk r s : FractionRing A) =
      (algebraMap _ _ r / algebraMap A _ s : FractionRing A) :=
  by rw [Localization.mk_eq_mk', IsFractionRing.mk'_eq_div]
     -- 🎉 no goals
#align fraction_ring.mk_eq_div FractionRing.mk_eq_div

noncomputable instance [IsDomain R] [Field K] [Algebra R K] [NoZeroSMulDivisors R K] :
    Algebra (FractionRing R) K :=
  RingHom.toAlgebra (IsFractionRing.lift (NoZeroSMulDivisors.algebraMap_injective R _))

-- Porting note: had to fill in the `_` by hand for this instance
instance [IsDomain R] [Field K] [Algebra R K] [NoZeroSMulDivisors R K] :
    IsScalarTower R (FractionRing R) K :=
  IsScalarTower.of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap (NoZeroSMulDivisors.algebraMap_injective R K ) x).symm

/-- Given an integral domain `A` and a localization map to a field of fractions
`f : A →+* K`, we get an `A`-isomorphism between the field of fractions of `A` as a quotient
type and `K`. -/
noncomputable def algEquiv (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] :
    FractionRing A ≃ₐ[A] K :=
  Localization.algEquiv (nonZeroDivisors A) K
#align fraction_ring.alg_equiv FractionRing.algEquiv

instance [Algebra R A] [NoZeroSMulDivisors R A] : NoZeroSMulDivisors R (FractionRing A) := by
  apply NoZeroSMulDivisors.of_algebraMap_injective
  -- ⊢ Function.Injective ↑(algebraMap R (FractionRing A))
  rw [IsScalarTower.algebraMap_eq R A]
  -- ⊢ Function.Injective ↑(RingHom.comp (algebraMap A (FractionRing A)) (algebraMa …
  apply Function.Injective.comp (NoZeroSMulDivisors.algebraMap_injective A (FractionRing A))
    (NoZeroSMulDivisors.algebraMap_injective R A)

end FractionRing
