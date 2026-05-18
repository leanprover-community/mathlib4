/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.Algebra.Field.Equiv
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Submonoid
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.SimpleRing.Basic

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

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

@[expose] public section

assert_not_exists Ideal

open nonZeroDivisors

variable (R : Type*) [CommRing R] {M : Submonoid R} (S : Type*) [CommRing S]
variable [Algebra R S] {P : Type*} [CommRing P]
variable {A : Type*} [CommRing A] (K : Type*)

-- TODO: should this extend `Algebra` instead of assuming it?
-- TODO: this was recently generalized from `CommRing` to `CommSemiring`, but all lemmas below are
-- still stated for `CommRing`. Generalize these lemmas where it is appropriate.
/-- `IsFractionRing R K` states `K` is the ring of fractions of a commutative ring `R`. -/
abbrev IsFractionRing (R : Type*) [CommSemiring R] (K : Type*) [CommSemiring K] [Algebra R K] :=
  IsLocalization (nonZeroDivisors R) K

instance {R : Type*} [Field R] : IsFractionRing R R :=
  IsLocalization.of_le_isUnit fun _ ↦ isUnit_of_mem_nonZeroDivisors

theorem IsFractionRing.of_algEquiv {R : Type*} [CommSemiring R] {K L : Type*}
    [CommSemiring K] [Algebra R K] [CommSemiring L] [Algebra R L] [h : IsFractionRing R K]
    (e : K ≃ₐ[R] L) :
    IsFractionRing R L := IsLocalization.isLocalization_of_algEquiv _ e

/-- The cast from `Int` to `Rat` as a `FractionRing`. -/
instance Rat.isFractionRing : IsFractionRing ℤ ℚ where
  map_units := by
    rintro ⟨x, hx⟩
    rw [mem_nonZeroDivisors_iff_ne_zero] at hx
    simpa only [eq_intCast, isUnit_iff_ne_zero, Int.cast_eq_zero, Ne, Subtype.coe_mk] using hx
  surj := by
    rintro ⟨n, d, hd, h⟩
    refine ⟨⟨n, ⟨d, ?_⟩⟩, Rat.mul_den_eq_num _⟩
    rw [mem_nonZeroDivisors_iff_ne_zero, Int.natCast_ne_zero_iff_pos]
    exact Nat.zero_lt_of_ne_zero hd
  exists_of_eq {x y} := by
    rw [eq_intCast, eq_intCast, Int.cast_inj]
    rintro rfl
    use 1

/-- As a corollary, `Rat` is also a localization at only positive integers. -/
instance : IsLocalization (Submonoid.pos ℤ) ℚ where
  map_units y := by simpa using y.prop.ne'
  surj z := by
    obtain ⟨⟨x1, x2⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors ℤ) z
    obtain hx2 | hx2 := lt_or_gt_of_ne (show x2.val ≠ 0 by simp)
    · exact ⟨⟨-x1, ⟨-x2.val, by simpa using hx2⟩⟩, by simpa using hx⟩
    · exact ⟨⟨x1, ⟨x2.val, hx2⟩⟩, hx⟩
  exists_of_eq {x y} h := ⟨1, by simpa using Rat.intCast_inj.mp h⟩

/-- `NNRat` is the ring of fractions of `Nat`. -/
instance NNRat.isFractionRing : IsFractionRing ℕ ℚ≥0 where
  map_units y := by simp
  surj z := ⟨⟨z.num, ⟨z.den, by simp⟩⟩, by simp⟩
  exists_of_eq {x y} h := ⟨1, by simpa using h⟩

namespace IsFractionRing

open IsLocalization

theorem of_field [Field K] [Algebra R K] [FaithfulSMul R K]
    (surj : ∀ z : K, ∃ x y, z = algebraMap R K x / algebraMap R K y) :
    IsFractionRing R K :=
  have inj := FaithfulSMul.algebraMap_injective R K
  have := inj.noZeroDivisors _ (map_zero _) (map_mul _)
  have := Module.nontrivial R K
{ map_units x :=
    .mk0 _ <| (map_ne_zero_iff _ inj).mpr <| mem_nonZeroDivisors_iff_ne_zero.mp x.2
  surj z := by
    have ⟨x, y, eq⟩ := surj z
    obtain rfl | hy := eq_or_ne y 0
    · obtain rfl : z = 0 := by simpa using eq
      exact ⟨(0, 1), by simp⟩
    exact ⟨⟨x, y, mem_nonZeroDivisors_iff_ne_zero.mpr hy⟩,
      (eq_div_iff_mul_eq <| (map_ne_zero_iff _ inj).mpr hy).mp eq⟩
  exists_of_eq eq := ⟨1, by simpa using inj eq⟩ }

variable {R K}

section CommSemiring

theorem of_ringEquiv_left {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]
    {K : Type*} [CommSemiring K] [Algebra R K] (e : R ≃+* S) [Algebra S K]
    (h : ∀ x, algebraMap R K x = algebraMap S K (e x)) [IsFractionRing S K] :
    IsFractionRing R K := IsLocalization.of_ringEquiv_left e (MulEquivClass.map_nonZeroDivisors e) h

end CommSemiring

section CommRing

variable [CommRing K] [Algebra R K] [IsFractionRing R K] [Algebra A K] [IsFractionRing A K]

theorem to_map_eq_zero_iff {x : R} : algebraMap R K x = 0 ↔ x = 0 :=
  IsLocalization.to_map_eq_zero_iff _ le_rfl

variable (R K)

protected theorem injective : Function.Injective (algebraMap R K) :=
  IsLocalization.injective _ (le_of_eq rfl)

include R in
theorem nonZeroDivisors_eq_isUnit : K⁰ = IsUnit.submonoid K := by
  refine le_antisymm (fun x hx ↦ ?_) (isUnit_le_nonZeroDivisors K)
  have ⟨r, eq⟩ := surj R⁰ x
  let r' : R⁰ := ⟨r.1, mem_nonZeroDivisors_of_injective (IsFractionRing.injective R K)
    (eq ▸ mul_mem hx (map_units ..).mem_nonZeroDivisors)⟩
  exact isUnit_of_mul_isUnit_left <| eq ▸ map_units K r'

include R in
/-- If `L` is a fraction ring of `K` which is a fraction ring of `R`,
the `K`-algebra homomorphism from `K` to `L` is an isomorphism. -/
noncomputable def algEquiv (L) [CommRing L] [Algebra K L] [IsFractionRing K L] : K ≃ₐ[K] L :=
  atUnits K _ (nonZeroDivisors_eq_isUnit R K).le

include R in
theorem idem : IsFractionRing K K := IsLocalization.self (nonZeroDivisors_eq_isUnit R K).le

/-- Taking fraction ring is idempotent: a fraction ring of a fraction ring of `R` is
itself a fraction ring of `R`. -/
theorem trans (L) [CommRing L] [Algebra K L] [IsFractionRing K L] [Algebra R L]
    [IsScalarTower R K L] : IsFractionRing R L :=
  isLocalization_of_algEquiv _ <| (algEquiv R K L).restrictScalars R

instance (priority := 100) : FaithfulSMul R K :=
  (faithfulSMul_iff_algebraMap_injective R K).mpr <| IsFractionRing.injective R K

variable {R}

theorem self_iff_nonZeroDivisors_eq_isUnit : IsFractionRing R R ↔ R⁰ = IsUnit.submonoid R where
  mp _ := nonZeroDivisors_eq_isUnit R R
  mpr h := IsLocalization.self h.le

theorem self_iff_nonZeroDivisors_le_isUnit : IsFractionRing R R ↔ R⁰ ≤ IsUnit.submonoid R := by
  rw [self_iff_nonZeroDivisors_eq_isUnit, le_antisymm_iff,
    and_iff_left (isUnit_le_nonZeroDivisors R)]

theorem self_iff_bijective : IsFractionRing R R ↔ Function.Bijective (algebraMap R K) where
  mp h := (atUnits R _ <| self_iff_nonZeroDivisors_le_isUnit.mp h).bijective
  mpr h := isLocalization_of_algEquiv _ (AlgEquiv.ofBijective (Algebra.ofId R K) h).symm

theorem self_iff_surjective : IsFractionRing R R ↔ Function.Surjective (algebraMap R K) := by
  rw [self_iff_bijective K, Function.Bijective, and_iff_right (IsFractionRing.injective R K)]

variable {K}

open algebraMap in
@[norm_cast]
theorem coe_inj {a b : R} : (↑a : K) = ↑b ↔ a = b :=
  algebraMap.coe_inj _ _

protected theorem to_map_ne_zero_of_mem_nonZeroDivisors [Nontrivial R] {x : R}
    (hx : x ∈ nonZeroDivisors R) : algebraMap R K x ≠ 0 :=
  IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _ le_rfl hx

variable (A) [IsDomain A]

include A in
/-- A `CommRing` `K` which is the localization of an integral domain `R` at `R - {0}` is an
integral domain. -/
protected theorem isDomain : IsDomain K :=
  isDomain_of_le_nonZeroDivisors _ (le_refl (nonZeroDivisors A))

/-- The inverse of an element in the field of fractions of an integral domain. -/
protected noncomputable irreducible_def inv (z : K) : K := open scoped Classical in
  if h : z = 0 then 0
  else
    mk' K ↑(sec (nonZeroDivisors A) z).2
      ⟨(sec _ z).1,
        mem_nonZeroDivisors_iff_ne_zero.2 fun h0 =>
          h <| eq_zero_of_fst_eq_zero (sec_spec (nonZeroDivisors A) z) h0⟩

protected theorem mul_inv_cancel (x : K) (hx : x ≠ 0) : x * IsFractionRing.inv A x = 1 := by
  rw [IsFractionRing.inv, dif_neg hx, ←
    IsUnit.mul_left_inj
      (map_units K
        ⟨(sec _ x).1,
          mem_nonZeroDivisors_iff_ne_zero.2 fun h0 =>
            hx <| eq_zero_of_fst_eq_zero (sec_spec (nonZeroDivisors A) x) h0⟩),
    one_mul, mul_assoc]
  rw [mk'_spec, ← eq_mk'_iff_mul_eq]
  exact (mk'_sec _ x).symm

/-- A `CommRing` `K` which is the localization of an integral domain `R` at `R - {0}` is a field.
See note [reducible non-instances]. -/
@[stacks 09FJ]
noncomputable abbrev toField : Field K where
  __ := IsFractionRing.isDomain A
  inv := IsFractionRing.inv A
  mul_inv_cancel := IsFractionRing.mul_inv_cancel A
  inv_zero := show IsFractionRing.inv A (0 : K) = 0 by rw [IsFractionRing.inv]; exact dif_pos rfl
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

lemma surjective_iff_isField [IsDomain R] : Function.Surjective (algebraMap R K) ↔ IsField R where
  mp h := (RingEquiv.ofBijective (algebraMap R K)
      ⟨IsFractionRing.injective R K, h⟩).toMulEquiv.isField (IsFractionRing.toField R).toIsField
  mpr h :=
    letI := h.toField
    (IsLocalization.atUnits R _ (S := K)
      (fun _ hx ↦ Ne.isUnit (mem_nonZeroDivisors_iff_ne_zero.mp hx))).surjective

end CommRing

variable {B : Type*} [CommRing B] [IsDomain B] [Field K] {L : Type*} [Field L] [Algebra A K]
  [IsFractionRing A K] {g : A →+* L}

theorem mk'_mk_eq_div {r s} (hs : s ∈ nonZeroDivisors A) :
    mk' K r ⟨s, hs⟩ = algebraMap A K r / algebraMap A K s :=
  haveI := (algebraMap A K).domain_nontrivial
  mk'_eq_iff_eq_mul.2 <|
    (div_mul_cancel₀ (algebraMap A K r)
        (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs)).symm

@[simp]
theorem mk'_eq_div {r} (s : nonZeroDivisors A) : mk' K r s = algebraMap A K r / algebraMap A K s :=
  mk'_mk_eq_div s.2

variable (A) in
theorem div_surjective (z : K) :
    ∃ x y : A, y ∈ nonZeroDivisors A ∧ algebraMap _ _ x / algebraMap _ _ y = z :=
  let ⟨x, ⟨y, hy⟩, h⟩ := exists_mk'_eq (nonZeroDivisors A) z
  ⟨x, y, hy, by rwa [mk'_eq_div] at h⟩

theorem isUnit_map_of_injective (hg : Function.Injective g) (y : nonZeroDivisors A) :
    IsUnit (g y) :=
  haveI := g.domain_nontrivial
  IsUnit.mk0 (g y) <|
    show g.toMonoidWithZeroHom y ≠ 0 from map_ne_zero_of_mem_nonZeroDivisors g hg y.2

theorem mk'_eq_zero_iff_eq_zero [Algebra R K] [IsFractionRing R K] {x : R} {y : nonZeroDivisors R} :
    mk' K x y = 0 ↔ x = 0 := by
  haveI := (algebraMap R K).domain_nontrivial
  simp [nonZeroDivisors.ne_zero]

theorem mk'_eq_one_iff_eq {x : A} {y : nonZeroDivisors A} : mk' K x y = 1 ↔ x = y := by
  haveI := (algebraMap A K).domain_nontrivial
  refine ⟨?_, fun hxy => by rw [hxy, mk'_self']⟩
  intro hxy
  have hy : (algebraMap A K) ↑y ≠ (0 : K) :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.property
  rw [IsFractionRing.mk'_eq_div, div_eq_one_iff_eq hy] at hxy
  exact IsFractionRing.injective A K hxy

section commutes

variable [Algebra A B] {K₁ K₂ : Type*} [Field K₁] [Field K₂] [Algebra A K₁] [Algebra A K₂]
  [IsFractionRing A K₁] {L₁ L₂ : Type*} [Field L₁] [Field L₂] [Algebra B L₁] [Algebra B L₂]
  [Algebra K₁ L₁] [Algebra K₂ L₂] [Algebra A L₁] [Algebra A L₂] [IsScalarTower A K₁ L₁]
  [IsScalarTower A K₂ L₂] [IsScalarTower A B L₁] [IsScalarTower A B L₂]

omit [IsDomain B]

theorem algHom_commutes (e : K₁ →ₐ[A] K₂) (f : L₁ →ₐ[B] L₂) (x : K₁) :
    algebraMap K₂ L₂ (e x) = f (algebraMap K₁ L₁ x) := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective A x
  simp_rw [map_div₀, AlgHom.commutes, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply A B L₁, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

theorem algEquiv_commutes (e : K₁ ≃ₐ[A] K₂) (f : L₁ ≃ₐ[B] L₂) (x : K₁) :
    algebraMap K₂ L₂ (e x) = f (algebraMap K₁ L₁ x) := by
  exact algHom_commutes e.toAlgHom f.toAlgHom _

end commutes

section Subfield

variable (A K) in
/-- If `A` is a commutative ring with fraction field `K`, then the subfield of `K` generated by
the image of `algebraMap A K` is equal to the whole field `K`. -/
theorem closure_range_algebraMap : Subfield.closure (Set.range (algebraMap A K)) = ⊤ :=
  top_unique fun z _ ↦ by
    obtain ⟨_, _, -, rfl⟩ := div_surjective A z
    apply div_mem <;> exact Subfield.subset_closure ⟨_, rfl⟩

variable {L : Type*} [Field L] {g : A →+* L} {f : K →+* L}

/-- If `A` is a commutative ring with fraction field `K`, `L` is a field, `g : A →+* L` lifts to
`f : K →+* L`, then the image of `f` is the subfield generated by the image of `g`. -/
theorem ringHom_fieldRange_eq_of_comp_eq (h : RingHom.comp f (algebraMap A K) = g) :
    f.fieldRange = Subfield.closure g.range := by
  rw [f.fieldRange_eq_map, ← closure_range_algebraMap A K,
    f.map_field_closure, ← Set.range_comp, ← f.coe_comp, h, g.coe_range]

/-- If `A` is a commutative ring with fraction field `K`, `L` is a field, `g : A →+* L` lifts to
`f : K →+* L`, `s` is a set such that the image of `g` is the subring generated by `s`,
then the image of `f` is the subfield generated by `s`. -/
theorem ringHom_fieldRange_eq_of_comp_eq_of_range_eq (h : RingHom.comp f (algebraMap A K) = g)
    {s : Set L} (hs : g.range = Subring.closure s) : f.fieldRange = Subfield.closure s := by
  rw [ringHom_fieldRange_eq_of_comp_eq h, hs]
  ext
  simp_rw [Subfield.mem_closure_iff, Subring.closure_eq]

end Subfield

open Function

/-- Given a commutative ring `A` with field of fractions `K`,
and an injective ring hom `g : A →+* L` where `L` is a field, we get a
field hom sending `z : K` to `g x * (g y)⁻¹`, where `(x, y) : A × (NonZeroDivisors A)` are
such that `z = f x * (f y)⁻¹`. -/
noncomputable def lift (hg : Injective g) : K →+* L :=
  IsLocalization.lift fun y : nonZeroDivisors A => isUnit_map_of_injective hg y

theorem lift_unique (hg : Function.Injective g) {f : K →+* L}
    (hf1 : ∀ x, f (algebraMap A K x) = g x) : IsFractionRing.lift hg = f :=
  IsLocalization.lift_unique _ hf1

/-- Another version of unique to give two lift maps should be equal -/
theorem ringHom_ext {f1 f2 : K →+* L}
    (hf : ∀ x : A, f1 (algebraMap A K x) = f2 (algebraMap A K x)) : f1 = f2 := by
  ext z
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective A z
  rw [map_div₀, map_div₀, hf, hf]

theorem injective_comp_algebraMap :
    Function.Injective fun (f : K →+* L) => f.comp (algebraMap A K) :=
  fun _ _ h => ringHom_ext (fun x => RingHom.congr_fun h x)

section liftAlgHom

variable [Algebra R A] [Algebra R K] [IsScalarTower R A K] [Algebra R L]
  {g : A →ₐ[R] L} (hg : Injective g) (x : K)
include hg

/-- `AlgHom` version of `IsFractionRing.lift`. -/
noncomputable def liftAlgHom : K →ₐ[R] L :=
  IsLocalization.liftAlgHom fun y : nonZeroDivisors A => isUnit_map_of_injective hg y

theorem liftAlgHom_toRingHom : (liftAlgHom hg : K →ₐ[R] L).toRingHom = lift hg := rfl

@[simp]
theorem coe_liftAlgHom : ⇑(liftAlgHom hg : K →ₐ[R] L) = lift hg := rfl

theorem liftAlgHom_apply : liftAlgHom hg x = lift hg x := rfl

end liftAlgHom

/-- Given a commutative ring `A` with field of fractions `K`,
and an injective ring hom `g : A →+* L` where `L` is a field,
the field hom induced from `K` to `L` maps `x` to `g x` for all
`x : A`. -/
@[simp]
theorem lift_algebraMap (hg : Injective g) (x) : lift hg (algebraMap A K x) = g x :=
  lift_eq _ _

/-- The image of `IsFractionRing.lift` is the subfield generated by the image
of the ring hom. -/
theorem lift_fieldRange (hg : Injective g) :
    (lift hg : K →+* L).fieldRange = Subfield.closure g.range :=
  ringHom_fieldRange_eq_of_comp_eq (by ext; simp)

/-- The image of `IsFractionRing.lift` is the subfield generated by `s`, if the image
of the ring hom is the subring generated by `s`. -/
theorem lift_fieldRange_eq_of_range_eq (hg : Injective g)
    {s : Set L} (hs : g.range = Subring.closure s) :
    (lift hg : K →+* L).fieldRange = Subfield.closure s :=
  ringHom_fieldRange_eq_of_comp_eq_of_range_eq (by ext; simp) hs

/-- Given a commutative ring `A` with field of fractions `K`,
and an injective ring hom `g : A →+* L` where `L` is a field,
field hom induced from `K` to `L` maps `f x / f y` to `g x / g y` for all
`x : A, y ∈ NonZeroDivisors A`. -/
theorem lift_mk' (hg : Injective g) (x) (y : nonZeroDivisors A) :
    lift hg (mk' K x y) = g x / g y := by simp only [mk'_eq_div, map_div₀, lift_algebraMap]

/-- Given commutative rings `A, B` where `B` is an integral domain, with fraction rings `K`, `L`
and an injective ring hom `j : A →+* B`, we get a ring hom
sending `z : K` to `g (j x) * (g (j y))⁻¹`, where `(x, y) : A × (NonZeroDivisors A)` are
such that `z = f x * (f y)⁻¹`. -/
noncomputable def map {A B K L : Type*} [CommRing A] [CommRing B] [IsDomain B] [CommRing K]
    [Algebra A K] [IsFractionRing A K] [CommRing L] [Algebra B L] [IsFractionRing B L] {j : A →+* B}
    (hj : Injective j) : K →+* L :=
  IsLocalization.map L j
    (show nonZeroDivisors A ≤ (nonZeroDivisors B).comap j from
      nonZeroDivisors_le_comap_nonZeroDivisors_of_injective j hj)

section ringEquivOfRingEquiv

variable {A K B L : Type*} [CommRing A] [CommRing B] [CommRing K] [CommRing L]
  [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
  (h : A ≃+* B)

/-- Given rings `A, B` and localization maps to their fraction rings
`f : A →+* K, g : B →+* L`, an isomorphism `h : A ≃+* B` induces an isomorphism of
fraction rings `K ≃+* L`. -/
@[simps!]
noncomputable def ringEquivOfRingEquiv : K ≃+* L :=
  IsLocalization.ringEquivOfRingEquiv K L h (MulEquivClass.map_nonZeroDivisors h)

lemma ringEquivOfRingEquiv_algebraMap
    (a : A) : ringEquivOfRingEquiv h (algebraMap A K a) = algebraMap B L (h a) := by
  simp

@[simp]
lemma ringEquivOfRingEquiv_symm :
    (ringEquivOfRingEquiv h : K ≃+* L).symm = ringEquivOfRingEquiv h.symm := rfl

variable (K L) in
theorem ringEquivOfRingEquiv_comp {C : Type*} (M : Type*) [CommRing C]
  [CommRing M] [Algebra C M] [IsFractionRing C M] (f : A ≃+* B) (g : B ≃+* C) :
  (ringEquivOfRingEquiv (f.trans g)) =
    (ringEquivOfRingEquiv (K := K) f).trans (ringEquivOfRingEquiv (K := L) (L := M) g) := by
  ext a
  simp [IsLocalization.map_map]

end ringEquivOfRingEquiv

section semilinearEquivOfRingEquiv

variable {A B : Type*} (K L : Type*) [CommRing A] [CommRing B] [CommRing K] [CommRing L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L] (f : A ≃+* B)

local instance : RingHomInvPair (f : A →+* B) f.symm :=
  RingHomInvPair.of_ringEquiv f

/-- Given rings `A, B` and localization maps to their fraction rings
`f : A →+* K, g : B →+* L`, an isomorphism `h : A ≃+* B` induces a semilinear equivalence
fraction rings `K ≃ₛₗ[f.toRingHom] L`. -/
noncomputable def semilinearEquivOfRingEquiv : K ≃ₛₗ[(f : A →+* B)] L :=
{ ringEquivOfRingEquiv f with
  map_smul' r x := by simp [Algebra.smul_def] }

lemma semilinearEquivOfRingEquiv_apply (x : K) :
    (semilinearEquivOfRingEquiv K L f) x = (ringEquivOfRingEquiv f) x := rfl

@[simp]
lemma semilinearEquivOfRingEquiv_algebraMap (a : A) :
    semilinearEquivOfRingEquiv K L f (algebraMap A K a) = algebraMap B L (f a) := by
  simp [semilinearEquivOfRingEquiv, ringEquivOfRingEquiv]

lemma semilinearEquivOfRingEquiv_symm_apply (x : L) :
    (semilinearEquivOfRingEquiv K L f).symm x = (ringEquivOfRingEquiv f).symm x := rfl

lemma semilinearEquivOfRingEquiv_comp {C : Type*} (M : Type*) [CommRing C] [CommRing M]
    [Algebra C M] [IsFractionRing C M] (g : B ≃+* C) :
    let : RingHomCompTriple f (g : B →+* C) (f.trans g : A →+* C) := ⟨rfl⟩
    let : RingHomCompTriple g.symm (f.symm : B →+* A) ((f.trans g).symm : C →+* A) := ⟨rfl⟩
    (semilinearEquivOfRingEquiv K M (f.trans g)) =
      LinearEquiv.trans (σ₁₃ := (f.trans g)) (σ₃₁ := (f.trans g).symm)
      (semilinearEquivOfRingEquiv K L f)
      (semilinearEquivOfRingEquiv L M g) := by
  ext a
  simp [-RingEquiv.coe_ringHom_trans, semilinearEquivOfRingEquiv_apply,
    semilinearEquivOfRingEquiv_apply K M, ringEquivOfRingEquiv_comp K L M]

end semilinearEquivOfRingEquiv

section algEquivOfAlgEquiv

variable {R A K B L : Type*} [CommSemiring R] [CommRing A] [CommRing B] [CommRing K] [CommRing L]
  [Algebra R A] [Algebra R K] [Algebra A K] [IsFractionRing A K] [IsScalarTower R A K]
  [Algebra R B] [Algebra R L] [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  (h : A ≃ₐ[R] B)

/-- Given `R`-algebras `A, B` and localization maps to their fraction rings
`f : A →ₐ[R] K, g : B →ₐ[R] L`, an isomorphism `h : A ≃ₐ[R] B` induces an isomorphism of
fraction rings `K ≃ₐ[R] L`. -/
noncomputable def algEquivOfAlgEquiv : K ≃ₐ[R] L :=
  IsLocalization.algEquivOfAlgEquiv K L h (MulEquivClass.map_nonZeroDivisors h)

@[simp]
lemma algEquivOfAlgEquiv_algebraMap
    (a : A) : algEquivOfAlgEquiv h (algebraMap A K a) = algebraMap B L (h a) := by
  simp [algEquivOfAlgEquiv]

@[simp]
lemma algEquivOfAlgEquiv_symm :
    (algEquivOfAlgEquiv h : K ≃ₐ[R] L).symm = algEquivOfAlgEquiv h.symm := rfl

end algEquivOfAlgEquiv

section fieldEquivOfAlgEquiv

variable {A B C D : Type*}
  [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Algebra A C] [Algebra A D]
  (FA FB FC FD : Type*) [Field FA] [Field FB] [Field FC] [Field FD]
  [Algebra A FA] [Algebra B FB] [Algebra C FC] [Algebra D FD]
  [IsFractionRing A FA] [IsFractionRing B FB] [IsFractionRing C FC] [IsFractionRing D FD]
  [Algebra A FB] [IsScalarTower A B FB]
  [Algebra A FC] [IsScalarTower A C FC]
  [Algebra A FD] [IsScalarTower A D FD]
  [Algebra FA FB] [IsScalarTower A FA FB]
  [Algebra FA FC] [IsScalarTower A FA FC]
  [Algebra FA FD] [IsScalarTower A FA FD]

/-- An algebra isomorphism of rings induces an algebra isomorphism of fraction fields. -/
noncomputable def fieldEquivOfAlgEquiv (f : B ≃ₐ[A] C) : FB ≃ₐ[FA] FC where
  __ := IsFractionRing.ringEquivOfRingEquiv f.toRingEquiv
  commutes' x := by
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective A x
    simp_rw [map_div₀, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B FB]
    simp [← IsScalarTower.algebraMap_apply A C FC]

lemma restrictScalars_fieldEquivOfAlgEquiv (f : B ≃ₐ[A] C) :
    (fieldEquivOfAlgEquiv FA FB FC f).restrictScalars A = algEquivOfAlgEquiv f := by
  ext; rfl

/-- This says that `fieldEquivOfAlgEquiv f` is an extension of `f` (i.e., it agrees with `f` on
`B`). Whereas `(fieldEquivOfAlgEquiv f).commutes` says that `fieldEquivOfAlgEquiv f` fixes `K`. -/
@[simp]
lemma fieldEquivOfAlgEquiv_algebraMap (f : B ≃ₐ[A] C) (b : B) :
    fieldEquivOfAlgEquiv FA FB FC f (algebraMap B FB b) = algebraMap C FC (f b) :=
  ringEquivOfRingEquiv_algebraMap f.toRingEquiv b

variable (A B) in
@[simp]
lemma fieldEquivOfAlgEquiv_refl :
    fieldEquivOfAlgEquiv FA FB FB (AlgEquiv.refl : B ≃ₐ[A] B) = AlgEquiv.refl := by
  ext x
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective B x
  simp

lemma fieldEquivOfAlgEquiv_trans (f : B ≃ₐ[A] C) (g : C ≃ₐ[A] D) :
    fieldEquivOfAlgEquiv FA FB FD (f.trans g) =
      (fieldEquivOfAlgEquiv FA FB FC f).trans (fieldEquivOfAlgEquiv FA FC FD g) := by
  ext x
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective B x
  simp

end fieldEquivOfAlgEquiv

section fieldEquivOfAlgEquivHom

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (K L : Type*) [Field K] [Field L]
  [Algebra A K] [Algebra B L] [IsFractionRing A K] [IsFractionRing B L]
  [Algebra A L] [IsScalarTower A B L] [Algebra K L] [IsScalarTower A K L]

/-- An algebra automorphism of a ring induces an algebra automorphism of its fraction field.

This is a bundled version of `fieldEquivOfAlgEquiv`. -/
noncomputable def fieldEquivOfAlgEquivHom : (B ≃ₐ[A] B) →* (L ≃ₐ[K] L) where
  toFun := fieldEquivOfAlgEquiv K L L
  map_one' := fieldEquivOfAlgEquiv_refl A B K L
  map_mul' f g := fieldEquivOfAlgEquiv_trans K L L L g f

@[simp]
lemma fieldEquivOfAlgEquivHom_apply (f : B ≃ₐ[A] B) :
    fieldEquivOfAlgEquivHom K L f = fieldEquivOfAlgEquiv K L L f :=
  rfl

variable (A B)

lemma fieldEquivOfAlgEquivHom_injective :
    Function.Injective (fieldEquivOfAlgEquivHom K L : (B ≃ₐ[A] B) →* (L ≃ₐ[K] L)) := by
  intro f g h
  ext b
  simpa using AlgEquiv.ext_iff.mp h (algebraMap B L b)

end fieldEquivOfAlgEquivHom

theorem isFractionRing_iff_of_base_ringEquiv (h : R ≃+* P) :
    IsFractionRing R S ↔
      @IsFractionRing P _ S _ ((algebraMap R S).comp h.symm.toRingHom).toAlgebra := by
  delta IsFractionRing
  convert isLocalization_iff_of_base_ringEquiv (nonZeroDivisors R) S h
  exact (MulEquivClass.map_nonZeroDivisors h).symm

variable (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] [h : IsFractionRing R S]

theorem nontrivial_iff_nontrivial : Nontrivial R ↔ Nontrivial S := by
  by_contra! ⟨_, _⟩ | ⟨_, _⟩
  · obtain ⟨c, hc⟩ := h.exists_of_eq (x := 1) (y := 0) (Subsingleton.elim _ _)
    simp at hc
  · apply (h.map_units S 1).ne_zero
    rw [Subsingleton.eq_zero ((1 : nonZeroDivisors R) : R), map_zero]

protected theorem nontrivial [hR : Nontrivial R] : Nontrivial S :=
  h.nontrivial_iff_nontrivial.mp hR

section MulAction

variable (G A B K L : Type*) [Group G] [CommRing A] [CommRing B] [MulSemiringAction G B]
  [Algebra A B] [Field K] [Field L] [Algebra K L] [Algebra A K] [Algebra B L] [Algebra A L]
  [IsFractionRing A K] [IsFractionRing B L] [IsScalarTower A K L] [IsScalarTower A B L]

/-- Given a `MulSemiringAction G B`, extend the action of `G` on `B` to a `MulSemiringAction G L`
on the fraction field `L` of `B`. -/
@[implicit_reducible]
noncomputable def mulSemiringAction [SMulCommClass G A B] :
    MulSemiringAction G L :=
  MulSemiringAction.compHom L
    ((fieldEquivOfAlgEquivHom K L).comp (MulSemiringAction.toAlgAut G A B))

/-- The action of `G` on the fraction field `L` of `B` given by `IsFractionRing.mulSemiringAction`
is compatible with the embedding `B ⊆ L`. -/
instance smulDistribClass [SMulCommClass G A B] :
    letI := mulSemiringAction G A B K L
    SMulDistribClass G B L :=
  let := mulSemiringAction G A B K L
  ⟨fun g b x ↦ by
    rw [Algebra.smul_def', Algebra.smul_def', smul_mul']
    congr
    apply fieldEquivOfAlgEquiv_algebraMap⟩

variable [MulSemiringAction G L] [SMulDistribClass G B L]

protected theorem faithfulSMul [FaithfulSMul G B] : FaithfulSMul G L :=
  ⟨fun h ↦ eq_of_smul_eq_smul fun x ↦ by simpa [← algebraMap.coe_smul'] using h (algebraMap B L x)⟩

protected theorem smulCommClass [SMulCommClass G A B] : SMulCommClass G K L :=
  ⟨fun g x y ↦ by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A x
    obtain ⟨c, d, hd, rfl⟩ := IsFractionRing.div_surjective B y
    simp [Algebra.smul_def, map_div₀, ← IsScalarTower.algebraMap_apply A K L,
      IsScalarTower.algebraMap_apply A B L, smul_mul', smul_div₀',
      ← algebraMap.coe_smul', smul_algebraMap]⟩

end MulAction

end IsFractionRing

section algebraMap_injective

theorem algebraMap_injective_of_field_isFractionRing (K L : Type*) [Field K] [Semiring L]
    [Nontrivial L] [Algebra R K] [IsFractionRing R K] [Algebra S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L] : Function.Injective (algebraMap R S) := by
  refine Function.Injective.of_comp (f := algebraMap S L) ?_
  rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R K L]
  exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)

theorem FaithfulSMul.of_field_isFractionRing (K L : Type*) [Field K] [Semiring L]
    [Nontrivial L] [Algebra R K] [IsFractionRing R K] [Algebra S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L] : FaithfulSMul R S :=
  (faithfulSMul_iff_algebraMap_injective R S).mpr <|
    algebraMap_injective_of_field_isFractionRing R S K L

end algebraMap_injective

variable (A)

/-- The fraction ring of a commutative ring `R` as a quotient type.

We instantiate this definition as generally as possible, and assume that the
commutative ring `R` is an integral domain only when this is needed for proving.

In this generality, this construction is also known as the *total fraction ring* of `R`.
-/
abbrev FractionRing :=
  Localization (nonZeroDivisors R)

namespace FractionRing

instance : IsFractionRing (FractionRing R) (FractionRing R) := IsFractionRing.idem R _

instance unique [Subsingleton R] : Unique (FractionRing R) := inferInstance

instance [Nontrivial R] : Nontrivial (FractionRing R) := inferInstance

variable {R} in
instance [DecidableEq R] : DecidableEq (FractionRing R) := by
  intro x y
  apply Localization.recOnSubsingleton₂ x y (r := fun x y ↦ Decidable (x = y))
  intro a c b d
  simp only [Localization.mk_eq_mk_iff, Localization.r_iff_of_le_nonZeroDivisors (le_refl _)]
  infer_instance

variable [IsDomain A]

noncomputable instance field : Field (FractionRing A) := inferInstance

@[simp]
theorem mk_eq_div {r s} :
    (Localization.mk r s : FractionRing A) =
      (algebraMap _ _ r / algebraMap A _ s : FractionRing A) := by
  rw [Localization.mk_eq_mk', IsFractionRing.mk'_eq_div]

section liftAlgebra

variable [Field K] [Algebra R K] [FaithfulSMul R K]

/-- This is not an instance because it creates a diamond when `K = FractionRing R`.
Should usually be introduced locally along with `isScalarTower_liftAlgebra`
See note [reducible non-instances]. -/
noncomputable abbrev liftAlgebra : Algebra (FractionRing R) K :=
  have := IsDomain.of_faithfulSMul R K
  RingHom.toAlgebra (IsFractionRing.lift (FaithfulSMul.algebraMap_injective R K))

attribute [local instance] liftAlgebra

instance isScalarTower_liftAlgebra : IsScalarTower R (FractionRing R) K :=
  have := IsDomain.of_faithfulSMul R K
  .of_algebraMap_eq fun x ↦
    (IsFractionRing.lift_algebraMap (FaithfulSMul.algebraMap_injective R K) x).symm

lemma algebraMap_liftAlgebra :
    have := IsDomain.of_faithfulSMul R K
    algebraMap (FractionRing R) K = IsFractionRing.lift (FaithfulSMul.algebraMap_injective R _) :=
  rfl

instance {R₀} [SMul R₀ R] [IsScalarTower R₀ R R] [SMul R₀ K] [IsScalarTower R₀ R K] :
    IsScalarTower R₀ (FractionRing R) K := IsScalarTower.to₁₃₄ _ R _ _

end liftAlgebra

/-- Given a ring `A` and a localization map to a fraction ring
`f : A →+* K`, we get an `A`-isomorphism between the fraction ring of `A` as a quotient
type and `K`. -/
noncomputable def algEquiv (K : Type*) [CommRing K] [Algebra A K] [IsFractionRing A K] :
    FractionRing A ≃ₐ[A] K :=
  Localization.algEquiv (nonZeroDivisors A) K

instance [Algebra R A] [FaithfulSMul R A] : FaithfulSMul R (FractionRing A) := by
  rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq R A]
  exact (FaithfulSMul.algebraMap_injective A (FractionRing A)).comp
    (FaithfulSMul.algebraMap_injective R A)

section IsScalarTower

attribute [local instance] liftAlgebra

instance (k K : Type*) [Field k] [Field K] [Algebra A k] [Algebra A K] [Algebra k K]
    [FaithfulSMul A k] [FaithfulSMul A K] [IsScalarTower A k K] :
    IsScalarTower (FractionRing A) k K where
  smul_assoc a b c := a.ind fun ⟨a₁, a₂⟩ ↦ by
    rw [← smul_right_inj (nonZeroDivisors.coe_ne_zero a₂)]
    simp_rw [← smul_assoc, Localization.smul_mk, smul_eq_mul, Localization.mk_eq_mk',
      IsLocalization.mk'_mul_cancel_left, algebraMap_smul, smul_assoc]

end IsScalarTower

end FractionRing
