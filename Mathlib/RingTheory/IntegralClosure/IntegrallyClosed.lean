/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Integrally closed rings

An integrally closed ring `R` contains all the elements of `Frac(R)` that are
integral over `R`. A special case of integrally closed rings are the Dedekind domains.

## Main definitions

* `IsIntegrallyClosedIn R A` states `R` contains all integral elements of `A`
* `IsIntegrallyClosed R` states `R` contains all integral elements of `Frac(R)`

## Main results

* `isIntegrallyClosed_iff K`, where `K` is a fraction field of `R`, states `R`
  is integrally closed iff it is the integral closure of `R` in `K`

## TODO Related notions

The following definitions are closely related, especially in their applications in Mathlib.

A *normal domain* is a domain that is integrally closed in its field of fractions.
[Stacks: normal domain](https://stacks.math.columbia.edu/tag/037B#0309)
Normal domains are the major use case of `IsIntegrallyClosed` at the time of writing, and we have
quite a few results that can be moved wholesale to a new `NormalDomain` definition.
In fact, before PR https://github.com/leanprover-community/mathlib4/pull/6126 `IsIntegrallyClosed` was exactly defined to be a normal domain.
(So you might want to copy some of its API when you define normal domains.)

A normal ring means that localizations at all prime ideals are normal domains.
[Stacks: normal ring](https://stacks.math.columbia.edu/tag/037B#00GV)
This implies `IsIntegrallyClosed`,
[Stacks: Tag 034M](https://stacks.math.columbia.edu/tag/037B#034M)
but is equivalent to it only under some conditions (reduced + finitely many minimal primes),
[Stacks: Tag 030C](https://stacks.math.columbia.edu/tag/037B#030C)
in which case it's also equivalent to being a finite product of normal domains.

We'd need to add these conditions if we want exactly the products of Dedekind domains.

In fact Noetherianity is sufficient to guarantee finitely many minimal primes, so `IsDedekindRing`
could be defined as `IsReduced`, `IsNoetherian`, `Ring.DimensionLEOne`, and either
`IsIntegrallyClosed` or `NormalDomain`. If we use `NormalDomain` then `IsReduced` is automatic,
but we could also consider a version of `NormalDomain` that only requires the localizations are
`IsIntegrallyClosed` but may not be domains, and that may not equivalent to the ring itself being
`IsIntegrallyClosed` (even for Noetherian rings?).
-/


open scoped nonZeroDivisors Polynomial

open Polynomial

/-- `R` is integrally closed in `A` if all integral elements of `A` are also elements of `R`.
-/
abbrev IsIntegrallyClosedIn (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] :=
  IsIntegralClosure R R A

/-- `R` is integrally closed if all integral elements of `Frac(R)` are also elements of `R`.

This definition uses `FractionRing R` to denote `Frac(R)`. See `isIntegrallyClosed_iff`
if you want to choose another field of fractions for `R`.
-/
abbrev IsIntegrallyClosed (R : Type*) [CommRing R] := IsIntegrallyClosedIn R (FractionRing R)

section Iff

variable {R : Type*} [CommRing R]
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Being integrally closed is preserved under injective algebra homomorphisms. -/
theorem AlgHom.isIntegrallyClosedIn (f : A →ₐ[R] B) (hf : Function.Injective f) :
    IsIntegrallyClosedIn R B → IsIntegrallyClosedIn R A := by
  rintro ⟨inj, cl⟩
  refine ⟨Function.Injective.of_comp (f := f) ?_, fun hx => ?_, ?_⟩
  · convert inj
    aesop
  · obtain ⟨y, fx_eq⟩ := cl.mp ((isIntegral_algHom_iff f hf).mpr hx)
    aesop
  · rintro ⟨y, rfl⟩
    apply (isIntegral_algHom_iff f hf).mp
    simp_all

/-- Being integrally closed is preserved under algebra isomorphisms. -/
theorem AlgEquiv.isIntegrallyClosedIn (e : A ≃ₐ[R] B) :
    IsIntegrallyClosedIn R A ↔ IsIntegrallyClosedIn R B :=
  ⟨AlgHom.isIntegrallyClosedIn e.symm e.symm.injective, AlgHom.isIntegrallyClosedIn e e.injective⟩

variable (K : Type*) [CommRing K] [Algebra R K] [IsFractionRing R K]

/-- `R` is integrally closed iff it is the integral closure of itself in its field of fractions. -/
theorem isIntegrallyClosed_iff_isIntegrallyClosedIn :
    IsIntegrallyClosed R ↔ IsIntegrallyClosedIn R K :=
  (IsLocalization.algEquiv R⁰ _ _).isIntegrallyClosedIn

/-- `R` is integrally closed iff it is the integral closure of itself in its field of fractions. -/
theorem isIntegrallyClosed_iff_isIntegralClosure : IsIntegrallyClosed R ↔ IsIntegralClosure R R K :=
  isIntegrallyClosed_iff_isIntegrallyClosedIn K

/-- `R` is integrally closed in `A` iff all integral elements of `A` are also elements of `R`. -/
theorem isIntegrallyClosedIn_iff {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] :
    IsIntegrallyClosedIn R A ↔
      Function.Injective (algebraMap R A) ∧
        ∀ {x : A}, IsIntegral R x → ∃ y, algebraMap R A y = x := by
  constructor
  · rintro ⟨_, cl⟩
    simp_all
  · rintro ⟨inj, cl⟩
    refine ⟨inj, by simp_all, ?_⟩
    rintro ⟨y, rfl⟩
    apply isIntegral_algebraMap

/-- `R` is integrally closed iff all integral elements of its fraction field `K`
are also elements of `R`. -/
theorem isIntegrallyClosed_iff :
    IsIntegrallyClosed R ↔ ∀ {x : K}, IsIntegral R x → ∃ y, algebraMap R K y = x := by
  simp [isIntegrallyClosed_iff_isIntegrallyClosedIn K, isIntegrallyClosedIn_iff,
        IsFractionRing.injective R K]

end Iff

namespace IsIntegrallyClosedIn

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem algebraMap_eq_of_integral [IsIntegrallyClosedIn R A] {x : A} :
    IsIntegral R x → ∃ y : R, algebraMap R A y = x :=
  IsIntegralClosure.isIntegral_iff.mp

theorem isIntegral_iff [IsIntegrallyClosedIn R A] {x : A} :
    IsIntegral R x ↔ ∃ y : R, algebraMap R A y = x :=
  IsIntegralClosure.isIntegral_iff

theorem exists_algebraMap_eq_of_isIntegral_pow [IsIntegrallyClosedIn R A]
    {x : A} {n : ℕ} (hn : 0 < n)
    (hx : IsIntegral R <| x ^ n) : ∃ y : R, algebraMap R A y = x :=
  isIntegral_iff.mp <| hx.of_pow hn

theorem exists_algebraMap_eq_of_pow_mem_subalgebra {A : Type*} [CommRing A] [Algebra R A]
    {S : Subalgebra R A} [IsIntegrallyClosedIn S A] {x : A} {n : ℕ} (hn : 0 < n)
    (hx : x ^ n ∈ S) : ∃ y : S, algebraMap S A y = x :=
  exists_algebraMap_eq_of_isIntegral_pow hn <| isIntegral_iff.mpr ⟨⟨x ^ n, hx⟩, rfl⟩

variable (A)

theorem integralClosure_eq_bot_iff (hRA : Function.Injective (algebraMap R A)) :
    integralClosure R A = ⊥ ↔ IsIntegrallyClosedIn R A := by
  refine eq_bot_iff.trans ?_
  constructor
  · intro h
    refine ⟨ hRA, fun hx => Set.mem_range.mp (Algebra.mem_bot.mp (h hx)), ?_⟩
    rintro ⟨y, rfl⟩
    apply isIntegral_algebraMap
  · intro h x hx
    rw [Algebra.mem_bot, Set.mem_range]
    exact isIntegral_iff.mp hx

variable (R)

@[simp]
theorem integralClosure_eq_bot [IsIntegrallyClosedIn R A] [NoZeroSMulDivisors R A] [Nontrivial A] :
    integralClosure R A = ⊥ :=
  (integralClosure_eq_bot_iff A (FaithfulSMul.algebraMap_injective _ _)).mpr ‹_›

variable {A} {B : Type*} [CommRing B]

/-- If `R` is the integral closure of `S` in `A`, then it is integrally closed in `A`. -/
lemma of_isIntegralClosure [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [IsIntegralClosure A R B] :
    IsIntegrallyClosedIn A B :=
  have : Algebra.IsIntegral R A := IsIntegralClosure.isIntegral_algebra R B
  IsIntegralClosure.tower_top (R := R)

variable {R}

lemma _root_.IsIntegralClosure.of_isIntegrallyClosedIn
    [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [IsIntegrallyClosedIn A B] [Algebra.IsIntegral R A] :
    IsIntegralClosure A R B := by
  refine ⟨IsIntegralClosure.algebraMap_injective _ A _, fun {x} ↦
    ⟨fun hx ↦ IsIntegralClosure.isIntegral_iff.mp (IsIntegral.tower_top (A := A) hx), ?_⟩⟩
  rintro ⟨y, rfl⟩
  exact IsIntegral.map (IsScalarTower.toAlgHom A A B) (Algebra.IsIntegral.isIntegral y)

end IsIntegrallyClosedIn

namespace IsIntegrallyClosed

variable {R S : Type*} [CommRing R] [CommRing S]
variable {K : Type*} [CommRing K] [Algebra R K] [ifr : IsFractionRing R K]

/-- Note that this is not a duplicate instance, since `IsIntegrallyClosed R` is instead defined
as `IsIntegrallyClosed R R (FractionRing R)`. -/
instance [iic : IsIntegrallyClosed R] : IsIntegralClosure R R K :=
  (isIntegrallyClosed_iff_isIntegralClosure K).mp iic

theorem algebraMap_eq_of_integral [IsIntegrallyClosed R] {x : K} :
    IsIntegral R x → ∃ y : R, algebraMap R K y = x :=
  IsIntegralClosure.isIntegral_iff.mp

theorem isIntegral_iff [IsIntegrallyClosed R] {x : K} :
    IsIntegral R x ↔ ∃ y : R, algebraMap R K y = x :=
  IsIntegrallyClosedIn.isIntegral_iff

theorem exists_algebraMap_eq_of_isIntegral_pow [IsIntegrallyClosed R] {x : K} {n : ℕ} (hn : 0 < n)
    (hx : IsIntegral R <| x ^ n) : ∃ y : R, algebraMap R K y = x :=
  IsIntegrallyClosedIn.exists_algebraMap_eq_of_isIntegral_pow hn hx

theorem exists_algebraMap_eq_of_pow_mem_subalgebra {K : Type*} [CommRing K] [Algebra R K]
    {S : Subalgebra R K} [IsIntegrallyClosed S] [IsFractionRing S K] {x : K} {n : ℕ} (hn : 0 < n)
    (hx : x ^ n ∈ S) : ∃ y : S, algebraMap S K y = x :=
  IsIntegrallyClosedIn.exists_algebraMap_eq_of_pow_mem_subalgebra hn hx

theorem of_equiv (f : R ≃+* S) [h : IsIntegrallyClosed R] : IsIntegrallyClosed S := by
  let _ : Algebra S R := f.symm.toRingHom.toAlgebra
  let f : S ≃ₐ[S] R := AlgEquiv.ofRingEquiv fun _ ↦ rfl
  let g : FractionRing S ≃ₐ[S] FractionRing R := IsFractionRing.algEquivOfAlgEquiv f
  refine (isIntegrallyClosed_iff (FractionRing S)).mpr (fun hx ↦ ?_)
  rcases (isIntegrallyClosed_iff _).mp h ((isIntegral_algEquiv g).mpr hx).tower_top with ⟨z, hz⟩
  exact ⟨f.symm z, (IsFractionRing.algEquivOfAlgEquiv_algebraMap f.symm z).symm.trans <|
    (AlgEquiv.symm_apply_eq g).mpr hz⟩

variable (R S K)

instance _root_.IsIntegralClosure.of_isIntegrallyClosed [IsIntegrallyClosed R]
    [Algebra S R] [Algebra S K] [IsScalarTower S R K] [Algebra.IsIntegral S R] :
    IsIntegralClosure R S K :=
  IsIntegralClosure.of_isIntegrallyClosedIn

variable {R}

theorem integralClosure_eq_bot_iff : integralClosure R K = ⊥ ↔ IsIntegrallyClosed R :=
  (IsIntegrallyClosedIn.integralClosure_eq_bot_iff _ (IsFractionRing.injective _ _)).trans
    (isIntegrallyClosed_iff_isIntegrallyClosedIn _).symm

@[simp]
theorem pow_dvd_pow_iff [IsDomain R] [IsIntegrallyClosed R]
    {n : ℕ} (hn : n ≠ 0) {a b : R} : a ^ n ∣ b ^ n ↔ a ∣ b := by
  refine ⟨fun ⟨x, hx⟩ ↦ ?_, fun h ↦ pow_dvd_pow_of_dvd h n⟩
  by_cases ha : a = 0
  · simpa [ha, hn] using hx
  let K := FractionRing R
  replace ha : algebraMap R K a ≠ 0 := fun h ↦
    ha <| (injective_iff_map_eq_zero _).1 (IsFractionRing.injective R K) _ h
  let y := (algebraMap R K b) / (algebraMap R K a)
  have hy : IsIntegral R y := by
    refine ⟨X ^ n - C x, monic_X_pow_sub_C _ hn, ?_⟩
    simp only [y, eval₂_sub, eval₂_X_pow, div_pow, eval₂_C]
    replace hx := congr_arg (algebraMap R K) hx
    rw [map_pow] at hx
    simp [hx, ha]
  obtain ⟨k, hk⟩ := algebraMap_eq_of_integral hy
  refine ⟨k, IsFractionRing.injective R K ?_⟩
  rw [map_mul, hk, mul_div_cancel₀ _ ha]

@[simp]
theorem _root_.Associated.pow_iff [IsDomain R] [IsIntegrallyClosed R] {n : ℕ} (hn : n ≠ 0)
    {a b : R} :
    Associated (a ^ n) (b ^ n) ↔ Associated a b := by
  simp_rw [← dvd_dvd_iff_associated, pow_dvd_pow_iff hn]

variable (R)

/-- This is almost a duplicate of `IsIntegrallyClosedIn.integralClosure_eq_bot`,
except the `NoZeroSMulDivisors` hypothesis isn't inferred automatically from `IsFractionRing`. -/
@[simp]
theorem integralClosure_eq_bot [IsIntegrallyClosed R] : integralClosure R K = ⊥ :=
  (integralClosure_eq_bot_iff K).mpr ‹_›

end IsIntegrallyClosed

namespace integralClosure

open IsIntegrallyClosed

variable {R : Type*} [CommRing R]
variable (K : Type*) [Field K] [Algebra R K]
variable [IsFractionRing R K]
variable {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]

-- Can't be an instance because you need to supply `K`.
theorem isIntegrallyClosedOfFiniteExtension [IsDomain R] [FiniteDimensional K L] :
    IsIntegrallyClosed (integralClosure R L) :=
  letI : IsFractionRing (integralClosure R L) L := isFractionRing_of_finite_extension K L
  (integralClosure_eq_bot_iff L).mp integralClosure_idem

end integralClosure

section localization

variable {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]

lemma isIntegrallyClosed_of_isLocalization [IsIntegrallyClosed R] [IsDomain R] (M : Submonoid R)
    (hM : M ≤ R⁰) [IsLocalization M S] : IsIntegrallyClosed S := by
  let K := FractionRing R
  let g : S →+* K := IsLocalization.map _ (T := R⁰) (RingHom.id R) hM
  letI := g.toAlgebra
  have : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  have := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M S K
  refine (isIntegrallyClosed_iff_isIntegralClosure (K := K)).mpr
    ⟨IsFractionRing.injective _ _, fun {x} ↦ ⟨?_, fun e ↦ e.choose_spec ▸ isIntegral_algebraMap⟩⟩
  intro hx
  obtain ⟨⟨y, y_mem⟩, hy⟩ := hx.exists_multiple_integral_of_isLocalization M _
  obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff _).mp ‹_› hy
  refine ⟨IsLocalization.mk' S z ⟨y, y_mem⟩, (IsLocalization.lift_mk'_spec _ _ _ _).mpr ?_⟩
  rw [RingHom.comp_id, hz, ← Algebra.smul_def, Submonoid.mk_smul]

end localization

/-- Any field is integral closed. -/
/- Although `infer_instance` can find this if you import Mathlib, in this file they have not been
  proven yet. However, it is used to prove a fundamental property of `IsIntegrallyClosed`,
  and it is not desirable to involve more content from other files. -/
instance Field.instIsIntegrallyClosed (K : Type*) [Field K] : IsIntegrallyClosed K :=
  (isIntegrallyClosed_iff K).mpr fun {x} _ ↦ ⟨x, rfl⟩
