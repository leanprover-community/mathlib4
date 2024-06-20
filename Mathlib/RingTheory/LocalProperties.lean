/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.RingHomProperties
import Mathlib.Data.Set.Subsingleton

#align_import ring_theory.local_properties from "leanprover-community/mathlib"@"a7c017d750512a352b623b1824d75da5998457d0"

/-!
# Local properties of commutative rings

In this file, we provide the proofs of various local properties.

## Naming Conventions

* `localization_P` : `P` holds for `S⁻¹R` if `P` holds for `R`.
* `P_of_localization_maximal` : `P` holds for `R` if `P` holds for `Rₘ` for all maximal `m`.
* `P_of_localization_prime` : `P` holds for `R` if `P` holds for `Rₘ` for all prime `m`.
* `P_ofLocalizationSpan` : `P` holds for `R` if given a spanning set `{fᵢ}`, `P` holds for all
  `R_{fᵢ}`.

## Main results

The following properties are covered:

* The triviality of an ideal or an element:
  `ideal_eq_bot_of_localization`, `eq_zero_of_localization`
* `isReduced` : `localization_isReduced`, `isReduced_of_localization_maximal`.
* `finite`: `localization_finite`, `finite_ofLocalizationSpan`
* `finiteType`: `localization_finiteType`, `finiteType_ofLocalizationSpan`

-/

open scoped Pointwise Classical

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (M : Submonoid R)
variable (N : Submonoid S) (R' S' : Type u) [CommRing R'] [CommRing S'] (f : R →+* S)
variable [Algebra R R'] [Algebra S S']

section Properties

section CommRing

variable (P : ∀ (R : Type u) [CommRing R], Prop)

/-- A property `P` of comm rings is said to be preserved by localization
  if `P` holds for `M⁻¹R` whenever `P` holds for `R`. -/
def LocalizationPreserves : Prop :=
  ∀ {R : Type u} [hR : CommRing R] (M : Submonoid R) (S : Type u) [hS : CommRing S] [Algebra R S]
    [IsLocalization M S], @P R hR → @P S hS
#align localization_preserves LocalizationPreserves

/-- A property `P` of comm rings satisfies `OfLocalizationMaximal`
  if `P` holds for `R` whenever `P` holds for `Rₘ` for all maximal ideal `m`. -/
def OfLocalizationMaximal : Prop :=
  ∀ (R : Type u) [CommRing R],
    (∀ (J : Ideal R) (_ : J.IsMaximal), P (Localization.AtPrime J)) → P R
#align of_localization_maximal OfLocalizationMaximal

end CommRing

section RingHom

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S] (_ : R →+* S), Prop)

/-- A property `P` of ring homs is said to be preserved by localization
 if `P` holds for `M⁻¹R →+* M⁻¹S` whenever `P` holds for `R →+* S`. -/
def RingHom.LocalizationPreserves :=
  ∀ ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R →+* S) (M : Submonoid R) (R' S' : Type u)
    [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S'] [IsLocalization M R']
    [IsLocalization (M.map f) S'],
    P f → P (IsLocalization.map S' f (Submonoid.le_comap_map M) : R' →+* S')
#align ring_hom.localization_preserves RingHom.LocalizationPreserves

/-- A property `P` of ring homs satisfies `RingHom.OfLocalizationFiniteSpan`
if `P` holds for `R →+* S` whenever there exists a finite set `{ r }` that spans `R` such that
`P` holds for `Rᵣ →+* Sᵣ`.

Note that this is equivalent to `RingHom.OfLocalizationSpan` via
`RingHom.ofLocalizationSpan_iff_finite`, but this is easier to prove. -/
def RingHom.OfLocalizationFiniteSpan :=
  ∀ ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R →+* S) (s : Finset R)
    (_ : Ideal.span (s : Set R) = ⊤) (_ : ∀ r : s, P (Localization.awayMap f r)), P f
#align ring_hom.of_localization_finite_span RingHom.OfLocalizationFiniteSpan

/-- A property `P` of ring homs satisfies `RingHom.OfLocalizationFiniteSpan`
if `P` holds for `R →+* S` whenever there exists a set `{ r }` that spans `R` such that
`P` holds for `Rᵣ →+* Sᵣ`.

Note that this is equivalent to `RingHom.OfLocalizationFiniteSpan` via
`RingHom.ofLocalizationSpan_iff_finite`, but this has less restrictions when applying. -/
def RingHom.OfLocalizationSpan :=
  ∀ ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R →+* S) (s : Set R) (_ : Ideal.span s = ⊤)
    (_ : ∀ r : s, P (Localization.awayMap f r)), P f
#align ring_hom.of_localization_span RingHom.OfLocalizationSpan

/-- A property `P` of ring homs satisfies `RingHom.HoldsForLocalizationAway`
 if `P` holds for each localization map `R →+* Rᵣ`. -/
def RingHom.HoldsForLocalizationAway : Prop :=
  ∀ ⦃R : Type u⦄ (S : Type u) [CommRing R] [CommRing S] [Algebra R S] (r : R)
    [IsLocalization.Away r S], P (algebraMap R S)
#align ring_hom.holds_for_localization_away RingHom.HoldsForLocalizationAway

/-- A property `P` of ring homs satisfies `RingHom.OfLocalizationFiniteSpanTarget`
if `P` holds for `R →+* S` whenever there exists a finite set `{ r }` that spans `S` such that
`P` holds for `R →+* Sᵣ`.

Note that this is equivalent to `RingHom.OfLocalizationSpanTarget` via
`RingHom.ofLocalizationSpanTarget_iff_finite`, but this is easier to prove. -/
def RingHom.OfLocalizationFiniteSpanTarget : Prop :=
  ∀ ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R →+* S) (s : Finset S)
    (_ : Ideal.span (s : Set S) = ⊤)
    (_ : ∀ r : s, P ((algebraMap S (Localization.Away (r : S))).comp f)), P f
#align ring_hom.of_localization_finite_span_target RingHom.OfLocalizationFiniteSpanTarget

/-- A property `P` of ring homs satisfies `RingHom.OfLocalizationSpanTarget`
if `P` holds for `R →+* S` whenever there exists a set `{ r }` that spans `S` such that
`P` holds for `R →+* Sᵣ`.

Note that this is equivalent to `RingHom.OfLocalizationFiniteSpanTarget` via
`RingHom.ofLocalizationSpanTarget_iff_finite`, but this has less restrictions when applying. -/
def RingHom.OfLocalizationSpanTarget : Prop :=
  ∀ ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R →+* S) (s : Set S) (_ : Ideal.span s = ⊤)
    (_ : ∀ r : s, P ((algebraMap S (Localization.Away (r : S))).comp f)), P f
#align ring_hom.of_localization_span_target RingHom.OfLocalizationSpanTarget

/-- A property `P` of ring homs satisfies `RingHom.OfLocalizationPrime`
if `P` holds for `R` whenever `P` holds for `Rₘ` for all prime ideals `p`. -/
def RingHom.OfLocalizationPrime : Prop :=
  ∀ ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R →+* S),
    (∀ (J : Ideal S) (_ : J.IsPrime), P (Localization.localRingHom _ J f rfl)) → P f
#align ring_hom.of_localization_prime RingHom.OfLocalizationPrime

/-- A property of ring homs is local if it is preserved by localizations and compositions, and for
each `{ r }` that spans `S`, we have `P (R →+* S) ↔ ∀ r, P (R →+* Sᵣ)`. -/
structure RingHom.PropertyIsLocal : Prop where
  LocalizationPreserves : RingHom.LocalizationPreserves @P
  OfLocalizationSpanTarget : RingHom.OfLocalizationSpanTarget @P
  StableUnderComposition : RingHom.StableUnderComposition @P
  HoldsForLocalizationAway : RingHom.HoldsForLocalizationAway @P
#align ring_hom.property_is_local RingHom.PropertyIsLocal

theorem RingHom.ofLocalizationSpan_iff_finite :
    RingHom.OfLocalizationSpan @P ↔ RingHom.OfLocalizationFiniteSpan @P := by
  delta RingHom.OfLocalizationSpan RingHom.OfLocalizationFiniteSpan
  apply forall₅_congr
  -- TODO: Using `refine` here breaks `resetI`.
  intros
  constructor
  · intro h s; exact h s
  · intro h s hs hs'
    obtain ⟨s', h₁, h₂⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
    exact h s' h₂ fun x => hs' ⟨_, h₁ x.prop⟩
#align ring_hom.of_localization_span_iff_finite RingHom.ofLocalizationSpan_iff_finite

theorem RingHom.ofLocalizationSpanTarget_iff_finite :
    RingHom.OfLocalizationSpanTarget @P ↔ RingHom.OfLocalizationFiniteSpanTarget @P := by
  delta RingHom.OfLocalizationSpanTarget RingHom.OfLocalizationFiniteSpanTarget
  apply forall₅_congr
  -- TODO: Using `refine` here breaks `resetI`.
  intros
  constructor
  · intro h s; exact h s
  · intro h s hs hs'
    obtain ⟨s', h₁, h₂⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
    exact h s' h₂ fun x => hs' ⟨_, h₁ x.prop⟩
#align ring_hom.of_localization_span_target_iff_finite RingHom.ofLocalizationSpanTarget_iff_finite

variable {P f R' S'}

theorem RingHom.PropertyIsLocal.respectsIso (hP : RingHom.PropertyIsLocal @P) :
    RingHom.RespectsIso @P := by
  apply hP.StableUnderComposition.respectsIso
  introv
  letI := e.toRingHom.toAlgebra
  -- Porting note: was `apply_with hP.holds_for_localization_away { instances := ff }`
  have : IsLocalization.Away (1 : R) S := by
    apply IsLocalization.away_of_isUnit_of_bijective _ isUnit_one e.bijective
  exact RingHom.PropertyIsLocal.HoldsForLocalizationAway hP S (1 : R)
#align ring_hom.property_is_local.respects_iso RingHom.PropertyIsLocal.respectsIso

-- Almost all arguments are implicit since this is not intended to use mid-proof.
theorem RingHom.LocalizationPreserves.away (H : RingHom.LocalizationPreserves @P) (r : R)
    [IsLocalization.Away r R'] [IsLocalization.Away (f r) S'] (hf : P f) :
    P (IsLocalization.Away.map R' S' f r) := by
  have : IsLocalization ((Submonoid.powers r).map f) S' := by rw [Submonoid.map_powers]; assumption
  exact H f (Submonoid.powers r) R' S' hf
#align ring_hom.localization_preserves.away RingHom.LocalizationPreserves.away

theorem RingHom.PropertyIsLocal.ofLocalizationSpan (hP : RingHom.PropertyIsLocal @P) :
    RingHom.OfLocalizationSpan @P := by
  introv R hs hs'
  apply_fun Ideal.map f at hs
  rw [Ideal.map_span, Ideal.map_top] at hs
  apply hP.OfLocalizationSpanTarget _ _ hs
  rintro ⟨_, r, hr, rfl⟩
  convert hP.StableUnderComposition
    _ _ (hP.HoldsForLocalizationAway (Localization.Away r) r) (hs' ⟨r, hr⟩) using 1
  exact (IsLocalization.map_comp _).symm
#align ring_hom.property_is_local.of_localization_span RingHom.PropertyIsLocal.ofLocalizationSpan

lemma RingHom.OfLocalizationSpanTarget.ofIsLocalization
    (hP : RingHom.OfLocalizationSpanTarget P) (hP' : RingHom.RespectsIso P)
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (s : Set S) (hs : Ideal.span s = ⊤)
    (hT : ∀ r : s, ∃ (T : Type u) (_ : CommRing T) (_ : Algebra S T)
      (_ : IsLocalization.Away (r : S) T), P ((algebraMap S T).comp f)) : P f := by
  apply hP _ s hs
  intros r
  obtain ⟨T, _, _, _, hT⟩ := hT r
  convert hP'.1 _
    (Localization.algEquiv (R := S) (Submonoid.powers (r : S)) T).symm.toRingEquiv hT
  rw [← RingHom.comp_assoc, RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, Localization.coe_algEquiv_symm, IsLocalization.map_comp,
    RingHom.comp_id]

end RingHom

end Properties

section Ideal

open scoped nonZeroDivisors

/-- Let `I J : Ideal R`. If the localization of `I` at each maximal ideal `P` is included in
the localization of `J` at `P`, then `I ≤ J`. -/
theorem Ideal.le_of_localization_maximal {I J : Ideal R}
    (h : ∀ (P : Ideal R) (hP : P.IsMaximal),
      Ideal.map (algebraMap R (Localization.AtPrime P)) I ≤
        Ideal.map (algebraMap R (Localization.AtPrime P)) J) :
    I ≤ J := by
  intro x hx
  suffices J.colon (Ideal.span {x}) = ⊤ by
    simpa using Submodule.mem_colon.mp
      (show (1 : R) ∈ J.colon (Ideal.span {x}) from this.symm ▸ Submodule.mem_top) x
      (Ideal.mem_span_singleton_self x)
  refine Not.imp_symm (J.colon (Ideal.span {x})).exists_le_maximal ?_
  push_neg
  intro P hP le
  obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, eq⟩ :=
    (IsLocalization.mem_map_algebraMap_iff P.primeCompl _).mp (h P hP (Ideal.mem_map_of_mem _ hx))
  rw [← _root_.map_mul, ← sub_eq_zero, ← map_sub] at eq
  obtain ⟨⟨m, hm⟩, eq⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl _ _).mp eq
  refine hs ((hP.isPrime.mem_or_mem (le (Ideal.mem_colon_singleton.mpr ?_))).resolve_right hm)
  simp only [Subtype.coe_mk, mul_sub, sub_eq_zero, mul_comm x s, mul_left_comm] at eq
  simpa only [mul_assoc, eq] using J.mul_mem_left m ha
#align ideal.le_of_localization_maximal Ideal.le_of_localization_maximal

/-- Let `I J : Ideal R`. If the localization of `I` at each maximal ideal `P` is equal to
the localization of `J` at `P`, then `I = J`. -/
theorem Ideal.eq_of_localization_maximal {I J : Ideal R}
    (h : ∀ (P : Ideal R) (_ : P.IsMaximal),
      Ideal.map (algebraMap R (Localization.AtPrime P)) I =
        Ideal.map (algebraMap R (Localization.AtPrime P)) J) :
    I = J :=
  le_antisymm (Ideal.le_of_localization_maximal fun P hP => (h P hP).le)
    (Ideal.le_of_localization_maximal fun P hP => (h P hP).ge)
#align ideal.eq_of_localization_maximal Ideal.eq_of_localization_maximal

/-- An ideal is trivial if its localization at every maximal ideal is trivial. -/
theorem ideal_eq_bot_of_localization' (I : Ideal R)
    (h : ∀ (J : Ideal R) (hJ : J.IsMaximal),
      Ideal.map (algebraMap R (Localization.AtPrime J)) I = ⊥) :
    I = ⊥ :=
  Ideal.eq_of_localization_maximal fun P hP => by simpa using h P hP
#align ideal_eq_bot_of_localization' ideal_eq_bot_of_localization'

-- TODO: This proof should work for all modules, once we have enough material on submodules of
-- localized modules.
/-- An ideal is trivial if its localization at every maximal ideal is trivial. -/
theorem ideal_eq_bot_of_localization (I : Ideal R)
    (h : ∀ (J : Ideal R) (hJ : J.IsMaximal),
      IsLocalization.coeSubmodule (Localization.AtPrime J) I = ⊥) :
    I = ⊥ :=
  ideal_eq_bot_of_localization' _ fun P hP =>
    (Ideal.map_eq_bot_iff_le_ker _).mpr fun x hx => by
      rw [RingHom.mem_ker, ← Submodule.mem_bot R, ← h P hP, IsLocalization.mem_coeSubmodule]
      exact ⟨x, hx, rfl⟩
#align ideal_eq_bot_of_localization ideal_eq_bot_of_localization

theorem eq_zero_of_localization (r : R)
    (h : ∀ (J : Ideal R) (hJ : J.IsMaximal), algebraMap R (Localization.AtPrime J) r = 0) :
    r = 0 := by
  rw [← Ideal.span_singleton_eq_bot]
  apply ideal_eq_bot_of_localization
  intro J hJ
  delta IsLocalization.coeSubmodule
  erw [Submodule.map_span, Submodule.span_eq_bot]
  rintro _ ⟨_, h', rfl⟩
  cases Set.mem_singleton_iff.mpr h'
  exact h J hJ
#align eq_zero_of_localization eq_zero_of_localization

end Ideal

section Reduced

theorem localization_isReduced : LocalizationPreserves fun R hR => IsReduced R := by
  introv R _ _
  constructor
  rintro x ⟨_ | n, e⟩
  · simpa using congr_arg (· * x) e
  obtain ⟨⟨y, m⟩, hx⟩ := IsLocalization.surj M x
  dsimp only at hx
  let hx' := congr_arg (· ^ n.succ) hx
  simp only [mul_pow, e, zero_mul, ← RingHom.map_pow] at hx'
  rw [← (algebraMap R S).map_zero] at hx'
  obtain ⟨m', hm'⟩ := (IsLocalization.eq_iff_exists M S).mp hx'
  apply_fun (· * (m' : R) ^ n) at hm'
  simp only [mul_assoc, zero_mul, mul_zero] at hm'
  rw [← mul_left_comm, ← pow_succ', ← mul_pow] at hm'
  replace hm' := IsNilpotent.eq_zero ⟨_, hm'.symm⟩
  rw [← (IsLocalization.map_units S m).mul_left_inj, hx, zero_mul,
    IsLocalization.map_eq_zero_iff M]
  exact ⟨m', by rw [← hm', mul_comm]⟩
#align localization_is_reduced localization_isReduced

instance [IsReduced R] : IsReduced (Localization M) :=
  localization_isReduced M _ inferInstance

theorem isReduced_ofLocalizationMaximal : OfLocalizationMaximal fun R hR => IsReduced R := by
  introv R h
  constructor
  intro x hx
  apply eq_zero_of_localization
  intro J hJ
  specialize h J hJ
  exact (hx.map <| algebraMap R <| Localization.AtPrime J).eq_zero
#align is_reduced_of_localization_maximal isReduced_ofLocalizationMaximal

end Reduced

section Surjective

theorem localizationPreserves_surjective :
    RingHom.LocalizationPreserves fun {R S} _ _ f => Function.Surjective f := by
  introv R H x
  obtain ⟨x, ⟨_, s, hs, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (M.map f) x
  obtain ⟨y, rfl⟩ := H x
  use IsLocalization.mk' R' y ⟨s, hs⟩
  rw [IsLocalization.map_mk']
#align localization_preserves_surjective localizationPreserves_surjective

theorem surjective_ofLocalizationSpan :
    RingHom.OfLocalizationSpan fun {R S} _ _ f => Function.Surjective f := by
  introv R e H
  rw [← Set.range_iff_surjective, Set.eq_univ_iff_forall]
  letI := f.toAlgebra
  intro x
  apply Submodule.mem_of_span_eq_top_of_smul_pow_mem
    (LinearMap.range (Algebra.linearMap R S)) s e
  intro r
  obtain ⟨a, e'⟩ := H r (algebraMap _ _ x)
  obtain ⟨b, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (r : R)) a
  erw [IsLocalization.map_mk'] at e'
  rw [eq_comm, IsLocalization.eq_mk'_iff_mul_eq, Subtype.coe_mk, Subtype.coe_mk, ← map_mul] at e'
  obtain ⟨⟨_, n', rfl⟩, e''⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (f r)) _).mp e'
  dsimp only at e''
  rw [mul_comm x, ← mul_assoc, ← map_pow, ← map_mul, ← map_mul, ← pow_add] at e''
  exact ⟨n' + n, _, e''.symm⟩
#align surjective_of_localization_span surjective_ofLocalizationSpan

/-- A surjective ring homomorphism `R →+* S` induces a surjective homomorphism `R_{f⁻¹(P)} →+* S_P`
for every prime ideal `P` of `S`. -/
theorem surjective_localRingHom_of_surjective (h : Function.Surjective f) (P : Ideal S)
    [P.IsPrime] : Function.Surjective (Localization.localRingHom (P.comap f) P f rfl) :=
  have : IsLocalization (Submonoid.map f (Ideal.comap f P).primeCompl) (Localization.AtPrime P) :=
    (Submonoid.map_comap_eq_of_surjective h P.primeCompl).symm ▸ Localization.isLocalization
  localizationPreserves_surjective _ _ _ _ h

end Surjective

section Finite

lemma Module.Finite_of_isLocalization (R S Rₚ Sₚ) [CommSemiring R] [CommRing S] [CommRing Rₚ]
    [CommRing Sₚ] [Algebra R S] [Algebra R Rₚ] [Algebra R Sₚ] [Algebra S Sₚ] [Algebra Rₚ Sₚ]
    [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ] (M : Submonoid R) [IsLocalization M Rₚ]
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₚ] [hRS : Module.Finite R S] :
    Module.Finite Rₚ Sₚ := by
  classical
  have : algebraMap Rₚ Sₚ = IsLocalization.map (T := Algebra.algebraMapSubmonoid S M) Sₚ
      (algebraMap R S) (Submonoid.le_comap_map M) := by
    apply IsLocalization.ringHom_ext M
    simp only [IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq]
  -- We claim that if `S` is generated by `T` as an `R`-module,
  -- then `S'` is generated by `T` as an `R'`-module.
  obtain ⟨T, hT⟩ := hRS
  use T.image (algebraMap S Sₚ)
  rw [eq_top_iff]
  rintro x -
  -- By the hypotheses, for each `x : S'`, we have `x = y / (f r)` for some `y : S` and `r : M`.
  -- Since `S` is generated by `T`, the image of `y` should fall in the span of the image of `T`.
  obtain ⟨y, ⟨_, ⟨r, hr, rfl⟩⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid S M) x
  rw [IsLocalization.mk'_eq_mul_mk'_one, mul_comm, Finset.coe_image]
  have hy : y ∈ Submodule.span R ↑T := by rw [hT]; trivial
  replace hy : algebraMap S Sₚ y ∈ Submodule.map (IsScalarTower.toAlgHom R S Sₚ).toLinearMap
    (Submodule.span R (T : Set S)) := Submodule.mem_map_of_mem
--     -- Note: #8386 had to specify the value of `f` below
      (f := (IsScalarTower.toAlgHom R S Sₚ).toLinearMap) hy
  rw [Submodule.map_span (IsScalarTower.toAlgHom R S Sₚ).toLinearMap T] at hy
  have H : Submodule.span R (algebraMap S Sₚ '' T) ≤
      (Submodule.span Rₚ (algebraMap S Sₚ '' T)).restrictScalars R := by
    rw [Submodule.span_le]; exact Submodule.subset_span
  -- Now, since `y ∈ span T`, and `(f r)⁻¹ ∈ R'`, `x / (f r)` is in `span T` as well.
  convert (Submodule.span Rₚ (algebraMap S Sₚ '' T)).smul_mem
    (IsLocalization.mk' Rₚ (1 : R) ⟨r, hr⟩) (H hy) using 1
  rw [Algebra.smul_def, this, IsLocalization.map_mk', map_one]

/-- If `S` is a finite `R`-algebra, then `S' = M⁻¹S` is a finite `R' = M⁻¹R`-algebra. -/
theorem localization_finite : RingHom.LocalizationPreserves @RingHom.Finite := by
  introv R hf
  letI := f.toAlgebra
  letI := ((algebraMap S S').comp f).toAlgebra
  let f' : R' →+* S' := IsLocalization.map S' f (Submonoid.le_comap_map M)
  letI := f'.toAlgebra
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq'
    (IsLocalization.map_comp M.le_comap_map).symm
  have : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsLocalization (Algebra.algebraMapSubmonoid S M) S' := by
    rwa [Algebra.algebraMapSubmonoid, RingHom.algebraMap_toAlgebra]
  have : Module.Finite R S := hf
  apply Module.Finite_of_isLocalization R S R' S' M
#align localization_finite localization_finite

theorem localization_away_map_finite (r : R) [IsLocalization.Away r R']
    [IsLocalization.Away (f r) S'] (hf : f.Finite) : (IsLocalization.Away.map R' S' f r).Finite :=
  localization_finite.away r hf
#align localization_away_map_finite localization_away_map_finite

/-- Let `S` be an `R`-algebra, `M` a submonoid of `R`, and `S' = M⁻¹S`.
If the image of some `x : S` falls in the span of some finite `s ⊆ S'` over `R`,
then there exists some `m : M` such that `m • x` falls in the
span of `IsLocalization.finsetIntegerMultiple _ s` over `R`.
-/
theorem IsLocalization.smul_mem_finsetIntegerMultiple_span [Algebra R S] [Algebra R S']
    [IsScalarTower R S S'] [IsLocalization (M.map (algebraMap R S)) S'] (x : S) (s : Finset S')
    (hx : algebraMap S S' x ∈ Submodule.span R (s : Set S')) :
    ∃ m : M, m • x ∈
      Submodule.span R
        (IsLocalization.finsetIntegerMultiple (M.map (algebraMap R S)) s : Set S) := by
  let g : S →ₐ[R] S' :=
    AlgHom.mk' (algebraMap S S') fun c x => by simp [Algebra.algebraMap_eq_smul_one]
  -- We first obtain the `y' ∈ M` such that `s' = y' • s` is falls in the image of `S` in `S'`.
  let y := IsLocalization.commonDenomOfFinset (M.map (algebraMap R S)) s
  have hx₁ : (y : S) • (s : Set S') = g '' _ :=
    (IsLocalization.finsetIntegerMultiple_image _ s).symm
  obtain ⟨y', hy', e : algebraMap R S y' = y⟩ := y.prop
  have : algebraMap R S y' • (s : Set S') = y' • (s : Set S') := by
    simp_rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
  rw [← e, this] at hx₁
  replace hx₁ := congr_arg (Submodule.span R) hx₁
  rw [Submodule.span_smul] at hx₁
  replace hx : _ ∈ y' • Submodule.span R (s : Set S') := Set.smul_mem_smul_set hx
  rw [hx₁] at hx
  erw [← g.map_smul, ← Submodule.map_span (g : S →ₗ[R] S')] at hx
  -- Since `x` falls in the span of `s` in `S'`, `y' • x : S` falls in the span of `s'` in `S'`.
  -- That is, there exists some `x' : S` in the span of `s'` in `S` and `x' = y' • x` in `S'`.
  -- Thus `a • (y' • x) = a • x' ∈ span s'` in `S` for some `a ∈ M`.
  obtain ⟨x', hx', hx'' : algebraMap _ _ _ = _⟩ := hx
  obtain ⟨⟨_, a, ha₁, rfl⟩, ha₂⟩ :=
    (IsLocalization.eq_iff_exists (M.map (algebraMap R S)) S').mp hx''
  use (⟨a, ha₁⟩ : M) * (⟨y', hy'⟩ : M)
  convert (Submodule.span R
    (IsLocalization.finsetIntegerMultiple (Submonoid.map (algebraMap R S) M) s : Set S)).smul_mem
      a hx' using 1
  convert ha₂.symm using 1
  · rw [Subtype.coe_mk, Submonoid.smul_def, Submonoid.coe_mul, ← smul_smul]
    exact Algebra.smul_def _ _
  · exact Algebra.smul_def _ _
#align is_localization.smul_mem_finset_integer_multiple_span IsLocalization.smul_mem_finsetIntegerMultiple_span

/-- If `S` is an `R' = M⁻¹R` algebra, and `x ∈ span R' s`,
then `t • x ∈ span R s` for some `t : M`. -/
theorem multiple_mem_span_of_mem_localization_span [Algebra R' S] [Algebra R S]
    [IsScalarTower R R' S] [IsLocalization M R'] (s : Set S) (x : S)
    (hx : x ∈ Submodule.span R' s) : ∃ t : M, t • x ∈ Submodule.span R s := by
  obtain ⟨s', hss', hs'⟩ := Submodule.mem_span_finite_of_mem_span hx
  rsuffices ⟨t, ht⟩ : ∃ t : M, t • x ∈ Submodule.span R (s' : Set S)
  · exact ⟨t, Submodule.span_mono hss' ht⟩
  clear hx hss' s
  induction s' using Finset.induction_on generalizing x
  · use 1; simpa using hs'
  rename_i a s _ hs
  simp only [Finset.coe_insert, Finset.image_insert, Finset.coe_image, Subtype.coe_mk,
    Submodule.mem_span_insert] at hs' ⊢
  rcases hs' with ⟨y, z, hz, rfl⟩
  rcases IsLocalization.surj M y with ⟨⟨y', s'⟩, e⟩
  replace e : _ * a = _ * a := (congr_arg (fun x => algebraMap R' S x * a) e : _)
  simp_rw [RingHom.map_mul, ← IsScalarTower.algebraMap_apply, mul_comm (algebraMap R' S y),
    mul_assoc, ← Algebra.smul_def] at e
  rcases hs _ hz with ⟨t, ht⟩
  refine ⟨t * s', t * y', _, (Submodule.span R (s : Set S)).smul_mem s' ht, ?_⟩
  rw [smul_add, ← smul_smul, mul_comm, ← smul_smul, ← smul_smul, ← e]
  rfl
#align multiple_mem_span_of_mem_localization_span multiple_mem_span_of_mem_localization_span

/-- If `S` is an `R' = M⁻¹R` algebra, and `x ∈ adjoin R' s`,
then `t • x ∈ adjoin R s` for some `t : M`. -/
theorem multiple_mem_adjoin_of_mem_localization_adjoin [Algebra R' S] [Algebra R S]
    [IsScalarTower R R' S] [IsLocalization M R'] (s : Set S) (x : S)
    (hx : x ∈ Algebra.adjoin R' s) : ∃ t : M, t • x ∈ Algebra.adjoin R s := by
  change ∃ t : M, t • x ∈ Subalgebra.toSubmodule (Algebra.adjoin R s)
  change x ∈ Subalgebra.toSubmodule (Algebra.adjoin R' s) at hx
  simp_rw [Algebra.adjoin_eq_span] at hx ⊢
  exact multiple_mem_span_of_mem_localization_span M R' _ _ hx
#align multiple_mem_adjoin_of_mem_localization_adjoin multiple_mem_adjoin_of_mem_localization_adjoin

theorem finite_ofLocalizationSpan : RingHom.OfLocalizationSpan @RingHom.Finite := by
  rw [RingHom.ofLocalizationSpan_iff_finite]
  introv R hs H
  -- We first setup the instances
  letI := f.toAlgebra
  letI := fun r : s => (Localization.awayMap f r).toAlgebra
  have : ∀ r : s,
      IsLocalization ((Submonoid.powers (r : R)).map (algebraMap R S)) (Localization.Away (f r)) :=
    by intro r; rw [Submonoid.map_powers]; exact Localization.isLocalization
  haveI : ∀ r : s, IsScalarTower R (Localization.Away (r : R)) (Localization.Away (f r)) :=
    fun r => IsScalarTower.of_algebraMap_eq'
      (IsLocalization.map_comp (Submonoid.powers (r : R)).le_comap_map).symm
  -- By the hypothesis, we may find a finite generating set for each `Sᵣ`. This set can then be
  -- lifted into `R` by multiplying a sufficiently large power of `r`. I claim that the union of
  -- these generates `S`.
  constructor
  replace H := fun r => (H r).1
  choose s₁ s₂ using H
  let sf := fun x : s => IsLocalization.finsetIntegerMultiple (Submonoid.powers (f x)) (s₁ x)
  use s.attach.biUnion sf
  rw [Submodule.span_attach_biUnion, eq_top_iff]
  -- It suffices to show that `r ^ n • x ∈ span T` for each `r : s`, since `{ r ^ n }` spans `R`.
  -- This then follows from the fact that each `x : R` is a linear combination of the generating set
  -- of `Sᵣ`. By multiplying a sufficiently large power of `r`, we can cancel out the `r`s in the
  -- denominators of both the generating set and the coefficients.
  rintro x -
  apply Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (s : Set R) hs _ _
  intro r
  obtain ⟨⟨_, n₁, rfl⟩, hn₁⟩ :=
    multiple_mem_span_of_mem_localization_span (Submonoid.powers (r : R))
      (Localization.Away (r : R)) (s₁ r : Set (Localization.Away (f r))) (algebraMap S _ x)
      (by rw [s₂ r]; trivial)
  dsimp only at hn₁
  rw [Submonoid.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply R S, ← map_mul] at hn₁
  obtain ⟨⟨_, n₂, rfl⟩, hn₂⟩ :=
    IsLocalization.smul_mem_finsetIntegerMultiple_span (Submonoid.powers (r : R))
      (Localization.Away (f r)) _ (s₁ r) hn₁
  rw [Submonoid.smul_def, ← Algebra.smul_def, smul_smul, Subtype.coe_mk, ← pow_add] at hn₂
  simp_rw [Submonoid.map_powers] at hn₂
  use n₂ + n₁
  exact le_iSup (fun x : s => Submodule.span R (sf x : Set S)) r hn₂
#align finite_of_localization_span finite_ofLocalizationSpan

end Finite

section FiniteType

theorem localization_finiteType : RingHom.LocalizationPreserves @RingHom.FiniteType := by
  introv R hf
  -- mirrors the proof of `localization_map_finite`
  letI := f.toAlgebra
  letI := ((algebraMap S S').comp f).toAlgebra
  let f' : R' →+* S' := IsLocalization.map S' f (Submonoid.le_comap_map M)
  letI := f'.toAlgebra
  haveI : IsScalarTower R R' S' :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.map_comp M.le_comap_map).symm
  let fₐ : S →ₐ[R] S' := AlgHom.mk' (algebraMap S S') fun c x => RingHom.map_mul _ _ _
  obtain ⟨T, hT⟩ := id hf
  use T.image (algebraMap S S')
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, ⟨_, ⟨r, hr, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (M.map f) x
  rw [IsLocalization.mk'_eq_mul_mk'_one, mul_comm, Finset.coe_image]
  have hy : y ∈ Algebra.adjoin R (T : Set S) := by rw [hT]; trivial
  replace hy : algebraMap S S' y ∈ (Algebra.adjoin R (T : Set S)).map fₐ :=
    Subalgebra.mem_map.mpr ⟨_, hy, rfl⟩
  rw [fₐ.map_adjoin T] at hy
  have H : Algebra.adjoin R (algebraMap S S' '' T) ≤
      (Algebra.adjoin R' (algebraMap S S' '' T)).restrictScalars R := by
    rw [Algebra.adjoin_le_iff]; exact Algebra.subset_adjoin
  convert (Algebra.adjoin R' (algebraMap S S' '' T)).smul_mem (H hy)
    (IsLocalization.mk' R' (1 : R) ⟨r, hr⟩) using 1
  rw [Algebra.smul_def]
  erw [IsLocalization.map_mk' M.le_comap_map]
  rw [map_one]
#align localization_finite_type localization_finiteType

theorem localization_away_map_finiteType (r : R) [IsLocalization.Away r R']
    [IsLocalization.Away (f r) S'] (hf : f.FiniteType) :
    (IsLocalization.Away.map R' S' f r).FiniteType :=
  localization_finiteType.away r hf
#align localization_away_map_finite_type localization_away_map_finiteType

variable {S'}

/-- Let `S` be an `R`-algebra, `M` a submonoid of `S`, `S' = M⁻¹S`.
Suppose the image of some `x : S` falls in the adjoin of some finite `s ⊆ S'` over `R`,
and `A` is an `R`-subalgebra of `S` containing both `M` and the numerators of `s`.
Then, there exists some `m : M` such that `m • x` falls in `A`.
-/
theorem IsLocalization.exists_smul_mem_of_mem_adjoin [Algebra R S] [Algebra R S']
    [IsScalarTower R S S'] (M : Submonoid S) [IsLocalization M S'] (x : S) (s : Finset S')
    (A : Subalgebra R S) (hA₁ : (IsLocalization.finsetIntegerMultiple M s : Set S) ⊆ A)
    (hA₂ : M ≤ A.toSubmonoid) (hx : algebraMap S S' x ∈ Algebra.adjoin R (s : Set S')) :
    ∃ m : M, m • x ∈ A := by
  let g : S →ₐ[R] S' := IsScalarTower.toAlgHom R S S'
  let y := IsLocalization.commonDenomOfFinset M s
  have hx₁ : (y : S) • (s : Set S') = g '' _ :=
    (IsLocalization.finsetIntegerMultiple_image _ s).symm
  obtain ⟨n, hn⟩ :=
    Algebra.pow_smul_mem_of_smul_subset_of_mem_adjoin (y : S) (s : Set S') (A.map g)
      (by rw [hx₁]; exact Set.image_subset _ hA₁) hx (Set.mem_image_of_mem _ (hA₂ y.2))
  obtain ⟨x', hx', hx''⟩ := hn n (le_of_eq rfl)
  rw [Algebra.smul_def, ← _root_.map_mul] at hx''
  obtain ⟨a, ha₂⟩ := (IsLocalization.eq_iff_exists M S').mp hx''
  use a * y ^ n
  convert A.mul_mem hx' (hA₂ a.prop) using 1
  rw [Submonoid.smul_def, smul_eq_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow, mul_assoc, ← ha₂,
    mul_comm]
#align is_localization.exists_smul_mem_of_mem_adjoin IsLocalization.exists_smul_mem_of_mem_adjoin

/-- Let `S` be an `R`-algebra, `M` a submonoid of `R`, and `S' = M⁻¹S`.
If the image of some `x : S` falls in the adjoin of some finite `s ⊆ S'` over `R`,
then there exists some `m : M` such that `m • x` falls in the
adjoin of `IsLocalization.finsetIntegerMultiple _ s` over `R`.
-/
theorem IsLocalization.lift_mem_adjoin_finsetIntegerMultiple [Algebra R S] [Algebra R S']
    [IsScalarTower R S S'] [IsLocalization (M.map (algebraMap R S)) S'] (x : S) (s : Finset S')
    (hx : algebraMap S S' x ∈ Algebra.adjoin R (s : Set S')) :
    ∃ m : M, m • x ∈
      Algebra.adjoin R
        (IsLocalization.finsetIntegerMultiple (M.map (algebraMap R S)) s : Set S) := by
  obtain ⟨⟨_, a, ha, rfl⟩, e⟩ :=
    IsLocalization.exists_smul_mem_of_mem_adjoin (M.map (algebraMap R S)) x s (Algebra.adjoin R _)
      Algebra.subset_adjoin (by rintro _ ⟨a, _, rfl⟩; exact Subalgebra.algebraMap_mem _ a) hx
  refine ⟨⟨a, ha⟩, ?_⟩
  simpa only [Submonoid.smul_def, algebraMap_smul] using e
#align is_localization.lift_mem_adjoin_finset_integer_multiple IsLocalization.lift_mem_adjoin_finsetIntegerMultiple

theorem finiteType_ofLocalizationSpan : RingHom.OfLocalizationSpan @RingHom.FiniteType := by
  rw [RingHom.ofLocalizationSpan_iff_finite]
  introv R hs H
  -- mirrors the proof of `finite_ofLocalizationSpan`
  letI := f.toAlgebra
  letI := fun r : s => (Localization.awayMap f r).toAlgebra
  have : ∀ r : s,
      IsLocalization ((Submonoid.powers (r : R)).map (algebraMap R S)) (Localization.Away (f r)) :=
    by intro r; rw [Submonoid.map_powers]; exact Localization.isLocalization
  haveI : ∀ r : s, IsScalarTower R (Localization.Away (r : R)) (Localization.Away (f r)) :=
    fun r => IsScalarTower.of_algebraMap_eq'
      (IsLocalization.map_comp (Submonoid.powers (r : R)).le_comap_map).symm
  constructor
  replace H := fun r => (H r).1
  choose s₁ s₂ using H
  let sf := fun x : s => IsLocalization.finsetIntegerMultiple (Submonoid.powers (f x)) (s₁ x)
  use s.attach.biUnion sf
  convert (Algebra.adjoin_attach_biUnion (R := R) sf).trans _
  rw [eq_top_iff]
  rintro x -
  apply (⨆ x : s, Algebra.adjoin R (sf x : Set S)).toSubmodule.mem_of_span_eq_top_of_smul_pow_mem
    _ hs _ _
  intro r
  obtain ⟨⟨_, n₁, rfl⟩, hn₁⟩ :=
    multiple_mem_adjoin_of_mem_localization_adjoin (Submonoid.powers (r : R))
      (Localization.Away (r : R)) (s₁ r : Set (Localization.Away (f r)))
      (algebraMap S (Localization.Away (f r)) x) (by rw [s₂ r]; trivial)
  rw [Submonoid.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply R S, ← map_mul] at hn₁
  obtain ⟨⟨_, n₂, rfl⟩, hn₂⟩ :=
    IsLocalization.lift_mem_adjoin_finsetIntegerMultiple (Submonoid.powers (r : R)) _ (s₁ r) hn₁
  rw [Submonoid.smul_def, ← Algebra.smul_def, smul_smul, Subtype.coe_mk, ← pow_add] at hn₂
  simp_rw [Submonoid.map_powers] at hn₂
  use n₂ + n₁
  exact le_iSup (fun x : s => Algebra.adjoin R (sf x : Set S)) r hn₂
#align finite_type_of_localization_span finiteType_ofLocalizationSpan

end FiniteType
