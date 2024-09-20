/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.RingHomProperties

/-!
# Local properties of commutative rings

In this file, we define local properties in general.

## Naming Conventions

* `localization_P` : `P` holds for `S⁻¹R` if `P` holds for `R`.
* `P_of_localization_maximal` : `P` holds for `R` if `P` holds for `Rₘ` for all maximal `m`.
* `P_of_localization_prime` : `P` holds for `R` if `P` holds for `Rₘ` for all prime `m`.
* `P_ofLocalizationSpan` : `P` holds for `R` if given a spanning set `{fᵢ}`, `P` holds for all
  `R_{fᵢ}`.

## Main definitions

* `LocalizationPreserves` : A property `P` of comm rings is said to be preserved by localization
  if `P` holds for `M⁻¹R` whenever `P` holds for `R`.
* `OfLocalizationMaximal` : A property `P` of comm rings satisfies `OfLocalizationMaximal`
  if `P` holds for `R` whenever `P` holds for `Rₘ` for all maximal ideal `m`.
* `RingHom.LocalizationPreserves` : A property `P` of ring homs is said to be preserved by
  localization if `P` holds for `M⁻¹R →+* M⁻¹S` whenever `P` holds for `R →+* S`.
* `RingHom.OfLocalizationSpan` : A property `P` of ring homs satisfies
  `RingHom.OfLocalizationSpan` if `P` holds for `R →+* S` whenever there exists a
  set `{ r }` that spans `R` such that `P` holds for `Rᵣ →+* Sᵣ`.

## Main results

* The triviality of an ideal or an element:
  `ideal_eq_bot_of_localization`, `eq_zero_of_localization`

-/

open scoped Pointwise Classical

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (M : Submonoid R) (f : R →+* S)
variable (N : Submonoid S) (R' S' : Type u) [CommRing R'] [CommRing S']
variable [Algebra R R'] [Algebra S S']

section Properties

section CommRing

variable (P : ∀ (R : Type u) [CommRing R], Prop)

/-- A property `P` of comm rings is said to be preserved by localization
  if `P` holds for `M⁻¹R` whenever `P` holds for `R`. -/
def LocalizationPreserves : Prop :=
  ∀ {R : Type u} [hR : CommRing R] (M : Submonoid R) (S : Type u) [hS : CommRing S] [Algebra R S]
    [IsLocalization M S], @P R hR → @P S hS

/-- A property `P` of comm rings satisfies `OfLocalizationMaximal`
  if `P` holds for `R` whenever `P` holds for `Rₘ` for all maximal ideal `m`. -/
def OfLocalizationMaximal : Prop :=
  ∀ (R : Type u) [CommRing R],
    (∀ (J : Ideal R) (_ : J.IsMaximal), P (Localization.AtPrime J)) → P R

end CommRing

section RingHom

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S] (_ : R →+* S), Prop)

/-- A property `P` of ring homs is said to contain identities if `P` holds
for the identity homomorphism of every ring. -/
def RingHom.ContainsIdentities := ∀ (R : Type u) [CommRing R], P (RingHom.id R)

/-- A property `P` of ring homs is said to be preserved by localization
 if `P` holds for `M⁻¹R →+* M⁻¹S` whenever `P` holds for `R →+* S`. -/
def RingHom.LocalizationPreserves :=
  ∀ ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R →+* S) (M : Submonoid R) (R' S' : Type u)
    [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S'] [IsLocalization M R']
    [IsLocalization (M.map f) S'],
    P f → P (IsLocalization.map S' f (Submonoid.le_comap_map M) : R' →+* S')

/-- A property `P` of ring homs satisfies `RingHom.OfLocalizationFiniteSpan`
if `P` holds for `R →+* S` whenever there exists a finite set `{ r }` that spans `R` such that
`P` holds for `Rᵣ →+* Sᵣ`.

Note that this is equivalent to `RingHom.OfLocalizationSpan` via
`RingHom.ofLocalizationSpan_iff_finite`, but this is easier to prove. -/
def RingHom.OfLocalizationFiniteSpan :=
  ∀ ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R →+* S) (s : Finset R)
    (_ : Ideal.span (s : Set R) = ⊤) (_ : ∀ r : s, P (Localization.awayMap f r)), P f

/-- A property `P` of ring homs satisfies `RingHom.OfLocalizationFiniteSpan`
if `P` holds for `R →+* S` whenever there exists a set `{ r }` that spans `R` such that
`P` holds for `Rᵣ →+* Sᵣ`.

Note that this is equivalent to `RingHom.OfLocalizationFiniteSpan` via
`RingHom.ofLocalizationSpan_iff_finite`, but this has less restrictions when applying. -/
def RingHom.OfLocalizationSpan :=
  ∀ ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R →+* S) (s : Set R) (_ : Ideal.span s = ⊤)
    (_ : ∀ r : s, P (Localization.awayMap f r)), P f

/-- A property `P` of ring homs satisfies `RingHom.HoldsForLocalizationAway`
 if `P` holds for each localization map `R →+* Rᵣ`. -/
def RingHom.HoldsForLocalizationAway : Prop :=
  ∀ ⦃R : Type u⦄ (S : Type u) [CommRing R] [CommRing S] [Algebra R S] (r : R)
    [IsLocalization.Away r S], P (algebraMap R S)

/-- A property `P` of ring homs satisfies `RingHom.StableUnderCompositionWithLocalizationAway`
if whenever `P` holds for `f` it also holds for the composition with
localization maps on the left and on the right. -/
def RingHom.StableUnderCompositionWithLocalizationAway : Prop :=
  (∀ ⦃R S : Type u⦄ (T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra S T] (s : S)
    [IsLocalization.Away s T] (f : R →+* S), P f → P ((algebraMap S T).comp f)) ∧
    ∀ ⦃R : Type u⦄ (S : Type u) ⦃T : Type u⦄ [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
      (r : R) [IsLocalization.Away r S] (f : S →+* T), P f → P (f.comp (algebraMap R S))

/-- A property `P` of ring homs satisfies `RingHom.OfLocalizationFiniteSpanTarget`
if `P` holds for `R →+* S` whenever there exists a finite set `{ r }` that spans `S` such that
`P` holds for `R →+* Sᵣ`.

Note that this is equivalent to `RingHom.OfLocalizationSpanTarget` via
`RingHom.ofLocalizationSpanTarget_iff_finite`, but this is easier to prove. -/
def RingHom.OfLocalizationFiniteSpanTarget : Prop :=
  ∀ ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R →+* S) (s : Finset S)
    (_ : Ideal.span (s : Set S) = ⊤)
    (_ : ∀ r : s, P ((algebraMap S (Localization.Away (r : S))).comp f)), P f

/-- A property `P` of ring homs satisfies `RingHom.OfLocalizationSpanTarget`
if `P` holds for `R →+* S` whenever there exists a set `{ r }` that spans `S` such that
`P` holds for `R →+* Sᵣ`.

Note that this is equivalent to `RingHom.OfLocalizationFiniteSpanTarget` via
`RingHom.ofLocalizationSpanTarget_iff_finite`, but this has less restrictions when applying. -/
def RingHom.OfLocalizationSpanTarget : Prop :=
  ∀ ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R →+* S) (s : Set S) (_ : Ideal.span s = ⊤)
    (_ : ∀ r : s, P ((algebraMap S (Localization.Away (r : S))).comp f)), P f

/-- A property `P` of ring homs satisfies `RingHom.OfLocalizationPrime`
if `P` holds for `R` whenever `P` holds for `Rₘ` for all prime ideals `p`. -/
def RingHom.OfLocalizationPrime : Prop :=
  ∀ ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R →+* S),
    (∀ (J : Ideal S) (_ : J.IsPrime), P (Localization.localRingHom _ J f rfl)) → P f

/-- A property of ring homs is local if it is preserved by localizations and compositions, and for
each `{ r }` that spans `S`, we have `P (R →+* S) ↔ ∀ r, P (R →+* Sᵣ)`. -/
structure RingHom.PropertyIsLocal : Prop where
  LocalizationPreserves : RingHom.LocalizationPreserves @P
  OfLocalizationSpanTarget : RingHom.OfLocalizationSpanTarget @P
  StableUnderCompositionWithLocalizationAway : RingHom.StableUnderCompositionWithLocalizationAway @P

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

theorem RingHom.HoldsForLocalizationAway.of_bijective
    (H : RingHom.HoldsForLocalizationAway P) (hf : Function.Bijective f) :
    P f := by
  letI := f.toAlgebra
  have := IsLocalization.at_units (.powers (1 : R)) (by simp)
  have := IsLocalization.isLocalization_of_algEquiv (.powers (1 : R))
    (AlgEquiv.ofBijective (Algebra.ofId R S) hf)
  exact H _ 1

variable {P f R' S'}

lemma RingHom.StableUnderComposition.stableUnderCompositionWithLocalizationAway
    (hPc : RingHom.StableUnderComposition P) (hPl : HoldsForLocalizationAway P) :
    StableUnderCompositionWithLocalizationAway P := by
  constructor
  · introv _ hf
    exact hPc _ _ hf (hPl T s)
  · introv _ hf
    exact hPc _ _ (hPl S r) hf

lemma RingHom.HoldsForLocalizationAway.containsIdentities (hPl : HoldsForLocalizationAway P) :
    ContainsIdentities P := by
  introv R
  exact hPl.of_bijective _ _ Function.bijective_id

theorem RingHom.PropertyIsLocal.respectsIso (hP : RingHom.PropertyIsLocal @P) :
    RingHom.RespectsIso @P := by
  constructor
  · intro R S T _ _ _ f e hf
    letI := e.toRingHom.toAlgebra
    have : IsLocalization.Away (1 : S) T :=
      IsLocalization.away_of_isUnit_of_bijective _ isUnit_one e.bijective
    exact hP.StableUnderCompositionWithLocalizationAway.left T (1 : S) f hf
  · intro R S T _ _ _ f e hf
    letI := e.toRingHom.toAlgebra
    have : IsLocalization.Away (1 : R) S :=
      IsLocalization.away_of_isUnit_of_bijective _ isUnit_one e.bijective
    exact hP.StableUnderCompositionWithLocalizationAway.right S (1 : R) f hf

-- Almost all arguments are implicit since this is not intended to use mid-proof.
theorem RingHom.LocalizationPreserves.away (H : RingHom.LocalizationPreserves @P) (r : R)
    [IsLocalization.Away r R'] [IsLocalization.Away (f r) S'] (hf : P f) :
    P (IsLocalization.Away.map R' S' f r) := by
  have : IsLocalization ((Submonoid.powers r).map f) S' := by rw [Submonoid.map_powers]; assumption
  exact H f (Submonoid.powers r) R' S' hf

lemma RingHom.PropertyIsLocal.HoldsForLocalizationAway (hP : RingHom.PropertyIsLocal @P)
    (hPi : ContainsIdentities P) :
    RingHom.HoldsForLocalizationAway @P := by
  introv R _
  have : algebraMap R S = (algebraMap R S).comp (RingHom.id R) := by simp
  rw [this]
  apply (hP.StableUnderCompositionWithLocalizationAway).left S r
  apply hPi

theorem RingHom.PropertyIsLocal.ofLocalizationSpan (hP : RingHom.PropertyIsLocal @P) :
    RingHom.OfLocalizationSpan @P := by
  introv R hs hs'
  apply_fun Ideal.map f at hs
  rw [Ideal.map_span, Ideal.map_top] at hs
  apply hP.OfLocalizationSpanTarget _ _ hs
  rintro ⟨_, r, hr, rfl⟩
  rw [← IsLocalization.map_comp (M := Submonoid.powers r) (S := Localization.Away r)
    (T := Submonoid.powers (f r))]
  apply hP.StableUnderCompositionWithLocalizationAway.right _ r
  exact hs' ⟨r, hr⟩

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

/-- Let `I J : Ideal R`. If the localization of `I` at each maximal ideal `P` is equal to
the localization of `J` at `P`, then `I = J`. -/
theorem Ideal.eq_of_localization_maximal {I J : Ideal R}
    (h : ∀ (P : Ideal R) (_ : P.IsMaximal),
      Ideal.map (algebraMap R (Localization.AtPrime P)) I =
        Ideal.map (algebraMap R (Localization.AtPrime P)) J) :
    I = J :=
  le_antisymm (Ideal.le_of_localization_maximal fun P hP => (h P hP).le)
    (Ideal.le_of_localization_maximal fun P hP => (h P hP).ge)

/-- An ideal is trivial if its localization at every maximal ideal is trivial. -/
theorem ideal_eq_bot_of_localization' (I : Ideal R)
    (h : ∀ (J : Ideal R) (hJ : J.IsMaximal),
      Ideal.map (algebraMap R (Localization.AtPrime J)) I = ⊥) :
    I = ⊥ :=
  Ideal.eq_of_localization_maximal fun P hP => by simpa using h P hP

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

end Ideal
