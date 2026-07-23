/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.RingHomProperties

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

@[expose] public section

open scoped Pointwise

universe u

section Properties

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
variable (R' S' : Type u) [CommRing R'] [CommRing S']
variable [Algebra R R'] [Algebra S S']

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

/-- A property `P` of ring homs is said to be preserved by localization away
if `P` holds for `Rᵣ →+* Sᵣ` whenever `P` holds for `R →+* S`. -/
def RingHom.LocalizationAwayPreserves :=
  ∀ ⦃R S : Type u⦄ [CommRing R] [CommRing S] (f : R →+* S) (r : R) (R' S' : Type u)
    [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S'] [IsLocalization.Away r R']
    [IsLocalization.Away (f r) S'],
    P f → P (IsLocalization.Away.map R' S' f r : R' →+* S')

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

/-- A property `P` of ring homs satisfies `RingHom.HoldsForLocalization`
if `P` holds for each localization map `R →+* M⁻¹R`. -/
def RingHom.HoldsForLocalization : Prop :=
  ∀ ⦃R : Type u⦄ (S : Type u) [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R)
    [IsLocalization M S], P (algebraMap R S)

/-- A property `P` of ring homs satisfies `RingHom.HoldsForLocalizationAway`
if `P` holds for each localization map `R →+* Rᵣ`. -/
def RingHom.HoldsForLocalizationAway : Prop :=
  ∀ ⦃R : Type u⦄ (S : Type u) [CommRing R] [CommRing S] [Algebra R S] (r : R)
    [IsLocalization.Away r S], P (algebraMap R S)

/-- A property `P` of ring homs satisfies `RingHom.StableUnderCompositionWithLocalizationAwaySource`
if whenever `P` holds for `f` it also holds for the composition with
localization maps on the source. -/
def RingHom.StableUnderCompositionWithLocalizationAwaySource : Prop :=
  ∀ ⦃R : Type u⦄ (S : Type u) ⦃T : Type u⦄ [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    (r : R) [IsLocalization.Away r S] (f : S →+* T), P f → P (f.comp (algebraMap R S))

/-- A property `P` of ring homs satisfies `RingHom.StableUnderCompositionWithLocalizationAway`
if whenever `P` holds for `f` it also holds for the composition with
localization maps on the target. -/
def RingHom.StableUnderCompositionWithLocalizationAwayTarget : Prop :=
  ∀ ⦃R S : Type u⦄ (T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra S T] (s : S)
    [IsLocalization.Away s T] (f : R →+* S), P f → P ((algebraMap S T).comp f)

/-- A property `P` of ring homs satisfies `RingHom.StableUnderCompositionWithLocalizationAway`
if whenever `P` holds for `f` it also holds for the composition with
localization maps on the left and on the right. -/
def RingHom.StableUnderCompositionWithLocalizationAway : Prop :=
  StableUnderCompositionWithLocalizationAwaySource P ∧
    StableUnderCompositionWithLocalizationAwayTarget P

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
  localizationAwayPreserves : RingHom.LocalizationAwayPreserves @P
  ofLocalizationSpanTarget : RingHom.OfLocalizationSpanTarget @P
  ofLocalizationSpan : RingHom.OfLocalizationSpan @P
  StableUnderCompositionWithLocalizationAwayTarget :
    RingHom.StableUnderCompositionWithLocalizationAwayTarget @P

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

open TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
lemma RingHom.OfLocalizationSpan.mk (hP : RingHom.RespectsIso P)
    (H : ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (s : Set R),
      Ideal.span s = ⊤ →
      (∀ r ∈ s, P (algebraMap (Localization.Away r) (Localization.Away r ⊗[R] S))) →
      P (algebraMap R S)) :
    OfLocalizationSpan P := by
  introv R hs hf
  algebraize [f]
  let _ := fun r : R => (Localization.awayMap (algebraMap R S) r).toAlgebra
  refine H s hs (fun r hr ↦ ?_)
  have : algebraMap (Localization.Away r) (Localization.Away r ⊗[R] S) =
      ((IsLocalization.Away.tensorRightEquiv S r (Localization.Away r)).symm : _ →+* _).comp
        (algebraMap (Localization.Away r) (Localization.Away (algebraMap R S r))) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext
    simp [RingHom.algebraMap_toAlgebra, Localization.awayMap, IsLocalization.Away.map,
      Algebra.TensorProduct.tmul_one_eq_one_tmul, RingHom.algebraMap_toAlgebra]
  rw [this]
  exact hP.1 _ _ (hf ⟨r, hr⟩)

section HoldsForLocalization

variable {P}

lemma RingHom.HoldsForLocalization.mk (hP : RespectsIso P)
    (H : ∀ {R : Type u} [CommRing R] (M : Submonoid R), P (algebraMap R (Localization M))) :
    HoldsForLocalization P := by
  introv R _
  rw [← (IsLocalization.algEquiv M (Localization M) S).toAlgHom.comp_algebraMap]
  exact hP.1 _ _ (H _)

lemma RingHom.HoldsForLocalization.holdsForLocalizationAway (hP : HoldsForLocalization P) :
    HoldsForLocalizationAway P :=
  fun _ _ _ _ _ r _ ↦ hP _ (Submonoid.powers r)

lemma RingHom.HoldsForLocalization.isLocalizationMap
    (hPc : StableUnderComposition P) (hPp : LocalizationPreserves P)
    (hPl : HoldsForLocalization P)
    {M : Submonoid R} {T : Submonoid S}
    {R' : Type u} [CommRing R'] [Algebra R R'] [IsLocalization M R']
    (S' : Type u) [CommRing S'] [Algebra S S'] [IsLocalization T S']
    {f : R →+* S} (hy : M ≤ Submonoid.comap f T) (hf : P f) :
    P (IsLocalization.map (S := R') S' f hy) := by
  have hle : Submonoid.map f M ≤ T := by simpa [Submonoid.map_le_iff_le_comap]
  let : Algebra (Localization (M.map f)) S' :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (M.map f) T hle
  have : IsScalarTower S (Localization (Submonoid.map f M)) S' :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ _
  have : IsLocalization (T.map (algebraMap S (Localization (M.map f)))) S' :=
    IsLocalization.isLocalization_of_submonoid_le _ _ (M.map f) T hle
  have heq : IsLocalization.map (S := R') S' f hy =
      (algebraMap _ _).comp
        (IsLocalization.map (M := M) (T := M.map f) (S := R') (Localization (M.map f)) f
          (M.le_comap_map)) := by
    apply IsLocalization.ringHom_ext M
    ext
    simp [← IsScalarTower.algebraMap_apply]
  rw [heq]
  exact hPc _ _ (hPp _ _ _ _ hf) (hPl _ (T.map (algebraMap S (Localization (M.map f)))))

lemma RingHom.HoldsForLocalization.localRingHom (hPc : StableUnderComposition P)
    (hPp : LocalizationPreserves P) (hPl : HoldsForLocalization P)
    {R S : Type u} [CommRing R] [CommRing S] {p : Ideal R} [p.IsPrime] {q : Ideal S} [q.IsPrime]
    {f : R →+* S} (h : p = q.comap f) (hf : P f) :
    P (Localization.localRingHom p q f h) :=
  hPl.isLocalizationMap hPc hPp _ _ hf

end HoldsForLocalization

theorem RingHom.HoldsForLocalizationAway.of_bijective
    (H : RingHom.HoldsForLocalizationAway P) (hf : Function.Bijective f) :
    P f := by
  let := f.toAlgebra
  have := IsLocalization.of_le_isUnit (S := .powers (1 : R)) (by simp)
  have := IsLocalization.isLocalization_of_algEquiv (.powers (1 : R))
    (AlgEquiv.ofBijective (Algebra.ofId R S) hf)
  exact H _ 1

variable {P f R' S'}

lemma RingHom.StableUnderComposition.stableUnderCompositionWithLocalizationAway
    (hPc : RingHom.StableUnderComposition P) (hPl : HoldsForLocalizationAway P) :
    StableUnderCompositionWithLocalizationAway P := by
  constructor
  · introv _ _ hf
    exact hPc _ _ (hPl S r) hf
  · introv _ _ hf
    exact hPc _ _ hf (hPl T s)

lemma RingHom.HoldsForLocalizationAway.containsIdentities (hPl : HoldsForLocalizationAway P) :
    ContainsIdentities P := by
  introv R
  exact hPl.of_bijective _ _ Function.bijective_id

lemma RingHom.LocalizationAwayPreserves.respectsIso
    (hP : LocalizationAwayPreserves P) :
    RespectsIso P where
  left {R S T} _ _ _ f e hf := by
    let := e.toRingHom.toAlgebra
    have : IsLocalization.Away (1 : R) R :=
      IsLocalization.away_of_isUnit_of_bijective _ isUnit_one (Equiv.refl _).bijective
    have : IsLocalization.Away (f 1) T :=
      IsLocalization.away_of_isUnit_of_bijective _ (by simp) e.bijective
    convert! hP f 1 R T hf
    trans (IsLocalization.Away.map R T f 1).comp (algebraMap R R)
    · rw [IsLocalization.Away.map, IsLocalization.map_comp]; rfl
    · rfl
  right {R S T} _ _ _ f e hf := by
    let := e.symm.toRingHom.toAlgebra
    have : IsLocalization.Away (1 : S) R :=
      IsLocalization.away_of_isUnit_of_bijective _ isUnit_one e.symm.bijective
    have : IsLocalization.Away (f 1) T :=
      IsLocalization.away_of_isUnit_of_bijective _ (by simp) (Equiv.refl _).bijective
    convert! hP f 1 R T hf
    have : RingHomInvPair (e : R →+* S) e.symm := RingHomInvPair.of_ringEquiv _
    have : (IsLocalization.Away.map R T f 1).comp e.symm.toRingHom = f :=
      IsLocalization.map_comp ..
    conv_lhs => rw [← this, RingHom.comp_assoc]
    simp only [RingEquiv.toRingHom_eq_coe, RingHomCompTriple.comp_eq]

lemma RingHom.StableUnderCompositionWithLocalizationAway.respectsIso
    (hP : StableUnderCompositionWithLocalizationAway P) :
    RespectsIso P where
  left {R S T} _ _ _ f e hf := by
    let := e.toRingHom.toAlgebra
    have : IsLocalization.Away (1 : S) T :=
      IsLocalization.away_of_isUnit_of_bijective _ isUnit_one e.bijective
    exact hP.right T (1 : S) f hf
  right {R S T} _ _ _ f e hf := by
    let := e.toRingHom.toAlgebra
    have : IsLocalization.Away (1 : R) S :=
      IsLocalization.away_of_isUnit_of_bijective _ isUnit_one e.bijective
    exact hP.left S (1 : R) f hf

theorem RingHom.PropertyIsLocal.respectsIso (hP : RingHom.PropertyIsLocal @P) :
    RingHom.RespectsIso @P :=
  hP.localizationAwayPreserves.respectsIso

-- Almost all arguments are implicit since this is not intended to use mid-proof.
theorem RingHom.LocalizationPreserves.away (H : RingHom.LocalizationPreserves @P) :
    RingHom.LocalizationAwayPreserves P := by
  intro R S _ _ f r R' S' _ _ _ _ _ _ hf
  have : IsLocalization ((Submonoid.powers r).map f) S' := by rw [Submonoid.map_powers]; assumption
  exact H f (Submonoid.powers r) R' S' hf

lemma RingHom.PropertyIsLocal.HoldsForLocalizationAway (hP : RingHom.PropertyIsLocal @P)
    (hPi : ContainsIdentities P) :
    RingHom.HoldsForLocalizationAway @P := by
  introv R _
  have : algebraMap R S = (algebraMap R S).comp (RingHom.id R) := by simp
  rw [this]
  apply hP.StableUnderCompositionWithLocalizationAwayTarget S r
  apply hPi

theorem RingHom.OfLocalizationSpanTarget.ofLocalizationSpan
    (hP : RingHom.OfLocalizationSpanTarget @P)
    (hP' : RingHom.StableUnderCompositionWithLocalizationAwaySource @P) :
    RingHom.OfLocalizationSpan @P := by
  introv R hs hs'
  apply_fun Ideal.map f at hs
  rw [Ideal.map_span, Ideal.map_top] at hs
  apply hP _ _ hs
  rintro ⟨_, r, hr, rfl⟩
  rw [← IsLocalization.map_comp (M := Submonoid.powers r) (S := Localization.Away r)
    (T := Submonoid.powers (f r))]
  · apply hP' _ r
    exact hs' ⟨r, hr⟩

lemma RingHom.OfLocalizationSpan.ofIsLocalization
    (hP : RingHom.OfLocalizationSpan P) (hPi : RingHom.RespectsIso P)
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (s : Set R) (hs : Ideal.span s = ⊤)
    (hT : ∀ r : s, ∃ (Rᵣ Sᵣ : Type u) (_ : CommRing Rᵣ) (_ : CommRing Sᵣ)
      (_ : Algebra R Rᵣ) (_ : Algebra S Sᵣ) (_ : IsLocalization.Away r.val Rᵣ)
      (_ : IsLocalization.Away (f r.val) Sᵣ) (fᵣ : Rᵣ →+* Sᵣ)
      (_ : fᵣ.comp (algebraMap R Rᵣ) = (algebraMap S Sᵣ).comp f),
        P fᵣ) : P f := by
  apply hP _ s hs
  intro r
  obtain ⟨Rᵣ, Sᵣ, _, _, _, _, _, _, fᵣ, hfᵣ, hf⟩ := hT r
  let e₁ := (Localization.algEquiv (.powers r.val) Rᵣ).toRingEquiv
  let e₂ := (IsLocalization.algEquiv (.powers (f r.val))
    (Localization (.powers (f r.val))) Sᵣ).symm.toRingEquiv
  have : Localization.awayMap f r.val =
      (e₂.toRingHom.comp fᵣ).comp e₁.toRingHom := by
    apply IsLocalization.ringHom_ext (.powers r.val)
    ext x
    have : fᵣ ((algebraMap R Rᵣ) x) = algebraMap S Sᵣ (f x) := by
      rw [← RingHom.comp_apply, hfᵣ, RingHom.comp_apply]
    simp [-AlgEquiv.symm_toRingEquiv, e₂, e₁, Localization.awayMap, IsLocalization.Away.map, this]
  rw [this]
  apply hPi.right
  apply hPi.left
  exact hf

/-- Variant of `RingHom.OfLocalizationSpan.ofIsLocalization` where
`fᵣ = IsLocalization.Away.map`. -/
lemma RingHom.OfLocalizationSpan.ofIsLocalization'
    (hP : RingHom.OfLocalizationSpan P) (hPi : RingHom.RespectsIso P)
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (s : Set R) (hs : Ideal.span s = ⊤)
    (hT : ∀ r : s, ∃ (Rᵣ Sᵣ : Type u) (_ : CommRing Rᵣ) (_ : CommRing Sᵣ)
      (_ : Algebra R Rᵣ) (_ : Algebra S Sᵣ) (_ : IsLocalization.Away r.val Rᵣ)
      (_ : IsLocalization.Away (f r.val) Sᵣ),
        P (IsLocalization.Away.map Rᵣ Sᵣ f r)) : P f := by
  apply hP.ofIsLocalization hPi _ s hs
  intro r
  obtain ⟨Rᵣ, Sᵣ, _, _, _, _, _, _, hf⟩ := hT r
  exact ⟨Rᵣ, Sᵣ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, IsLocalization.Away.map Rᵣ Sᵣ f r, IsLocalization.map_comp _, hf⟩

set_option backward.isDefEq.respectTransparency.types false in
lemma RingHom.OfLocalizationSpanTarget.ofIsLocalization
    (hP : RingHom.OfLocalizationSpanTarget P) (hP' : RingHom.RespectsIso P)
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (s : Set S) (hs : Ideal.span s = ⊤)
    (hT : ∀ r : s, ∃ (T : Type u) (_ : CommRing T) (_ : Algebra S T)
      (_ : IsLocalization.Away (r : S) T), P ((algebraMap S T).comp f)) : P f := by
  apply hP _ s hs
  intro r
  obtain ⟨T, _, _, _, hT⟩ := hT r
  convert! hP'.1 _ (Localization.algEquiv (R := S) (Submonoid.powers (r : S)) T).symm.toRingEquiv hT
  rw [← RingHom.comp_assoc, RingEquiv.toRingHom_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, Localization.coe_algEquiv_symm, IsLocalization.map_comp,
    RingHom.comp_id]

section

variable {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}

lemma RingHom.OfLocalizationSpanTarget.and (hP : OfLocalizationSpanTarget P)
    (hQ : OfLocalizationSpanTarget Q) :
    OfLocalizationSpanTarget (fun f ↦ P f ∧ Q f) := by
  introv R hs hf
  exact ⟨hP f s hs fun r ↦ (hf r).1, hQ f s hs fun r ↦ (hf r).2⟩

lemma RingHom.OfLocalizationSpan.and (hP : OfLocalizationSpan P) (hQ : OfLocalizationSpan Q) :
    OfLocalizationSpan (fun f ↦ P f ∧ Q f) := by
  introv R hs hf
  exact ⟨hP f s hs fun r ↦ (hf r).1, hQ f s hs fun r ↦ (hf r).2⟩

lemma RingHom.LocalizationAwayPreserves.and (hP : LocalizationAwayPreserves P)
    (hQ : LocalizationAwayPreserves Q) :
    LocalizationAwayPreserves (fun f ↦ P f ∧ Q f) := by
  introv R h
  exact ⟨hP f r R' S' h.1, hQ f r R' S' h.2⟩

lemma RingHom.StableUnderCompositionWithLocalizationAwayTarget.and
    (hP : StableUnderCompositionWithLocalizationAwayTarget P)
    (hQ : StableUnderCompositionWithLocalizationAwayTarget Q) :
    StableUnderCompositionWithLocalizationAwayTarget (fun f ↦ P f ∧ Q f) := by
  introv R h hf
  exact ⟨hP T s f hf.1, hQ T s f hf.2⟩

lemma RingHom.PropertyIsLocal.and (hP : PropertyIsLocal P) (hQ : PropertyIsLocal Q) :
    PropertyIsLocal (fun f ↦ P f ∧ Q f) where
  localizationAwayPreserves := hP.localizationAwayPreserves.and hQ.localizationAwayPreserves
  ofLocalizationSpanTarget := hP.ofLocalizationSpanTarget.and hQ.ofLocalizationSpanTarget
  ofLocalizationSpan := hP.ofLocalizationSpan.and hQ.ofLocalizationSpan
  StableUnderCompositionWithLocalizationAwayTarget :=
    hP.StableUnderCompositionWithLocalizationAwayTarget.and
    hQ.StableUnderCompositionWithLocalizationAwayTarget

end

section

variable (hP : RingHom.IsStableUnderBaseChange @P)
variable {R S Rᵣ Sᵣ : Type u} [CommRing R] [CommRing S] [CommRing Rᵣ] [CommRing Sᵣ] [Algebra R Rᵣ]
  [Algebra S Sᵣ]

include hP

/-- Let `S` be an `R`-algebra and `Sᵣ` and `Rᵣ` be the respective localizations at a submonoid
`M` of `R`. If `P` is stable under base change and `P` holds for `algebraMap R S`, then
`P` holds for `algebraMap Rᵣ Sᵣ`. -/
lemma RingHom.IsStableUnderBaseChange.of_isLocalization [Algebra R S] [Algebra R Sᵣ] [Algebra Rᵣ Sᵣ]
    [IsScalarTower R S Sᵣ] [IsScalarTower R Rᵣ Sᵣ]
    (M : Submonoid R) [IsLocalization M Rᵣ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sᵣ]
    (h : P (algebraMap R S)) : P (algebraMap Rᵣ Sᵣ) :=
  letI : Algebra.IsPushout R S Rᵣ Sᵣ := Algebra.isPushout_of_isLocalization M Rᵣ S Sᵣ
  hP R S Rᵣ Sᵣ h

/-- If `P` is stable under base change and holds for `f`, then `P` holds for `f` localized
at any submonoid `M` of `R`. -/
lemma RingHom.IsStableUnderBaseChange.isLocalization_map (M : Submonoid R) [IsLocalization M Rᵣ]
    (f : R →+* S) [IsLocalization (M.map f) Sᵣ] (hf : P f) :
    P (IsLocalization.map Sᵣ f M.le_comap_map : Rᵣ →+* Sᵣ) := by
  algebraize [f, IsLocalization.map (S := Rᵣ) Sᵣ f M.le_comap_map,
    (IsLocalization.map (S := Rᵣ) Sᵣ f M.le_comap_map).comp (algebraMap R Rᵣ)]
  have : IsScalarTower R S Sᵣ := IsScalarTower.of_algebraMap_eq'
    (IsLocalization.map_comp M.le_comap_map)
  have : IsLocalization (Algebra.algebraMapSubmonoid S M) Sᵣ :=
    inferInstanceAs <| IsLocalization (M.map f) Sᵣ
  apply hP.of_isLocalization M hf

lemma RingHom.IsStableUnderBaseChange.localizationPreserves : LocalizationPreserves P := by
  introv R hf
  exact hP.isLocalization_map _ _ hf

end

end RingHom

end Properties

section Ideal

variable {R : Type*} (S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]
variable (p : Submonoid R) [IsLocalization p S]

theorem Ideal.localized'_eq_map (I : Ideal R) :
    Submodule.localized' S p (Algebra.linearMap R S) I = I.map (algebraMap R S) := by
  rw [map, span, Submodule.localized'_eq_span, Algebra.coe_linearMap]

theorem Ideal.localized₀_eq_restrictScalars_map (I : Ideal R) :
    Submodule.localized₀ p (Algebra.linearMap R S) I = (I.map (algebraMap R S)).restrictScalars R :=
  congr(Submodule.restrictScalars R $(localized'_eq_map S p I))

theorem Algebra.idealMap_eq_ofEq_comp_toLocalized₀ (I : Ideal R) :
    Algebra.idealMap S I =
      (LinearEquiv.ofEq _ _ <| Ideal.localized₀_eq_restrictScalars_map S p I).toLinearMap ∘ₗ
      Submodule.toLocalized₀ p (Algebra.linearMap R S) I :=
  rfl

theorem Ideal.mem_of_localization_maximal {r : R} {J : Ideal R}
    (h : ∀ (P : Ideal R) (_ : P.IsMaximal),
      algebraMap R _ r ∈ Ideal.map (algebraMap R (Localization.AtPrime P)) J) :
    r ∈ J :=
  Submodule.mem_of_localization_maximal _ _ _ _ fun P hP ↦ by
    apply (localized'_eq_map (Localization.AtPrime P) P.primeCompl J).symm ▸ h P hP

/-- Let `I J : Ideal R`. If the localization of `I` at each maximal ideal `P` is included in
the localization of `J` at `P`, then `I ≤ J`. -/
theorem Ideal.le_of_localization_maximal {I J : Ideal R}
    (h : ∀ (P : Ideal R) (_ : P.IsMaximal),
      Ideal.map (algebraMap R (Localization.AtPrime P)) I ≤
        Ideal.map (algebraMap R (Localization.AtPrime P)) J) :
    I ≤ J :=
  fun _ hm ↦ mem_of_localization_maximal fun P hP ↦ h P hP (mem_map_of_mem _ hm)

lemma Ideal.iInf_ker_le (I : Ideal R) :
    ⨅ (p : Ideal R) (_ : p.IsPrime) (_ : I ≤ p),
      RingHom.ker (algebraMap R (Localization.AtPrime p)) ≤ I := by
  intro x hx
  refine Ideal.mem_of_localization_maximal fun m hm ↦ ?_
  simp only [Submodule.mem_iInf, RingHom.mem_ker] at hx
  by_cases hle : I ≤ m
  · simp [hx _ _ hle]
  · simp [IsLocalization.AtPrime.map_eq_top_of_not_le _ hle]

/-- Let `I J : Ideal R`. If the localization of `I` at each maximal ideal `P` is equal to
the localization of `J` at `P`, then `I = J`. -/
theorem Ideal.eq_of_localization_maximal {I J : Ideal R}
    (h : ∀ (P : Ideal R) (_ : P.IsMaximal),
      Ideal.map (algebraMap R (Localization.AtPrime P)) I =
        Ideal.map (algebraMap R (Localization.AtPrime P)) J) :
    I = J :=
  le_antisymm (le_of_localization_maximal fun P hP ↦ (h P hP).le)
    (le_of_localization_maximal fun P hP ↦ (h P hP).ge)

/-- An ideal is trivial if its localization at every maximal ideal is trivial. -/
theorem ideal_eq_bot_of_localization' (I : Ideal R)
    (h : ∀ (J : Ideal R) (_ : J.IsMaximal),
      Ideal.map (algebraMap R (Localization.AtPrime J)) I = ⊥) :
    I = ⊥ :=
  Ideal.eq_of_localization_maximal fun P hP => by simpa using h P hP

theorem eq_zero_of_localization (r : R)
    (h : ∀ (J : Ideal R) (_ : J.IsMaximal), algebraMap R (Localization.AtPrime J) r = 0) :
    r = 0 :=
  Module.eq_zero_of_localization_maximal _ (fun _ _ ↦ Algebra.linearMap R _) r h

/-- An ideal is trivial if its localization at every maximal ideal is trivial. -/
theorem ideal_eq_bot_of_localization (I : Ideal R)
    (h : ∀ (J : Ideal R) (_ : J.IsMaximal),
      IsLocalization.coeSubmodule (Localization.AtPrime J) I = ⊥) :
    I = ⊥ :=
  bot_unique fun r hr ↦ eq_zero_of_localization r fun J hJ ↦ (h J hJ).le ⟨r, hr, rfl⟩

end Ideal
