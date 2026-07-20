/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.RudimentarySuccessorExtensionOrder

/-!
# Coherent unions of internally represented stage orders

At a limit stage, a union of arbitrary external well-orders is not enough.
This file records the exact coherence and initial-segment hypotheses under
which the union relation well-orders the limit carrier.  If the family of
graphs is itself represented by a constructible set, its internal union is
then the required graph in `L`.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Model

noncomputable section

/-- Include the internal carrier of an earlier stage into a later one. -/
def internalStageInclusion {alpha beta : Ordinal.{u}}
    (h : alpha ≤ beta) :
    InternalCarrier (stageLCarrier alpha) ->
      InternalCarrier (stageLCarrier beta) :=
  fun x => ⟨x.1, LStageZF_mono h x.2⟩

@[simp]
theorem internalStageInclusion_val {alpha beta : Ordinal.{u}}
    (h : alpha ≤ beta)
    (x : InternalCarrier (stageLCarrier alpha)) :
    (internalStageInclusion h x).1 = x.1 := rfl

theorem internalStageInclusion_injective {alpha beta : Ordinal.{u}}
    (h : alpha ≤ beta) :
    Function.Injective (internalStageInclusion h) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg
    (fun z : InternalCarrier (stageLCarrier beta) => z.1.1) hxy

/--
A coherent system of supported stage graphs below `limit`.  Coherence says
later graphs restrict to earlier graphs; `initial` says every earlier stage
is an initial segment of every later order.
-/
structure CoherentStageGraphSystem (limit : Ordinal.{u})
    (graphs : Set.Iio limit -> LCarrier.{u}) : Prop where
  wellOrders : ∀ beta : Set.Iio limit,
    InternallyWellOrders (graphs beta) (stageLCarrier beta.1)
  supported : ∀ beta : Set.Iio limit, ∀ x y : LCarrier.{u},
    GraphRel (graphs beta) x y ->
      x.1 ∈ LStageZF beta.1 ∧ y.1 ∈ LStageZF beta.1
  coherent : ∀ beta gamma : Set.Iio limit, beta.1 ≤ gamma.1 ->
    ∀ x y : LCarrier.{u},
      x.1 ∈ LStageZF beta.1 -> y.1 ∈ LStageZF beta.1 ->
        (GraphRel (graphs gamma) x y ↔ GraphRel (graphs beta) x y)
  initial : ∀ beta gamma : Set.Iio limit, beta.1 ≤ gamma.1 ->
    ∀ x y : LCarrier.{u},
      x.1 ∈ LStageZF beta.1 -> y.1 ∈ LStageZF gamma.1 ->
        GraphRel (graphs gamma) y x -> y.1 ∈ LStageZF beta.1

/-- The external union of all stage relations below a limit. -/
def coherentLimitRel {limit : Ordinal.{u}}
    (graphs : Set.Iio limit -> LCarrier.{u}) :
    InternalCarrier (stageLCarrier limit) ->
      InternalCarrier (stageLCarrier limit) -> Prop :=
  fun x y => ∃ beta : Set.Iio limit,
    GraphRel (graphs beta) x.1 y.1

private theorem commonStageBelowLimit {limit : Ordinal.{u}}
    (hl : Order.IsSuccLimit limit)
    (x y : InternalCarrier (stageLCarrier limit)) :
    ∃ beta : Set.Iio limit,
      x.1.1 ∈ LStageZF beta.1 ∧ y.1.1 ∈ LStageZF beta.1 := by
  rcases (mem_LStageZF_limit_iff hl).mp x.2 with ⟨alpha, ha, hx⟩
  rcases (mem_LStageZF_limit_iff hl).mp y.2 with ⟨beta, hb, hy⟩
  let gamma : Set.Iio limit := ⟨max alpha beta, max_lt ha hb⟩
  refine ⟨gamma, ?_, ?_⟩
  · exact LStageZF_mono (le_max_left alpha beta) hx
  · exact LStageZF_mono (le_max_right alpha beta) hy

/-- Coherent initial-segment unions are well-orders on the limit carrier. -/
theorem coherentLimitRel_isWellOrder {limit : Ordinal.{u}}
    (hl : Order.IsSuccLimit limit)
    (graphs : Set.Iio limit -> LCarrier.{u})
    (hsystem : CoherentStageGraphSystem limit graphs) :
    IsWellOrder (InternalCarrier (stageLCarrier limit))
      (coherentLimitRel graphs) := by
  refine
    { wf := ?_
      trichotomous := ?_ }
  · apply WellFounded.wellFounded_iff_has_min.mpr
    intro candidates hcandidates
    rcases hcandidates with ⟨chosen, hchosen⟩
    rcases (mem_LStageZF_limit_iff hl).mp chosen.2 with
      ⟨betaRaw, hbetaLimit, hchosenBeta⟩
    let beta : Set.Iio limit := ⟨betaRaw, hbetaLimit⟩
    let chosenBeta : InternalCarrier (stageLCarrier beta.1) :=
      ⟨chosen.1, hchosenBeta⟩
    let localCandidates : Set
        (InternalCarrier (stageLCarrier beta.1)) :=
      {x | internalStageInclusion hbetaLimit.le x ∈ candidates}
    have hlocalNonempty : localCandidates.Nonempty := by
      refine ⟨chosenBeta, ?_⟩
      have hinclusion :
          internalStageInclusion hbetaLimit.le chosenBeta = chosen := by
        apply Subtype.ext
        rfl
      change internalStageInclusion hbetaLimit.le chosenBeta ∈ candidates
      simpa only [hinclusion] using hchosen
    letI : IsWellOrder (InternalCarrier (stageLCarrier beta.1))
        (graphRelOn (graphs beta) (stageLCarrier beta.1)) :=
      hsystem.wellOrders beta
    rcases (IsWellFounded.wf : WellFounded
        (graphRelOn (graphs beta) (stageLCarrier beta.1))).has_min
        localCandidates hlocalNonempty with
      ⟨minimum, hminimum, hminimal⟩
    let limitMinimum : InternalCarrier (stageLCarrier limit) :=
      internalStageInclusion hbetaLimit.le minimum
    refine ⟨limitMinimum, hminimum, ?_⟩
    intro y hyCandidates hyBelow
    rcases hyBelow with ⟨gamma, hyBelowGamma⟩
    have hsupportGamma :=
      hsystem.supported gamma y.1 limitMinimum.1 hyBelowGamma
    have hdeltaLimit : max beta.1 gamma.1 < limit :=
      max_lt beta.2 gamma.2
    let delta : Set.Iio limit :=
      ⟨max beta.1 gamma.1, hdeltaLimit⟩
    have hbetaDelta : beta.1 ≤ delta.1 :=
      le_max_left beta.1 gamma.1
    have hgammaDelta : gamma.1 ≤ delta.1 :=
      le_max_right beta.1 gamma.1
    have hyBelowDelta :
        GraphRel (graphs delta) y.1 limitMinimum.1 :=
      (hsystem.coherent gamma delta hgammaDelta y.1 limitMinimum.1
        hsupportGamma.1 hsupportGamma.2).mpr hyBelowGamma
    have hyDelta : y.1.1 ∈ LStageZF delta.1 :=
      LStageZF_mono hgammaDelta hsupportGamma.1
    have hyBeta : y.1.1 ∈ LStageZF beta.1 :=
      hsystem.initial beta delta hbetaDelta limitMinimum.1 y.1
        minimum.2 hyDelta hyBelowDelta
    have hyBelowBeta :
        GraphRel (graphs beta) y.1 limitMinimum.1 :=
      (hsystem.coherent beta delta hbetaDelta y.1 limitMinimum.1
        hyBeta minimum.2).mp hyBelowDelta
    let yBeta : InternalCarrier (stageLCarrier beta.1) :=
      ⟨y.1, hyBeta⟩
    have hyLocal : yBeta ∈ localCandidates := by
      have hinclusion :
          internalStageInclusion hbetaLimit.le yBeta = y := by
        apply Subtype.ext
        rfl
      change internalStageInclusion hbetaLimit.le yBeta ∈ candidates
      simpa only [hinclusion] using hyCandidates
    exact hminimal yBeta hyLocal hyBelowBeta
  · intro x y hnxy hnyx
    rcases commonStageBelowLimit hl x y with ⟨beta, hx, hy⟩
    let xBeta : InternalCarrier (stageLCarrier beta.1) := ⟨x.1, hx⟩
    let yBeta : InternalCarrier (stageLCarrier beta.1) := ⟨y.1, hy⟩
    letI : IsWellOrder (InternalCarrier (stageLCarrier beta.1))
        (graphRelOn (graphs beta) (stageLCarrier beta.1)) :=
      hsystem.wellOrders beta
    rcases trichotomous_of
        (graphRelOn (graphs beta) (stageLCarrier beta.1))
        xBeta yBeta with hxy | hxy | hyx
    · exact (hnxy ⟨beta, hxy⟩).elim
    · apply Subtype.ext
      apply Subtype.ext
      exact congrArg
        (fun z : InternalCarrier (stageLCarrier beta.1) => z.1.1) hxy
    · exact (hnyx ⟨beta, hyx⟩).elim

/-! ## Internalizing the union graph -/

/-- A constructible set represents precisely the range of the graph system. -/
def RepresentsStageGraphFamily {limit : Ordinal.{u}}
    (graphs : Set.Iio limit -> LCarrier.{u})
    (family : LCarrier.{u}) : Prop :=
  ∀ relation : LCarrier.{u}, relation.1 ∈ family.1 ↔
    ∃ beta : Set.Iio limit, relation = graphs beta

/-- Membership in the internal union is exactly membership in one stage
graph, provided `family` represents the graph range. -/
theorem graphRel_sUnion_family_iff {limit : Ordinal.{u}}
    (graphs : Set.Iio limit -> LCarrier.{u})
    (family : LCarrier.{u})
    (hfamily : RepresentsStageGraphFamily graphs family)
    (x y : LCarrier.{u}) :
    GraphRel (sUnionLCarrier family) x y ↔
      ∃ beta : Set.Iio limit, GraphRel (graphs beta) x y := by
  change (orderedPairLCarrier x y).1 ∈ (sUnionLCarrier family).1 ↔ _
  rw [mem_sUnionLCarrier_iff]
  constructor
  · rintro ⟨relation, hrelation, hpair⟩
    rcases (hfamily relation).mp hrelation with ⟨beta, rfl⟩
    exact ⟨beta, hpair⟩
  · rintro ⟨beta, hpair⟩
    exact ⟨graphs beta, (hfamily (graphs beta)).mpr ⟨beta, rfl⟩, hpair⟩

/-- A constructibly represented coherent graph family gives an internal
well-order of the limit stage. -/
theorem internallyWellOrders_limit_of_coherentFamily
    {limit : Ordinal.{u}} (hl : Order.IsSuccLimit limit)
    (graphs : Set.Iio limit -> LCarrier.{u})
    (hsystem : CoherentStageGraphSystem limit graphs)
    (family : LCarrier.{u})
    (hfamily : RepresentsStageGraphFamily graphs family) :
    InternallyWellOrders (sUnionLCarrier family) (stageLCarrier limit) := by
  have heq :
      graphRelOn (sUnionLCarrier family) (stageLCarrier limit) =
        coherentLimitRel graphs := by
    funext x y
    apply propext
    exact graphRel_sUnion_family_iff graphs family hfamily x.1 y.1
  rw [InternallyWellOrders, heq]
  exact coherentLimitRel_isWellOrder hl graphs hsystem

/-! ## Retaining coherence after the limit step -/

/-- The data needed to adjoin the union graph at a limit stage to the
preceding coherent system. -/
structure LimitOrderExtension (limit : Ordinal.{u})
    (graphs : Set.Iio limit → LCarrier.{u}) where
  nextRelation : LCarrier.{u}
  wellOrders : InternallyWellOrders nextRelation (stageLCarrier limit)
  supported : ∀ x y : LCarrier.{u}, GraphRel nextRelation x y →
    x.1 ∈ LStageZF limit ∧ y.1 ∈ LStageZF limit
  agreesOnEarlier : ∀ beta : Set.Iio limit, ∀ x y : LCarrier.{u},
    x.1 ∈ LStageZF beta.1 → y.1 ∈ LStageZF beta.1 →
      (GraphRel nextRelation x y ↔ GraphRel (graphs beta) x y)
  earlierIsInitial : ∀ beta : Set.Iio limit, ∀ x y : LCarrier.{u},
    x.1 ∈ LStageZF beta.1 → y.1 ∈ LStageZF limit →
      GraphRel nextRelation y x → y.1 ∈ LStageZF beta.1

/-- A constructibly represented coherent family has a canonical union which
retains support, coherence, and every earlier initial segment. -/
def coherentLimitOrderExtension
    {limit : Ordinal.{u}} (hl : Order.IsSuccLimit limit)
    (graphs : Set.Iio limit → LCarrier.{u})
    (hsystem : CoherentStageGraphSystem limit graphs)
    (family : LCarrier.{u})
    (hfamily : RepresentsStageGraphFamily graphs family) :
    LimitOrderExtension limit graphs where
  nextRelation := sUnionLCarrier family
  wellOrders :=
    internallyWellOrders_limit_of_coherentFamily
      hl graphs hsystem family hfamily
  supported := by
    intro x y hxy
    rcases (graphRel_sUnion_family_iff
        graphs family hfamily x y).mp hxy with ⟨beta, hbeta⟩
    have hsupported := hsystem.supported beta x y hbeta
    exact
      ⟨LStageZF_mono beta.2.le hsupported.1,
        LStageZF_mono beta.2.le hsupported.2⟩
  agreesOnEarlier := by
    intro beta x y hx hy
    constructor
    · intro hlimit
      rcases (graphRel_sUnion_family_iff
          graphs family hfamily x y).mp hlimit with ⟨gamma, hgamma⟩
      let delta : Set.Iio limit :=
        ⟨max beta.1 gamma.1, by
          change max beta.1 gamma.1 < limit
          exact max_lt beta.2 gamma.2⟩
      have hgammaDelta : gamma.1 ≤ delta.1 :=
        le_max_right beta.1 gamma.1
      have hbetaDelta : beta.1 ≤ delta.1 :=
        le_max_left beta.1 gamma.1
      have hgammaSupport := hsystem.supported gamma x y hgamma
      have hdelta : GraphRel (graphs delta) x y :=
        (hsystem.coherent gamma delta hgammaDelta x y
          hgammaSupport.1 hgammaSupport.2).mpr hgamma
      exact (hsystem.coherent beta delta hbetaDelta x y hx hy).mp hdelta
    · intro hbeta
      exact (graphRel_sUnion_family_iff
        graphs family hfamily x y).mpr ⟨beta, hbeta⟩
  earlierIsInitial := by
    intro beta x y hx _hyLimit hyx
    rcases (graphRel_sUnion_family_iff
        graphs family hfamily y x).mp hyx with ⟨gamma, hgamma⟩
    let delta : Set.Iio limit :=
      ⟨max beta.1 gamma.1, by
        change max beta.1 gamma.1 < limit
        exact max_lt beta.2 gamma.2⟩
    have hgammaDelta : gamma.1 ≤ delta.1 :=
      le_max_right beta.1 gamma.1
    have hbetaDelta : beta.1 ≤ delta.1 :=
      le_max_left beta.1 gamma.1
    have hgammaSupport := hsystem.supported gamma y x hgamma
    have hdelta : GraphRel (graphs delta) y x :=
      (hsystem.coherent gamma delta hgammaDelta y x
        hgammaSupport.1 hgammaSupport.2).mpr hgamma
    have hyDelta : y.1 ∈ LStageZF delta.1 :=
      LStageZF_mono hgammaDelta hgammaSupport.1
    exact hsystem.initial beta delta hbetaDelta x y hx hyDelta hdelta

@[simp]
theorem coherentLimitOrderExtension_nextRelation
    {limit : Ordinal.{u}} (hl : Order.IsSuccLimit limit)
    (graphs : Set.Iio limit → LCarrier.{u})
    (hsystem : CoherentStageGraphSystem limit graphs)
    (family : LCarrier.{u})
    (hfamily : RepresentsStageGraphFamily graphs family) :
    (coherentLimitOrderExtension hl graphs hsystem family hfamily).nextRelation =
      sUnionLCarrier family :=
  rfl

end

end Constructible.Model
