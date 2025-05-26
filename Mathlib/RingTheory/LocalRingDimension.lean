/-
Copyright (c) 2025 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
import Mathlib.RingTheory.EmbeddingDimension
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Local Ring Dimension

* This file contains results about the Krull dimension of a commutative noetherian local ring.

## Main results

* `IsLocalRing.Quotient_singleton_ringKrullDim`: If `x ∈ m` then
`ringKrullDim R ≤ 1 + ringKrullDim R ⧸ x`
* `IsLocalRing.ringKrullDim_le_EmbDim`: The embedding dimension of `R` is an upper bound on the
Krull Dimension of `R`
* `IsLocalRing.ringKrullDim_quotient_succ_eq_of_nonZeroDivisor`: If `x` is a non-unit,
non-zerodivisor then
`ringKrullDim R = 1 + ringKrullDim R ⧸ x`

-/

local notation3:max "maxl" A => (IsLocalRing.maximalIdeal A)
open Ideal
variable {R : Type*} [CommRing R]

/-- The Krull dimension of R cast as a natural number. If R has infinite Krull dimension or
is the zero ring then finRingKrullDim R = 0 -/
noncomputable def finRingKrullDim (R : Type*) [CommRing R] : ℕ :=
  ENat.toNat (WithBot.unbotD 0 (ringKrullDim R))

instance {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    FiniteRingKrullDim R := by
  apply finiteRingKrullDim_iff_ne_bot_and_top.mpr
  constructor
  · have KDge0 := @ringKrullDim_nonneg_of_nontrivial R _ _
    by_contra hc
    rw[hc] at KDge0
    contradiction
  rw[← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  have finHeight := Ideal.height_le_spanFinrank (maxl R) Ideal.IsPrime.ne_top'
  have : Submodule.spanFinrank (maxl R) < (⊤ : ℕ∞) :=
    ENat.coe_lt_top (Submodule.spanFinrank maxl R)
  by_contra hc
  have : (maxl R).height < ⊤ := lt_of_le_of_lt finHeight this
  have : (maxl R).height < (⊤ : WithBot ℕ∞) := WithBot.coe_lt_coe.mpr this
  rw[hc] at this
  contradiction

theorem finRingKrullDim_ringKrullDim (R : Type*) [CommRing R] [FiniteRingKrullDim R] :
    ringKrullDim R = finRingKrullDim R := by
  obtain ⟨hn , hm⟩ := (finiteRingKrullDim_iff_ne_bot_and_top.mp ‹_›)
  let n : ℕ∞ := WithBot.unbot (ringKrullDim R) hn
  have h1 : ringKrullDim R = n := (WithBot.unbot_eq_iff hn).mp rfl
  have h3 : WithBot.unbotD 0 (ringKrullDim R) = (ringKrullDim R) := by
    rw[h1]
    rfl
  have : WithBot.unbotD 0 (ringKrullDim R) ≠ ⊤ := by
    by_contra hc
    obtain hl|hr := (@WithBot.unbotD_eq_iff ℕ∞ 0 ⊤ (ringKrullDim R)).mp hc
    exact hm hl
    exact hn hr.left
  have : ENat.toNat (WithBot.unbotD 0 (ringKrullDim R)) = WithBot.unbotD 0 (ringKrullDim R) :=
    ENat.coe_toNat this
  unfold finRingKrullDim
  nth_rw 1 [← h3]
  nth_rw 1 [← this]
  rfl

lemma le_minimalPrimes
    {R : Type*} [CommRing R] {I : Ideal R} [I.IsPrime] {P : Ideal R}
    (hP : P ∈ minimalPrimes R) (hI : I ≤ P) :
    I = P := by
  rw[minimalPrimes_eq_minimals] at hP
  obtain ⟨hP1, hP2⟩ := hP
  have := hP2 ‹_› hI
  exact le_antisymm_iff.mpr ⟨hI, this⟩

theorem IsLocalRing.exists_finset_card_eq_ringKrullDim
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ∃ s : Finset R, s.card ≤ finRingKrullDim R ∧ (maxl R) ∈ (Ideal.span s).minimalPrimes := by
  obtain ⟨s, hs1, hs2⟩ := Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maxl R)
  have a : (maxl R).height = ringKrullDim R := IsLocalRing.maximalIdeal_height_eq_ringKrullDim
  have b : ringKrullDim R = finRingKrullDim R := finRingKrullDim_ringKrullDim R
  rw[b, ← hs2] at a
  have : s.card = finRingKrullDim R :=
    (@Nat.cast_inj (WithBot ℕ∞) _ _ s.card (finRingKrullDim R)).mp a
  use s
  rw[this]
  exact ⟨Nat.le_refl (finRingKrullDim R), hs1⟩

/-- If `x ∈ m` then `ringKrullDim R ≤ 1 + ringKrullDim R ⧸ x`. In other words, when you
quotient out by a single non-unit, the dimension drops by at most 1 -/
theorem IsLocalRing.Quotient_singleton_ringKrullDim [IsLocalRing R] [IsNoetherianRing R] (x : R)
[Nontrivial (R ⧸ (Ideal.span {x}))] :
    ringKrullDim R ≤ ringKrullDim (R ⧸ (Ideal.span {x})) + 1 := by
  obtain ⟨s , hs1 , hs2⟩ := exists_finset_card_eq_ringKrullDim (R ⧸ (Ideal.span {x}))
  let q : (R ⧸ (Ideal.span {x})) ↪ R := {
    toFun := Quotient.out
    inj' := Quotient.out_injective
  }
  let S : Finset R := Finset.map q s
  have Scard : S.card = s.card := Finset.card_map q
  have hS' : (S ∪ {x} : Set R).Finite := Set.toFinite (↑S ∪ {x})
  have ncard := Set.ncard_union_le S {x}
  rw[Set.ncard_singleton x, Set.ncard_coe_Finset] at ncard
  let S' := Set.Finite.toFinset hS'
  have cardsle : S'.card ≤ S.card + 1 := by
    rw[← Set.ncard_coe_Finset]
    have : (S' : Set R).ncard = (S ∪ {x} : Set R).ncard := by
      rw[Set.Finite.coe_toFinset hS']
    linarith
  have im : Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) (Ideal.span S) = Ideal.span s := by
    have imS : (Ideal.Quotient.mk (Ideal.span {x}))'' S = s := by
      simp_all only [Finset.card_map, Finset.coe_map, Function.Embedding.coeFn_mk, S, q]
      ext x_1 : 1
      simp_all only [Set.mem_image, Finset.mem_coe, exists_exists_and_eq_and,
      Ideal.Quotient.mk_out, exists_eq_right]
    rw[Ideal.map_span, imS]
  have comapmap := Ideal.comap_map_of_surjective'
    (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective (Ideal.span S)
  rw[im] at comapmap
  rw[Ideal.mk_ker] at comapmap
  have spanunion : Ideal.span (↑S ∪ {x}) = Ideal.span S ⊔ Ideal.span {x} :=
    @Submodule.span_union R R _ _ _ S {x}
  have smspan : span S' = span (S ∪ {x}) := by simp_all only [Finset.card_map, Finset.coe_map,
    Function.Embedding.coeFn_mk, Set.union_singleton, submodule_span_eq, Set.Finite.subset_toFinset,
    Set.subset_insert, Set.Finite.coe_toFinset, q, S, S']
  rw[spanunion, ← comapmap] at smspan
  have comapMinPrimes := @Ideal.comap_minimalPrimes_eq_of_surjective R (R ⧸ span {x}) _ _
    (Ideal.Quotient.mk (span {x})) Ideal.Quotient.mk_surjective (span s)
  rw[← smspan] at comapMinPrimes
  have maxmin : (maxl R) ∈ (span S').minimalPrimes := by
    have : (maxl R) = comap (Ideal.Quotient.mk (span {x})) (maxl (R ⧸ span {x})) :=
      Eq.symm (IsLocalRing.Quotient_comap_maximalIdeal (span {x}))
    have : (maxl R) ∈ comap (Ideal.Quotient.mk (span {x})) '' (span ↑s).minimalPrimes := by
      simp_all only [Finset.card_map, Finset.coe_map, Function.Embedding.coeFn_mk,
      Set.union_singleton, Set.encard_singleton, Set.Finite.coe_toFinset, Set.mem_image, S', S, q]
      apply Exists.intro
      · apply And.intro
        on_goal 2 => {rfl
        }
        · simp_all only [S', S, q]
    rw[← comapMinPrimes] at this
    exact this
  have KDRle :=
    (Ideal.height_le_spanRank_toENat_of_mem_minimal_primes (span (S' : Set R)) (maxl R)) maxmin
  have maxKDR : (maxl R).height = ringKrullDim R := maximalIdeal_height_eq_ringKrullDim
  have spanrk :=
    @Submodule.spanFinrank_span_le_ncard_of_finite R R _ _ _ S' (Finset.finite_toSet S')
  rw[Set.ncard_coe_Finset S'] at spanrk
  have g : (span (S' : Set R)).FG := by
    use S'
  rw[Submodule.fg_iff_spanRank_eq_spanFinrank.mpr g] at KDRle
  simp at KDRle
  have a := ENat.coe_le_coe.mpr spanrk
  have maxleK : (maxl R).height ≤ finRingKrullDim (R ⧸ span {x}) + 1 := by
    have a : (maxl R).height ≤ S'.card := le_trans KDRle a
    have b : S'.card ≤ finRingKrullDim (R ⧸ span {x}) + 1 := by linarith
    have c : (S'.card : ℕ∞) ≤ finRingKrullDim (R ⧸ span {x}) + 1 := ENat.coe_le_coe.mpr b
    exact le_trans a c
  have al : ((maxl R).height : WithBot ℕ∞) ≤ finRingKrullDim (R ⧸ span {x}) + 1 :=
    (WithBot.coe_le rfl).mpr maxleK
  rw[maxKDR, ← finRingKrullDim_ringKrullDim (R ⧸ span {x})] at al
  exact al

theorem IsLocalRing.Quotient_span_singleton_spanFinrank
    [IsLocalRing R] [IsNoetherianRing R] (x : R) [Nontrivial (R ⧸ (Ideal.span {x}))]
    (hx1 : x ∈ (maxl R)) (hx2 : x ∉ (maxl R)^2) :
    Submodule.spanFinrank (maxl (R ⧸ Ideal.span {x})) + 1 = Submodule.spanFinrank (maxl R) := by
  rw[← IsLocalRing.Embdim_eq_spanFinrank_maximalIdeal R,
  ← IsLocalRing.Embdim_eq_spanFinrank_maximalIdeal (R ⧸ Ideal.span {x})]
  exact Eq.symm (IsLocalRing.Embdim_Quotient_span_singleton hx1 hx2)

theorem IsLocalRing.ringKrullDim_le_spanFinrank
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ringKrullDim R ≤ Submodule.spanFinrank (maxl R) := by
  rw[← maximalIdeal_height_eq_ringKrullDim]
  have := Ideal.height_le_spanFinrank (maxl R) Ideal.IsPrime.ne_top'
  exact (WithBot.coe_le rfl).mpr this

/-- The embedding dimension of `R` is an upper bound on the Krull Dimension of `R`. -/
theorem IsLocalRing.ringKrullDim_le_EmbDim
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ringKrullDim R ≤ EmbDim R := by
  rw[IsLocalRing.Embdim_eq_spanFinrank_maximalIdeal]
  exact IsLocalRing.ringKrullDim_le_spanFinrank R

/-- If `x` is a non-unit, non-zerodivisor then `ringKrullDim R = 1 + ringKrullDim R ⧸ x` -/
theorem IsLocalRing.ringKrullDim_quotient_succ_eq_of_nonZeroDivisor
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {r : R} (hr : r ∈ nonZeroDivisors R) (hr' : ¬IsUnit r) :
    ringKrullDim (R ⧸ Ideal.span {r}) + 1 = ringKrullDim R :=
  le_antisymm_iff.mpr ⟨ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr ,
  @IsLocalRing.Quotient_singleton_ringKrullDim R _ _ _ r
  (Ideal.Quotient.nontrivial (span_singleton_ne_top hr'))⟩
