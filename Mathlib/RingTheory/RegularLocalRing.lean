/-
Copyright (c) 2025 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/

import Mathlib.RingTheory.LocalRingDimension
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.KrullDimension.Field

/-!
# Regular Local Rings

* This file defines regular local rings and proves properties about them.

## Main results

* `IsRegularLocalRing`: definition of a regular local ring
* `IsRegularLocalRing.Quotient_span_singleton_IsRegularLocalRing`: If `x ∈ m \ m²` and `R` is
regular, then `R ⧸ x` is regular. This is used to inductively prove things about regular local
rings
* `IsRegularLocalRing.ringKrullDim_zero_IsField`: A regular local ring of dimension 0 is a field
* `IsLocalRing.IsDiscreteValuationRing_iff_IsRegularLocalRing_ringKrullDim_one` : A regular local
ring of dimension 1 is a discrete valuation ring.
* `IsRegularLocalRing.IsDomain`: A regular local ring is an integral domain.

-/

local notation3:max "maxl" A => (IsLocalRing.maximalIdeal A)

/-- A commutative local noetherian ring `R` is regular if its embedding dimension equals
its Krull dimension -/
class IsRegularLocalRing (R : Type*) [CommRing R] : Prop extends
IsLocalRing R, IsNoetherianRing R where
  reg : IsLocalRing.EmbDim R = ringKrullDim R

/-- If `x ∈ m \ m²` and R is regular, then `R ⧸ x` is regular. -/
theorem IsRegularLocalRing.Quotient_span_singleton_IsRegularLocalRing
{R : Type*} [CommRing R] [hreg : IsRegularLocalRing R] (x : R) [Nontrivial (R ⧸ (Ideal.span {x}))]
(hx1 : x ∈ maxl R) (hx2 : x ∉ (maxl R)^2) :
    IsRegularLocalRing (R ⧸ Ideal.span {x}) := by
  apply IsRegularLocalRing.mk
  rw[IsLocalRing.Embdim_eq_spanFinrank_maximalIdeal]
  refine le_antisymm_iff.mpr ⟨?_, IsLocalRing.ringKrullDim_le_spanFinrank (R ⧸ Ideal.span {x})⟩
  have KDle := IsLocalRing.Quotient_singleton_ringKrullDim x
  have hh : ((Submodule.spanFinrank maxl R ⧸ Ideal.span {x}) + 1 : ℕ) ≤
  ringKrullDim (R ⧸ Ideal.span {x}) + 1 := by
    rw[IsLocalRing.Quotient_span_singleton_spanFinrank x hx1 hx2]
    rw[← IsLocalRing.Embdim_eq_spanFinrank_maximalIdeal, hreg.reg]
    exact KDle
  have : ((Submodule.spanFinrank maxl R ⧸ Ideal.span {x}) + 1 : ℕ) =
  (((Submodule.spanFinrank maxl R ⧸ Ideal.span {x}) : WithBot ℕ∞) + 1) := rfl
  rw[this] at hh
  clear this
  rw[finRingKrullDim_ringKrullDim] at hh
  rw[finRingKrullDim_ringKrullDim]
  have natle :
  (Submodule.spanFinrank maxl R ⧸ Ideal.span {x}) + 1 ≤
  (finRingKrullDim (R ⧸ Ideal.span {x})) + 1 :=
    Nat.cast_le.mp hh
  have natle' : (Submodule.spanFinrank maxl R ⧸ Ideal.span {x}) ≤
  (finRingKrullDim (R ⧸ Ideal.span {x})) :=
    Nat.le_of_lt_succ natle
  exact Nat.cast_le.mpr natle'

/-- A regular local ring of dimension 0 is a field -/
lemma IsRegularLocalRing.ringKrullDim_zero_IsField
    (R : Type*) [CommRing R] [hR : IsRegularLocalRing R] (kd0 : ringKrullDim R = 0) :
    IsField R := by
  rw[← hR.reg, IsLocalRing.Embdim_eq_spanFinrank_maximalIdeal] at kd0
  have hm : Submodule.spanFinrank (maxl R) = 0 := by simp_all only [Nat.cast_eq_zero]
  have SPzero : Submodule.spanRank (maxl R) = 0 := by
    rw[IsNoetherianRing.Ideal_spanRank_eq_spanFinrank maxl R, hm]
    rfl
  have mBot := Submodule.spanRank_eq_zero_iff_eq_bot.mp SPzero
  exact IsLocalRing.isField_iff_maximalIdeal_eq.mpr (id (mBot))

lemma IsLocalRing.IsNoetherianRing_span_singleton_IsPrime_not_minimalPrimes_IsDomain
{R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
(x : R) [hx : (Ideal.span {x}).IsPrime] (notMin : ¬Ideal.span {x} ∈ minimalPrimes R) :
    IsDomain R := by
  have zero_in_x : ⊥ ≤ Ideal.span {x} := bot_le
  have min_in_x := Ideal.exists_minimalPrimes_le zero_in_x
  obtain ⟨q , hq1, hq2⟩ := min_in_x
  have x_not_in_q : x ∉ q := by
    by_contra hx
    have : Ideal.span {x} ≤ q := (Ideal.span_singleton_le_iff_mem q).mpr hx
    have := le_antisymm_iff.mpr ⟨hq2, this⟩
    rw[this] at hq1
    exact notMin hq1
  have q_in_x_pow : ∀ n : ℕ, q ≤ Ideal.span {x}^n := by
    intro n
    induction n with
    | zero =>
      rw[Ideal.span_singleton_pow x 0]
      rw[pow_zero x]
      rw[Ideal.span_singleton_one]
      exact fun ⦃x⦄ a ↦ trivial
    | succ n ih =>
      intro y hy
      rw[Ideal.span_singleton_pow]
      rw[Ideal.span_singleton_pow] at ih
      obtain ⟨r , hr⟩ := Ideal.mem_span_singleton'.mp (ih hy)
      have qPrime : q.IsPrime := Ideal.minimalPrimes_isPrime hq1
      have xpow_not_q : x^n ∉ q := by
        by_contra hxp
        have := Ideal.IsPrime.mem_of_pow_mem qPrime n hxp
        contradiction
      rw[← hr] at hy
      have : r ∈ q := by
        have := Ideal.IsPrime.mem_or_mem qPrime hy
        subst hr
        simp_all only [bot_le, or_false]
      obtain ⟨a , ha⟩ := Ideal.mem_span_singleton'.mp (hq2 this)
      apply Ideal.mem_span_singleton'.mpr
      rw[← ha] at hr
      use a
      rw[← hr]
      ring
  have x_not_top : Ideal.span {x} ≠ ⊤ := Ideal.IsPrime.ne_top ‹_›
  have KIT := Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {x}) ‹_›
  have qZero : q ≤ ⊥ := by
    intro y hy
    have hyx : ∀(n : ℕ), y ∈ Ideal.span {x} ^ n := by
      intro n
      exact q_in_x_pow n hy
    have := Ideal.mem_iInf.mpr hyx
    rw[KIT] at this
    assumption
  have qeqZero : q = ⊥ := (Submodule.eq_bot_iff q).mpr qZero
  have qPrime : q.IsPrime := Ideal.minimalPrimes_isPrime hq1
  rw[qeqZero] at qPrime
  exact IsDomain.of_bot_isPrime R

theorem IsRegularLocalRing.IsDomain_Induction :
    ∀(n : ℕ) (R : Type*) [CommRing R] [IsRegularLocalRing R]
    (_ : Submodule.spanFinrank (maxl R) = n), IsDomain R := by
  intro n
  induction n with
  | zero =>
    intro R _ hR hm
    have : ringKrullDim R = 0 := by
      rw[← hR.reg]
      simp only [Nat.cast_eq_zero]
      rw[IsLocalRing.Embdim_eq_spanFinrank_maximalIdeal]
      exact hm
    let FS : Field R := IsField.toField (IsRegularLocalRing.ringKrullDim_zero_IsField R this)
    exact Field.isDomain
  | succ n ih =>
    intro R _ hR hn
    by_contra hR_not_Dom
    have isMinPrime : ∀(x : R), (x ∈ maxl R) → (x ∉ (maxl R)^2) →
    (Ideal.span {x} ∈ minimalPrimes R) := by
      intro x hx hx2
      have xPrime : (Ideal.span {x}).IsPrime := by
        apply (Ideal.Quotient.isDomain_iff_prime (Ideal.span {x})).mp
        have _ : Nontrivial (R ⧸ (Ideal.span {x})) :=
          Ideal.Quotient.nontrivial (Ideal.span_singleton_ne_top hx)
        have minGenquot : Submodule.spanFinrank (maxl (R ⧸ (Ideal.span {x}))) = n := by
          have := IsLocalRing.Quotient_span_singleton_spanFinrank x hx hx2
          simp_all only [Nat.add_left_inj]
        have quotReg : IsRegularLocalRing (R ⧸ (Ideal.span {x})) :=
          IsRegularLocalRing.Quotient_span_singleton_IsRegularLocalRing x hx hx2
        exact ih (R ⧸ (Ideal.span {x})) minGenquot
      by_contra hx3
      exact hR_not_Dom
        (IsLocalRing.IsNoetherianRing_span_singleton_IsPrime_not_minimalPrimes_IsDomain x hx3)
    clear ih
    let S' := (minimalPrimes R) ∪ {(maxl R)^2}
    have sFin : S'.Finite := Set.Finite.union
      (minimalPrimes.finite_of_isNoetherianRing R) (Set.finite_singleton ((maxl R) ^ 2))
    let S := Set.Finite.toFinset sFin
    have hp : (∀ i ∈ S, (i ≠ (maxl R)^2) → (i ≠ (maxl R)^2) → i.IsPrime) := by
      intro I hI hm1 _
      have : I ∈ S' := (Set.Finite.mem_toFinset sFin).mp hI
      obtain h1|h2 := this
      exact Ideal.minimalPrimes_isPrime h1
      contradiction
    have maxinmin : ∃ i ∈ S, (maxl R) ≤ i := by
      apply (@Ideal.subset_union_prime (Ideal R) R _ S (fun x => x) ((maxl R)^2) ((maxl R)^2) hp
        (maxl R)).mp
      intro x hx
      obtain xinm2|xnotinm2 := Classical.em (x ∈ (maxl R) ^ 2)
      refine Set.mem_iUnion₂.mpr ?_
      use ((maxl R)^2)
      use (Set.Finite.mem_toFinset sFin).mpr (Set.mem_union_right (minimalPrimes R) rfl)
      exact xinm2
      have xminP := isMinPrime x hx xnotinm2
      refine Set.mem_iUnion₂.mpr ?_
      use Ideal.span {x}
      use (Set.Finite.mem_toFinset sFin).mpr (Set.mem_union_left {(maxl R) ^ 2}
      (isMinPrime x hx xnotinm2))
      exact Ideal.mem_span_singleton_self x
    obtain ⟨P, hP1, hP2⟩ := maxinmin
    have dimNotZero : ringKrullDim R ≠ 0 := by
      rw[← hR.reg, IsLocalRing.Embdim_eq_spanFinrank_maximalIdeal, hn]
      have : n+1 ≠ 0 := Ne.symm (Nat.zero_ne_add_one n)
      exact Nat.cast_ne_zero.mpr this
    apply dimNotZero
    clear hn hR_not_Dom isMinPrime dimNotZero hp
    obtain h1|h2 := (Set.Finite.mem_toFinset sFin).mp hP1
    · clear hP1 S sFin S'
      rw[← ringKrullDimZero_iff_ringKrullDim_eq_zero]
      refine Ring.KrullDimLE.mk₀ ?_
      intro I hI
      have : I ≤ maxl R := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top hI)
      have : I ≤ P := fun ⦃x⦄ a ↦ hP2 (this a)
      have IP := le_minimalPrimes ‹_› this
      have mP := le_minimalPrimes ‹_› hP2
      have Im : I = maxl R := by
        rw[IP, mP]
      rw[Im]
      exact IsLocalRing.maximalIdeal.isMaximal R
    have hm : (maxl R) ≤ (maxl R)^2 := by
      simp_all only [Set.union_singleton, Set.Finite.mem_toFinset, Set.mem_insert_iff,
      Set.mem_singleton_iff, true_or, S, S']
    have mFG := (isNoetherianRing_iff_ideal_fg R).mp inferInstance maxl R
    have mlem2 : (maxl R) ≤ (maxl R) • (maxl R) := by
      have : (maxl R) • (maxl R) = (maxl R) * (maxl R) := rfl
      rw[this, Eq.symm (pow_two maxl R)]
      exact hm
    have mlejac : (maxl R) ≤ Ideal.jacobson ⊥ := by
      have : (⊥ : Ideal R) ≠ ⊤ := bot_ne_top
      rw[IsLocalRing.jacobson_eq_maximalIdeal ⊥ this]
    have mbot :=
      @Submodule.eq_bot_of_le_smul_of_le_jacobson_bot R R _ _ _ (maxl R) (maxl R) mFG mlem2 mlejac
    exact ringKrullDim_eq_zero_of_isField (IsLocalRing.isField_iff_maximalIdeal_eq.mpr mbot)

/-- Regular local rings are integral domains. -/
theorem IsRegularLocalRing.IsDomain
{R : Type*} [CommRing R] [IsRegularLocalRing R] :
    IsDomain R :=
  IsRegularLocalRing.IsDomain_Induction (Submodule.spanFinrank maxl R) R rfl

instance inst_IsRegularLocalRing_IsDomain
{R : Type*} [CommRing R] [IsRegularLocalRing R] :
    IsDomain R := IsRegularLocalRing.IsDomain

/-- A regular local ring of dimension `1` is a discrete valuation ring. -/
theorem IsLocalRing.IsDiscreteValuationRing_iff_IsRegularLocalRing_ringKrullDim_one
    (R : Type*) [CommRing R] [hR : IsRegularLocalRing R] :
    ringKrullDim R = 1 → IsDiscreteValuationRing R := by
  rw[← IsLocalRing.finrank_CotangentSpace_eq_one_iff, ← hR.reg]
  simp_all only [Nat.cast_eq_one]
  exact fun a => a
