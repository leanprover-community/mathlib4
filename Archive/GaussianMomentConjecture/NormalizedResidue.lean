/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.ChannelDilation
import Archive.GaussianMomentConjecture.FrobeniusResidue
import Archive.GaussianMomentConjecture.NormalizedMoment
import Archive.GaussianMomentConjecture.ResidueAssembly
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Embedding.Basic

/-!
# Normalized GMC(2) residue on an indexed lowest face

This module is the concrete junction between the indexed Wick-channel sum,
face dilation, and the three characteristic-`p` residue cases.  The geometric
input is deliberately stated for an arbitrary indexed face `F : Finset ι`:

* balanced mass-`p*m0` channels have height at least `p*A0` (the hypothesis
  needed upstream to relate raw and normalized moments);
* balanced mass-`m0` channels supported on `F` have height exactly `A0`;
* balanced mass-`m0` channels not supported on `F` have height at least
  `A0 + 1`.

The residue proof then has no hidden geometry.  Non-dilated channels vanish
through their multinomial coefficient, dilated off-face channels vanish
through their normalized factorial, and face channels survive as the
Frobenius power of the balanced integral face sum.
-/

open Finset MvPolynomial

namespace GMC2.NormalizedResidue

variable {ι R : Type*} [Fintype ι] [DecidableEq ι]

/-- Pointwise dilation on a full indexed multiplicity vector. -/
def fullDilate (p : ℕ) (r : ι → ℕ) : ι → ℕ :=
  fun i ↦ p * r i

/-- Division by `p`, used only on channels known to be componentwise
`p`-divisible. -/
def undilate (p : ℕ) (r : ι → ℕ) : ι → ℕ :=
  fun i ↦ r i / p

/-- A channel is supported on the indexed face `F`. -/
def SupportedOn (F : Finset ι) (r : ι → ℕ) : Prop :=
  ∀ i, i ∉ F → r i = 0

noncomputable instance instDecidableSupportedOn (F : Finset ι) (r : ι → ℕ) :
    Decidable (SupportedOn F r) :=
  Classical.propDecidable _

/-- Positive pointwise dilation as an embedding. -/
def fullDilationEmbedding (p : ℕ) (hp : 0 < p) :
    (ι → ℕ) ↪ (ι → ℕ) :=
  ⟨fullDilate p, by
    intro r s hrs
    funext i
    exact Nat.eq_of_mul_eq_mul_left hp (congrFun hrs i)⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem fullDilationEmbedding_apply (p : ℕ) (hp : 0 < p)
    (r : ι → ℕ) :
    fullDilationEmbedding p hp r = fullDilate p r :=
  rfl

omit [Fintype ι] in
@[simp] theorem faceDilationEmbedding_apply (p : ℕ) (hp : 0 < p)
    (F : Finset ι) (s : ↥F → ℕ) :
    GMC2.ChannelDilation.dilationEmbedding p hp F s =
      GMC2.ChannelDilation.dilate p F s :=
  rfl

/-- All channels of the amplified mass `p*m0`. -/
noncomputable def fullChannels (p m0 : ℕ) : Finset (ι → ℕ) :=
  Finset.piAntidiag (Finset.univ : Finset ι) (p * m0)

/-- The exact image of all mass-`m0` channels under pointwise dilation. -/
noncomputable def dilatedChannels (p : ℕ) (hp : 0 < p) (m0 : ℕ) :
    Finset (ι → ℕ) :=
  (Finset.piAntidiag (Finset.univ : Finset ι) m0).map
    (fullDilationEmbedding p hp)

/-- The exact dilation image of mass-`m0` channels supported on `F`.  It is
left unfiltered by balance so that support, dilation, and balance remain three
separate pieces of structure. -/
noncomputable def faceChannels (p : ℕ) (hp : 0 < p)
    (F : Finset ι) (m0 : ℕ) : Finset (ι → ℕ) :=
  (Finset.piAntidiag (Finset.univ : Finset ↥F) m0).map
    (GMC2.ChannelDilation.dilationEmbedding p hp F)

/-- Balanced undilated face channels, the index set of the integral face
constant-term sum. -/
noncomputable def balancedFaceChannels
    (exponent : ι → Fin 2 →₀ ℕ) (F : Finset ι) (m0 : ℕ) :
    Finset (↥F → ℕ) :=
  (Finset.piAntidiag (Finset.univ : Finset ↥F) m0).filter
    (fun s ↦ GMC2.NormalizedMoment.IsBalanced exponent
      (GMC2.ChannelDilation.extendByZero F s))

/-- One summand of the evaluated normalized moment relation. -/
noncomputable def normalizedTerm [CommRing R]
    (exponent : ι → Fin 2 →₀ ℕ) (coefficient : ι → R)
    (Amin : ℕ) (r : ι → ℕ) : R :=
  if GMC2.NormalizedMoment.IsBalanced exponent r then
    (Nat.multinomial Finset.univ r : R) *
      (∏ i, coefficient i ^ r i) *
        (GMC2.NormalizedMoment.normalizedFactorial Amin
          (GMC2.NormalizedMoment.channelHeight exponent r) : R)
  else 0

/-- The undilated balanced multinomial weight attached to a dilated channel.
It is zero on unbalanced channels. -/
noncomputable def residueWeight (p : ℕ)
    (exponent : ι → Fin 2 →₀ ℕ) (r : ι → ℕ) : ℕ :=
  if GMC2.NormalizedMoment.IsBalanced exponent (undilate p r) then
    Nat.multinomial Finset.univ (undilate p r)
  else 0

/-- The coefficient monomial of the undilated channel. -/
def residueCoefficient [CommMonoid R]
    (p : ℕ) (coefficient : ι → R) (r : ι → ℕ) : R :=
  ∏ i, coefficient i ^ undilate p r i

/-- Coefficient monomial of a face multiplicity vector. -/
def faceMonomial [CommMonoid R]
    (coefficient : ι → R) {F : Finset ι} (s : ↥F → ℕ) : R :=
  ∏ i : ↥F, coefficient i ^ s i

/-- The balanced integral face constant-term sum before Frobenius
amplification. -/
noncomputable def faceConstantTerm [CommRing R]
    (exponent : ι → Fin 2 →₀ ℕ) (coefficient : ι → R)
    (F : Finset ι) (m0 : ℕ) : R :=
  ∑ s ∈ balancedFaceChannels exponent F m0,
    (Nat.multinomial Finset.univ
        (GMC2.ChannelDilation.extendByZero F s) : R) *
      faceMonomial coefficient s

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem undilate_fullDilate {p : ℕ} (hp : 0 < p) (r : ι → ℕ) :
    undilate p (fullDilate p r) = r := by
  funext i
  simp [undilate, fullDilate, hp]

omit [Fintype ι] in
theorem faceDilate_eq_fullDilate (p : ℕ) (F : Finset ι) (s : ↥F → ℕ) :
    GMC2.ChannelDilation.dilate p F s =
      fullDilate p (GMC2.ChannelDilation.extendByZero F s) :=
  rfl

omit [DecidableEq ι] in
/-- Full mass scales exactly under pointwise dilation. -/
theorem sum_fullDilate (p : ℕ) (r : ι → ℕ) :
    ∑ i, fullDilate p r i = p * ∑ i, r i := by
  simp only [fullDilate]
  rw [Finset.mul_sum]

omit [DecidableEq ι] in
/-- Exact accumulated bidegree scaling for a full channel. -/
theorem channelExponent_fullDilate
    (p : ℕ) (exponent : ι → Fin 2 →₀ ℕ) (r : ι → ℕ) :
    GMC2.MomentRelations.channelExponent exponent (fullDilate p r) =
      p • GMC2.MomentRelations.channelExponent exponent r := by
  unfold GMC2.MomentRelations.channelExponent
  calc
    ∑ i, (fullDilate p r i) • exponent i =
        ∑ i, p • ((r i) • exponent i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [fullDilate, Nat.mul_comm, mul_nsmul]
    _ = p • ∑ i, (r i) • exponent i := by
      rw [Finset.sum_nsmul]

omit [DecidableEq ι] in
/-- Height is the first coordinate of the accumulated bidegree, so it scales
by `p` as well. -/
theorem channelHeight_fullDilate
    (p : ℕ) (exponent : ι → Fin 2 →₀ ℕ) (r : ι → ℕ) :
    GMC2.NormalizedMoment.channelHeight exponent (fullDilate p r) =
      p * GMC2.NormalizedMoment.channelHeight exponent r := by
  have h := congrArg (fun e : Fin 2 →₀ ℕ ↦ e 0)
    (channelExponent_fullDilate p exponent r)
  simpa [GMC2.NormalizedMoment.channelHeight, nsmul_eq_mul] using h

omit [DecidableEq ι] in
/-- Positive dilation preserves and reflects balance. -/
theorem isBalanced_fullDilate_iff {p : ℕ} (hp : 0 < p)
    (exponent : ι → Fin 2 →₀ ℕ) (r : ι → ℕ) :
    GMC2.NormalizedMoment.IsBalanced exponent (fullDilate p r) ↔
      GMC2.NormalizedMoment.IsBalanced exponent r := by
  unfold GMC2.NormalizedMoment.IsBalanced
  rw [channelExponent_fullDilate]
  constructor
  · intro h
    apply Nat.eq_of_mul_eq_mul_left hp
    simpa [nsmul_eq_mul] using h
  · intro h
    simp [h]

/-- Extension by zero sends the face antidiagonal into the full
antidiagonal of the same mass. -/
theorem extendByZero_mem_piAntidiag {m0 : ℕ}
    (F : Finset ι) (s : ↥F → ℕ)
    (hs : s ∈ Finset.piAntidiag (Finset.univ : Finset ↥F) m0) :
    GMC2.ChannelDilation.extendByZero F s ∈
      Finset.piAntidiag (Finset.univ : Finset ι) m0 := by
  rw [Finset.mem_piAntidiag] at hs ⊢
  constructor
  · calc
      ∑ i, GMC2.ChannelDilation.extendByZero F s i =
          ∑ i : ↥F, s i := by
            exact GMC2.ChannelDilation.sum_extendByZero F s
              (fun _ n ↦ n) (fun _ ↦ rfl)
      _ = m0 := hs.1
  · simp

/-- Pointwise dilation sends the full mass-`m0` antidiagonal into the
mass-`p*m0` antidiagonal. -/
theorem fullDilate_mem_piAntidiag {p m0 : ℕ} (r : ι → ℕ)
    (hr : r ∈ Finset.piAntidiag (Finset.univ : Finset ι) m0) :
    fullDilate p r ∈ fullChannels p m0 := by
  rw [Finset.mem_piAntidiag] at hr
  rw [fullChannels, Finset.mem_piAntidiag]
  constructor
  · calc
      ∑ i, fullDilate p r i = p * ∑ i, r i := sum_fullDilate p r
      _ = p * m0 := congrArg (fun n ↦ p * n) hr.1
  · simp

/-- Exact characterization of the full dilation image. -/
theorem mem_dilatedChannels_iff {p m0 : ℕ} (hp : 0 < p) (r : ι → ℕ) :
    r ∈ dilatedChannels p hp m0 ↔
      r ∈ fullChannels p m0 ∧ ∀ i, p ∣ r i := by
  constructor
  · intro hr
    rw [dilatedChannels, Finset.mem_map] at hr
    obtain ⟨s, hs, rfl⟩ := hr
    refine ⟨fullDilate_mem_piAntidiag s hs, ?_⟩
    intro i
    exact ⟨s i, rfl⟩
  · rintro ⟨hr, hdvd⟩
    let s : ι → ℕ := undilate p r
    have hsr : fullDilate p s = r := by
      funext i
      exact Nat.mul_div_cancel' (hdvd i)
    have hs : s ∈ Finset.piAntidiag (Finset.univ : Finset ι) m0 := by
      rw [Finset.mem_piAntidiag]
      constructor
      · apply Nat.eq_of_mul_eq_mul_left hp
        calc
          p * ∑ i, s i = ∑ i, fullDilate p s i :=
            (sum_fullDilate p s).symm
          _ = ∑ i, r i := by rw [hsr]
          _ = p * m0 := (Finset.mem_piAntidiag.mp hr).1
      · simp
    rw [dilatedChannels, Finset.mem_map]
    exact ⟨s, hs, hsr⟩

/-- The face dilation image is exactly the support-and-divisibility slice of
the full amplified antidiagonal. -/
theorem faceChannels_eq_filter {p m0 : ℕ} (hp : 0 < p) (F : Finset ι) :
    faceChannels p hp F m0 =
      (fullChannels p m0).filter
        (fun r ↦ SupportedOn F r ∧ ∀ i, i ∈ F → p ∣ r i) := by
  classical
  simp only [faceChannels, fullChannels, SupportedOn]
  convert GMC2.ChannelDilation.map_piAntidiag_dilation (ι := ι) (m := m0) hp F using 2
  exact Finset.filter_congr_decidable _ _ _

theorem faceChannels_subset_dilated {p m0 : ℕ} (hp : 0 < p)
    (F : Finset ι) :
    faceChannels p hp F m0 ⊆ dilatedChannels p hp m0 := by
  intro r hr
  have hfilter : r ∈ (fullChannels p m0).filter
      (fun r ↦ SupportedOn F r ∧ ∀ i, i ∈ F → p ∣ r i) := by
    simpa only [faceChannels_eq_filter hp F] using hr
  have hdata := Finset.mem_filter.mp hfilter
  refine (mem_dilatedChannels_iff (ι := ι) hp r).2 ⟨hdata.1, ?_⟩
  intro i
  by_cases hi : i ∈ F
  · exact hdata.2.2 i hi
  · rw [hdata.2.1 i hi]
    exact dvd_zero p

theorem dilatedChannels_subset_full {p m0 : ℕ} (hp : 0 < p) :
    dilatedChannels (ι := ι) p hp m0 ⊆
      fullChannels (ι := ι) p m0 := by
  intro r hr
  have hdata :=
    (mem_dilatedChannels_iff (ι := ι) (p := p) (m0 := m0) hp r).1 hr
  exact hdata.1

/-- A full amplified channel outside the exact dilation image has a
multinomial coefficient divisible by `p`. -/
theorem prime_dvd_multinomial_of_not_mem_dilated
    {p m0 : ℕ} [Fact p.Prime] (hp : 0 < p) (r : ι → ℕ)
    (hr : r ∈ fullChannels p m0)
    (hrNot : r ∉ dilatedChannels p hp m0) :
    p ∣ Nat.multinomial Finset.univ r := by
  have hnotAll : ¬ ∀ i, p ∣ r i := by
    intro hdvd
    exact hrNot ((mem_dilatedChannels_iff (ι := ι) hp r).2 ⟨hr, hdvd⟩)
  push Not at hnotAll
  obtain ⟨i, hi⟩ := hnotAll
  apply GMC2.FrobeniusResidue.multinomial_dvd_of_exists_not_dvd
    (Fact.out : Nat.Prime p) Finset.univ r
  · rw [(Finset.mem_piAntidiag.mp hr).1]
    exact dvd_mul_right p m0
  · exact ⟨i, Finset.mem_univ i, hi⟩

/-- The non-dilated residue case: the multinomial coefficient vanishes in
characteristic `p`. -/
theorem normalizedTerm_eq_zero_of_not_dilated
    [Field R] {p m0 Amin : ℕ} [Fact p.Prime] [CharP R p]
    (hp : 0 < p) (exponent : ι → Fin 2 →₀ ℕ) (coefficient : ι → R)
    (r : ι → ℕ) (hr : r ∈ fullChannels p m0)
    (hrNot : r ∉ dilatedChannels p hp m0) :
    normalizedTerm exponent coefficient Amin r = 0 := by
  by_cases hbalanced : GMC2.NormalizedMoment.IsBalanced exponent r
  · have hdvd := prime_dvd_multinomial_of_not_mem_dilated hp r hr hrNot
    have hcast : (Nat.multinomial Finset.univ r : R) = 0 :=
      (CharP.cast_eq_zero_iff R p _).2 hdvd
    simp [normalizedTerm, hbalanced, hcast]
  · simp [normalizedTerm, hbalanced]

/-- The dilated off-face residue case: the one-step base-height gap inserts
a factor `p` into the normalized factorial quotient. -/
theorem normalizedTerm_eq_zero_of_dilated_not_face
    [Field R] {p m0 A0 : ℕ} [Fact p.Prime] [CharP R p]
    (hp : 0 < p) (exponent : ι → Fin 2 →₀ ℕ) (coefficient : ι → R)
    (F : Finset ι)
    (hoffHeight : ∀ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) m0,
      GMC2.NormalizedMoment.IsBalanced exponent r →
      ¬ SupportedOn F r →
      A0 + 1 ≤ GMC2.NormalizedMoment.channelHeight exponent r)
    (r : ι → ℕ) (hr : r ∈ dilatedChannels p hp m0)
    (hrNotFace : r ∉ faceChannels p hp F m0) :
    normalizedTerm exponent coefficient (p * A0) r = 0 := by
  rw [dilatedChannels, Finset.mem_map] at hr
  obtain ⟨s, hs, hsr⟩ := hr
  change fullDilate p s = r at hsr
  subst r
  by_cases hbalanced :
      GMC2.NormalizedMoment.IsBalanced exponent (fullDilate p s)
  · have hsBalanced : GMC2.NormalizedMoment.IsBalanced exponent s :=
      (isBalanced_fullDilate_iff hp exponent s).1 hbalanced
    have hsNotSupported : ¬ SupportedOn F s := by
      intro hsSupported
      apply hrNotFace
      rw [faceChannels_eq_filter hp F, Finset.mem_filter]
      refine ⟨fullDilate_mem_piAntidiag s hs, ?_, fun i hi ↦ ⟨s i, rfl⟩⟩
      intro i hi
      simp [fullDilate, hsSupported i hi]
    have hgap := hoffHeight s hs hsBalanced hsNotSupported
    have hdvd : p ∣ GMC2.NormalizedMoment.normalizedFactorial
        (p * A0)
        (GMC2.NormalizedMoment.channelHeight exponent (fullDilate p s)) := by
      rw [channelHeight_fullDilate]
      simpa [GMC2.NormalizedMoment.normalizedFactorial] using
        (GMC2.FrobeniusResidue.prime_dvd_normalized_factorial_of_gap
          p A0 (GMC2.NormalizedMoment.channelHeight exponent s)
          (Fact.out : Nat.Prime p) hgap)
    have hcast :
        (GMC2.NormalizedMoment.normalizedFactorial (p * A0)
          (GMC2.NormalizedMoment.channelHeight exponent (fullDilate p s)) : R) = 0 :=
      (CharP.cast_eq_zero_iff R p _).2 hdvd
    simp [normalizedTerm, hbalanced, hcast]
  · simp [normalizedTerm, hbalanced]

/-- The on-face residue case, term by term.  Its normalized factorial is one,
Lucas identifies the multinomial weight, and its coefficient monomial is a
`p`-th power. -/
theorem normalizedTerm_eq_face_frobenius_term
    [Field R] {p m0 A0 : ℕ} [Fact p.Prime] [CharP R p]
    (hp : 0 < p) (exponent : ι → Fin 2 →₀ ℕ) (coefficient : ι → R)
    (F : Finset ι)
    (hfaceHeight : ∀ s ∈
        Finset.piAntidiag (Finset.univ : Finset ↥F) m0,
      GMC2.NormalizedMoment.IsBalanced exponent
        (GMC2.ChannelDilation.extendByZero F s) →
      GMC2.NormalizedMoment.channelHeight exponent
        (GMC2.ChannelDilation.extendByZero F s) = A0)
    (r : ι → ℕ) (hr : r ∈ faceChannels p hp F m0) :
    normalizedTerm exponent coefficient (p * A0) r =
      (residueWeight p exponent r : R) *
        (residueCoefficient p coefficient r) ^ p := by
  rw [faceChannels, Finset.mem_map] at hr
  obtain ⟨s, hs, hsr⟩ := hr
  change GMC2.ChannelDilation.dilate p F s = r at hsr
  subst r
  let t : ι → ℕ := GMC2.ChannelDilation.extendByZero F s
  change normalizedTerm exponent coefficient (p * A0) (fullDilate p t) =
    (residueWeight p exponent (fullDilate p t) : R) *
      residueCoefficient p coefficient (fullDilate p t) ^ p
  by_cases hsBalanced : GMC2.NormalizedMoment.IsBalanced exponent t
  · have hdilatedBalanced : GMC2.NormalizedMoment.IsBalanced exponent
        (fullDilate p t) :=
      (isBalanced_fullDilate_iff hp exponent t).2 hsBalanced
    have hsBalanced' : GMC2.NormalizedMoment.IsBalanced exponent
        (GMC2.ChannelDilation.extendByZero F s) := by
      simpa [t] using hsBalanced
    have hheight : GMC2.NormalizedMoment.channelHeight exponent
        (fullDilate p t) = p * A0 := by
      rw [channelHeight_fullDilate]
      simpa [t] using congrArg (fun n ↦ p * n)
        (hfaceHeight s hs hsBalanced')
    have hfactorial : GMC2.NormalizedMoment.normalizedFactorial
        (p * A0)
        (GMC2.NormalizedMoment.channelHeight exponent
          (fullDilate p t)) = 1 := by
      rw [hheight]
      exact Nat.div_self (Nat.factorial_pos _)
    have hmultinomial :
        (Nat.multinomial Finset.univ
          (fullDilate p t) : R) =
        (Nat.multinomial Finset.univ t : R) := by
      apply (CharP.cast_eq_iff_mod_eq R p).2
      simpa [Nat.ModEq, show fullDilate p t = fun i ↦ p * t i from rfl] using
        (GMC2.FrobeniusResidue.multinomial_dilate_modEq p
          (Finset.univ : Finset ι) t)
    have htargetProduct :
        (∏ i, coefficient i ^ fullDilate p t i) =
          (∏ i, coefficient i ^ t i) ^ p := by
      calc
        ∏ i, coefficient i ^ fullDilate p t i =
            ∏ i, (coefficient i ^ t i) ^ p := by
              apply Finset.prod_congr rfl
              intro i hi
              rw [fullDilate, Nat.mul_comm, pow_mul]
        _ = (∏ i, coefficient i ^ t i) ^ p := by
          rw [Finset.prod_pow]
    simp only [normalizedTerm, if_pos hdilatedBalanced]
    rw [hfactorial, Nat.cast_one, mul_one, hmultinomial, htargetProduct]
    simp [residueWeight, residueCoefficient, undilate_fullDilate hp,
      hsBalanced]
  · have hdilatedNotBalanced : ¬ GMC2.NormalizedMoment.IsBalanced exponent
        (fullDilate p t) := fun h ↦
      hsBalanced ((isBalanced_fullDilate_iff hp exponent t).1 h)
    simp [normalizedTerm, hdilatedNotBalanced, residueWeight,
      undilate_fullDilate hp, hsBalanced]

/-- Reindexing the exact face dilation image recovers the balanced integral
face constant-term sum. -/
theorem face_base_sum_reindex
    [CommRing R] {p m0 : ℕ} (hp : 0 < p)
    (exponent : ι → Fin 2 →₀ ℕ) (coefficient : ι → R)
    (F : Finset ι) :
    ∑ r ∈ faceChannels p hp F m0,
        (residueWeight p exponent r : R) *
          residueCoefficient p coefficient r =
      faceConstantTerm exponent coefficient F m0 := by
  classical
  rw [faceChannels]
  rw [GMC2.ChannelDilation.sum_map_dilation hp F]
  rw [faceConstantTerm, balancedFaceChannels, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hbalanced : GMC2.NormalizedMoment.IsBalanced exponent
      (GMC2.ChannelDilation.extendByZero F s)
  · have hproduct :
        residueCoefficient p coefficient
          (fullDilate p (GMC2.ChannelDilation.extendByZero F s)) =
          faceMonomial coefficient s := by
      rw [residueCoefficient]
      simp only [undilate_fullDilate hp]
      simpa [faceMonomial] using
        (GMC2.ChannelDilation.prod_extendByZero F s
          (fun i n ↦ coefficient i ^ n) (fun _ ↦ pow_zero _))
    simp only [residueWeight, faceDilate_eq_fullDilate,
      undilate_fullDilate hp, if_pos hbalanced]
    rw [hproduct]
  · simp [residueWeight, faceDilate_eq_fullDilate,
      undilate_fullDilate hp, hbalanced]

/-- Compatibility with the integrated Frobenius face-sum theorem. -/
theorem balancedFace_sum_frobenius
    [Field R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (exponent : ι → Fin 2 →₀ ℕ) (coefficient : ι → R)
    (F : Finset ι) (m0 : ℕ) :
    ∑ s ∈ balancedFaceChannels exponent F m0,
        (Nat.multinomial Finset.univ
          (fun i ↦ p * GMC2.ChannelDilation.extendByZero F s i) : R) *
          (faceMonomial coefficient s) ^ p =
      (faceConstantTerm exponent coefficient F m0) ^ p := by
  unfold faceConstantTerm
  exact GMC2.FrobeniusResidue.face_sum_frobenius p
    (Finset.univ : Finset ι)
    (balancedFaceChannels exponent F m0)
    (fun s ↦ GMC2.ChannelDilation.extendByZero F s)
    (fun s ↦ faceMonomial coefficient s)

/-- Concrete three-case normalized residue identity on an indexed face. -/
theorem aeval_normalizedMoment_eq_faceConstantTerm_pow
    [Field R] (p m0 A0 : ℕ) [Fact p.Prime] [CharP R p]
    (exponent : ι → Fin 2 →₀ ℕ) (coefficient : ι → R)
    (F : Finset ι)
    (_hfullFloor : ∀ r ∈ fullChannels p m0,
      GMC2.NormalizedMoment.IsBalanced exponent r →
      p * A0 ≤ GMC2.NormalizedMoment.channelHeight exponent r)
    (hfaceHeight : ∀ s ∈
        Finset.piAntidiag (Finset.univ : Finset ↥F) m0,
      GMC2.NormalizedMoment.IsBalanced exponent
        (GMC2.ChannelDilation.extendByZero F s) →
      GMC2.NormalizedMoment.channelHeight exponent
        (GMC2.ChannelDilation.extendByZero F s) = A0)
    (hoffHeight : ∀ r ∈ Finset.piAntidiag
        (Finset.univ : Finset ι) m0,
      GMC2.NormalizedMoment.IsBalanced exponent r →
      ¬ SupportedOn F r →
      A0 + 1 ≤ GMC2.NormalizedMoment.channelHeight exponent r) :
    MvPolynomial.aeval coefficient
        (GMC2.NormalizedMoment.normalizedMomentRelationInt
          exponent (p * m0) (p * A0)) =
      (faceConstantTerm exponent coefficient F m0) ^ p := by
  letI : ExpChar R p := ExpChar.prime Fact.out
  rw [GMC2.NormalizedMoment.aeval_normalizedMomentRelationInt]
  change
    (∑ r ∈ fullChannels p m0,
      normalizedTerm exponent coefficient (p * A0) r) = _
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  calc
    ∑ r ∈ fullChannels p m0,
        normalizedTerm exponent coefficient (p * A0) r =
      (∑ r ∈ faceChannels p hp F m0,
        (residueWeight p exponent r : R) *
          residueCoefficient p coefficient r) ^ p := by
      exact GMC2.ResidueAssembly.three_case_sum_eq_frobenius
        p (fullChannels p m0) (dilatedChannels p hp m0)
        (faceChannels p hp F m0)
        (normalizedTerm exponent coefficient (p * A0))
        (residueWeight p exponent) (residueCoefficient p coefficient)
        (faceChannels_subset_dilated hp F)
        (dilatedChannels_subset_full hp)
        (fun r hr hrNot ↦
          normalizedTerm_eq_zero_of_not_dilated hp exponent coefficient
            r hr hrNot)
        (fun r hr hrNotFace ↦
          normalizedTerm_eq_zero_of_dilated_not_face hp exponent coefficient
            F hoffHeight r hr hrNotFace)
        (fun r hrFace ↦
          normalizedTerm_eq_face_frobenius_term hp exponent coefficient
            F hfaceHeight r hrFace)
    _ = (faceConstantTerm exponent coefficient F m0) ^ p := by
      rw [face_base_sum_reindex hp exponent coefficient F]

/-- Nonvanishing of the balanced face constant term survives in the evaluated
normalized moment residue. -/
theorem aeval_normalizedMoment_ne_zero
    [Field R] (p m0 A0 : ℕ) [Fact p.Prime] [CharP R p]
    (exponent : ι → Fin 2 →₀ ℕ) (coefficient : ι → R)
    (F : Finset ι)
    (hfullFloor : ∀ r ∈ fullChannels p m0,
      GMC2.NormalizedMoment.IsBalanced exponent r →
      p * A0 ≤ GMC2.NormalizedMoment.channelHeight exponent r)
    (hfaceHeight : ∀ s ∈
        Finset.piAntidiag (Finset.univ : Finset ↥F) m0,
      GMC2.NormalizedMoment.IsBalanced exponent
        (GMC2.ChannelDilation.extendByZero F s) →
      GMC2.NormalizedMoment.channelHeight exponent
        (GMC2.ChannelDilation.extendByZero F s) = A0)
    (hoffHeight : ∀ r ∈ Finset.piAntidiag
        (Finset.univ : Finset ι) m0,
      GMC2.NormalizedMoment.IsBalanced exponent r →
      ¬ SupportedOn F r →
      A0 + 1 ≤ GMC2.NormalizedMoment.channelHeight exponent r)
    (hfaceNonzero : faceConstantTerm exponent coefficient F m0 ≠ 0) :
    MvPolynomial.aeval coefficient
        (GMC2.NormalizedMoment.normalizedMomentRelationInt
          exponent (p * m0) (p * A0)) ≠ 0 := by
  rw [aeval_normalizedMoment_eq_faceConstantTerm_pow
    p m0 A0 exponent coefficient F hfullFloor hfaceHeight hoffHeight]
  exact pow_ne_zero p hfaceNonzero

end GMC2.NormalizedResidue
