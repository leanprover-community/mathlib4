/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Real.Spectrum
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.UnitizationL1
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Algebra.Module.Spaces.CharacterSpace
public import Mathlib.Topology.Semicontinuity.Hemicontinuity

/-!
# The spectrum of elements in a complete normed algebra

This file contains the basic theory for the resolvent and spectrum of a Banach algebra.
Theorems specific to *complex* Banach algebras, such as *Gelfand's formula* can be found in
`Mathlib/Analysis/Normed/Algebra/GelfandFormula.lean`.

## Main definitions

* `spectralRadius : ℝ≥0∞`: supremum of `‖k‖ₑ` for all `k ∈ quasispectrum 𝕜 a`

## Main statements

* `spectralRadius_le_enorm`: the spectral radius is bounded above by the norm.
* `spectrum.isClosed`/`quasispectrum.isClosed` and `spectrum.isCompact`/`quasispectrum.isCompact`:
  the (quasi)spectrum is closed and, if `𝕜` is proper, compact.
* `Subalgebra.spectrum_eq_union_sUnion_connectedComponentIn`/
  `Subalgebra.isBounded_connectedComponentIn_spectrum_compl`: the spectrum of an element `x : S`
  lying in a closed subalgebra `S` of `A` is the union of the spectrum of `↑x : A` along with some
  of the connected components of the complement of the spectrum of `↑x : A`. Consequently, if the
  complement of the spectrum of `↑x : A` is connected, the spectra of `x : S` and `↑x : A` coincide.
* `spectrum.resolvent_tendsto_cobounded`: the resolvent function tends to zero along `cobounded 𝕜`.
  This is a key step in establishing that the `ℂ`-spectrum is nonempty.
* `upperHemicontinuous_spectrum`/`upperHemicontinuous_quasispectrum`: the (quasi)spectrum is
  upper hemicontinuous.
* `NonUnitalAlgHom.toStrongDual`: multiplicative linear functional are continuous.

## Implementation notes

`spectralRadius` is defined via `quasispectrum` rather than `spectrum` so that it makes sense for
non-unital normed algebras too. When `A` is unital, `quasispectrum 𝕜 a = spectrum 𝕜 a ∪ {0}`
(`quasispectrum_eq_spectrum_union_zero`), and since `0` never increases the supremum defining
`spectralRadius`, `spectralRadius_eq_of_unital` shows this agrees with the supremum over
`spectrum 𝕜 a` alone.
-/

@[expose] public section

variable {𝕜 A : Type*}

local notation "σ" => spectrum
local notation "σₙ" => quasispectrum


assert_not_exists ProbabilityTheory.cond
assert_not_exists HasFDerivAt

open NormedSpace Topology Filter Set WithLp Unitization ENNReal
open scoped ENNReal NNReal Topology Set.Notation

/- The *spectral radius* is the supremum of the `enorm` (`‖·‖ₑ`) of elements in the quasispectrum.

It is also possible that `quasispectrum 𝕜 a` be unbounded (though not for Banach
algebras, see `spectrum.isBounded`/`quasispectrum.isBounded`, below). In this case,
`spectralRadius a = ∞`.

When `A` is unital, `spectrum` and `quasispectrum` differ only by the inclusion of `0` which does
not affect the spectral radius, so in the unital case, one may take the spectral radius to be the
supremum over the spectrum instead of the quasispectrum (see `spectralRadius_eq_of_unital`). -/
@[wikidata Q249748]
noncomputable def spectralRadius (𝕜 : Type*) {A : Type*}
    [NormedField 𝕜] [NonUnitalRing A] [Module 𝕜 A]
    (a : A) : ℝ≥0∞ :=
  ⨆ k ∈ σₙ 𝕜 a, ‖k‖ₑ

/-! ### Elementary properties of the spectral radius in Banach algebras

The spectral radius in a Banach `𝕜`-algebra (or, in fact, in any algebra satisfying
`HasSummableGeomSeries`) is bounded by the norm. Moreover, it is always closed. Therefore,
if `𝕜` is a proper space, then the `𝕜`-(quasi)spectrum is compact. In that setting, the
spectral radius is achieved by some element of the (quasi)spectrum. In addition,
`spectralRadius 𝕜 a ≤ ⨅ n : ℕ, ‖a ^ (n + 1)‖ₑ ^ (1 / (n + 1) : ℝ)`. -/

section NotNormed

variable [NormedField 𝕜] [NonUnitalRing A] [Module 𝕜 A]

@[simp]
theorem spectralRadius_of_subsingleton [Subsingleton A] (a : A) :
    spectralRadius 𝕜 a = 0 := by
  simp [spectralRadius]

@[deprecated (since := "2026-09-21")]
alias spectrum.SpectralRadius.of_subsingleton := spectralRadius_of_subsingleton

@[simp]
theorem spectralRadius_zero : spectralRadius 𝕜 (0 : A) = 0 := by
  simp [spectralRadius]

@[simp]
theorem Unitization.spectralRadius_inr [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] (a : A) :
    spectralRadius 𝕜 (a : Unitization 𝕜 A) = spectralRadius 𝕜 a := by
  simp [spectralRadius, quasispectrum_eq_spectrum_union_zero, ← quasispectrum_eq_spectrum_inr']


-- this should move out of this file. Does it work when `𝕜` is not a (semi)field?
open Pointwise Unitization in
@[simp]
theorem quasispectrum_smul [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] (k : 𝕜) (a : A) :
    σₙ 𝕜 (k • a) = k • σₙ 𝕜 a := by
  ext r
  obtain (rfl | hk) := eq_or_ne k 0
  · simp [Set.zero_smul_set (quasispectrum.nonempty 𝕜 a)]
  · lift k to 𝕜ˣ using IsUnit.mk0 k hk
    simp_rw [quasispectrum_eq_spectrum_inr 𝕜, inr_smul, ← Units.smul_def,
      spectrum.unit_smul_eq_smul]

@[simp]
theorem spectralRadius_smul [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] (k : 𝕜) (a : A) :
    spectralRadius 𝕜 (k • a) = ‖k‖ₑ * spectralRadius 𝕜 a := by
  simp only [spectralRadius, quasispectrum_smul, ← Set.image_smul, iSup_image, ← smul_eq_mul]
  simp [↓ENNReal.smul_iSup, enorm_eq_nnnorm]

end NotNormed

section quasispectrum
open quasispectrum

section Generic

variable [NormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
variable [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

variable (𝕜) in
private lemma quasispectrum_eq_spectrum_toLp_inr (a : A) :
    σₙ 𝕜 a = σ 𝕜 (toLp 1 (a : Unitization 𝕜 A)) := by
  simpa [Unitization.quasispectrum_eq_spectrum_inr 𝕜, unitizationAlgEquiv] using
    AlgEquiv.spectrum_eq (WithLp.unitizationAlgEquiv 𝕜).symm (a : Unitization 𝕜 A) |>.symm

variable [HasSummableGeomSeries A]

private theorem withLp_one_unitization_notMem_of_norm_lt {a : WithLp 1 (Unitization 𝕜 A)} {k : 𝕜}
    (h : ‖a‖ < ‖k‖) : k ∉ σ 𝕜 a := by
  have hk : k ≠ 0 := by grind [norm_nonneg, norm_ne_zero_iff]
  rw [spectrum.notMem_iff, Algebra.algebraMap_eq_smul_one]
  let ku := Units.map (algebraMap 𝕜 (WithLp 1 (Unitization 𝕜 A))).toMonoidHom (Units.mk0 k hk)
  have hku : ‖-a‖ < ‖(↑ku⁻¹ : WithLp 1 (Unitization 𝕜 A))‖⁻¹ := by simpa [ku] using h
  simpa [ku, sub_eq_add_neg, Algebra.algebraMap_eq_smul_one] using (ku.add (-a) hku).isUnit

-- move to another file
attribute [simp] WithLp.unitization_norm_inr

theorem quasispectrum.norm_le_norm_of_mem {a : A} {k : 𝕜} (hk : k ∈ σₙ 𝕜 a) :
    ‖k‖ ≤ ‖a‖ := by
  contrapose! hk
  simpa [quasispectrum_eq_spectrum_toLp_inr] using
    withLp_one_unitization_notMem_of_norm_lt (by simpa)

variable (𝕜) in
theorem spectralRadius_le_enorm (a : A) : spectralRadius 𝕜 a ≤ ‖a‖ₑ :=
  iSup₂_le fun _ ↦ by simpa [enorm_eq_nnnorm] using mod_cast norm_le_norm_of_mem

@[deprecated (since := "2026-09-21")]
alias spectrum.spectralRadius_le_nnnorm := spectralRadius_le_enorm

variable (𝕜) in
theorem quasispectrum.subset_closedBall_norm (a : A) :
    σₙ 𝕜 a ⊆ Metric.closedBall (0 : 𝕜) ‖a‖ :=
  fun _ ↦ by simpa using norm_le_norm_of_mem

variable (𝕜) in
theorem quasispectrum.isBounded (a : A) : Bornology.IsBounded (σₙ 𝕜 a) :=
  Metric.isBounded_closedBall.subset (subset_closedBall_norm 𝕜 a)

variable (𝕜) in
theorem quasispectrum.isClosed (a : A) : IsClosed (σₙ 𝕜 a) := by
  rw [quasispectrum_eq_spectrum_toLp_inr, spectrum, isClosed_compl_iff]
  exact Units.isOpen.preimage (by fun_prop)

variable [ProperSpace 𝕜]

variable (𝕜) in
@[simp]
theorem quasispectrum.isCompact (a : A) : IsCompact (σₙ 𝕜 a) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed 𝕜 a) (isBounded 𝕜 a)

grind_pattern isCompact => IsCompact (σₙ 𝕜 a)

instance quasispectrum.instCompactSpace (a : A) :
    CompactSpace (σₙ 𝕜 a) :=
  isCompact_iff_compactSpace.mp <| isCompact 𝕜 a

variable (𝕜) in
theorem exists_enorm_quasispectrum_eq_spectralRadius (a : A) :
    ∃ k ∈ σₙ 𝕜 a, ‖k‖ₑ = spectralRadius 𝕜 a := by
  obtain ⟨k, hk, h⟩ := (isCompact 𝕜 a).exists_isMaxOn (nonempty 𝕜 a) continuous_enorm.continuousOn
  unfold spectralRadius
  exact ⟨k, hk, le_antisymm (by grw [← le_iSup₂ k hk]) (iSup₂_le h)⟩

@[deprecated (since := "2026-09-21")]
alias exists_nnnorm_quasispectrum_eq_spectralRadius := exists_enorm_quasispectrum_eq_spectralRadius

theorem spectralRadius_lt_of_forall_lt {a : A} {r : ℝ≥0∞}
    (hr : ∀ k ∈ σₙ 𝕜 a, ‖k‖ₑ < r) : spectralRadius 𝕜 a < r :=
  sSup_image.symm.trans_lt <| ((isCompact 𝕜 a).sSup_lt_iff_of_continuous
    (nonempty 𝕜 a) continuous_enorm.continuousOn (r : ℝ≥0∞)).mpr (by simpa using hr)

end Generic

section NNReal

variable [NonUnitalNormedRing A] [NormedSpace ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]

instance quasispectrum.instCompactSpaceNNReal (a : A) [CompactSpace (σₙ ℝ a)] :
    CompactSpace (σₙ ℝ≥0 a) := by
  rw [← isCompact_iff_compactSpace] at *
  rw [← preimage_algebraMap ℝ]
  exact isClosed_nonneg.isClosedEmbedding_subtypeVal.isCompact_preimage ‹_›

@[simp]
theorem quasispectrum.isCompact_nnreal (a : A) [CompactSpace (σₙ ℝ a)] :
    IsCompact (σₙ ℝ≥0 a) := by
  rw [isCompact_iff_compactSpace]
  infer_instance

grind_pattern isCompact_nnreal => IsCompact (σₙ ℝ≥0 a)

variable [HasSummableGeomSeries A]

theorem quasispectrum.le_nnnorm_of_mem {a : A} {r : ℝ≥0} (hr : r ∈ σₙ ℝ≥0 a) :
    r ≤ ‖a‖₊ := calc
  r ≤ ‖(r : ℝ)‖ := Real.le_norm_self _
  _ ≤ ‖a‖ := norm_le_norm_of_mem <| by rwa [← preimage_algebraMap ℝ] at hr

theorem quasispectrum.coe_le_norm_of_mem {a : A} {r : ℝ≥0} (hr : r ∈ σₙ ℝ≥0 a) :
    r ≤ ‖a‖ :=
  NNReal.coe_mono <| le_nnnorm_of_mem hr

end NNReal

end quasispectrum

section SpectrumCompact

open spectrum

variable [NormedField 𝕜]

section Unital

section NotNormed

variable [Ring A] [Algebra 𝕜 A]

lemma spectralRadius_eq_of_unital (a : A) : spectralRadius 𝕜 a = ⨆ k ∈ σ 𝕜 a, ‖k‖ₑ := by
  simp [spectralRadius, quasispectrum_eq_spectrum_union_zero, iSup_or, iSup_sup_eq]

@[simp]
theorem spectralRadius_one [Nontrivial A] : spectralRadius 𝕜 (1 : A) = 1 := by
  simp [spectralRadius_eq_of_unital]

@[deprecated (since := "2026-09-21")]
protected alias spectrum.spectralRadius_one := spectralRadius_one

theorem spectrum.mem_resolventSet_of_spectralRadius_lt {a : A} {k : 𝕜}
    (h : spectralRadius 𝕜 a < ‖k‖ₑ) : k ∈ resolventSet 𝕜 a := by
  rw [spectralRadius_eq_of_unital] at h
  contrapose! h
  grw [← le_iSup₂ k h]

lemma spectralRadius_pow_le (a : A) (n : ℕ) (hn : n ≠ 0) :
    (spectralRadius 𝕜 a) ^ n ≤ spectralRadius 𝕜 (a ^ n) := by
  simp only [spectralRadius_eq_of_unital, ENNReal.iSup₂_pow_of_ne_zero _ hn]
  refine iSup₂_le fun x hx ↦ ?_
  apply le_iSup₂_of_le (x ^ n) <| pow_mem_pow a n hx
  simp

@[deprecated (since := "2026-09-21")]
protected alias spectrum.spectralRadius_pow_le := spectralRadius_pow_le

lemma spectralRadius_pow_le' [Nontrivial A] (a : A) (n : ℕ) :
    (spectralRadius 𝕜 a) ^ n ≤ spectralRadius 𝕜 (a ^ n) := by
  cases n
  · simp
  · exact spectralRadius_pow_le a _ (by simp)

@[deprecated (since := "2026-09-21")]
protected alias spectrum.spectralRadius_pow_le' := spectralRadius_pow_le'

end NotNormed

variable [NormedRing A] [NormedAlgebra 𝕜 A] [HasSummableGeomSeries A]

variable (𝕜) in
theorem isOpen_resolventSet (a : A) : IsOpen (resolventSet 𝕜 a) :=
  Units.isOpen.preimage (by fun_prop)

@[deprecated (since := "2026-09-21")]
protected alias spectrum.isOpen_resolventSet := isOpen_resolventSet

theorem mem_resolventSet_of_norm_lt {a : A} {k : 𝕜} (h : ‖a‖ < ‖k‖) : k ∈ resolventSet 𝕜 a := by
  rw [mem_resolventSet_iff, ← spectrum.notMem_iff]
  contrapose! h
  exact quasispectrum.norm_le_norm_of_mem (spectrum_subset_quasispectrum _ _ h)

@[deprecated (since := "2026-09-21")]
protected alias spectrum.mem_resolventSet_of_norm_lt := mem_resolventSet_of_norm_lt

variable (𝕜) in
@[simp]
protected theorem spectrum.isClosed (a : A) : IsClosed (σ 𝕜 a) :=
  (isOpen_resolventSet 𝕜 a).isClosed_compl

@[deprecated mem_resolventSet_of_norm_lt +typeChanged (since := "2026-09-21")]
theorem spectrum.mem_resolventSet_of_norm_lt_mul {a : A} {k : 𝕜} (h : ‖a‖ * ‖(1 : A)‖ < ‖k‖) :
    k ∈ resolventSet 𝕜 a := by
  nontriviality A
  grw [← one_le_norm_one, mul_one] at h
  exact mem_resolventSet_of_norm_lt h

theorem spectrum.norm_le_norm_of_mem {a : A} {k : 𝕜} (hk : k ∈ σ 𝕜 a) : ‖k‖ ≤ ‖a‖ :=
  le_of_not_gt <| mt mem_resolventSet_of_norm_lt hk

@[deprecated norm_le_norm_of_mem +typeChanged (since := "2026-09-21")]
theorem spectrum.norm_le_norm_mul_of_mem {a : A} {k : 𝕜} (hk : k ∈ σ 𝕜 a) : ‖k‖ ≤ ‖a‖ * ‖(1 : A)‖ :=
  le_of_not_gt <| mt mem_resolventSet_of_norm_lt_mul hk

theorem spectrum.subset_closedBall_norm (a : A) : σ 𝕜 a ⊆ Metric.closedBall (0 : 𝕜) ‖a‖ :=
  fun k hk => by simp [norm_le_norm_of_mem hk]

@[deprecated subset_closedBall_norm +typeChanged (since := "2026-09-21")]
theorem spectrum.subset_closedBall_norm_mul (a : A) :
    σ 𝕜 a ⊆ Metric.closedBall (0 : 𝕜) (‖a‖ * ‖(1 : A)‖) :=
  fun k hk => by simp [norm_le_norm_mul_of_mem hk]

variable (𝕜) in
@[simp]
theorem spectrum.isBounded (a : A) : Bornology.IsBounded (σ 𝕜 a) :=
  Metric.isBounded_closedBall.subset (subset_closedBall_norm a)

section ProperSpace

variable [ProperSpace 𝕜]

variable (𝕜) in
@[simp]
protected theorem spectrum.isCompact (a : A) : IsCompact (σ 𝕜 a) :=
  Metric.isCompact_of_isClosed_isBounded (spectrum.isClosed 𝕜 a) (isBounded 𝕜 a)

grind_pattern spectrum.isCompact => IsCompact (σ 𝕜 a)

variable (𝕜) in
instance spectrum.instCompactSpace (a : A) : CompactSpace (σ 𝕜 a) :=
  isCompact_iff_compactSpace.mp <| spectrum.isCompact 𝕜 a

theorem exists_enorm_spectrum_eq_spectralRadius_of_nonempty {a : A}
    (ha : (σ 𝕜 a).Nonempty) :
    ∃ k ∈ σ 𝕜 a, ‖k‖ₑ = spectralRadius 𝕜 a := by
  obtain ⟨k, hk, h⟩ := (spectrum.isCompact 𝕜 a).exists_isMaxOn ha continuous_enorm.continuousOn
  rw [spectralRadius_eq_of_unital]
  exact ⟨k, hk, le_antisymm (by grw [← le_iSup₂ k hk]) (iSup₂_le h)⟩

@[deprecated (since := "2026-09-21")]
alias spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty :=
  exists_enorm_spectrum_eq_spectralRadius_of_nonempty

theorem spectralRadius_lt_of_forall_lt_of_nonempty {a : A} {r : ℝ≥0∞}
    (ha : (σ 𝕜 a).Nonempty) (hr : ∀ k ∈ σ 𝕜 a, ‖k‖ₑ < r) :
    spectralRadius 𝕜 a < r := by
  rw [spectralRadius_eq_of_unital]
  exact sSup_image.symm.trans_lt <|
    ((spectrum.isCompact 𝕜 a).sSup_lt_iff_of_continuous ha continuous_enorm.continuousOn r).mpr hr

@[deprecated (since := "2026-09-21")]
alias spectrum.spectralRadius_lt_of_forall_lt_of_nonempty :=
  spectralRadius_lt_of_forall_lt_of_nonempty

end ProperSpace
section LiminfPow

open Polynomial

variable (𝕜)

-- TODO: generalize this and the next two to `PNat` powers in semigroups once Mathlib has those.
theorem spectralRadius_le_pow_enorm_rpow_one_div (a : A) (n : ℕ) :
    spectralRadius 𝕜 a ≤ ‖a ^ (n + 1)‖ₑ ^ (1 / (n + 1) : ℝ) := by
  rw [spectralRadius_eq_of_unital]
  refine iSup₂_le fun k hk => ?_
  -- apply easy direction of the spectral mapping theorem for polynomials
  have pow_mem : k ^ (n + 1) ∈ σ 𝕜 (a ^ (n + 1)) := by
    simpa only [one_mul, Algebra.algebraMap_eq_smul_one, one_smul, aeval_monomial, one_mul,
      eval_monomial] using subset_polynomial_aeval a (@monomial 𝕜 _ (n + 1) (1 : 𝕜)) ⟨k, hk, rfl⟩
  -- power of the norm is bounded by norm of the power
  have enorm_pow_le : ‖k‖ₑ ^ (n + 1) ≤ ‖a ^ (n + 1)‖ₑ := by
    simpa using ENNReal.ofReal_mono (norm_le_norm_of_mem pow_mem)
  -- take (n + 1)ᵗʰ roots and clean up the left-hand side
  have hn : 0 < (n + 1 : ℝ) := mod_cast Nat.succ_pos'
  convert monotone_rpow_of_nonneg (one_div_pos.mpr hn).le enorm_pow_le
  simp [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_inv_cancel₀ hn.ne']

@[deprecated (since := "2026-09-21")]
alias spectrum.spectralRadius_le_pow_nnnorm_pow_one_div := spectralRadius_le_pow_enorm_rpow_one_div

theorem spectralRadius_le_iInf_pow_enorm_rpow_one_div (a : A) :
    spectralRadius 𝕜 a ≤ ⨅ n : ℕ, ‖a ^ (n + 1)‖ₑ ^ (1 / (n + 1) : ℝ) :=
  le_iInf <| spectralRadius_le_pow_enorm_rpow_one_div 𝕜 a

@[deprecated (since := "2026-09-21")]
alias spectrum.spectralRadius_le_iInf_pow_nnnorm_pow_one_div :=
  spectralRadius_le_iInf_pow_enorm_rpow_one_div

theorem spectralRadius_le_liminf_pow_enorm_rpow_one_div (a : A) :
    spectralRadius 𝕜 a ≤ atTop.liminf fun n : ℕ => ‖a ^ n‖ₑ ^ (1 / n : ℝ) := by
  apply Filter.le_liminf_of_le (by isBoundedDefault)
  filter_upwards [Ici_mem_atTop 1] with n (hn : 1 ≤ n)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact mod_cast spectralRadius_le_pow_enorm_rpow_one_div 𝕜 a n

@[deprecated (since := "2026-09-21")]
alias spectrum.spectralRadius_le_liminf_pow_nnnorm_pow_one_div :=
  spectralRadius_le_liminf_pow_enorm_rpow_one_div

end LiminfPow

end Unital

section NNReal

open NNReal

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

instance spectrum.instCompactSpaceNNReal (a : A) [CompactSpace (σ ℝ a)] :
    CompactSpace (σ ℝ≥0 a) := by
  rw [← isCompact_iff_compactSpace] at *
  rw [← preimage_algebraMap ℝ]
  exact isClosed_nonneg.isClosedEmbedding_subtypeVal.isCompact_preimage <| by assumption

@[simp]
theorem spectrum.isCompact_nnreal (a : A) [CompactSpace (σ ℝ a)] :
    IsCompact (σ ℝ≥0 a) := by
  rw [isCompact_iff_compactSpace]
  infer_instance

grind_pattern spectrum.isCompact_nnreal => IsCompact (σ ℝ≥0 a)

variable [HasSummableGeomSeries A]

theorem spectrum.le_nnnorm_of_mem {a : A} {r : ℝ≥0} (hr : r ∈ σ ℝ≥0 a) :
    r ≤ ‖a‖₊ := calc
  r ≤ ‖(r : ℝ)‖ := Real.le_norm_self _
  _ ≤ ‖a‖ := norm_le_norm_of_mem hr

theorem spectrum.coe_le_norm_of_mem {a : A} {r : ℝ≥0} (hr : r ∈ σ ℝ≥0 a) :
    r ≤ ‖a‖ :=
  coe_mono <| le_nnnorm_of_mem hr

end NNReal

end SpectrumCompact

/-! ### Properties of the resolvent in Banach algebras

In a Banach `𝕜`-algebra, the resolvent `z ↦ (algebraMap 𝕜 A z - a)⁻¹` tends to `0` along
`cobounded 𝕜`. In fact, it is big-O of `z ↦ z⁻¹`.

The related function `z ↦ (1 - z • a)⁻¹` has a natural power series centered at `0` on the ball of
radius `‖a‖ₑ⁻¹`. This is used later to help establish Gelfand's formula for the spectral radius
in complex Banach algebras.
-/
section resolvent

open Filter Asymptotics Bornology spectrum

open scoped Topology

variable [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [HasSummableGeomSeries A]

theorem spectrum.eventually_isUnit_resolvent (a : A) :
    ∀ᶠ z in cobounded 𝕜, IsUnit (resolvent a z) := by
  rw [atTop_basis_Ioi.cobounded_of_norm.eventually_iff]
  exact ⟨‖a‖, trivial, fun _ ↦ isUnit_resolvent.mp ∘ mem_resolventSet_of_norm_lt⟩

theorem spectrum.resolvent_isBigO_inv (a : A) :
    resolvent a =O[cobounded 𝕜] (·⁻¹) :=
  have h : (fun z ↦ resolvent (z⁻¹ • a) (1 : 𝕜)) =O[cobounded 𝕜] (fun _ ↦ (1 : ℝ)) := by
    simpa [Function.comp_def, resolvent] using
      (NormedRing.inverse_one_sub_norm (R := A)).comp_tendsto
        (by simpa using (tendsto_inv₀_cobounded (α := 𝕜)).smul_const a)
  calc
    resolvent a =ᶠ[cobounded 𝕜] fun z ↦ z⁻¹ • resolvent (z⁻¹ • a) (1 : 𝕜) := by
      filter_upwards [isBounded_singleton (x := 0)] with z hz
      lift z to 𝕜ˣ using Ne.isUnit hz
      simpa [Units.smul_def] using congr(z⁻¹ • $(units_smul_resolvent_self (r := z) (a := a)))
    _ =O[cobounded 𝕜] (· ⁻¹) := .of_norm_right <| by
      simpa using (isBigO_refl (· ⁻¹) (cobounded 𝕜)).norm_right.smul h

theorem spectrum.resolvent_tendsto_cobounded (a : A) : Tendsto (resolvent a) (cobounded 𝕜) (𝓝 0) :=
  resolvent_isBigO_inv a |>.trans_tendsto tendsto_inv₀_cobounded

end resolvent

section OneSubSMul

open FormalMultilinearSeries

variable [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

variable (𝕜) in
/-- In a Banach algebra `A` over a nontrivially normed field `𝕜`, for any `a : A` the
power series with coefficients `a ^ n` represents the function `z ↦ (1 - z • a)⁻¹` in a disk of
radius `‖a‖₊⁻¹`. -/
theorem hasFPowerSeriesOnBall_inverse_one_sub_smul [HasSummableGeomSeries A] (a : A) :
    HasFPowerSeriesOnBall (fun z : 𝕜 => Ring.inverse (1 - z • a))
      (fun n ↦ ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n) (a ^ n)) 0 ‖a‖ₑ⁻¹ := by
  have : (fun n ↦ ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n) (a ^ n)) =
      (formalMultilinearSeries_geometric 𝕜 A).compContinuousLinearMap
        ((ContinuousLinearMap.id 𝕜 𝕜).smulRightL 𝕜 𝕜 A a) := by
    ext
    simp [compContinuousLinearMap, formalMultilinearSeries_geometric]
  rw [this]
  let h := map_zero <| (ContinuousLinearMap.id 𝕜 𝕜).smulRightL 𝕜 𝕜 A a
  convert (h ▸ hasFPowerSeriesOnBall_inverse_one_sub 𝕜 A).compContinuousLinearMap
  all_goals simp [enorm_eq_nnnorm]

theorem isUnit_one_sub_smul_of_lt_inv_spectralRadius {a : A} {z : 𝕜}
    (h : ‖z‖ₑ < (spectralRadius 𝕜 a)⁻¹) :
    IsUnit (1 - z • a) := by
  by_cases hz : z = 0
  · simp only [hz, isUnit_one, sub_zero, zero_smul]
  · have : spectralRadius 𝕜 a < ‖z⁻¹‖ₑ := by simpa [hz] using ENNReal.inv_lt_inv' h
    simpa [hz, Algebra.algebraMap_eq_smul_one, smul_sub]
      using spectrum.mem_resolventSet_of_spectralRadius_lt this |>.smul <| Units.mk0 z hz

end OneSubSMul

/-! ### The boundary of the spectrum and closed subalgebras

In a Banach `𝕜`-algebra `A` with closed subalgebra `S`, the frontier of the spectrum of `x : S`
is contained in the spectrum of `↑x : A` and is in fact in its frontier. The relative complement of
the spectrum of `↑x : A` in the spectrum of `x : S` consists of a union of connected components of
the latter.

Consequently, if the complement of the spectrum of `↑x : A` is connected, then the spectra of
`↑x : A` and `x : S` coincide.
-/

section BoundarySpectrum

variable {𝕜 A SA : Type*}
  [NormedRing A] [HasSummableGeomSeries A] [SetLike SA A] [SubringClass SA A]

open Filter Set

open scoped Topology

section NormedField

-- Move me elsewhere
open scoped Ring
theorem IsUnit.map_inverse {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀']
    [FunLike F M₀ M₀'] [MonoidWithZeroHomClass F M₀ M₀'] (f : F) {a : M₀} (h : IsUnit a) :
    f a⁻¹ʳ = (f a)⁻¹ʳ := by
  lift a to M₀ˣ using h
  convert a.coe_map_inv (MonoidHom.ofClass f) |>.symm
  · simp
  · simp [← Ring.inverse_unit]

variable [NormedField 𝕜] [NormedAlgebra 𝕜 A] [instSMulMem : SMulMemClass SA 𝕜 A]
variable (S : SA) [hS : IsClosed (S : Set A)] (x : S)

open SubalgebraClass in
include instSMulMem in
/-- Let `S` be a closed subalgebra of a Banach algebra `A`. If `a : S` is invertible in `A`,
and for all `x : S` sufficiently close to `a` within some filter `l`, `x` is invertible in `S`,
then `a` is invertible in `S` as well. -/
lemma _root_.Subalgebra.isUnit_of_isUnit_val_of_eventually {l : Filter S} {a : S}
    (ha : IsUnit (a : A)) (hla : l ≤ 𝓝 a) (hl : ∀ᶠ x in l, IsUnit x) (hl' : l.NeBot) :
    IsUnit a := by
  lift (a : A) to Aˣ using ha with u hu
  have hla₂ : Tendsto Ring.inverse (map (val S) l) (𝓝 (↑u⁻¹ : A)) := by
    rw [← Ring.inverse_unit]
    exact (NormedRing.inverse_continuousAt _).tendsto.comp <|
      hu ▸ continuousAt_subtype_val.tendsto.comp (map_mono hla)
  suffices mem : (↑u⁻¹ : A) ∈ S by
    refine ⟨⟨a, ⟨(↑u⁻¹ : A), mem⟩, ?_, ?_⟩, rfl⟩
    all_goals ext; simp [hu]
  apply hS.mem_of_tendsto hla₂
  rw [Filter.eventually_map]
  apply hl.mono fun x hx ↦ ?_
  rw [← hx.map_inverse (val S)]
  simp

/-- If `S : Subalgebra 𝕜 A` is a closed subalgebra of a Banach algebra `A`, then for any
`x : S`, the boundary of the spectrum of `x` relative to `S` is a subset of the spectrum of
`↑x : A` relative to `A`. -/
lemma Subalgebra.frontier_spectrum_subset_spectrum : frontier (σ 𝕜 x) ⊆ σ 𝕜 (x : A) := by
  intro μ hμ
  by_contra h
  rw [spectrum.notMem_iff] at h
  rw [← frontier_compl, (spectrum.isClosed 𝕜 _).isOpen_compl.frontier_eq, Set.mem_sdiff] at hμ
  obtain ⟨hμ₁, hμ₂⟩ := hμ
  rw [mem_closure_iff_clusterPt] at hμ₁
  apply hμ₂
  rw [mem_compl_iff, spectrum.notMem_iff]
  refine Subalgebra.isUnit_of_isUnit_val_of_eventually S h ?_ ?_ <| .map hμ₁ (algebraMap 𝕜 S · - x)
  · calc
      _ ≤ Filter.map _ (𝓝 μ) := Filter.map_mono (by simp)
      _ ≤ _ := by rw [← Filter.Tendsto, ← ContinuousAt]; fun_prop
  · rw [eventually_map]
    apply Eventually.filter_mono inf_le_right
    simp [spectrum.notMem_iff]

@[deprecated (since := "2026-09-21")]
alias Subalgebra.frontier_spectrum := Subalgebra.frontier_spectrum_subset_spectrum

/-- If `S` is a closed subalgebra of a Banach algebra `A`, then for any `x : S`, the boundary of
the spectrum of `x` relative to `S` is a subset of the boundary of the spectrum of `↑x : A`
relative to `A`. -/
lemma Subalgebra.frontier_spectrum_subset_frontier :
    frontier (σ 𝕜 x) ⊆ frontier (σ 𝕜 (x : A)) := by
  rw [frontier_eq_closure_inter_closure (s := σ 𝕜 (x : A)),
    (spectrum.isClosed 𝕜 (x : A)).closure_eq]
  apply subset_inter (frontier_spectrum_subset_spectrum S x)
  rw [frontier_eq_closure_inter_closure]
  grw [inter_subset_right, spectrum.subset_subalgebra]

@[deprecated (since := "2026-09-21")]
alias Subalgebra.frontier_subset_frontier := Subalgebra.frontier_spectrum_subset_frontier

/-- If `S` is a closed subalgebra of a Banach algebra `A`, then for any `x : S`, the spectrum of `x`
is the spectrum of `↑x : A` along with the connected components of the complement of the spectrum of
`↑x : A` which contain an element of the spectrum of `x : S`. -/
lemma Subalgebra.spectrum_eq_union_sUnion_connectedComponentIn :
    σ 𝕜 x = σ 𝕜 (x : A) ∪ (⋃ z ∈ (σ 𝕜 x \ σ 𝕜 (x : A)), connectedComponentIn (σ 𝕜 (x : A))ᶜ z) := by
  suffices IsClopen ((σ 𝕜 (x : A))ᶜ ↓∩ (σ 𝕜 x \ σ 𝕜 (x : A))) by
    rw [← this.biUnion_connectedComponentIn (sdiff_subset_compl _ _),
      union_sdiff_cancel (spectrum.subset_subalgebra x)]
  have h_open : IsOpen (σ 𝕜 x \ σ 𝕜 (x : A)) := by
    rw [← (spectrum.isClosed (𝕜 := 𝕜) x).closure_eq, closure_eq_interior_union_frontier,
      union_sdiff_distrib, sdiff_eq_empty.mpr (frontier_spectrum_subset_spectrum S x),
      sdiff_eq_compl_inter, union_empty]
    exact (spectrum.isClosed _ _).isOpen_compl.inter isOpen_interior
  apply isClopen_preimage_val h_open
  suffices h_frontier : frontier (σ 𝕜 x \ σ 𝕜 (x : A)) ⊆ frontier (σ 𝕜 (x : A)) from
    disjoint_of_subset_left h_frontier <| disjoint_compl_right.frontier_left
      (spectrum.isClosed _ _).isOpen_compl
  grw [sdiff_eq_compl_inter, frontier_inter_subset, inter_subset_left, inter_subset_right,
    frontier_compl, frontier_spectrum_subset_frontier, union_self]

@[deprecated (since := "2026-09-21")]
alias Subalgebra.spectrum_sUnion_connectedComponentIn :=
  Subalgebra.spectrum_eq_union_sUnion_connectedComponentIn

/-- Let `S` be a closed subalgebra of a Banach algebra `A`, and let `x : S`. If `z` is in the
spectrum of `x`, then the connected component of `z` in the complement of the spectrum of `↑x : A`
is bounded (or else `z` actually belongs to the spectrum of `↑x : A`). -/
lemma Subalgebra.isBounded_connectedComponentIn_spectrum_compl {z : 𝕜} (hz : z ∈ σ 𝕜 x) :
    Bornology.IsBounded (connectedComponentIn (σ 𝕜 (x : A))ᶜ z) := by
  by_cases hz' : z ∈ σ 𝕜 (x : A)
  · simp [connectedComponentIn_eq_empty (show z ∉ (σ 𝕜 (x : A))ᶜ from not_not.mpr hz')]
  · suffices connectedComponentIn (σ 𝕜 (x : A))ᶜ z ⊆ σ 𝕜 x
      from spectrum.isBounded _ x |>.subset this
    rw [spectrum_eq_union_sUnion_connectedComponentIn S]
    exact subset_biUnion_of_mem (mem_sdiff_of_mem hz hz') |>.trans subset_union_right

@[deprecated (since := "2026-09-21")]
alias Subalgebra.spectrum_isBounded_connectedComponentIn :=
  Subalgebra.isBounded_connectedComponentIn_spectrum_compl

end NormedField

variable [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 A] [SMulMemClass SA 𝕜 A]
variable (S : SA) [hS : IsClosed (S : Set A)] (x : S)

/-- Let `S` be a closed subalgebra of a Banach algebra `A`. If for `x : S` the complement of the
spectrum of `↑x : A` is connected, then `spectrum 𝕜 x = spectrum 𝕜 (x : A)`. -/
lemma Subalgebra.spectrum_eq_of_isPreconnected_compl (h : IsPreconnected (σ 𝕜 (x : A))ᶜ) :
    σ 𝕜 x = σ 𝕜 (x : A) := by
  suffices σ 𝕜 x \ σ 𝕜 (x : A) = ∅ by
    rw [spectrum_eq_union_sUnion_connectedComponentIn, this]
    simp
  refine eq_empty_of_forall_notMem fun z hz ↦ NormedSpace.unbounded_univ 𝕜 𝕜 ?_
  obtain ⟨hz, hz'⟩ := mem_sdiff _ |>.mp hz
  have := (spectrum.isBounded 𝕜 (x : A)).union <|
    h.connectedComponentIn hz' ▸ isBounded_connectedComponentIn_spectrum_compl S x hz
  simpa

end BoundarySpectrum

/-! ### Upper hemicontinuity of the (quasi)spectrum -/

section UpperHemicontinuous

variable (𝕜 A)
variable [NormedField 𝕜] [ProperSpace 𝕜]

/-- The map `a ↦ spectrum 𝕜 a` is upper hemicontinuous. -/
lemma upperHemicontinuous_spectrum [NormedRing A] [NormedAlgebra 𝕜 A] [HasSummableGeomSeries A] :
    UpperHemicontinuous (σ 𝕜 : A → Set 𝕜) := by
  /- It suffices to use the sequential characterization of upper hemicontinuity.
  Suppose that `a : ℕ → A` converges to `a₀`, `x : ℕ → 𝕜` converges to `x₀`, and for all `n`,
  `x n ∈ spectrum 𝕜 (a n)`. -/
  rw [upperHemicontinuous_iff]
  refine fun a₀ ↦ .of_sequences (isCompact_closedBall 0 (‖a₀‖ + 1)).isSeqCompact ?_ <|
    fun a ha x hx_mem x₀ hx ↦ ?_
  /- We must show that `spectrum 𝕜 (a n)` is eventually contained in some fixed compact set
  (we've chosen `closedBall 0 (‖a₀‖ + 1)`). This follows since the spectrum of any
  `b` is bounded `‖b‖ * ‖1‖` and `a` converges to `a₀`.  -/
  · filter_upwards [Metric.closedBall_mem_nhds a₀ zero_lt_one] with a ha
    apply spectrum.subset_closedBall_norm a |>.trans <| Metric.closedBall_subset_closedBall ?_
    apply norm_le_norm_add_norm_sub' a a₀ |>.trans
    gcongr
    simpa [dist_eq_norm] using ha
  /- Finally, `x₀ ∈ spectrum 𝕜 a₀` since `algebraMap 𝕜 A x₀ - a₀` is not invertible, being itself
  the limit of the non-invertible elements `algebraMap 𝕜 A (x n) - (a n)`. -/
  · exact nonunits.isClosed.mem_of_tendsto
      (continuous_algebraMap 𝕜 A |>.tendsto x₀ |>.comp hx |>.sub ha) <| .of_forall hx_mem

/-- The map `a ↦ spectrum ℝ≥0 a` is upper hemicontinuous. -/
theorem upperHemicontinuous_spectrum_nnreal [NormedRing A] [NormedAlgebra ℝ A]
    [HasSummableGeomSeries A] :
    UpperHemicontinuous (σ ℝ≥0 : A → Set ℝ≥0) := by
  obtain ⟨⟨h₁, -⟩, h₂⟩ : IsClosedEmbedding ((↑) : ℝ≥0 → ℝ) := NNReal.isClosedEmbedding_coe
  exact upperHemicontinuous_spectrum ℝ A |>.isInducing_comp h₁ h₂

/-- The map `a ↦ quasispectrum 𝕜 a` is upper hemicontinuous. -/
theorem upperHemicontinuous_quasispectrum [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
    [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A] [HasSummableGeomSeries A] :
    UpperHemicontinuous (σₙ 𝕜 : A → Set 𝕜) := by
  convert!
    upperHemicontinuous_spectrum 𝕜 (WithLp 1 (Unitization 𝕜 A)) |>.comp
      unitization_isometry_inr.continuous
  ext1 a
  rw [quasispectrum_eq_spectrum_toLp_inr]
  congr

/-- The map `a ↦ quasispectrum ℝ≥0 a` is upper hemicontinuous. -/
theorem upperHemicontinuous_quasispectrum_nnreal [NonUnitalNormedRing A] [NormedSpace ℝ A]
    [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] [HasSummableGeomSeries A] :
    UpperHemicontinuous (σₙ ℝ≥0 : A → Set ℝ≥0) := by
  obtain ⟨⟨h₁, -⟩, h₂⟩ := NNReal.isClosedEmbedding_coe
  simpa [← NNReal.algebraMap_eq_coe] using
    upperHemicontinuous_quasispectrum ℝ A |>.isInducing_comp h₁ h₂

end UpperHemicontinuous


/-! ### Characters in Banach algebras

In a Banach `𝕜`-algebra, multiplicative linear functionals (i.e., non-unital `𝕜`-algebra
homomorphisms from `A` to `𝕜`) are automatically continuous.
-/

namespace NonUnitalAlgHom

section NormedField

-- this should go elsewhere
attribute [local grind .] add_mul add_comm add_right_comm zero_add one_ne_zero in
theorem apply_mem_quasispectrum {F R A : Type*} [CommSemiring R] [Nontrivial R] [NonUnitalRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [FunLike F A R]
    [NonUnitalAlgHomClass F R A R] (φ : F) (a : A) :
    φ a ∈ quasispectrum R a := by
  intro ha
  lift φ a to Rˣ using ha with r hr
  simp_rw [isQuasiregular_iff, IsUnit.unit_of_val_units]
  rintro ⟨b, hb, -⟩
  replace hb := congr(φ $hb)
  have h1 : φ (r⁻¹ • a) = 1 := by simp [Units.smul_def, hr]
  have := congr(φ ($(neg_add_cancel (r⁻¹ • a))))
  replace h1 : φ (-(r⁻¹ • a)) + 1 = 0 := by simp [← h1, ← map_add]
  grind =>
    have huv : (φ (-(r⁻¹ • a)) + 1) * φ b = 0
    have : 1 = 0

variable {F : Type*} [NormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [HasSummableGeomSeries A]

theorem norm_apply_le_self [FunLike F A 𝕜] [NonUnitalAlgHomClass F 𝕜 A 𝕜]
    (f : F) (a : A) : ‖f a‖ ≤ ‖a‖ :=
  quasispectrum.norm_le_norm_of_mem (apply_mem_quasispectrum f _)

@[deprecated (since := "2026-09-21")] alias _root_.AlgHom.norm_apply_le_self := norm_apply_le_self

@[deprecated norm_apply_le_self +typeChanged (since := "2026-09-21")]
theorem _root_.AlgHom.norm_apply_le_self_mul_norm_one {F 𝕜 A : Type*} [NormedField 𝕜] [NormedRing A]
    [NormedAlgebra 𝕜 A] [HasSummableGeomSeries A] [FunLike F A 𝕜] [AlgHomClass F 𝕜 A 𝕜]
    (f : F) (a : A) : ‖f a‖ ≤ ‖a‖ * ‖(1 : A)‖ :=
  spectrum.norm_le_norm_mul_of_mem (AlgHom.apply_mem_spectrum f _)

instance (priority := 100) [FunLike F A 𝕜] [NonUnitalAlgHomClass F 𝕜 A 𝕜] :
    ContinuousLinearMapClass F 𝕜 A 𝕜 :=
  { NonUnitalAlgHomClass.instLinearMapClass with
    map_continuous φ := AddMonoidHomClass.continuous_of_bound φ 1 <| by
      simpa using norm_apply_le_self φ }

/-- A non-unital algebra homomorphism into the base field (i.e., a multiplicative linear
functional), as an element of the strong dual (since it is automatically continuous). -/
def toStrongDual (φ : A →ₙₐ[𝕜] 𝕜) : StrongDual 𝕜 A :=
  { (φ : A →ₗ[𝕜] 𝕜) with }

@[simp]
theorem coe_toStrongDual (φ : A →ₙₐ[𝕜] 𝕜) : ⇑φ.toStrongDual = φ :=
  rfl

end NormedField

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [HasSummableGeomSeries A]

theorem norm_toStrongDual_le (φ : A →ₙₐ[𝕜] 𝕜) : ‖φ.toStrongDual‖ ≤ 1 :=
  φ.toStrongDual.opNorm_le_bound zero_le_one <| by simpa using norm_apply_le_self φ

end NontriviallyNormedField


end NonUnitalAlgHom

section Unital

variable [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [HasSummableGeomSeries A]

/-- An algebra homomorphism into the base field (i.e., a multiplicative linear functional),
as an element of the strong dual (since it is automatically continuous). -/
@[deprecated NonUnitalAlgHom.toStrongDual +typeChanged (since := "2026-09-21")]
def AlgHom.toContinuousLinearMap (φ : A →ₐ[𝕜] 𝕜) : StrongDual 𝕜 A :=
  φ.toNonUnitalAlgHom.toStrongDual

@[simp]
theorem AlgHom.norm_toStrongDual_toNonUnitalAlgHom [NormOneClass A] (φ : A →ₐ[𝕜] 𝕜) :
    ‖φ.toNonUnitalAlgHom.toStrongDual‖ = 1 :=
  le_antisymm φ.toNonUnitalAlgHom.norm_toStrongDual_le <| by
    have hφ (x : A) : φ.toNonUnitalAlgHom x = φ x := rfl -- missing lemma
    simpa [-AlgHom.toNonUnitalAlgHom_eq_coe, hφ] using
      φ.toNonUnitalAlgHom.toStrongDual.le_opNorm_of_le (x := 1) (c := 1) (by simp)

@[deprecated (since := "2026-09-21")]
alias AlgHom.toContinuousLinearMap_norm := AlgHom.norm_toStrongDual_toNonUnitalAlgHom

namespace WeakDual
namespace CharacterSpace

/-- The equivalence between characters and algebra homomorphisms into the base field. -/
noncomputable def equivAlgHom : characterSpace 𝕜 A ≃ (A →ₐ[𝕜] 𝕜) where
  toFun := toAlgHom
  invFun f :=
    { val := f.toNonUnitalAlgHom.toStrongDual
      property := by rw [eq_set_map_one_map_mul]; exact ⟨map_one f, map_mul f⟩ }

@[simp]
theorem equivAlgHom_coe (f : characterSpace 𝕜 A) : ⇑(equivAlgHom f) = f :=
  rfl

@[simp]
theorem equivAlgHom_symm_coe (f : A →ₐ[𝕜] 𝕜) : ⇑(equivAlgHom.symm f) = f :=
  rfl

end CharacterSpace
end WeakDual

end Unital


/-! ### Restriction -/

/-- If `𝕜₁` is a normed field contained as subfield of a larger normed field `𝕜₂`, and if `a : A`
is an element (in a possibly non-unital `𝕜₂`-algebra) whose `𝕜₂` quasispectrum restricts to `𝕜₁`,
then the spectral radii over each scalar field coincide. -/
lemma QuasispectrumRestricts.spectralRadius_eq {𝕜₁ 𝕜₂ A : Type*} [NormedField 𝕜₁]
    [NormedField 𝕜₂] [NonUnitalRing A] [Module 𝕜₁ A] [Module 𝕜₂ A] [NormedAlgebra 𝕜₁ 𝕜₂]
    [IsScalarTower 𝕜₁ 𝕜₂ A] [IsScalarTower 𝕜₂ A A] [SMulCommClass 𝕜₂ A A]
    {f : 𝕜₂ → 𝕜₁} {a : A} (h : QuasispectrumRestricts a f) :
    spectralRadius 𝕜₁ a = spectralRadius 𝕜₂ a := by
  rw [spectralRadius, spectralRadius]
  have (x : 𝕜₁) : ‖(algebraMap 𝕜₁ 𝕜₂) x‖ₑ = ‖x‖ₑ :=
    congr(($(algebraMap_isometry 𝕜₁ 𝕜₂ |>.nnnorm_map_of_map_zero (map_zero _) x) : ℝ≥0∞))
  simp_rw [h.algebraMap_image.symm, iSup_image, this]

/-- If `𝕜₁` is a normed field contained as subfield of a larger normed field `𝕜₂`, and if `a : A`
is an element whose `𝕜₂` spectrum restricts to `𝕜₁`, then the spectral radii over each scalar
field coincide. -/
lemma SpectrumRestricts.spectralRadius_eq {𝕜₁ 𝕜₂ A : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂]
    [NormedRing A] [NormedAlgebra 𝕜₁ A] [NormedAlgebra 𝕜₂ A] [NormedAlgebra 𝕜₁ 𝕜₂]
    [IsScalarTower 𝕜₁ 𝕜₂ A] {f : 𝕜₂ → 𝕜₁} {a : A} (h : SpectrumRestricts a f) :
    spectralRadius 𝕜₁ a = spectralRadius 𝕜₂ a :=
  QuasispectrumRestricts.spectralRadius_eq h

lemma QuasispectrumRestricts.compactSpace {R S A : Type*} [Semifield R] [Field S] [NonUnitalRing A]
    [Algebra R S] [Module R A] [Module S A] [IsScalarTower S A A] [SMulCommClass S A A]
    [IsScalarTower R S A] [TopologicalSpace R] [TopologicalSpace S] {a : A} (f : C(S, R))
    (h : QuasispectrumRestricts a f) [h_cpct : CompactSpace (quasispectrum S a)] :
    CompactSpace (quasispectrum R a) := by
  rw [← isCompact_iff_compactSpace] at h_cpct ⊢
  exact h.image ▸ h_cpct.image (map_continuous f)

lemma SpectrumRestricts.nnreal_iff_spectralRadius_le {A : Type*} [Ring A] [Algebra ℝ A]
    {a : A} {t : ℝ≥0} (ht : spectralRadius ℝ a ≤ t) :
    SpectrumRestricts a ContinuousMap.realToNNReal ↔
      spectralRadius ℝ (algebraMap ℝ A t - a) ≤ t := by
  simp only [spectralRadius_eq_of_unital] at ht ⊢
  have : σ ℝ a ⊆ Set.Icc (-t) t := by
    intro x hx
    rw [Set.mem_Icc, ← abs_le, ← Real.norm_eq_abs, ← coe_nnnorm, NNReal.coe_le_coe,
      ← ENNReal.coe_le_coe]
    exact le_iSup₂ x hx |>.trans ht
  rw [nnreal_iff]
  refine ⟨fun h ↦ iSup₂_le fun x hx ↦ ?_, fun h ↦ ?_⟩
  · rw [← spectrum.singleton_sub_eq] at hx
    obtain ⟨y, hy, rfl⟩ : ∃ y ∈ σ ℝ a, ↑t - y = x := by simpa using hx
    obtain ⟨hty, hyt⟩ := Set.mem_Icc.mp <| this hy
    lift y to ℝ≥0 using h y hy
    rw [← NNReal.coe_sub (by exact_mod_cast hyt)]
    simp
  · replace h : ∀ x ∈ σ ℝ a, ‖t - x‖₊ ≤ t := by
      simpa [spectralRadius, iSup₂_le_iff, ← spectrum.singleton_sub_eq] using h
    gconvert h with x hx h_le
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_le] at h_le
    linarith [h_le.2]

section RealNonUnital

variable [NonUnitalNormedRing A] [NormedSpace ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
  [HasSummableGeomSeries A] {a : A}

lemma NNReal.spectralRadius_mem_quasispectrum
    (ha : QuasispectrumRestricts a ContinuousMap.realToNNReal) :
    (spectralRadius ℝ a).toNNReal ∈ σₙ ℝ≥0 a := by
  obtain ⟨x, hx₁, hx₂⟩ := exists_enorm_quasispectrum_eq_spectralRadius ℝ a
  rwa [← hx₂, toNNReal_enorm, ← quasispectrum.algebraMap_mem_iff ℝ, algebraMap_eq_coe, coe_nnnorm,
    Real.norm_eq_abs, abs_of_nonneg (ha.rightInvOn hx₁ ▸ NNReal.zero_le_coe)]

lemma Real.spectralRadius_mem_quasispectrum
    (ha : QuasispectrumRestricts a ContinuousMap.realToNNReal) :
    (spectralRadius ℝ a).toReal ∈ σₙ ℝ a := by
  have := quasispectrum.preimage_algebraMap (R := ℝ≥0) ℝ (a := a) ▸
    NNReal.spectralRadius_mem_quasispectrum ha
  simpa

lemma Real.spectralRadius_mem_quasispectrum_or :
    (spectralRadius ℝ a).toReal ∈ σₙ ℝ a ∨ -(spectralRadius ℝ a).toReal ∈ σₙ ℝ a := by
  obtain ⟨x, hx₁, hx₂⟩ := exists_enorm_quasispectrum_eq_spectralRadius ℝ a
  grind [toReal_enorm, Real.norm_eq_abs]

end RealNonUnital

section RealUnital

variable [NormedRing A] [NormedAlgebra ℝ A] [HasSummableGeomSeries A] {a : A}

lemma NNReal.spectralRadius_mem_spectrum (ha : (σ ℝ a).Nonempty)
    (ha' : SpectrumRestricts a ContinuousMap.realToNNReal) :
    (spectralRadius ℝ a).toNNReal ∈ σ ℝ≥0 a := by
  obtain ⟨x, hx₁, hx₂⟩ := exists_enorm_spectrum_eq_spectralRadius_of_nonempty ha
  rwa [← hx₂, toNNReal_enorm, ← spectrum.algebraMap_mem_iff ℝ, algebraMap_eq_coe, coe_nnnorm,
    Real.norm_eq_abs, abs_of_nonneg (ha'.rightInvOn hx₁ ▸ NNReal.zero_le_coe)]

lemma Real.spectralRadius_mem_spectrum (ha : (σ ℝ a).Nonempty)
    (ha' : SpectrumRestricts a ContinuousMap.realToNNReal) :
    (spectralRadius ℝ a).toReal ∈ σ ℝ a :=
  NNReal.spectralRadius_mem_spectrum ha ha'

lemma Real.spectralRadius_mem_spectrum_or (ha : (σ ℝ a).Nonempty) :
    (spectralRadius ℝ a).toReal ∈ σ ℝ a ∨ -(spectralRadius ℝ a).toReal ∈ σ ℝ a := by
  obtain ⟨x, hx₁, hx₂⟩ := exists_enorm_spectrum_eq_spectralRadius_of_nonempty ha
  grind [toReal_enorm, Real.norm_eq_abs]

end RealUnital

/-! ### Exponential -/

section ExpMapping

/-- For `𝕜 = ℝ` or `𝕜 = ℂ`, `exp` maps the spectrum of `a` into the spectrum of `exp a`. -/
theorem exp_mem_spectrum_exp [RCLike 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
    (a : A) {z : 𝕜} (hz : z ∈ σ 𝕜 a) : exp z ∈ σ 𝕜 (exp a) := by
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ 𝕜 A
  have hexpmul : exp a = exp (a - algebraMap 𝕜 A z) * algebraMap 𝕜 A (exp z) := by
    rw [algebraMap_exp_comm z, ← exp_add_of_commute (Algebra.commutes z _).symm, sub_add_cancel]
  let b := ∑' n : ℕ, ((n + 1).factorial⁻¹ : 𝕜) • (a - algebraMap 𝕜 A z) ^ n
  have hb : Summable fun n : ℕ => ((n + 1).factorial⁻¹ : 𝕜) • (a - algebraMap 𝕜 A z) ^ n := by
    refine .of_norm_bounded_eventually (Real.summable_pow_div_factorial ‖a - algebraMap 𝕜 A z‖) ?_
    filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
    rw [norm_smul, mul_comm, norm_inv, RCLike.norm_natCast, ← div_eq_mul_inv]
    gcongr
    · exact norm_pow_le' _ (pos_iff_ne_zero.mpr hn)
    · exact n.le_succ
  have h₀ : (∑' n : ℕ, ((n + 1).factorial⁻¹ : 𝕜) • (a - algebraMap 𝕜 A z) ^ (n + 1))
      = (a - algebraMap 𝕜 A z) * b := by
    simpa only [mul_smul_comm, pow_succ'] using hb.tsum_mul_left (a - algebraMap 𝕜 A z)
  have h₁ : (∑' n : ℕ, ((n + 1).factorial⁻¹ : 𝕜) • (a - algebraMap 𝕜 A z) ^ (n + 1))
      = b * (a - algebraMap 𝕜 A z) := by
    simpa only [pow_succ, Algebra.smul_mul_assoc] using hb.tsum_mul_right (a - algebraMap 𝕜 A z)
  have h₃ : exp (a - algebraMap 𝕜 A z) = 1 + (a - algebraMap 𝕜 A z) * b := by
    rw [exp_eq_tsum 𝕜]
    convert! (expSeries_summable' (𝕂 := 𝕜) (a - algebraMap 𝕜 A z)).tsum_eq_zero_add
    · simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul]
    · exact h₀.symm
  rw [spectrum.mem_iff, IsUnit.sub_iff, ← one_mul (algebraMap 𝕜 A (exp z)), hexpmul, ← sub_mul,
    Commute.isUnit_mul_iff (Algebra.commutes (exp z) (exp (a - algebraMap 𝕜 A z) - 1)).symm,
    sub_eq_iff_eq_add'.mpr h₃, Commute.isUnit_mul_iff (h₀ ▸ h₁ : _ * b = b * _)]
  exact not_and_of_not_left _ (not_and_of_not_left _ ((not_iff_not.mpr IsUnit.sub_iff).mp hz))

@[deprecated (since := "2026-09-21")] alias spectrum.exp_mem_exp := exp_mem_spectrum_exp

end ExpMapping
