/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.NormedSpace.Star.ContinuousFunctionalCalculus.Restrict
import Mathlib.Analysis.NormedSpace.Star.Spectrum
import Mathlib.Analysis.NormedSpace.Star.ContinuousFunctionalCalculus

/-! # Instances of the continuous functional calculus

## Main definitions

* `IsStarNormal.instContinuousFunctionalCalculus`: the continuous functional calculus for normal
  elements in a unital C⋆-algebra over `ℂ`.
* `IsSelfAdjoint.instContinuousFunctionalCalculus`: the continuous functional calculus for
  selfadjoint elements in a unital C⋆-algebra over `ℂ`.
* `Nonneg.instContinuousFunctionalCalculus`: the continuous functional calculus for nonnegative
  elements in a unital C⋆-algebra over `ℂ`, which is also a `StarOrderedRing`.

## Tags

continuous functional calculus, normal, selfadjoint
-/

noncomputable section

section Normal

instance IsStarNormal.cfc_map {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R]
    [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A] [Ring A]
    [StarRing A] [Algebra R A] [ContinuousFunctionalCalculus R p] (a : A) (f : R → R) :
    IsStarNormal (cfc f a) where
  star_comm_self := by
    rw [Commute, SemiconjBy]
    by_cases h : ContinuousOn f (spectrum R a)
    · rw [← cfc_star, ← cfc_mul .., ← cfc_mul ..]
      congr! 2
      exact mul_comm _ _
    · simp [cfc_apply_of_not_continuousOn a h]

instance IsStarNormal.instContinuousFunctionalCalculus {A : Type*} [NormedRing A] [StarRing A]
    [CstarRing A] [CompleteSpace A] [NormedAlgebra ℂ A] [StarModule ℂ A] :
    ContinuousFunctionalCalculus ℂ (IsStarNormal : A → Prop) where
  exists_cfc_of_predicate a ha := by
    refine ⟨(elementalStarAlgebra ℂ a).subtype.comp <| continuousFunctionalCalculus a,
      ?hom_closedEmbedding, ?hom_id, ?hom_map_spectrum, ?predicate_hom⟩
    case hom_closedEmbedding => exact Isometry.closedEmbedding <|
      isometry_subtype_coe.comp <| StarAlgEquiv.isometry (continuousFunctionalCalculus a)
    case hom_id => exact congr_arg Subtype.val <| continuousFunctionalCalculus_map_id a
    case hom_map_spectrum =>
      intro f
      simp only [StarAlgHom.comp_apply, StarAlgHom.coe_coe, StarSubalgebra.coe_subtype]
      rw [← StarSubalgebra.spectrum_eq (elementalStarAlgebra.isClosed ℂ a),
        AlgEquiv.spectrum_eq (continuousFunctionalCalculus a), ContinuousMap.spectrum_eq_range]
    case predicate_hom => exact fun f ↦ ⟨by rw [← map_star]; exact Commute.all (star f) f |>.map _⟩

variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [Algebra ℂ A]
  [StarModule ℂ A] [ContinuousFunctionalCalculus ℂ (IsStarNormal : A → Prop)]

attribute [aesop safe apply] IsSelfAdjoint.isStarNormal

/-- An element in a C⋆-algebra is selfadjoint if and only if it is normal and its spectrum is
contained in `ℝ`. -/
lemma isSelfAdjoint_iff_isStarNormal_and_spectrumRestricts {a : A} :
    IsSelfAdjoint a ↔ IsStarNormal a ∧ SpectrumRestricts a Complex.reCLM := by
  refine ⟨fun ha ↦ ⟨ha.isStarNormal, ⟨fun x hx ↦ ?_, Complex.ofReal_re⟩⟩, ?_⟩
  · have := eqOn_of_cfc_eq_cfc <| (cfc_star (id : ℂ → ℂ) a).symm ▸ (cfc_id ℂ a).symm ▸ ha.star_eq
    exact Complex.conj_eq_iff_re.mp (by simpa using this hx)
  · rintro ⟨ha₁, ha₂⟩
    rw [isSelfAdjoint_iff]
    nth_rw 2 [← cfc_id ℂ a]
    rw [← cfc_star_id a (R := ℂ)]
    refine cfc_congr fun x hx ↦ ?_
    obtain ⟨x, -, rfl⟩ := ha₂.algebraMap_image.symm ▸ hx
    exact Complex.conj_ofReal _

lemma IsSelfAdjoint.spectrumRestricts {a : A} (ha : IsSelfAdjoint a) :
    SpectrumRestricts a Complex.reCLM :=
  isSelfAdjoint_iff_isStarNormal_and_spectrumRestricts.mp ha |>.right

/-- A normal element whose `ℂ`-spectrum is contained in `ℝ` is selfadjoint. -/
lemma SpectrumRestricts.isSelfAdjoint (a : A) (ha : SpectrumRestricts a Complex.reCLM)
    [IsStarNormal a] : IsSelfAdjoint a :=
  isSelfAdjoint_iff_isStarNormal_and_spectrumRestricts.mpr ⟨‹_›, ha⟩

theorem IsSelfAdjoint.continuousFunctionalCalculus_of_compactSpace_spectrum
    [h : ∀ x : A, CompactSpace (spectrum ℂ x)] :
    ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop) :=
  SpectrumRestricts.cfc (q := IsStarNormal) (p := IsSelfAdjoint) Complex.reCLM
    Complex.isometry_ofReal (fun _ ↦ isSelfAdjoint_iff_isStarNormal_and_spectrumRestricts)
    (fun _ _ ↦ h _)

instance IsSelfAdjoint.instContinuousFunctionalCalculus {A : Type*} [NormedRing A] [StarRing A]
    [CstarRing A] [CompleteSpace A] [NormedAlgebra ℂ A] [StarModule ℂ A] :
    ContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop) :=
  IsSelfAdjoint.continuousFunctionalCalculus_of_compactSpace_spectrum

lemma unitary_iff_isStarNormal_and_spectrum_subset_circle {u : A} :
    u ∈ unitary A ↔ IsStarNormal u ∧ spectrum ℂ u ⊆ circle := by
  refine ⟨fun hu ↦ ?_, ?_⟩
  · have h_normal := isStarNormal_of_mem_unitary hu
    refine ⟨h_normal, ?_⟩
    have h := unitary.star_mul_self_of_mem hu
    rw [← cfc_id ℂ u, ← cfc_star id u, ← cfc_mul .., ← cfc_one ℂ u] at h
    have := eqOn_of_cfc_eq_cfc h
    peel this with x hx _
    rw [SetLike.mem_coe, mem_circle_iff_normSq]
    simpa using congr($(this).re)
  · rintro ⟨_, hu⟩
    rw [unitary.mem_iff, ← cfc_id ℂ u, ← cfc_star, ← cfc_mul .., ← cfc_mul .., ← cfc_one ℂ u]
    simp only [id_eq]
    constructor
    all_goals
      apply cfc_congr (fun x hx ↦ ?_)
      simp only [RCLike.star_def, mul_comm x]
      apply hu at hx
      rwa [SetLike.mem_coe, mem_circle_iff_normSq, ← Complex.ofReal_injective.eq_iff,
        Complex.normSq_eq_conj_mul_self] at hx

lemma mem_unitary_of_spectrum_subset_circle {u : A}
    [IsStarNormal u] (hu : spectrum ℂ u ⊆ circle) : u ∈ unitary A :=
  unitary_iff_isStarNormal_and_spectrum_subset_circle.mpr ⟨‹_›, hu⟩

lemma spectrum_subset_circle_of_mem_unitary {u : A} (hu : u ∈ unitary A) :
    spectrum ℂ u ⊆ circle :=
  unitary_iff_isStarNormal_and_spectrum_subset_circle.mp hu |>.right

end Normal

section SpectrumRestricts

open NNReal ENNReal

variable {A : Type*} [NormedRing A] [StarRing A] [CstarRing A] [CompleteSpace A]
variable [NormedAlgebra ℂ A] [StarModule ℂ A]

lemma SpectrumRestricts.nnreal_iff_nnnorm {a : A} {t : ℝ≥0} (ha : IsSelfAdjoint a) (ht : ‖a‖₊ ≤ t) :
    SpectrumRestricts a ContinuousMap.realToNNReal ↔ ‖algebraMap ℝ A t - a‖₊ ≤ t := by
  have : IsSelfAdjoint (algebraMap ℝ A t - a) := IsSelfAdjoint.algebraMap A (.all (t : ℝ)) |>.sub ha
  rw [← ENNReal.coe_le_coe, ← IsSelfAdjoint.spectralRadius_eq_nnnorm,
    ← SpectrumRestricts.spectralRadius_eq (f := Complex.reCLM)] at ht ⊢
  exact SpectrumRestricts.nnreal_iff_spectralRadius_le ht
  all_goals
    try apply IsSelfAdjoint.spectrumRestricts
    assumption

lemma SpectrumRestricts.nnreal_add {a b : A} (ha₁ : IsSelfAdjoint a)
    (hb₁ : IsSelfAdjoint b) (ha₂ : SpectrumRestricts a ContinuousMap.realToNNReal)
    (hb₂ : SpectrumRestricts b ContinuousMap.realToNNReal) :
    SpectrumRestricts (a + b) ContinuousMap.realToNNReal := by
  rw [SpectrumRestricts.nnreal_iff_nnnorm (ha₁.add hb₁) (nnnorm_add_le a b), NNReal.coe_add,
    map_add, add_sub_add_comm]
  refine nnnorm_add_le _ _ |>.trans ?_
  gcongr
  all_goals rw [← SpectrumRestricts.nnreal_iff_nnnorm] <;> first | rfl | assumption


lemma IsSelfAdjoint.sq_spectrumRestricts {a : A} (ha : IsSelfAdjoint a) :
    SpectrumRestricts (a ^ 2) ContinuousMap.realToNNReal := by
  rw [SpectrumRestricts.nnreal_iff, ← cfc_id (R := ℝ) a, ← cfc_pow .., cfc_map_spectrum ..]
  rintro - ⟨x, -, rfl⟩
  exact sq_nonneg x

open ComplexStarModule

lemma SpectrumRestricts.eq_zero_of_neg {a : A} (ha : IsSelfAdjoint a)
    (ha₁ : SpectrumRestricts a ContinuousMap.realToNNReal)
    (ha₂ : SpectrumRestricts (-a) ContinuousMap.realToNNReal) :
    a = 0 := by
  nontriviality A
  rw [SpectrumRestricts.nnreal_iff] at ha₁ ha₂
  apply eq_zero_of_spectrum_subset_zero (R := ℝ) a
  rw [Set.subset_singleton_iff]
  simp only [← spectrum.neg_eq, Set.mem_neg] at ha₂
  peel ha₁ with x hx _
  linarith [ha₂ (-x) ((neg_neg x).symm ▸ hx)]

lemma SpectrumRestricts.smul_of_nonneg {A : Type*} [Ring A] [Algebra ℝ A] {a : A}
    (ha : SpectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ} (hr : 0 ≤ r) :
    SpectrumRestricts (r • a) ContinuousMap.realToNNReal := by
  rw [SpectrumRestricts.nnreal_iff] at ha ⊢
  nontriviality A
  intro x hx
  by_cases hr' : r = 0
  · simp [hr'] at hx ⊢
    exact hx.symm.le
  · lift r to ℝˣ using IsUnit.mk0 r hr'
    rw [← Units.smul_def, spectrum.unit_smul_eq_smul, Set.mem_smul_set_iff_inv_smul_mem] at hx
    refine le_of_smul_le_smul_left ?_ (inv_pos.mpr <| lt_of_le_of_ne hr <| ne_comm.mpr hr')
    simpa [Units.smul_def] using ha _ hx

lemma spectrum_star_mul_self_nonneg {b : A} : ∀ x ∈ spectrum ℝ (star b * b), 0 ≤ x := by
  set a := star b * b
  have a_def : a = star b * b := rfl
  let a_neg : A := cfc (fun x ↦ (- ContinuousMap.id ℝ ⊔ 0) x) a
  set c := b * a_neg
  have h_eq_a_neg : - (star c * c) = a_neg ^ 3 := by
    simp only [c, a_neg, star_mul]
    rw [← mul_assoc, mul_assoc _ _ b, ← cfc_star, ← cfc_id' ℝ (star b * b), a_def, ← neg_mul]
    rw [← cfc_mul _ _ (star b * b) (by simp; fun_prop), neg_mul]
    simp only [ContinuousMap.coe_neg, ContinuousMap.coe_id, Pi.sup_apply, Pi.neg_apply,
      star_trivial]
    rw [← cfc_mul .., ← cfc_neg .., ← cfc_pow ..]
    congr
    ext x
    by_cases hx : x ≤ 0
    · rw [← neg_nonneg] at hx
      simp [sup_eq_left.mpr hx, pow_succ]
    · rw [not_le, ← neg_neg_iff_pos] at hx
      simp [sup_eq_right.mpr hx.le]
  have h_c_spec₀ : SpectrumRestricts (- (star c * c)) (ContinuousMap.realToNNReal ·) := by
    simp only [SpectrumRestricts.nnreal_iff, h_eq_a_neg]
    rw [← cfc_pow _ _ (ha := .star_mul_self b)]
    simp only [cfc_map_spectrum (R := ℝ) (fun x => (-ContinuousMap.id ℝ ⊔ 0) x ^ 3) (star b * b)]
    rintro - ⟨x, -, rfl⟩
    simp
  have c_eq := star_mul_self_add_self_mul_star c
  rw [← eq_sub_iff_add_eq', sub_eq_add_neg, ← sq, ← sq] at c_eq
  have h_c_spec₁ : SpectrumRestricts (c * star c) ContinuousMap.realToNNReal := by
    rw [c_eq]
    refine SpectrumRestricts.nnreal_add ?_ ?_ ?_ h_c_spec₀
    · exact IsSelfAdjoint.smul (by rfl) <| ((ℜ c).prop.pow 2).add ((ℑ c).prop.pow 2)
    · exact (IsSelfAdjoint.star_mul_self c).neg
    · rw [nsmul_eq_smul_cast ℝ]
      refine (ℜ c).2.sq_spectrumRestricts.nnreal_add ((ℜ c).2.pow 2) ((ℑ c).2.pow 2)
        (ℑ c).2.sq_spectrumRestricts |>.smul_of_nonneg <| by norm_num
  have h_c_spec₂ : SpectrumRestricts (star c * c) ContinuousMap.realToNNReal := by
    rw [SpectrumRestricts.nnreal_iff] at h_c_spec₁ ⊢
    intro x hx
    replace hx := Set.subset_diff_union _ {(0 : ℝ)} hx
    rw [spectrum.nonzero_mul_eq_swap_mul, Set.diff_union_self, Set.union_singleton,
      Set.mem_insert_iff] at hx
    obtain (rfl | hx) := hx
    exacts [le_rfl, h_c_spec₁ x hx]
  rw [h_c_spec₂.eq_zero_of_neg (.star_mul_self c) h_c_spec₀, neg_zero] at h_eq_a_neg
  simp only [a_neg] at h_eq_a_neg
  rw [← cfc_pow _ _ (ha := by aesop (add simp a)), ← cfc_zero a (R := ℝ)] at h_eq_a_neg
  intro x hx
  by_contra! hx'
  rw [← neg_pos] at hx'
  apply (pow_pos hx' 3).ne
  have h_eqOn := eqOn_of_cfc_eq_cfc (a := star b * b) h_eq_a_neg
  simpa [sup_eq_left.mpr hx'.le] using h_eqOn hx

end SpectrumRestricts

section Nonneg

variable {A : Type*} [NormedRing A] [CompleteSpace A]
variable [PartialOrder A] [StarRing A] [StarOrderedRing A] [CstarRing A]
variable [NormedAlgebra ℂ A] [StarModule ℂ A]

lemma nonneg_iff_isSelfAdjoint_and_spectrumRestricts {a : A} :
    0 ≤ a ↔ IsSelfAdjoint a ∧ SpectrumRestricts a ContinuousMap.realToNNReal := by
  rw [SpectrumRestricts.nnreal_iff]
  refine ⟨fun ha ↦ ?_, ?_⟩
  · rw [StarOrderedRing.nonneg_iff] at ha
    induction ha using AddSubmonoid.closure_induction' with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      exact ⟨IsSelfAdjoint.star_mul_self b, spectrum_star_mul_self_nonneg⟩
    | one =>
      nontriviality A
      simp
    | mul x _ y _ hx hy =>
      rw [← SpectrumRestricts.nnreal_iff] at hx hy ⊢
      exact ⟨hx.1.add hy.1, hx.2.nnreal_add hx.1 hy.1 hy.2⟩
  · rintro ⟨ha₁, ha₂⟩
    let s := cfc Real.sqrt a
    have : a = star s * s := by
      rw [← cfc_id a (R := ℝ), ← cfc_star (R := ℝ) _ a, ← cfc_mul ..]
      apply cfc_congr
      peel ha₂ with x hx _
      simp [Real.mul_self_sqrt this]
    exact this ▸ star_mul_self_nonneg s

open NNReal in
instance Nonneg.instContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus ℝ≥0 (fun x : A ↦ 0 ≤ x) :=
  SpectrumRestricts.cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal
    isometry_subtype_coe (fun _ ↦ nonneg_iff_isSelfAdjoint_and_spectrumRestricts)
    (fun _ _ ↦ inferInstance)

end Nonneg

end
