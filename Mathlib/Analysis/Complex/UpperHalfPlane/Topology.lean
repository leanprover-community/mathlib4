/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.Normed
import Mathlib.Analysis.Convex.Complex
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.PartialHomeomorph

/-!
# Topology on the upper half plane

In this file we introduce a `TopologicalSpace` structure on the upper half plane and provide
various instances.
-/


noncomputable section

open Set Filter Function TopologicalSpace Complex

open scoped Filter Topology UpperHalfPlane

namespace UpperHalfPlane

instance : TopologicalSpace ℍ :=
  instTopologicalSpaceSubtype

theorem isOpenEmbedding_coe : IsOpenEmbedding ((↑) : ℍ → ℂ) :=
  IsOpen.isOpenEmbedding_subtypeVal <| isOpen_lt continuous_const Complex.continuous_im

@[deprecated (since := "2024-10-18")]
alias openEmbedding_coe := isOpenEmbedding_coe

theorem isEmbedding_coe : IsEmbedding ((↑) : ℍ → ℂ) :=
  IsEmbedding.subtypeVal

@[deprecated (since := "2024-10-26")]
alias embedding_coe := isEmbedding_coe

theorem continuous_coe : Continuous ((↑) : ℍ → ℂ) :=
  isEmbedding_coe.continuous

theorem continuous_re : Continuous re :=
  Complex.continuous_re.comp continuous_coe

theorem continuous_im : Continuous im :=
  Complex.continuous_im.comp continuous_coe

instance : SecondCountableTopology ℍ :=
  TopologicalSpace.Subtype.secondCountableTopology _

instance : T3Space ℍ := Subtype.t3Space

instance : T4Space ℍ := inferInstance

instance : ContractibleSpace ℍ :=
  (convex_halfspace_im_gt 0).contractibleSpace ⟨I, one_pos.trans_eq I_im.symm⟩

instance : LocPathConnectedSpace ℍ := isOpenEmbedding_coe.locPathConnectedSpace

instance : NoncompactSpace ℍ := by
  refine ⟨fun h => ?_⟩
  have : IsCompact (Complex.im ⁻¹' Ioi 0) := isCompact_iff_isCompact_univ.2 h
  replace := this.isClosed.closure_eq
  rw [closure_preimage_im, closure_Ioi, Set.ext_iff] at this
  exact absurd ((this 0).1 (@left_mem_Ici ℝ _ 0)) (@lt_irrefl ℝ _ 0)

instance : LocallyCompactSpace ℍ :=
  isOpenEmbedding_coe.locallyCompactSpace

section strips

/-- The vertical strip of width `A` and height `B`, defined by elements whose real part has absolute
value less than or equal to `A` and imaginary part is at least `B`. -/
def verticalStrip (A B : ℝ) := {z : ℍ | |z.re| ≤ A ∧ B ≤ z.im}

theorem mem_verticalStrip_iff (A B : ℝ) (z : ℍ) : z ∈ verticalStrip A B ↔ |z.re| ≤ A ∧ B ≤ z.im :=
  Iff.rfl

@[gcongr]
lemma verticalStrip_mono {A B A' B' : ℝ} (hA : A ≤ A') (hB : B' ≤ B) :
    verticalStrip A B ⊆ verticalStrip A' B' := by
  rintro z ⟨hzre, hzim⟩
  exact ⟨hzre.trans hA, hB.trans hzim⟩

@[gcongr]
lemma verticalStrip_mono_left {A A'} (h : A ≤ A') (B) : verticalStrip A B ⊆ verticalStrip A' B :=
  verticalStrip_mono h le_rfl

@[gcongr]
lemma verticalStrip_anti_right (A) {B B'} (h : B' ≤ B) : verticalStrip A B ⊆ verticalStrip A B' :=
  verticalStrip_mono le_rfl h

lemma subset_verticalStrip_of_isCompact {K : Set ℍ} (hK : IsCompact K) :
    ∃ A B : ℝ, 0 < B ∧ K ⊆ verticalStrip A B := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, 1, Real.zero_lt_one, empty_subset _⟩
  obtain ⟨u, _, hu⟩ := hK.exists_isMaxOn hne (_root_.continuous_abs.comp continuous_re).continuousOn
  obtain ⟨v, _, hv⟩ := hK.exists_isMinOn hne continuous_im.continuousOn
  exact ⟨|re u|, im v, v.im_pos, fun k hk ↦ ⟨isMaxOn_iff.mp hu _ hk, isMinOn_iff.mp hv _ hk⟩⟩

theorem ModularGroup_T_zpow_mem_verticalStrip (z : ℍ) {N : ℕ} (hn : 0 < N) :
    ∃ n : ℤ, ModularGroup.T ^ (N * n) • z ∈ verticalStrip N z.im := by
  let n := Int.floor (z.re/N)
  use -n
  rw [modular_T_zpow_smul z (N * -n)]
  refine ⟨?_, (by simp only [mul_neg, Int.cast_neg, Int.cast_mul, Int.cast_natCast, vadd_im,
    le_refl])⟩
  have h : (N * (-n : ℝ) +ᵥ z).re = -N * Int.floor (z.re / N) + z.re := by
    simp only [Int.cast_natCast, mul_neg, vadd_re, neg_mul]
  norm_cast at *
  rw [h, add_comm]
  simp only [neg_mul, Int.cast_neg, Int.cast_mul, Int.cast_natCast]
  have hnn : (0 : ℝ) < (N : ℝ) := by norm_cast at *
  have h2 : z.re + -(N * n) =  z.re - n * N := by ring
  rw [h2, abs_eq_self.2 (Int.sub_floor_div_mul_nonneg (z.re : ℝ) hnn)]
  apply (Int.sub_floor_div_mul_lt (z.re : ℝ) hnn).le

end strips

/-- A continuous section `ℂ → ℍ` of the natural inclusion map, bundled as a `PartialHomeomorph`. -/
def ofComplex : PartialHomeomorph ℂ ℍ := (isOpenEmbedding_coe.toPartialHomeomorph _).symm

/-- Extend a function on `ℍ` arbitrarily to a function on all of `ℂ`. -/
scoped notation "↑ₕ" f => f ∘ ofComplex

lemma ofComplex_apply (z : ℍ) : ofComplex (z : ℂ) = z :=
  IsOpenEmbedding.toPartialHomeomorph_left_inv ..

lemma ofComplex_apply_eq_ite (w : ℂ) :
    ofComplex w = if hw : 0 < w.im then ⟨w, hw⟩ else Classical.choice inferInstance := by
  split_ifs with hw
  · exact ofComplex_apply ⟨w, hw⟩
  · change (Function.invFunOn UpperHalfPlane.coe Set.univ w) = _
    simp only [invFunOn, dite_eq_right_iff, mem_univ, true_and]
    rintro ⟨a, rfl⟩
    exact (a.prop.not_le (by simpa using hw)).elim

lemma ofComplex_apply_of_im_nonpos {w : ℂ} (hw : w.im ≤ 0) :
    ofComplex w = Classical.choice inferInstance := by
  simp [ofComplex_apply_eq_ite w, hw]

lemma ofComplex_apply_eq_of_im_nonpos {w w' : ℂ} (hw : w.im ≤ 0) (hw' : w'.im ≤ 0) :
    ofComplex w = ofComplex w' := by
  simp [ofComplex_apply_of_im_nonpos, hw, hw']

lemma comp_ofComplex (f : ℍ → ℂ) (z : ℍ) : (↑ₕ f) z = f z :=
  congrArg _ <| ofComplex_apply z

lemma comp_ofComplex_of_im_pos (f : ℍ → ℂ) (z : ℂ) (hz : 0 < z.im) : (↑ₕ f) z = f ⟨z, hz⟩ :=
  congrArg _ <| ofComplex_apply ⟨z, hz⟩

lemma comp_ofComplex_of_im_le_zero (f : ℍ → ℂ) (z z' : ℂ) (hz : z.im ≤ 0) (hz' : z'.im ≤ 0)  :
    (↑ₕ f) z = (↑ₕ f) z' := by
  simp [ofComplex_apply_of_im_nonpos, hz, hz']

end UpperHalfPlane

lemma Complex.isConnected_of_upperHalfPlane {s : Set ℂ} (hs₁ : {z | 0 < z.im} ⊆ s)
    (hs₂ : s ⊆ {z | 0 ≤ z.im}) : IsConnected s := by
  refine IsConnected.subset_closure ?_ hs₁ (by simpa using hs₂)
  rw [isConnected_iff_connectedSpace]
  exact inferInstanceAs (ConnectedSpace UpperHalfPlane)

lemma Complex.isConnected_of_lowerHalfPlane {s : Set ℂ} (hs₁ : {z | z.im < 0} ⊆ s)
    (hs₂ : s ⊆ {z | z.im ≤ 0}) : IsConnected s := by
  rw [← Equiv.star.surjective.image_preimage s]
  refine IsConnected.image (f := Equiv.star) ?_ continuous_star.continuousOn
  apply Complex.isConnected_of_upperHalfPlane
  · exact fun z hz ↦ hs₁ <| show star z ∈ _ by simpa
  · exact fun z hz ↦ by simpa using show (star z).im ≤ 0 from hs₂ hz
