/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.Normed
import Mathlib.Analysis.Convex.Complex
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.PartialHomeomorph

#align_import analysis.complex.upper_half_plane.topology from "leanprover-community/mathlib"@"57f9349f2fe19d2de7207e99b0341808d977cdcf"

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

theorem openEmbedding_coe : OpenEmbedding ((↑) : ℍ → ℂ) :=
  IsOpen.openEmbedding_subtype_val <| isOpen_lt continuous_const Complex.continuous_im
#align upper_half_plane.open_embedding_coe UpperHalfPlane.openEmbedding_coe

theorem embedding_coe : Embedding ((↑) : ℍ → ℂ) :=
  embedding_subtype_val
#align upper_half_plane.embedding_coe UpperHalfPlane.embedding_coe

theorem continuous_coe : Continuous ((↑) : ℍ → ℂ) :=
  embedding_coe.continuous
#align upper_half_plane.continuous_coe UpperHalfPlane.continuous_coe

theorem continuous_re : Continuous re :=
  Complex.continuous_re.comp continuous_coe
#align upper_half_plane.continuous_re UpperHalfPlane.continuous_re

theorem continuous_im : Continuous im :=
  Complex.continuous_im.comp continuous_coe
#align upper_half_plane.continuous_im UpperHalfPlane.continuous_im

instance : SecondCountableTopology ℍ :=
  TopologicalSpace.Subtype.secondCountableTopology _

instance : T3Space ℍ := Subtype.t3Space

instance : T4Space ℍ := inferInstance

instance : ContractibleSpace ℍ :=
  (convex_halfspace_im_gt 0).contractibleSpace ⟨I, one_pos.trans_eq I_im.symm⟩

instance : LocPathConnectedSpace ℍ :=
  locPathConnected_of_isOpen <| isOpen_lt continuous_const Complex.continuous_im

instance : NoncompactSpace ℍ := by
  refine ⟨fun h => ?_⟩
  have : IsCompact (Complex.im ⁻¹' Ioi 0) := isCompact_iff_isCompact_univ.2 h
  replace := this.isClosed.closure_eq
  rw [closure_preimage_im, closure_Ioi, Set.ext_iff] at this
  exact absurd ((this 0).1 (@left_mem_Ici ℝ _ 0)) (@lt_irrefl ℝ _ 0)

instance : LocallyCompactSpace ℍ :=
  openEmbedding_coe.locallyCompactSpace

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
  simp only [neg_mul, Int.cast_neg, Int.cast_mul, Int.cast_natCast, ge_iff_le]
  have hnn : (0 : ℝ) < (N : ℝ) := by norm_cast at *
  have h2 : z.re + -(N * n) =  z.re - n * N := by ring
  rw [h2, abs_eq_self.2 (Int.sub_floor_div_mul_nonneg (z.re : ℝ) hnn)]
  apply (Int.sub_floor_div_mul_lt (z.re : ℝ) hnn).le

end strips

/-- A continuous section `ℂ → ℍ` of the natural inclusion map, bundled as a `PartialHomeomorph`. -/
def ofComplex : PartialHomeomorph ℂ ℍ := (openEmbedding_coe.toPartialHomeomorph _).symm

/-- Extend a function on `ℍ` arbitrarily to a function on all of `ℂ`. -/
scoped notation "↑ₕ" f => f ∘ ofComplex

lemma ofComplex_apply (z : ℍ) : ofComplex (z : ℂ) = z :=
  OpenEmbedding.toPartialHomeomorph_left_inv ..

lemma comp_ofComplex (f : ℍ → ℂ) (z : ℍ) : (↑ₕ f) z = f z := by
  rw [Function.comp_apply, ofComplex_apply]

end UpperHalfPlane
