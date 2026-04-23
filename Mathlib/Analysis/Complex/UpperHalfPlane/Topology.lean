/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Int.Cast.Field
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Order.Filter.Map
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Topology on the upper half plane

In this file we introduce a `TopologicalSpace` structure on the upper half plane and provide
various instances.
-/

@[expose] public section

noncomputable section

open Complex Filter Function Set TopologicalSpace Topology

open scoped ComplexConjugate

namespace UpperHalfPlane

instance : TopologicalSpace ℍ :=
  .induced UpperHalfPlane.coe inferInstance

@[fun_prop]
theorem isEmbedding_coe : IsEmbedding ((↑) : ℍ → ℂ) :=
  coe_injective.isEmbedding_induced

theorem isOpenEmbedding_coe : IsOpenEmbedding ((↑) : ℍ → ℂ) :=
  ⟨isEmbedding_coe, by simp [isOpen_upperHalfPlaneSet]⟩

@[fun_prop]
theorem continuous_coe : Continuous ((↑) : ℍ → ℂ) :=
  isEmbedding_coe.continuous

@[fun_prop]
theorem continuous_re : Continuous re :=
  Complex.continuous_re.comp continuous_coe

@[fun_prop]
theorem continuous_im : Continuous im :=
  Complex.continuous_im.comp continuous_coe

@[fun_prop]
theorem _root_.Continuous.upperHalfPlaneMk {X : Type*} [TopologicalSpace X] {f : X → ℂ}
    (hf : Continuous f) (hf₀ : ∀ x, 0 < (f x).im) :
    Continuous fun x ↦ mk (f x) (hf₀ x) :=
  isEmbedding_coe.continuous_iff.mpr hf

instance : SecondCountableTopology ℍ :=
  secondCountableTopology_induced ..

instance : T3Space ℍ := isEmbedding_coe.t3Space

instance : T4Space ℍ := inferInstance

instance : ContractibleSpace ℍ := by
  rw [isEmbedding_coe.toHomeomorph.trans (.setCongr range_coe) |>.contractibleSpace_iff]
  exact (convex_halfSpace_im_gt 0).contractibleSpace ⟨I, one_pos.trans_eq I_im.symm⟩

instance : LocPathConnectedSpace ℍ := isOpenEmbedding_coe.locPathConnectedSpace

instance : NoncompactSpace ℍ where
  noncompact_univ h := by
    have : IsCompact (Complex.im ⁻¹' Ioi 0) := by
      simpa [isEmbedding_coe.isCompact_iff] using h
    simpa [closure_preimage_im] using congr(0 ∈ $this.isClosed.closure_eq)

instance : LocallyCompactSpace ℍ :=
  isOpenEmbedding_coe.locallyCompactSpace

/-- Each element of `GL(2, ℝ)` defines a continuous map `ℍ → ℍ`. -/
instance instContinuousGLSMul : ContinuousConstSMul (GL (Fin 2) ℝ) ℍ where
  continuous_const_smul g := by
    simp_rw [continuous_induced_rng (f := UpperHalfPlane.coe), Function.comp_def,
      UpperHalfPlane.coe_smul, UpperHalfPlane.σ]
    refine .comp ?_ ?_
    · split_ifs
      exacts [continuous_id, continuous_conj]
    · refine .div ?_ ?_ (fun x ↦ denom_ne_zero g x) <;>
      exact (continuous_const.mul continuous_coe).add continuous_const

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

lemma verticalStrip_mono_left {A A'} (h : A ≤ A') (B) : verticalStrip A B ⊆ verticalStrip A' B :=
  verticalStrip_mono h le_rfl

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
  let n := Int.floor (z.re / N)
  use -n
  rw [modular_T_zpow_smul z (N * -n)]
  refine ⟨?_, by simp⟩
  have h : (N * (-n : ℝ) +ᵥ z).re = -N * Int.floor (z.re / N) + z.re := by
    simp only [n, mul_neg, vadd_re, neg_mul]
  norm_cast at *
  rw [h, add_comm]
  simp only [neg_mul, Int.cast_neg, Int.cast_mul, Int.cast_natCast]
  have hnn : (0 : ℝ) < (N : ℝ) := by norm_cast at *
  have h2 : z.re + -(N * n) = z.re - n * N := by ring
  rw [h2, abs_eq_self.2 (Int.sub_floor_div_mul_nonneg (z.re : ℝ) hnn)]
  apply (Int.sub_floor_div_mul_lt (z.re : ℝ) hnn).le

end strips

section ofComplex

/-- A section `ℂ → ℍ` of the natural inclusion map, bundled as an `OpenPartialHomeomorph`. -/
def ofComplex : OpenPartialHomeomorph ℂ ℍ := (isOpenEmbedding_coe.toOpenPartialHomeomorph _).symm

/-- Extend a function on `ℍ` arbitrarily to a function on all of `ℂ`. -/
scoped notation "↑ₕ" f => f ∘ ofComplex

@[simp]
lemma ofComplex_apply (z : ℍ) : ofComplex (z : ℂ) = z :=
  IsOpenEmbedding.toOpenPartialHomeomorph_left_inv ..

lemma ofComplex_apply_eq_ite (w : ℂ) :
    ofComplex w = if hw : 0 < w.im then ⟨w, hw⟩ else Classical.choice inferInstance := by
  split_ifs with hw
  · exact ofComplex_apply ⟨w, hw⟩
  · change (Function.invFunOn UpperHalfPlane.coe Set.univ w) = _
    simp only [invFunOn, dite_eq_right_iff, mem_univ, true_and]
    rintro ⟨a, rfl⟩
    exact (a.im_pos.not_ge (by simpa using hw)).elim

lemma ofComplex_apply_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    ofComplex z = ⟨z, hz⟩ :=
  ofComplex_apply ⟨z, hz⟩

lemma ofComplex_apply_of_im_nonpos {w : ℂ} (hw : w.im ≤ 0) :
    ofComplex w = Classical.choice inferInstance := by
  simp [ofComplex_apply_eq_ite w, hw]

lemma ofComplex_apply_eq_of_im_nonpos {w w' : ℂ} (hw : w.im ≤ 0) (hw' : w'.im ≤ 0) :
    ofComplex w = ofComplex w' := by
  simp [ofComplex_apply_of_im_nonpos, hw, hw']

lemma comp_ofComplex (f : ℍ → ℂ) (z : ℍ) : (↑ₕf) z = f z :=
  congrArg _ <| ofComplex_apply z

lemma comp_ofComplex_of_im_pos (f : ℍ → ℂ) (z : ℂ) (hz : 0 < z.im) : (↑ₕf) z = f ⟨z, hz⟩ :=
  congrArg _ <| ofComplex_apply ⟨z, hz⟩

lemma comp_ofComplex_of_im_le_zero (f : ℍ → ℂ) (z z' : ℂ) (hz : z.im ≤ 0) (hz' : z'.im ≤ 0) :
    (↑ₕf) z = (↑ₕf) z' := by
  simp [ofComplex_apply_of_im_nonpos, hz, hz']

lemma eventuallyEq_coe_comp_ofComplex {z : ℂ} (hz : 0 < z.im) :
    UpperHalfPlane.coe ∘ ofComplex =ᶠ[𝓝 z] id := by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with x hx
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hx, id_eq]

lemma J_smul (τ : ℍ) : J • τ = ofComplex (-(conj ↑τ)) := by
  ext
  rw [coe_J_smul, ofComplex_apply_of_im_pos (by simpa using τ.im_pos)]

end ofComplex

section IsOpenMap

lemma isOpenMap_re : IsOpenMap re :=
  Complex.isOpenMap_re.comp isOpenEmbedding_coe.isOpenMap

lemma isOpenMap_im : IsOpenMap im :=
  Complex.isOpenMap_im.comp isOpenEmbedding_coe.isOpenMap

lemma isOpenMap_norm : IsOpenMap (fun τ : ℍ ↦ ‖(τ : ℂ)‖) := by
  refine .of_nhds_le fun τ U hU ↦ ?_
  obtain ⟨s, hs, hs'⟩ := Filter.mem_map_iff_exists_image.mp hU
  simp_rw [← isOpenEmbedding_coe.image_mem_nhds, Metric.mem_nhds_iff] at hs ⊢
  obtain ⟨ε, hεpos, hεs⟩ := hs
  refine ⟨ε, hεpos, subset_trans (fun r hr ↦ ?_) hs'⟩
  have hr' : 0 ≤ r := by
    by_contra! hr'
    rw [mem_ball_iff_norm, Real.norm_eq_abs, abs_lt] at hr
    have : ‖(τ : ℂ)‖ < ε := by linarith
    have : 0 ∈ Metric.ball (τ : ℂ) ε := by rwa [mem_ball_iff_norm', sub_zero]
    simpa [UpperHalfPlane.ne_zero] using hεs this
  have : r / ‖(τ : ℂ)‖ * (τ : ℂ) ∈ Metric.ball (τ : ℂ) ε := by
    rwa [mem_ball_iff_norm,
      show r / ‖(τ : ℂ)‖ * (τ : ℂ) - τ = ↑(r / ‖(τ : ℂ)‖ - 1) * (τ : ℂ) by simp; ring,
      norm_mul, norm_real, ← norm_norm (τ : ℂ), ← norm_mul, sub_mul, norm_norm, one_mul,
      div_mul_cancel₀ _ (by simpa using τ.ne_zero), ← mem_ball_iff_norm]
  obtain ⟨ξ, hξs, hξτ⟩ := Set.mem_of_mem_of_subset this hεs
  use ξ, hξs
  simp_rw [hξτ, norm_mul, norm_div, norm_real, norm_norm]
  rw [div_mul_cancel₀ _ (by simpa using τ.ne_zero), Real.norm_of_nonneg hr']

end IsOpenMap

end UpperHalfPlane
