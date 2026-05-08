/-
Copyright (c) 2025 Haoen Feng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haoen Feng
-/
module

import Mathlib.Analysis.Calculus.DifferentialForm.BoxStokes
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Stokes' theorem on the half-space `ℝⁿ₊ = {x : x_m ≥ 0}`

This file proves the generalized Stokes theorem for compactly supported `C¹`
differential forms on the upper half-space `{x : Fin (m + 1) → ℝ | x (lastCoord m) ≥ 0}`.

The proof strategy:
1. Reduce to Stokes on a large box `[-R, R]^m × [0, R]` using compact support.
2. Apply `box_stokes_of_contDiff`.
3. All faces except the back face at `x_m = 0` vanish for large `R`.

## Main definitions

* `HalfSpace m`: the upper half-space `{x : x_m ≥ 0}` in `Fin (m + 1) → ℝ`.
* `boundaryIntegral m ω`: the integral of `ω` over `∂ℝ^{m+1}_+`.

## Main results

* `halfSpace_stokes`: For a compactly supported `C¹` `m`-form `ω` on `ℝ^{m+1}`,
  `∫_{ℝ^{m+1}_+} dω = ∫_{∂ℝ^{m+1}_+} ω`.

## Tags

Stokes theorem, half-space, differential form, exterior derivative, boundary integral
-/

noncomputable section

open ContinuousAlternatingMap Fin Set MeasureTheory Measure Matrix DifferentialForm
open scoped Topology

namespace DifferentialForm

/-! ## The Last Coordinate Index -/

/-- The index of the last coordinate: `lastCoord m = Fin.last m`. -/
def lastCoord (m : ℕ) : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩

@[simp]
theorem lastCoord_val (m : ℕ) : (lastCoord m : ℕ) = m := rfl

/-! ## Boundary Inclusion -/

/-- The boundary inclusion `y ↦ Fin.insertNth (lastCoord m) 0 y` maps
`Fin m → ℝ` into the face `x_m = 0` of the half-space. -/
def boundaryInclusion (m : ℕ) (y : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.insertNth (lastCoord m) (0 : ℝ) y

@[simp]
theorem boundaryInclusion_last (m : ℕ) (y : Fin m → ℝ) :
    boundaryInclusion m y (lastCoord m) = (0 : ℝ) := by
  simp [boundaryInclusion]

@[simp]
theorem boundaryInclusion_succAbove (m : ℕ) (y : Fin m → ℝ) (i : Fin m) :
    boundaryInclusion m y (Fin.succAbove (lastCoord m) i) = y i := by
  simp [boundaryInclusion]

/-! ## Half-Space Definitions -/

/-- The upper half-space `{x : x_m ≥ 0}` in `Fin (m + 1) → ℝ`. -/
def HalfSpace (m : ℕ) : Set (Fin (m + 1) → ℝ) :=
  {x | (0 : ℝ) ≤ x (lastCoord m)}

/-- The integral of an `m`-form over the boundary of the half-space.

The boundary `∂ℝ^{m+1}_+` is identified with `Fin m → ℝ` via
`boundaryInclusion m = Fin.insertNth (lastCoord m) 0`. -/
noncomputable def boundaryIntegral (m : ℕ)
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ) : ℝ :=
  -(∫ y : Fin m → ℝ,
      boxFaceComponent ω (lastCoord m) (boundaryInclusion m y))

/-! ## Half-Space Boxes -/

/-- Lower corner of the half-space box: `(-R, ..., -R, 0)`. -/
noncomputable def halfSpaceBoxLower (m : ℕ) (R : ℝ) : Fin (m + 1) → ℝ :=
  fun i => if i = lastCoord m then (0 : ℝ) else -(R : ℝ)

/-- Upper corner of the half-space box: `(R, ..., R)`. -/
noncomputable def halfSpaceBoxUpper (m : ℕ) (R : ℝ) : Fin (m + 1) → ℝ :=
  fun _ => (R : ℝ)

@[simp]
theorem halfSpaceBoxLower_last (m : ℕ) (R : ℝ) :
    halfSpaceBoxLower m R (lastCoord m) = (0 : ℝ) := by
  simp [halfSpaceBoxLower]

@[simp]
theorem halfSpaceBoxUpper_apply (m : ℕ) (R : ℝ) (i : Fin (m + 1)) :
    halfSpaceBoxUpper m R i = (R : ℝ) := rfl

theorem halfSpaceBoxLower_succAbove (m : ℕ) (R : ℝ) (i : Fin m) :
    halfSpaceBoxLower m R (Fin.succAbove (lastCoord m) i) = -(R : ℝ) := by
  have hne := Fin.succAbove_ne (lastCoord m) i
  simp [halfSpaceBoxLower, hne]

@[simp]
theorem halfSpaceBoxUpper_succAbove (m : ℕ) (R : ℝ) (i : Fin m) :
    halfSpaceBoxUpper m R (Fin.succAbove (lastCoord m) i) = (R : ℝ) := rfl

theorem halfSpaceBoxLower_le_upper (m : ℕ) {R : ℝ} (hR : (0 : ℝ) ≤ R) :
    halfSpaceBoxLower m R ≤ halfSpaceBoxUpper m R := by
  intro i; simp only [halfSpaceBoxUpper_apply]
  by_cases h : i = lastCoord m
  · subst h; simp [hR]
  · simp only [halfSpaceBoxLower, h]; exact neg_le_self hR

/-! ## Norm Bounds -/

/-- `‖Fin.insertNth i v x‖ ≥ ‖x‖` for the sup norm on finite products. -/
lemma norm_insertNth_ge_norm {m : ℕ} (i : Fin (m + 1)) (v : ℝ) (x : Fin m → ℝ) :
    ‖x‖ ≤ ‖(Fin.insertNth i v x : Fin (m + 1) → ℝ)‖ := by
  show Finset.univ.sup (fun b : Fin m => ‖(x : Fin m → ℝ) b‖₊) ≤
       Finset.univ.sup (fun b : Fin (m + 1) => ‖(Fin.insertNth i v x : Fin (m + 1) → ℝ) b‖₊)
  exact Finset.sup_le fun j _ => by
    have h_val : (Fin.insertNth i v x : Fin (m + 1) → ℝ) (Fin.succAbove i j) = x j := by simp
    rw [← h_val]
    exact NNReal.coe_le_coe.mp
      (norm_le_pi_norm (Fin.insertNth i v x : Fin (m + 1) → ℝ) (Fin.succAbove i j))

/-- `‖Fin.insertNth i v x‖ ≥ |v|`. -/
lemma norm_insertNth_ge {m : ℕ} (i : Fin (m + 1)) (v : ℝ) (x : Fin m → ℝ) :
    |v| ≤ ‖(Fin.insertNth i v x : Fin (m + 1) → ℝ)‖ := by
  have hval : (Fin.insertNth i v x : Fin (m + 1) → ℝ) i = v := by simp
  have hnorm : ‖((Fin.insertNth i v x : Fin (m + 1) → ℝ) i : ℝ)‖ ≤
      ‖(Fin.insertNth i v x : Fin (m + 1) → ℝ)‖ :=
    norm_le_pi_norm _ i
  rw [hval, Real.norm_eq_abs v] at hnorm
  exact hnorm

/-! ## Form Field Vanishing -/

/-- A form field that vanishes when `‖y‖ ≥ Rω` also vanishes at `insertNth i v x` when `‖x‖ ≥ Rω`. -/
lemma formField_vanishes_at_insertNth_norm {m : ℕ}
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    {Rω : ℝ} (hRω : ∀ y, Rω ≤ ‖y‖ → ω y = 0)
    (i : Fin (m + 1)) (v : ℝ) (x : Fin m → ℝ)
    (hx : Rω ≤ ‖x‖) :
    ω (Fin.insertNth i v x) = 0 :=
  hRω _ (le_trans hx (norm_insertNth_ge_norm i v x))

/-- A form field that vanishes when `‖y‖ ≥ Rω` also vanishes at `insertNth i v x` when `|v| ≥ Rω`. -/
lemma formField_vanishes_at_insertNth {m : ℕ}
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    {Rω : ℝ} (hRω : ∀ y, Rω ≤ ‖y‖ → ω y = 0)
    (i : Fin (m + 1)) (v : ℝ) (x : Fin m → ℝ)
    (hv : Rω ≤ |v|) :
    ω (Fin.insertNth i v x) = 0 :=
  hRω _ (le_trans hv (norm_insertNth_ge i v x))

/-- If `ω x = 0`, then `boxFaceComponent ω i x = 0`. -/
lemma boxFaceComponent_eq_zero_of_formField_eq_zero {m : ℕ}
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    (i : Fin (m + 1)) (x : Fin (m + 1) → ℝ)
    (h : ω x = 0) :
    boxFaceComponent ω i x = 0 := by
  unfold boxFaceComponent; simp [h]

/-! ## Compact Support Lemmas -/

/-- A function with compact support vanishes outside a large enough ball. -/
lemma exists_norm_bound_of_compact_support {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) :
    ∃ R₀ : ℝ, ∀ x : Fin n → ℝ, R₀ ≤ ‖x‖ → f x = 0 := by
  have h_norm_comp : IsCompact ((fun x : Fin n → ℝ => ‖x‖) '' tsupport f) :=
    hf.image continuous_norm
  have h_bdd : BddAbove ((fun x => ‖x‖) '' tsupport f) := h_norm_comp.bddAbove
  obtain ⟨C, hC⟩ := h_bdd
  use C + 1
  intro x hx
  have hnx : x ∉ tsupport f := fun hmem => by
    have : ‖x‖ ≤ C := hC ⟨x, hmem, rfl⟩
    linarith
  contrapose! hnx
  exact subset_tsupport f (by simpa using hnx)

/-- A compactly supported form field vanishes outside a large ball. -/
lemma exists_norm_bound_of_hasCompactSupport_form {m : ℕ}
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    (hω : HasCompactSupport ω) :
    ∃ R₀ : ℝ, ∀ x : Fin (m + 1) → ℝ, R₀ ≤ ‖x‖ → ω x = 0 :=
  exists_norm_bound_of_compact_support (fun x => ω x (Fin.removeNth (lastCoord m)
    (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ))) <| by
    refine HasCompactSupport.mono ?_ (fun x hx => by dsimp at hx; exact hx)
    exact hω.comp isClosedEmbedding_finInsertNth_of_succ _

/-! ## Top-Form Density Properties -/

/-- The top-form density vanishes where `extDeriv ω x = 0`. -/
lemma topFormDensity_eq_zero_of_extDeriv_eq_zero {m : ℕ}
    {ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ}
    {x : Fin (m + 1) → ℝ} (h : extDeriv ω x = 0) :
    topFormDensity (extDeriv ω) x = 0 := by
  simp only [topFormDensity, h, toTopFormFun_zero]

/-- The topFormDensity of dω has compact support when ω is C¹ with compact support. -/
lemma hasCompactSupport_topFormDensity_extDeriv {m : ℕ}
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    (hω : ContDiff ℝ (1 : ℕ∞) ω)
    (hω_support : HasCompactSupport ω) :
    HasCompactSupport (topFormDensity (extDeriv ω)) := by
  obtain ⟨R, hR⟩ := exists_norm_bound_of_hasCompactSupport_form ω hω_support
  have h_density_vanishes : ∀ x : Fin (m + 1) → ℝ, R < ‖x‖ →
      topFormDensity (extDeriv ω) x = 0 := by
    intro x hx
    have hω_zero_near : ∀ᶠ y in 𝓝 x, ω y = 0 := by
      have : {y : Fin (m + 1) → ℝ | R < ‖y‖} ∈ 𝓝 x :=
        (isOpen_lt continuous_const continuous_norm).mem_nhds hx
      filter_upwards [this] with y hy
      exact hR y (le_of_lt hy)
    have h_fderiv : fderiv ℝ ω x = 0 :=
      (hasFDerivAt_zero_of_eventually_const 0
        (hω_zero_near.mono fun y hy => hy)).fderiv
    have h_ext : extDeriv ω x = 0 := by
      unfold extDeriv; rw [h_fderiv]; exact _root_.map_zero (alternatizeUncurryFinCLM ℝ _ _)
    rw [topFormDensity, h_ext, toTopFormFun_zero]
  have h_sub : Function.support (topFormDensity (extDeriv ω)) ⊆
      Metric.closedBall (0 : Fin (m + 1) → ℝ) R := by
    intro x hx
    simp only [Function.mem_support, Metric.mem_closedBall, dist_zero_right] at *
    exact le_of_not_gt (fun h => hx (h_density_vanishes x h))
  have h_compact : IsCompact (Metric.closedBall (0 : Fin (m + 1) → ℝ) R) :=
    isCompact_closedBall 0 R
  have h_closed_ball : IsClosed (Metric.closedBall (0 : Fin (m + 1) → ℝ) R) :=
    h_compact.isClosed
  exact IsCompact.of_isClosed_subset h_compact isClosed_closure
    (closure_minimal h_sub h_closed_ball)

/-! ## Set Integral Reduction -/

/-- If `f = 0` on `t \ s` and `s ⊆ t`, both measurable, then `∫_t f = ∫_s f`. -/
lemma setIntegral_eq_of_zero_on_diff {n : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    {s t : Set (Fin n → ℝ)}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hsub : s ⊆ t)
    (hzero : ∀ x ∈ t \ s, f x = 0)
    (hf : IntegrableOn f t) :
    ∫ x in t, f x = ∫ x in s, f x := by
  have hst : t = s ∪ (t \ s) := (union_diff_cancel hsub).symm
  have h_disj : Disjoint s (t \ s) := Disjoint.symm disjoint_sdiff_self_left
  have h_meas_diff : MeasurableSet (t \ s) := ht.diff hs
  have hf_s : IntegrableOn f s := hf.mono_set hsub
  have hf_diff : IntegrableOn f (t \ s) := hf.mono_set (fun _ hx => hx.1)
  have h_zero_integral : ∫ x in t \ s, f x = 0 := by
    rw [setIntegral_congr_fun h_meas_diff (fun x hx => hzero x hx)]
    simp
  rw [hst, setIntegral_union h_disj h_meas_diff hf_s hf_diff]
  rw [h_zero_integral]
  simp

/-! ## Half-Space Box Properties -/

/-- The half-space box is contained in the half-space. -/
lemma halfSpaceBox_subset_halfSpace {m : ℕ} {R : ℝ} (hR : (0 : ℝ) ≤ R) :
    Icc (halfSpaceBoxLower m R) (halfSpaceBoxUpper m R) ⊆ HalfSpace m := by
  intro x hx
  rw [mem_Icc] at hx
  have := hx.1 (lastCoord m)
  simp only [halfSpaceBoxLower_last] at this
  simp [HalfSpace, this]

/-- HalfSpace is a measurable set. -/
lemma measurableSet_halfSpace (m : ℕ) : MeasurableSet (HalfSpace m) := by
  simp only [HalfSpace, mem_setOf_eq]
  exact measurableSet_le measurable_const (measurable_pi_apply (lastCoord m))

/-- For large R, the topFormDensity of dω vanishes outside the half-space box. -/
lemma topFormDensity_extDeriv_vanishes_outside_box {m : ℕ}
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    (hω : ContDiff ℝ (1 : ℕ∞) ω)
    (hω_support : HasCompactSupport ω) (R : ℝ) (hR : (0 : ℝ) < R)
    (hR_large : ∀ x : Fin (m + 1) → ℝ, R ≤ ‖x‖ → topFormDensity (extDeriv ω) x = 0) :
    ∀ x ∈ HalfSpace m \ Icc (halfSpaceBoxLower m R) (halfSpaceBoxUpper m R),
      topFormDensity (extDeriv ω) x = 0 := by
  intro x hx
  rw [Set.mem_diff] at hx
  obtain ⟨hx_hs, hx_box⟩ := hx
  rw [mem_Icc, not_and_or] at hx_box
  rcases hx_box with hx_low | hx_high
  · simp only [Pi.le_def, not_forall] at hx_low
    obtain ⟨i, hi⟩ := hx_low
    by_cases heq : i = lastCoord m
    · exfalso
      have h0 : halfSpaceBoxLower m R i = (0 : ℝ) := heq ▸ halfSpaceBoxLower_last m R
      rw [h0] at hi
      have hge : (0 : ℝ) ≤ x i := heq ▸ (by simp [HalfSpace] at hx_hs; exact hx_hs)
      exact hi hge
    · have hlow : halfSpaceBoxLower m R i = -(R : ℝ) := by
        simp [halfSpaceBoxLower, heq, if_neg (Ne.symm heq)]
      rw [hlow] at hi
      push_neg at hi
      have habs : R < |x i| := by
        rw [abs_of_neg (by linarith : (0 : ℝ) > x i)]; linarith
      exact hR_large x (le_of_lt (lt_of_lt_of_le habs (norm_le_pi_norm x i)))
  · simp only [Pi.le_def, not_forall] at hx_high
    obtain ⟨i, hi⟩ := hx_high
    have hxi : (R : ℝ) < x i := by simpa [halfSpaceBoxUpper_apply] using hi
    have habs : R < |x i| := lt_of_lt_of_le hxi (le_abs_self (x i))
    exact hR_large x (le_of_lt (lt_of_lt_of_le habs (norm_le_pi_norm x i)))

/-! ## Face Vanishing -/

/-- A face integral vanishes when the face value v satisfies `|v| ≥ Rω`. -/
lemma faceIntegral_eq_zero_of_large_v {m : ℕ}
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    (Rω : ℝ) (hRω : ∀ y, Rω ≤ ‖y‖ → ω y = 0)
    (a b : Fin (m + 1) → ℝ) (i : Fin (m + 1)) (v : ℝ)
    (hv : Rω ≤ |v|) :
    (∫ x : Fin m → ℝ in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
        boxFaceComponent ω i (Fin.insertNth i v x)) = 0 := by
  have hzero (x : Fin m → ℝ) :
      boxFaceComponent ω i (Fin.insertNth i v x) = 0 :=
    boxFaceComponent_eq_zero_of_formField_eq_zero ω i _
      (formField_vanishes_at_insertNth ω hRω i v x hv)
  rw [show (∫ x : Fin m → ℝ in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i),
        boxFaceComponent ω i (Fin.insertNth i v x)) =
      (∫ x : Fin m → ℝ in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i), (0 : ℝ)) by
    congr 1 with x : 1; exact hzero x]
  simp

/-! ## Main Theorem -/

/-- **Stokes' theorem on the half-space** for compactly supported `C¹` `m`-forms.

For `ω` a compactly supported `C¹` `m`-form on `ℝ^{m+1}`:

```
∫_{x_m ≥ 0} dω = ∫_{x_m = 0} ω
```

**Proof:**
1. The density `f = topFormDensity (extDeriv ω)` has compact support.
2. Pick `R₀` large so `f = 0` outside the half-space box.
3. `∫_{HalfSpace} f = ∫_{Icc} f` (since `Icc ⊆ HalfSpace` and `f = 0` on `HalfSpace \ Icc`).
4. `box_stokes_of_contDiff` gives `∫_{Icc} f = boxBoundaryIntegral ω lower upper`.
5. For `i ≠ lastCoord m`: both front and back vanish (compact support, values at `±R`).
6. For `i = lastCoord m`: front at `x_m = R` vanishes; back at `x_m = 0` equals `boundaryIntegral`. -/
theorem halfSpace_stokes (m : ℕ)
    (ω : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) [⋀^Fin m]→L[ℝ] ℝ)
    (hω : ContDiff ℝ (1 : ℕ∞) ω)
    (hω_support : HasCompactSupport ω) :
    ∫ x in HalfSpace m, topFormDensity (extDeriv ω) x =
      boundaryIntegral m ω := by
  -- Step 1: Compact support of the density
  have hf_comp : HasCompactSupport (topFormDensity (extDeriv ω)) :=
    hasCompactSupport_topFormDensity_extDeriv ω hω hω_support
  -- Step 2: Norm bounds for both density and ω
  obtain ⟨R₀, hR₀⟩ := exists_norm_bound_of_compact_support _ hf_comp
  obtain ⟨Rω, hRω⟩ := exists_norm_bound_of_hasCompactSupport_form ω hω_support
  -- Step 3: Use R large enough for both
  let R := max (max R₀ Rω) 1
  have hR₀_le : R₀ ≤ R := le_trans (le_max_left R₀ Rω) (le_max_left (max R₀ Rω) 1)
  have hRω_le : Rω ≤ R := le_trans (le_max_right R₀ Rω) (le_max_left (max R₀ Rω) 1)
  have hR_pos : (0 : ℝ) < R := lt_of_lt_of_le (by positivity : (0 : ℝ) < 1)
    (le_max_right (max R₀ Rω) 1)
  have hR_nneg : (0 : ℝ) ≤ R := le_of_lt hR_pos
  -- Step 4: Density vanishes outside the half-space box
  have hf_vanishes : ∀ x ∈ HalfSpace m \ Icc (halfSpaceBoxLower m R) (halfSpaceBoxUpper m R),
      topFormDensity (extDeriv ω) x = 0 :=
    topFormDensity_extDeriv_vanishes_outside_box ω hω hω_support R hR_pos
      (fun x hx => hR₀ x (le_trans hR₀_le hx))
  -- Step 5: ∫_{HalfSpace} f = ∫_{Icc} f
  have h_box_subset : Icc (halfSpaceBoxLower m R) (halfSpaceBoxUpper m R) ⊆ HalfSpace m :=
    halfSpaceBox_subset_halfSpace hR_nneg
  have h_meas_hs : MeasurableSet (HalfSpace m) := measurableSet_halfSpace m
  have h_meas_box : MeasurableSet (Icc (halfSpaceBoxLower m R) (halfSpaceBoxUpper m R)) :=
    measurableSet_Icc
  -- Integrability of the density
  have hf_cont : Continuous (topFormDensity (extDeriv ω)) := by
    have h_diff : ∀ x, DifferentiableAt ℝ ω x :=
      fun x => (hω.differentiable one_ne_zero).differentiableAt
    refine (continuous_finset_sum _ fun i _ => by
      have hface : ContDiff ℝ (1 : ℕ∞) (boxFaceComponent ω i) :=
        boxFaceComponent_contDiff ω i hω
      exact (hface.continuous_fderiv_apply one_ne_zero).comp
        (continuous_id.prodMk continuous_const)).congr
        (fun x => (topFormDensity_extDeriv_eq_boxFaceComponent_divergence ω (h_diff x)).symm)
  have hf_int : Integrable (topFormDensity (extDeriv ω)) :=
    hf_cont.integrable_of_hasCompactSupport hf_comp
  have hf_int_hs : IntegrableOn (topFormDensity (extDeriv ω)) (HalfSpace m) :=
    hf_int.integrableOn
  -- ∫_{HalfSpace} = ∫_{Icc}
  have h_hs_eq_box : ∫ x in HalfSpace m, topFormDensity (extDeriv ω) x =
      ∫ x in Icc (halfSpaceBoxLower m R) (halfSpaceBoxUpper m R),
        topFormDensity (extDeriv ω) x :=
    setIntegral_eq_of_zero_on_diff _ h_meas_box h_meas_hs h_box_subset hf_vanishes hf_int_hs
  -- Step 6: Apply box_stokes
  have h_box_stokes : topFormIntegral (extDeriv ω)
      (Icc (halfSpaceBoxLower m R) (halfSpaceBoxUpper m R)) =
      boxBoundaryIntegral ω (halfSpaceBoxLower m R) (halfSpaceBoxUpper m R) :=
    box_stokes_of_contDiff ω (halfSpaceBoxLower m R) (halfSpaceBoxUpper m R)
      (halfSpaceBoxLower_le_upper m hR_nneg) hω
  -- Step 7: boxBoundaryIntegral = boundaryIntegral
  calc ∫ x in HalfSpace m, topFormDensity (extDeriv ω) x
      = ∫ x in Icc (halfSpaceBoxLower m R) (halfSpaceBoxUpper m R),
          topFormDensity (extDeriv ω) x := h_hs_eq_box
    _ = boxBoundaryIntegral ω (halfSpaceBoxLower m R) (halfSpaceBoxUpper m R) :=
        h_box_stokes
    _ = boundaryIntegral m ω := by
      unfold boxBoundaryIntegral
      rw [Finset.sum_eq_single (lastCoord m)
        (fun i _ hne => by
          -- For i ≠ lastCoord m: both front and back vanish
          have hfront := faceIntegral_eq_zero_of_large_v ω Rω hRω
            (halfSpaceBoxLower m R) (halfSpaceBoxUpper m R) i (halfSpaceBoxUpper m R i)
            (le_trans hRω_le (le_of_eq (abs_of_pos hR_pos).symm))
          have hlow : halfSpaceBoxLower m R i = -(R : ℝ) := by
            unfold halfSpaceBoxLower; split_ifs with h
            · exact absurd h hne
            · rfl
          have hback := faceIntegral_eq_zero_of_large_v ω Rω hRω
            (halfSpaceBoxLower m R) (halfSpaceBoxUpper m R) i (-(R : ℝ))
            (by rw [abs_neg]; exact le_trans hRω_le (le_of_eq (abs_of_pos hR_pos).symm))
          rw [hfront, show halfSpaceBoxLower m R i = -(R : ℝ) from hlow, hback]; ring)
        (fun h => absurd (Finset.mem_univ (lastCoord m)) h)]
      -- Now just the (lastCoord m) term: front - back
      -- front = 0 (compact support at R)
      have hfront := faceIntegral_eq_zero_of_large_v ω Rω hRω
        (halfSpaceBoxLower m R) (halfSpaceBoxUpper m R) (lastCoord m)
        (halfSpaceBoxUpper m R (lastCoord m))
        (le_trans hRω_le (le_of_eq (abs_of_pos hR_pos).symm))
      rw [hfront]
      simp only [halfSpaceBoxLower_last]
      unfold boundaryIntegral boundaryInclusion
      simp only [zero_sub]
      rw [show halfSpaceBoxLower m R ∘ Fin.succAbove (lastCoord m) = fun _ => -(R : ℝ) from
        funext fun i => halfSpaceBoxLower_succAbove m R i]
      rw [show halfSpaceBoxUpper m R ∘ Fin.succAbove (lastCoord m) = fun _ => (R : ℝ) from rfl]
      congr 1
      -- ∫_{Icc(-R,R)^m} f = ∫ f (f vanishes outside Icc)
      have h_meas : MeasurableSet (Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ)) : Set (Fin m → ℝ)) :=
        measurableSet_Icc
      have h_vanish : ∀ x : Fin m → ℝ,
          x ∈ (Set.univ \ Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ))) →
          boxFaceComponent ω (lastCoord m) ((lastCoord m).insertNth (0 : ℝ) x) = 0 := by
        intro x hx
        simp only [Set.mem_diff, Set.mem_univ, true_and, Set.mem_Icc, Pi.le_def,
          not_and_or, not_le] at hx
        have h_norm_gt : R < ‖x‖ := by
          simp only [not_forall, not_and_or, not_le] at hx
          obtain ⟨i, hi⟩ | ⟨i, hi⟩ := hx
          · calc R < -(x i) := by linarith
              _ = |x i| := (abs_of_neg (by linarith : x i < 0)).symm
              _ ≤ ‖x‖ := norm_le_pi_norm x i
          · have hi_pos : 0 < x i := lt_trans hR_pos hi
            calc R < x i := hi
              _ = |x i| := (abs_of_pos hi_pos).symm
              _ ≤ ‖x‖ := norm_le_pi_norm x i
        have h_omega_norm : Rω ≤ ‖x‖ := le_trans hRω_le (le_of_lt h_norm_gt)
        exact boxFaceComponent_eq_zero_of_formField_eq_zero ω (lastCoord m) _
          (formField_vanishes_at_insertNth_norm ω hRω (lastCoord m) (0 : ℝ) x h_omega_norm)
      -- Integrability on univ
      have h_f_cont : Continuous fun x : Fin m → ℝ =>
          boxFaceComponent ω (lastCoord m) ((lastCoord m).insertNth (0 : ℝ) x) := by
        have h_comp := (boxFaceComponent_contDiff ω (lastCoord m) hω).continuous
        exact h_comp.comp (continuous_const.finInsertNth continuous_id)
      have h_f_compact : HasCompactSupport fun x : Fin m → ℝ =>
          boxFaceComponent ω (lastCoord m) ((lastCoord m).insertNth (0 : ℝ) x) := by
        refine HasCompactSupport.intro (K := Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ))) ?_ ?_
        · exact isCompact_Icc
        · intro x hx; exact h_vanish x (by simpa using hx)
      have h_f_int : Integrable (fun x : Fin m → ℝ =>
          boxFaceComponent ω (lastCoord m) ((lastCoord m).insertNth (0 : ℝ) x)) :=
        h_f_cont.integrable_of_hasCompactSupport h_f_compact
      have h_f_int_univ : IntegrableOn (fun x : Fin m → ℝ =>
          boxFaceComponent ω (lastCoord m) ((lastCoord m).insertNth (0 : ℝ) x))
          Set.univ := h_f_int.integrableOn
      have h_eq : ∫ (x : Fin m → ℝ) in Set.univ,
          boxFaceComponent ω (lastCoord m) ((lastCoord m).insertNth (0 : ℝ) x) =
          ∫ (x : Fin m → ℝ) in Icc (fun _ => -(R : ℝ)) (fun _ => (R : ℝ)),
          boxFaceComponent ω (lastCoord m) ((lastCoord m).insertNth (0 : ℝ) x) :=
        setIntegral_eq_of_zero_on_diff _ h_meas MeasurableSet.univ (Set.subset_univ _) h_vanish
          h_f_int_univ
      rw [h_eq.symm, setIntegral_univ]

end DifferentialForm
