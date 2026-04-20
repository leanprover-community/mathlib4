/-
Copyright (c) 2026 Michal Swietek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Swietek
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

/-!
# Signed measure, density, and duality of `Lp` spaces

Given a finite measure `μ` and `p ∈ [1, ∞)`, every bounded linear functional
`φ : StrongDual ℝ (Lp ℝ p μ)` induces a signed measure `φ.toSignedMeasure hp` on `α`,
defined on measurable sets `s` by `φ (indicatorConstLp p hs _ 1)`.

For a scalar field `𝕜` (any `RCLike`), a bounded linear functional
`φ : StrongDual 𝕜 (Lp 𝕜 p μ)` splits via `RCLike.re` / `RCLike.im` into two real-valued
functionals on `Lp ℝ p μ` (by precomposition with `Lp.ofReal`); the Radon–Nikodym derivatives
of their signed measures combine into a scalar density `φ.density hp : α → 𝕜`.

Specializing to `p = 1` and a finite measure, the density lives in `L^∞` and represents `φ`
via integration, yielding the isometric linear equivalence
`Lp 𝕜 ∞ μ ≃ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 1 μ)`. A representation theorem for `p > 1` is planned
as a follow-up.

## Main declarations

* `ContinuousLinearMap.toSignedMeasure`: the signed measure associated to a bounded
  real-valued functional on `Lp ℝ p μ`.
* `ContinuousLinearMap.toSignedMeasure_apply`: its value on a measurable set.
* `ContinuousLinearMap.toSignedMeasure_absolutelyContinuous`: absolute continuity
  w.r.t. `μ` as an `ℝ≥0∞`-valued vector measure.
* `ContinuousLinearMap.density`: the Radon–Nikodym density of a scalar-valued bounded
  linear functional, obtained by recombining the real and imaginary parts.
* `MeasureTheory.Lp.lInftyToL1Dualₗᵢ`: the natural pairing `g f ↦ ∫ x, g x * f x ∂μ` packaged
  as an isometric `𝕜`-linear embedding `Lp 𝕜 ∞ μ →ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 1 μ)`.
* `MeasureTheory.Lp.lInftyEquivL1Dual`: for a finite measure `μ`, the above embedding is an
  isometric linear equivalence `Lp 𝕜 ∞ μ ≃ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 1 μ)`.

## References

* Rudin, *Real and Complex Analysis*, Theorem 6.16.
-/

@[expose] public section

open ENNReal Filter MeasureTheory NNReal Topology

noncomputable section

namespace ContinuousLinearMap

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

open Classical in
/-- The signed measure associated to a bounded linear functional on `Lp ℝ p μ` for a finite
measure `μ` and `p ≠ ∞`. On a measurable set `s`, its value is
`φ (indicatorConstLp p hs _ 1)`. -/
noncomputable def toSignedMeasure
    (φ : StrongDual ℝ (Lp ℝ p μ)) (hp : p ≠ ∞) : SignedMeasure α where
  measureOf' s := if hs : MeasurableSet s
    then φ (indicatorConstLp p hs (measure_ne_top μ s) (1 : ℝ))
    else 0
  empty' := by simp
  not_measurable' _ hs := dif_neg hs
  m_iUnion' f hf hdisj := by
    simp only [dif_pos (hf _), dif_pos (MeasurableSet.iUnion hf)]
    exact (hasSum_indicatorConstLp_disjoint hp hf hdisj _).map φ φ.continuous

lemma toSignedMeasure_apply (φ : StrongDual ℝ (Lp ℝ p μ)) (hp : p ≠ ∞) {s : Set α}
    (hs : MeasurableSet s) :
    φ.toSignedMeasure hp s = φ (indicatorConstLp p hs (measure_ne_top μ s) (1 : ℝ)) :=
  dif_pos hs

/-- The signed measure from a bounded functional is absolutely continuous w.r.t. the underlying
measure. -/
lemma toSignedMeasure_absolutelyContinuous (φ : StrongDual ℝ (Lp ℝ p μ)) (hp : p ≠ ∞) :
    φ.toSignedMeasure hp ≪ᵥ μ.toENNRealVectorMeasure :=
  VectorMeasure.AbsolutelyContinuous.mk fun s hs_meas hs_null ↦ by
    rw [Measure.toENNRealVectorMeasure_apply_measurable hs_meas] at hs_null
    rw [φ.toSignedMeasure_apply hp hs_meas, ← map_zero φ,
      ← indicatorConstLp_empty (p := p) (c := (1 : ℝ)) (μ := μ),
      (indicatorConstLp_inj hs_meas (measure_ne_top μ s) .empty (by simp) one_ne_zero).mpr
        (ae_eq_empty.mpr hs_null)]

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The Radon–Nikodym density of a bounded linear functional on `Lp 𝕜 p μ` (for a finite measure
`μ` and `p ≠ ∞`), constructed by recombining the RN-derivatives of the signed measures
associated to its real and imaginary parts. -/
noncomputable def density (φ : StrongDual 𝕜 (Lp 𝕜 p μ)) (hp : p ≠ ∞) : α → 𝕜 :=
  fun x ↦ (algebraMap ℝ 𝕜)
      (((φ.reFunctional.comp (Lp.ofReal 𝕜 p μ)).toSignedMeasure hp).rnDeriv μ x) +
    RCLike.I * (algebraMap ℝ 𝕜)
      (((φ.imFunctional.comp (Lp.ofReal 𝕜 p μ)).toSignedMeasure hp).rnDeriv μ x)

/-- Key identity: for a scalar functional `φ` on `Lp 𝕜 p μ` with `p ≠ ∞` and a measurable set
`s`, `φ` applied to the scalar unit indicator of `s` equals the set integral of `φ.density hp`
over `s`. -/
lemma apply_indicator_one_eq_setIntegral_density
    (φ : StrongDual 𝕜 (Lp 𝕜 p μ)) (hp : p ≠ ∞) {s : Set α} (hs : MeasurableSet s) :
    φ (indicatorConstLp p hs (measure_ne_top μ s) (1 : 𝕜)) =
      ∫ x in s, φ.density hp x ∂μ := by
  set ofRe := Lp.ofReal 𝕜 p μ
  set reF := φ.reFunctional.comp ofRe
  set imF := φ.imFunctional.comp ofRe
  set d_re := (reF.toSignedMeasure hp).rnDeriv μ
  set d_im := (imF.toSignedMeasure hp).rnDeriv μ
  set z := φ (indicatorConstLp p hs (measure_ne_top μ s) (1 : 𝕜))
  have h_int_re : Integrable d_re μ := SignedMeasure.integrable_rnDeriv _ _
  have h_int_im : Integrable d_im μ := SignedMeasure.integrable_rnDeriv _ _
  -- Via ψ ↦ ∫_s rnDeriv ψ.toSignedMeasure μ = ψ(1_s): ∫_s d_re = re z, ∫_s d_im = im z.
  have aux (ψ : StrongDual ℝ (Lp ℝ p μ))
      (h_int : Integrable ((ψ.toSignedMeasure hp).rnDeriv μ) μ) :
      ∫ x in s, (ψ.toSignedMeasure hp).rnDeriv μ x ∂μ =
        ψ (indicatorConstLp p hs (measure_ne_top μ s) (1 : ℝ)) := by
    rw [← withDensityᵥ_apply h_int hs, SignedMeasure.withDensityᵥ_rnDeriv_eq _ _
      (ψ.toSignedMeasure_absolutelyContinuous hp),
      ψ.toSignedMeasure_apply hp hs]
  have h_re : ∫ x in s, d_re x ∂μ = RCLike.re z := (aux _ h_int_re).trans <| by
    simp [reF, ofRe, Lp.ofReal_indicatorConstLp, z]
  have h_im : ∫ x in s, d_im x ∂μ = RCLike.im z := (aux _ h_int_im).trans <| by
    simp [imF, ofRe, Lp.ofReal_indicatorConstLp, z]
  -- Unfold density as `ofReal d_re + I * ofReal d_im` under ∫, then combine using re_add_im.
  have h1 : Integrable (fun x ↦ (d_re x : 𝕜)) μ := h_int_re.ofReal
  have h2 : Integrable (fun x ↦ (d_im x : 𝕜)) μ := h_int_im.ofReal
  have : ∫ x in s, φ.density hp x ∂μ =
      ((∫ x in s, d_re x ∂μ : ℝ) : 𝕜) + RCLike.I * ((∫ x in s, d_im x ∂μ : ℝ) : 𝕜) := by
    change ∫ x in s, ((d_re x : 𝕜) + RCLike.I * (d_im x : 𝕜)) ∂μ = _
    rw [integral_add h1.integrableOn (h2.const_mul RCLike.I).integrableOn,
      integral_const_mul, integral_ofReal, integral_ofReal]
  rw [this, h_re, h_im, mul_comm, RCLike.re_add_im]

end ContinuousLinearMap

namespace MeasureTheory

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
  {𝕜 : Type*} [RCLike 𝕜]

namespace Lp

/-- The bilinear `Lp 𝕜 ∞ μ × Lp 𝕜 1 μ → 𝕜` pairing given by pointwise multiplication. -/
noncomputable abbrev lInftyL1Pairing (μ : Measure α) : Lp 𝕜 ∞ μ →L[𝕜] Lp 𝕜 1 μ →L[𝕜] 𝕜 :=
  (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ ∞ 1

/-! ### The isometry lower bound (scalar case) -/

section IsometryLowerBound

variable [IsFiniteMeasure μ]

/-- The lower bound for the L∞-L¹ pairing. -/
lemma norm_le_norm_lpPairing_mul_apply (g : Lp 𝕜 ∞ μ) : ‖g‖ ≤ ‖lInftyL1Pairing μ g‖ := by
  let P := lInftyL1Pairing (𝕜 := 𝕜) μ
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  by_cases hg : ε < ‖g‖
  swap
  · linarith [norm_nonneg (P g), not_lt.mp hg]
  let c : ℝ := ‖g‖ - ε
  have hc_nn : 0 ≤ c := by linarith
  have hc_lt : c < ‖g‖ := by linarith
  have hg_ae : AEStronglyMeasurable (g : α → 𝕜) μ := (Lp.memLp g).1
  let g₀ : α → 𝕜 := hg_ae.mk _
  have hg₀_sm : StronglyMeasurable g₀ := hg_ae.stronglyMeasurable_mk
  have hg_eq : (g : α → 𝕜) =ᵐ[μ] g₀ := hg_ae.ae_eq_mk
  let S : Set α := {x | c < ‖g₀ x‖}
  have hS_meas : MeasurableSet S := measurableSet_lt measurable_const hg₀_sm.measurable.norm
  have hS_pos : μ S ≠ 0 := by
    rw [← measure_congr (hg_eq.mono fun x hx ↦ by
      change (c < ‖(g : α → 𝕜) x‖) = (c < ‖g₀ x‖); rw [hx])]
    exact measure_norm_gt_pos_of_lt_norm hc_nn hc_lt
  set r : ℝ := μ.real S with hr
  have hr_pos : 0 < r := ENNReal.toReal_pos hS_pos (measure_lt_top μ S).ne
  let ψ : α → 𝕜 := S.indicator fun y ↦ star (g₀ y) / (‖g₀ y‖ : 𝕜)
  have hψ_meas : StronglyMeasurable ψ :=
    ((continuous_star.measurable.div (RCLike.continuous_ofReal.comp
      continuous_norm).measurable).comp hg₀_sm.measurable).stronglyMeasurable.indicator hS_meas
  have hψ_bound (x) : ‖ψ x‖ ≤ S.indicator (fun _ ↦ (1 : ℝ)) x := by
    simp only [ψ, Set.indicator]
    split_ifs <;> simp [norm_div, div_self_le_one]
  have hψ_int : Integrable ψ μ := .of_bound hψ_meas.aestronglyMeasurable 1 <| ae_of_all μ fun x ↦
    (hψ_bound x).trans <| Set.indicator_le_self' (fun _ _ ↦ zero_le_one) x
  let ψ_Lp : Lp 𝕜 1 μ := hψ_int.toL1 ψ
  have hψ_Lp_eq : (ψ_Lp : α → 𝕜) =ᵐ[μ] ψ := Integrable.coeFn_toL1 hψ_int
  have hψ_Lp_norm : ‖ψ_Lp‖ ≤ r := by
    rw [hr, L1.norm_of_fun_eq_integral_norm, ← integral_indicator_one hS_meas]
    exact integral_mono_ae hψ_int.norm ((integrable_indicator_iff hS_meas).mpr
      (integrable_const (1 : ℝ)).integrableOn) (ae_of_all μ hψ_bound)
  have hg₀_int_S : IntegrableOn (fun x ↦ ‖g₀ x‖) S μ :=
    ((integrable_const ‖g‖).mono' hg₀_sm.measurable.norm.aestronglyMeasurable
      ((ae_norm_le_norm g).mp (hg_eq.mono fun _ hxg hx ↦ by
        rwa [Real.norm_eq_abs, abs_norm, ← hxg]))).integrableOn
  have h_pairing : P g ψ_Lp = ((∫ x in S, ‖g₀ x‖ ∂μ : ℝ) : 𝕜) := by
    rw [ContinuousLinearMap.lpPairing_eq_integral,
      integral_congr_ae (g := S.indicator (fun y ↦ (‖g₀ y‖ : 𝕜))) ?_,
      integral_indicator hS_meas, integral_ofReal]
    filter_upwards [hg_eq, hψ_Lp_eq] with x hx hψx
    simp only [hx, hψx, ψ, Set.indicator]
    split_ifs <;> simp [ContinuousLinearMap.mul_apply', RCLike.star_def, ← mul_div_assoc,
      RCLike.mul_conj, sq, mul_self_div_self]
  have h_mul : c * r ≤ ‖P g‖ * r :=
    calc c * r
        = ∫ _ in S, c ∂μ := by rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ x in S, ‖g₀ x‖ ∂μ := setIntegral_mono_on (integrable_const c).integrableOn
          hg₀_int_S hS_meas fun _ hx ↦ hx.le
      _ = ‖P g ψ_Lp‖ := by rw [h_pairing, RCLike.norm_ofReal,
            abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
      _ ≤ ‖P g‖ * ‖ψ_Lp‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖P g‖ * r := mul_le_mul_of_nonneg_left hψ_Lp_norm (norm_nonneg _)
  linarith [le_of_mul_le_mul_right h_mul hr_pos]

/-- The natural pairing `g f ↦ ∫ x, g x * f x ∂μ` between `Lp 𝕜 ∞ μ` and `Lp 𝕜 1 μ`, packaged
as an isometric `𝕜`-linear embedding into the strong dual of `Lp 𝕜 1 μ` (for finite `μ`). -/
def lInftyToL1Dualₗᵢ : Lp 𝕜 ∞ μ →ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 1 μ) where
  toLinearMap := (lInftyL1Pairing μ).toLinearMap
  norm_map' g := le_antisymm
    ((ContinuousLinearMap.norm_lpPairing_apply_le _ g).trans <|
      mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜))
    (norm_le_norm_lpPairing_mul_apply g)

@[simp]
lemma lInftyToL1Dualₗᵢ_apply_apply (g : Lp 𝕜 ∞ μ) (f : Lp 𝕜 1 μ) :
    lInftyToL1Dualₗᵢ g f = ∫ x, g x * f x ∂μ := by
  simp [lInftyToL1Dualₗᵢ, ContinuousLinearMap.lpPairing_eq_integral]

end IsometryLowerBound

/-! ### Surjectivity via Radon–Nikodym

For a finite measure `μ`, every bounded linear functional on `L¹(μ; 𝕜)` is given by integration
against an `L∞(μ; 𝕜)` function. The proof decomposes a complex scalar functional into real and
imaginary parts (via `ContinuousLinearMap.reFunctional`, `ContinuousLinearMap.imFunctional`,
precomposed with `Lp.ofReal`), applies the signed-measure Radon–Nikodym to each, and recombines
into `ContinuousLinearMap.density`. -/

section Surjectivity

variable [IsFiniteMeasure μ]

/-- For a bounded real-valued functional on `L¹(μ; ℝ)` and finite `μ`, the Radon–Nikodym
derivative of its associated signed measure is essentially bounded by the operator norm. -/
private lemma ae_abs_rnDeriv_toSignedMeasure_le_opNorm
    (ψ : StrongDual ℝ (Lp ℝ 1 μ)) :
    ∀ᵐ x ∂μ, |(ψ.toSignedMeasure one_ne_top).rnDeriv μ x| ≤ ‖ψ‖ := by
  set d := (ψ.toSignedMeasure one_ne_top).rnDeriv μ
  have h_int : Integrable d μ := SignedMeasure.integrable_rnDeriv _ _
  have h_abs_bound {s : Set α} (hs : MeasurableSet s) :
      |∫ x in s, d x ∂μ| ≤ ‖ψ‖ * μ.real s := by
    rw [← withDensityᵥ_apply h_int hs,
      SignedMeasure.withDensityᵥ_rnDeriv_eq _ _ (ψ.toSignedMeasure_absolutelyContinuous one_ne_top),
      ψ.toSignedMeasure_apply one_ne_top hs, ← Real.norm_eq_abs]
    exact (ψ.le_opNorm _).trans_eq <| by simp [norm_indicatorConstLp]
  have h_le : d ≤ᵐ[μ] fun _ ↦ ‖ψ‖ :=
    ae_le_of_forall_setIntegral_le h_int (integrable_const _) fun s hs _ ↦ by
      rw [setIntegral_const, smul_eq_mul, mul_comm]; exact (le_abs_self _).trans (h_abs_bound hs)
  have h_ge : (fun _ ↦ -‖ψ‖) ≤ᵐ[μ] d :=
    ae_le_of_forall_setIntegral_le (integrable_const _).neg h_int fun s hs _ ↦ by
      rw [setIntegral_const, smul_eq_mul]; linarith [neg_le_of_abs_le (h_abs_bound hs)]
  filter_upwards [h_le, h_ge] with x hle hge using abs_le.mpr ⟨hge, hle⟩

/-- The density function is essentially bounded (lives in `L∞`) at `p = 1`. -/
lemma _root_.ContinuousLinearMap.density_memLp_top
    (φ : StrongDual 𝕜 (Lp 𝕜 1 μ)) : MemLp (φ.density one_ne_top) ∞ μ :=
  let ofRe := Lp.ofReal 𝕜 1 μ
  let h (ψ : StrongDual ℝ (Lp ℝ 1 μ)) : MemLp ((ψ.toSignedMeasure one_ne_top).rnDeriv μ) ∞ μ :=
    memLp_top_of_bound (SignedMeasure.integrable_rnDeriv _ _).aestronglyMeasurable ‖ψ‖ <|
      (ae_abs_rnDeriv_toSignedMeasure_le_opNorm ψ).mono fun _ hx ↦ Real.norm_eq_abs _ ▸ hx
  ((h (φ.reFunctional.comp ofRe)).ofReal (K := 𝕜)).add
    ((h (φ.imFunctional.comp ofRe)).ofReal (K := 𝕜) |>.const_mul RCLike.I)

/-- Representation theorem: every bounded linear functional on `L¹(μ; 𝕜)` for a finite measure
`μ` is given by integration against its density. -/
lemma _root_.ContinuousLinearMap.apply_eq_integral_mul_density
    (φ : StrongDual 𝕜 (Lp 𝕜 1 μ)) (f : Lp 𝕜 1 μ) :
    φ f = ∫ x, f x * φ.density one_ne_top x ∂μ := by
  set F : Lp 𝕜 1 μ →L[𝕜] 𝕜 :=
    lInftyL1Pairing μ φ.density_memLp_top.toLp
  have h_F (g : Lp 𝕜 1 μ) : F g = ∫ x, g x * φ.density one_ne_top x ∂μ := by
    rw [show F g = _ from ContinuousLinearMap.lpPairing_eq_integral ..]
    exact integral_congr_ae <| (MemLp.coeFn_toLp φ.density_memLp_top).mono fun x hx ↦ by
      simp [ContinuousLinearMap.mul_apply', hx, mul_comm]
  rw [← h_F]
  -- Show `φ = F` as CLMs on `Lp 𝕜 1 μ` by `Lp.induction`.
  refine Lp.induction one_ne_top (fun g ↦ φ g = F g) ?_ ?_ ?_ f
  · intro c s hs hμs
    -- Reduce indicator_c to c • indicator_1 via `MemLp.toLp_const_smul`, apply linearity.
    have h_smul : (indicatorConstLp (μ := μ) (E := 𝕜) 1 hs hμs.ne c : Lp 𝕜 1 μ) =
        c • indicatorConstLp 1 hs hμs.ne (1 : 𝕜) := by
      simp_rw [indicatorConstLp, ← MemLp.toLp_const_smul]
      congr 1; ext x; simp [Set.indicator]
    rw [Lp.simpleFunc.coe_indicatorConst, h_smul, map_smul, map_smul]
    congr 1
    rw [φ.apply_indicator_one_eq_setIntegral_density one_ne_top hs, h_F,
      ← integral_indicator hs]
    refine integral_congr_ae ?_
    filter_upwards [indicatorConstLp_coeFn (μ := μ) (E := 𝕜) (p := 1) (hs := hs)
      (hμs := hμs.ne) (c := (1 : 𝕜))] with x hx
    rw [hx]; by_cases hxs : x ∈ s <;> simp [hxs]
  · intro f g _ _ _ ihf ihg
    rw [map_add, ihf, ihg, F.map_add]
  · exact isClosed_eq φ.continuous F.continuous

lemma lInftyToL1Dualₗᵢ_surjective :
    Function.Surjective (lInftyToL1Dualₗᵢ : Lp 𝕜 ∞ μ → StrongDual 𝕜 (Lp 𝕜 1 μ)) := fun φ ↦ by
  refine ⟨φ.density_memLp_top.toLp, ContinuousLinearMap.ext fun f ↦ ?_⟩
  rw [lInftyToL1Dualₗᵢ_apply_apply, φ.apply_eq_integral_mul_density f]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp φ.density_memLp_top] with x hx using by rw [hx, mul_comm]

end Surjectivity

/-! ### The final `L^∞ ≃ (L¹)*` isomorphism -/

section DualEquiv

variable [IsFiniteMeasure μ]

/-- **Duality of `L¹` and `L^∞` for finite measures.** For a finite measure `μ` and scalar field
`𝕜` (either `ℝ` or `ℂ`), the space `Lp 𝕜 ∞ μ` is isometrically isomorphic to the strong dual of
`Lp 𝕜 1 μ` via the pairing `(g, f) ↦ ∫ x, g x * f x ∂μ`. -/
noncomputable def lInftyEquivL1Dual :
    Lp 𝕜 ∞ μ ≃ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 1 μ) :=
  LinearIsometryEquiv.ofSurjective lInftyToL1Dualₗᵢ lInftyToL1Dualₗᵢ_surjective

@[simp]
lemma lInftyEquivL1Dual_apply_apply (g : Lp 𝕜 ∞ μ) (f : Lp 𝕜 1 μ) :
    lInftyEquivL1Dual g f = ∫ x, g x * f x ∂μ :=
  lInftyToL1Dualₗᵢ_apply_apply g f

end DualEquiv

end Lp

end MeasureTheory
