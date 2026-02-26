module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.NumberTheory.ModularForms.Identities
public import Mathlib.RingTheory.PowerSeries.Basic


open UpperHalfPlane hiding I
open Real Complex ContinuousMap Metric Filter Function
open scoped MatrixGroups Topology BigOperators Manifold

@[expose] public noncomputable section

/-!
Definition of (Serre) derivative of modular forms.
-/
noncomputable def D (F : ℍ → ℂ) : ℍ → ℂ :=
  fun (z : ℍ) => (2 * π * I)⁻¹ * ((deriv (F ∘ ofComplex)) z)

/--
`MDifferentiableAt` on `ℍ` implies `DifferentiableAt` on `ℂ`.
-/
lemma MDifferentiableAt_DifferentiableAt {F : ℍ → ℂ} {z : ℍ}
  (h : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F z) :
  DifferentiableAt ℂ (F ∘ ofComplex) ↑z := by
  have h₁ : DifferentiableWithinAt ℂ (F ∘ ofComplex) Set.univ ↑z :=
    by simpa [writtenInExtChartAt, extChartAt, Set.range_id] using
      MDifferentiableWithinAt.differentiableWithinAt_writtenInExtChartAt h
  exact (differentiableWithinAt_univ.1 h₁)

/--
`DifferentiableAt` on `ℂ` implies `MDifferentiableAt` on `ℍ`.
-/
lemma DifferentiableAt_MDifferentiableAt {G : ℂ → ℂ} {z : ℍ}
    (h : DifferentiableAt ℂ G ↑z) : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (G ∘ (↑) : ℍ → ℂ) z := by
  rw [mdifferentiableAt_iff]
  apply DifferentiableAt.congr_of_eventuallyEq h
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw]

/--
The derivative operator `D` preserves MDifferentiability.
If `F : ℍ → ℂ` is MDifferentiable, then `D F` is also MDifferentiable.
-/
theorem D_differentiable {F : ℍ → ℂ} (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (D F) := fun z =>
  let hDiffOn : DifferentiableOn ℂ (F ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    fun w hw => (MDifferentiableAt_DifferentiableAt (hF ⟨w, hw⟩)).differentiableWithinAt
  MDifferentiableAt.mul mdifferentiableAt_const <| DifferentiableAt_MDifferentiableAt <|
    (hDiffOn.deriv isOpen_upperHalfPlaneSet).differentiableAt
      (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)

/--
Basic properties of derivatives: linearity, Leibniz rule, etc.
-/
theorem D_add (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) :
    D (F + G) = D F + D G := by
  ext z
  change (2 * π * I)⁻¹ * deriv ((F + G) ∘ ofComplex) z =
    (2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z + (2 * π * I)⁻¹ * deriv (G ∘ ofComplex) z
  rw [show ((F + G) ∘ ofComplex) = (F ∘ ofComplex) + (G ∘ ofComplex) by rfl]
  rw [deriv_add (MDifferentiableAt_DifferentiableAt (hF z))
    (MDifferentiableAt_DifferentiableAt (hG z)), mul_add]

theorem D_sub (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    : D (F - G) = D F - D G := by
  ext z
  change (2 * π * I)⁻¹ * deriv ((F - G) ∘ ofComplex) z =
    (2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z - (2 * π * I)⁻¹ * deriv (G ∘ ofComplex) z
  rw [show ((F - G) ∘ ofComplex) = (F ∘ ofComplex) - (G ∘ ofComplex) by rfl]
  rw [deriv_sub (MDifferentiableAt_DifferentiableAt (hF z))
    (MDifferentiableAt_DifferentiableAt (hG z)), mul_sub]

theorem D_smul (c : ℂ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    : D (c • F) = c • D F := by
  ext z
  change (2 * π * I)⁻¹ * deriv (c • (F ∘ ofComplex)) z =
    c * ((2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z)
  rw [deriv_const_smul c (MDifferentiableAt_DifferentiableAt (hF z)), smul_eq_mul]
  ring_nf

theorem D_mul (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    : D (F * G) = D F * G + F * D G := by
  ext z
  change (2 * π * I)⁻¹ * deriv ((F * G) ∘ ofComplex) z =
    ((2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z) * G z +
      F z * ((2 * π * I)⁻¹ * deriv (G ∘ ofComplex) z)
  rw [show ((F * G) ∘ ofComplex) = (F ∘ ofComplex) * (G ∘ ofComplex) by rfl]
  rw [deriv_mul (MDifferentiableAt_DifferentiableAt (hF z))
    (MDifferentiableAt_DifferentiableAt (hG z))]
  simp [Function.comp_apply, ofComplex_apply]
  ring_nf

theorem D_sq (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    D (F ^ 2) = 2 * F * D F := by
  ext z
  rw [pow_two]
  have h := congrArg (fun f : ℍ → ℂ => f z) (D_mul F F hF hF)
  have h' : D (F * F) z = D F z * F z + F z * D F z := by
    simpa [Pi.add_apply, Pi.mul_apply] using h
  rw [h']
  change D F z * F z + F z * D F z = (2 : ℂ) * F z * D F z
  ring_nf

theorem D_const (c : ℂ) (z : ℍ) : D (Function.const _ c) z = 0 := by
  change (2 * π * I)⁻¹ * deriv (fun _ : ℂ => c) (z : ℂ) = 0
  simp [deriv_const]


/--
Serre derivative of weight $k$.
Note that the definition makes sense for any analytic function $F : \mathbb{H} \to \mathbb{C}$.
-/
noncomputable def serre_D (k : ℂ) : (ℍ → ℂ) → (ℍ → ℂ) :=
  fun (F : ℍ → ℂ) => (fun z => D F z - k * 12⁻¹ * EisensteinSeries.E2 z * F z)

@[simp]
lemma serre_D_apply (k : ℂ) (F : ℍ → ℂ) (z : ℍ) :
    serre_D k F z = D F z - k * 12⁻¹ * EisensteinSeries.E2 z * F z := rfl

lemma serre_D_eq (k : ℂ) (F : ℍ → ℂ) :
    serre_D k F = fun z => D F z - k * 12⁻¹ * EisensteinSeries.E2 z * F z := rfl

/--
Basic properties of Serre derivative: linearity, Leibniz rule, etc.
-/
theorem serre_D_add (k : ℤ) (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) : serre_D k (F + G) = serre_D k F + serre_D k G := by
  ext z
  simp [serre_D, D_add F G hF hG]
  ring_nf

theorem serre_D_sub (k : ℤ) (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) : serre_D k (F - G) = serre_D k F - serre_D k G := by
  ext z
  simp [serre_D, D_sub F G hF hG]
  ring_nf

theorem serre_D_smul (k : ℤ) (c : ℂ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    serre_D k (c • F) = c • (serre_D k F) := by
  ext z
  simp [serre_D, D_smul c F hF, smul_eq_mul]
  ring_nf

theorem serre_D_mul (k₁ k₂ : ℤ) (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) :
    serre_D (k₁ + k₂) (F * G) = (serre_D k₁ F) * G + F * (serre_D k₂ G) := by
  ext z
  simp [serre_D, D_mul F G hF hG]
  ring_nf

private lemma mdifferentiable_E2 :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) EisensteinSeries.E2 := by
  have hlog : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      ((logDeriv ModularForm.eta) ∘ (↑) : ℍ → ℂ) :=
    fun z => DifferentiableAt_MDifferentiableAt (ModularForm.differentiableAt_logDeriv_eta z)
  have hEq : (fun z : ℍ => logDeriv ModularForm.eta (z : ℂ)) =
      fun z : ℍ => (π * I / 12 : ℂ) * EisensteinSeries.E2 z := by
    ext z
    simpa using (ModularForm.logDeriv_eta_eq_E2 z)
  have hscaled : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun z : ℍ => (π * I / 12 : ℂ) * EisensteinSeries.E2 z) := by
    simpa [Function.comp_def] using hEq ▸ hlog
  have hpi : (π * I / 12 : ℂ) ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) I_ne_zero) (by norm_num)
  have hE2' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun z : ℍ => (π * I / 12 : ℂ)⁻¹ * ((π * I / 12 : ℂ) * EisensteinSeries.E2 z)) :=
    MDifferentiable.mul mdifferentiable_const hscaled
  convert hE2' using 1 with z
  field_simp [hpi]

/--
The Serre derivative preserves MDifferentiability.
If `F : ℍ → ℂ` is MDifferentiable, then `serre_D k F` is also MDifferentiable.
-/
theorem serre_D_differentiable {F : ℍ → ℂ} {k : ℂ}
    (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (serre_D k F) := by
  refine (D_differentiable hF).sub ?_
  convert
    (MDifferentiable.mul mdifferentiable_const (mdifferentiable_E2.mul hF) :
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
        (fun z => (k * 12⁻¹) * (EisensteinSeries.E2 z * F z)))
  simp [Pi.mul_apply, mul_assoc, mul_left_comm, mul_comm]
