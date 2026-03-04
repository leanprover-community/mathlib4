module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable

open UpperHalfPlane hiding I
open Real Complex
open scoped Manifold

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
  (h : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F z) : DifferentiableAt ℂ (F ∘ ofComplex) ↑z := by
  have h₁ : DifferentiableWithinAt ℂ (F ∘ ofComplex) Set.univ ↑z :=
    by simpa [writtenInExtChartAt, extChartAt, Set.range_id] using
      MDifferentiableWithinAt.differentiableWithinAt_writtenInExtChartAt h
  exact differentiableWithinAt_univ.1 h₁

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
  simp only [D, Pi.add_apply]
  rw [show (F + G) ∘ ofComplex = F ∘ ofComplex + G ∘ ofComplex from rfl,
    deriv_add (MDifferentiableAt_DifferentiableAt (hF z))
      (MDifferentiableAt_DifferentiableAt (hG z)), mul_add]

theorem D_sub (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    : D (F - G) = D F - D G := by
  ext z
  simp only [D, Pi.sub_apply]
  rw [show (F - G) ∘ ofComplex = F ∘ ofComplex - G ∘ ofComplex from rfl,
    deriv_sub (MDifferentiableAt_DifferentiableAt (hF z))
      (MDifferentiableAt_DifferentiableAt (hG z)), mul_sub]

theorem D_smul (c : ℂ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    : D (c • F) = c • D F := by
  ext z
  simp only [D, Pi.smul_apply, smul_eq_mul]
  rw [show (c • F) ∘ ofComplex = c • (F ∘ ofComplex) from rfl,
    deriv_const_smul c (MDifferentiableAt_DifferentiableAt (hF z)), smul_eq_mul]
  ring

theorem D_mul (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    : D (F * G) = D F * G + F * D G := by
  ext z
  simp only [D, Pi.add_apply, Pi.mul_apply]
  rw [show (F * G) ∘ ofComplex = (F ∘ ofComplex) * (G ∘ ofComplex) from rfl,
    deriv_mul (MDifferentiableAt_DifferentiableAt (hF z))
      (MDifferentiableAt_DifferentiableAt (hG z))]
  simp [Function.comp_apply, ofComplex_apply]
  ring

theorem D_sq (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    D (F ^ 2) = 2 * F * D F := by
  rw [sq, D_mul F F hF hF]
  ext z
  simp only [Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply]
  ring

theorem D_const (c : ℂ) (z : ℍ) : D (Function.const _ c) z = 0 := by
  change (2 * π * I)⁻¹ * deriv (fun _ : ℂ => c) (z : ℂ) = 0
  simp [deriv_const]


/--
Serre derivative of weight $k$.
-/
noncomputable def SerreD (k : ℂ) (F : ℍ → ℂ) : ℍ → ℂ :=
  fun z => D F z - k * 12⁻¹ * EisensteinSeries.E2 z * F z

@[simp]
lemma SerreD_apply (k : ℂ) (F : ℍ → ℂ) (z : ℍ) :
    SerreD k F z = D F z - k * 12⁻¹ * EisensteinSeries.E2 z * F z := rfl

lemma SerreD_eq (k : ℂ) (F : ℍ → ℂ) :
    SerreD k F = fun z => D F z - k * 12⁻¹ * EisensteinSeries.E2 z * F z := rfl

/--
Basic properties of Serre derivative.
-/
theorem SerreD_add (k : ℂ) (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) : SerreD k (F + G) = SerreD k F + SerreD k G := by
  ext z
  simp [SerreD, D_add F G hF hG]
  ring_nf

theorem SerreD_sub (k : ℂ) (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) : SerreD k (F - G) = SerreD k F - SerreD k G := by
  ext z
  simp [SerreD, D_sub F G hF hG]
  ring_nf

theorem SerreD_smul (k : ℂ) (c : ℂ) (F : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    SerreD k (c • F) = c • (SerreD k F) := by
  ext z
  simp [SerreD, D_smul c F hF, smul_eq_mul]
  ring_nf

theorem SerreD_mul (k₁ k₂ : ℂ) (F G : ℍ → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) :
    SerreD (k₁ + k₂) (F * G) = (SerreD k₁ F) * G + F * (SerreD k₂ G) := by
  ext z
  simp [SerreD, D_mul F G hF hG]
  ring_nf

/--
The Serre derivative preserves MDifferentiability.
If `F : ℍ → ℂ` is MDifferentiable, then `SerreD k F` is also MDifferentiable.
-/
theorem SerreD_differentiable {F : ℍ → ℂ} (k : ℂ)
    (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (SerreD k F) := by
  refine (D_differentiable hF).sub ?_
  convert
    (MDifferentiable.mul mdifferentiable_const (E2_mdifferentiable.mul hF) :
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
        (fun z => (k * 12⁻¹) * (EisensteinSeries.E2 z * F z)))
  simp [Pi.mul_apply, mul_assoc, mul_left_comm, mul_comm]
