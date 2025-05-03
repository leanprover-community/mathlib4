import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Translation actions on modular forms

We show that if `f` is a slash-invariant form, modular form, or cusp form of level `Γ`, then its
translate by `g ∈ SL(2, ℤ)` is a slash-invariant form (resp. modular form, cusp form) of level
`g⁻¹ Γ g`.

## Main definitions and statements

* `SlashInvariantForm.translate`
* `ModularFormClass.translate`
* `CuspFormClass.translate`

## TO DO

Generalize this to `g ∈ GL(2, ℚ)⁺`, showing that the translate is a modular form of level
`SL(2, ℤ) ∩ g⁻¹ Γ g`. (This is somewhat subtle, because of the bounded-at-infinity condition.)
-/

open scoped MatrixGroups ModularForm UpperHalfPlane Manifold

/-- Translating a `SlashInvariantForm` by `SL(2, ℤ)`, to obtain a new `SlashInvariantForm`. -/
noncomputable def SlashInvariantForm.translate
    {k : ℤ} {Γ : Subgroup SL(2, ℤ)} (f : SlashInvariantForm Γ k) (g : SL(2, ℤ)) :
    SlashInvariantForm (Γ.map <| MulAut.conj g⁻¹) k where
  toFun := f ∣[k] g
  slash_action_eq' j hj := by
    obtain ⟨r, hr, hr'⟩ := hj
    simp only [map_inv, MonoidHom.coe_coe, MulAut.conj_inv_apply] at hr'
    rw [← hr', ← SlashAction.slash_mul, mul_assoc, mul_inv_cancel_left, SlashAction.slash_mul,
      SlashInvariantFormClass.slash_action_eq f r hr]

@[simp]
lemma SlashInvariantForm.coe_translate
    {k : ℤ} {Γ : Subgroup SL(2, ℤ)} (f : SlashInvariantForm Γ k) (g : SL(2, ℤ)) :
    ⇑(f.translate g) = (⇑f) ∣[k] g := rfl

lemma UpperHalfPlane.mdifferentiable_num (g : GL(2, ℝ)⁺) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (num g) :=
  (mdifferentiable_coe.const_smul _).add mdifferentiable_const

lemma UpperHalfPlane.mdifferentiable_denom (g : GL(2, ℝ)⁺) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (denom g) :=
  (mdifferentiable_coe.const_smul _).add mdifferentiable_const

lemma UpperHalfPlane.mdifferentiable_denom_zpow (g : GL(2, ℝ)⁺) (k : ℤ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (denom g · ^ k) := fun τ ↦ by
  have := (differentiableAt_zpow (m := k)).mpr (Or.inl <| denom_ne_zero g τ)
  exact this.mdifferentiableAt.comp τ (mdifferentiable_denom g τ)

lemma UpperHalfPlane.mdifferentiable_inv_denom (g : GL(2, ℝ)⁺) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ ↦ (denom g τ)⁻¹) := by
  simpa using mdifferentiable_denom_zpow g (-1)

/-- Each element of `GL(2, ℝ)⁺` defines a continuous map `ℍ → ℍ`. -/
instance UpperHalfPlane.instContinuousGLPosSMul : ContinuousConstSMul GL(2, ℝ)⁺ ℍ where
  continuous_const_smul g := by
    refine continuous_induced_rng.mpr ?_
    refine continuous_iff_continuousAt.mpr fun τ ↦ .div ?_ ?_ (τ.denom_ne_zero g)
    · exact (mdifferentiable_num g τ).continuousAt
    · exact (mdifferentiable_denom g τ).continuousAt

/-- Each element of `GL(2, ℝ)⁺` defines a complex-differentiable map `ℍ → ℍ`. -/
lemma UpperHalfPlane.mdifferentiable_smul (g : GL(2, ℝ)⁺) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ ↦ g • τ) := fun τ ↦ by
  refine mdifferentiableAt_iff_target.mpr ⟨(continuous_const_smul g).continuousAt, ?_⟩
  simpa [smulAux, Function.comp_def] using
    (mdifferentiable_num g τ).mul (mdifferentiable_inv_denom g τ)

/-- Translating a `ModularForm` by `SL(2, ℤ)`, to obtain a new `ModularForm`. -/
noncomputable def ModularFormClass.translate {k : ℤ} {Γ : Subgroup SL(2, ℤ)}
    {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f : F) (g : SL(2, ℤ)) :
    ModularForm (Γ.map <| MulAut.conj g⁻¹) k where
  __ := SlashInvariantForm.translate f g
  bdd_at_infty' h := by simpa [SlashAction.slash_mul] using bdd_at_infty f (g * h)
  holo' := by
    simp only [SlashInvariantForm.coe_translate, SlashInvariantForm.coe_mk, ModularForm.SL_slash,
      ModularForm.slash_def]
    refine .mul (.mul ?_ mdifferentiable_const) (UpperHalfPlane.mdifferentiable_denom_zpow g _)
    exact (holo f).comp (UpperHalfPlane.mdifferentiable_smul g)

@[simp]
lemma ModularFormClass.coe_translate {k : ℤ} {Γ : Subgroup SL(2, ℤ)} {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ k] (f : F) (g : SL(2, ℤ)) :
    ⇑(ModularFormClass.translate f g) = (⇑f) ∣[k] g := rfl

/-- Translating a `CuspForm` by `SL(2, ℤ)`, to obtain a new `CuspForm`. -/
noncomputable def CuspFormClass.translate {k : ℤ} {Γ : Subgroup SL(2, ℤ)}
    {F : Type*} [FunLike F ℍ ℂ] [CuspFormClass F Γ k] (f : F) (g : SL(2, ℤ)) :
    CuspForm (Γ.map <| MulAut.conj g⁻¹) k where
  __ := ModularFormClass.translate f g
  zero_at_infty' h := by simpa [SlashAction.slash_mul] using zero_at_infty f (g * h)

@[simp]
lemma CuspFormClass.coe_translate {k : ℤ} {Γ : Subgroup SL(2, ℤ)} {F : Type*} [FunLike F ℍ ℂ]
    [CuspFormClass F Γ k] (f : F) (g : SL(2, ℤ)) :
    ⇑(CuspFormClass.translate f g) = (⇑f) ∣[k] g := rfl
