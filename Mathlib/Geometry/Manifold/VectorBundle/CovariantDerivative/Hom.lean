/-
Copyright (c) 2026 Michał Pacholski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Pacholski
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Induced Hom-bundle covariant derivative

Given two fiber bundles `V₁` and `V₂` endowed with covariant derivatives, we define the induced
covariant derivative acting on a section `ϕ` of the Hom-bundle `Hom(V₁, V₂)`, such that is satisfies
the Leibnitz rule:

`(∇_X ϕ) v = ∇_X (ϕ v) - ϕ ∇_X v`,

where `v` is a section of `V₁`.

## Main definitions

* `CovariantDerivative.homBundle`: globally defined covariant derivative on the Hom-bundle,
  as a bundled object.
-/

open Bundle
open scoped Manifold

public noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

-- Base manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

-- First fiber bundle
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module 𝕜 (V₁ x)]
  [∀ x : M, TopologicalSpace (V₁ x)]
  [∀ x, IsTopologicalAddGroup (V₁ x)] [∀ x, ContinuousSMul 𝕜 (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁]

-- Second fiber bundle
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)]
  [∀ x : M, TopologicalSpace (V₂ x)]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul 𝕜 (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]

namespace IsCovariantDerivativeOn

-- Unbundled covariant derivatives on the two fiber bundles
variable
  (cov₁ : ((x : M) → V₁ x) → (x : M) → TangentSpace I x →L[𝕜] V₁ x)
  (cov₂ : ((x : M) → V₂ x) → (x : M) → TangentSpace I x →L[𝕜] V₂ x)

variable {s : Set M} {ϕ : (x : M) → V₁ x →L[𝕜] V₂ x}

/-- The induced covariant derivative acting on a section `ϕ` of a Hom bundle `Hom(V₁, V₂)`
as a bare function. -/
private def homBundleAux (ϕ : (x : M) → V₁ x →L[𝕜] V₂ x) (x : M) :
    TangentSpace I x → ((y : M) → V₁ y) → V₂ x := fun X v ↦
  cov₂ (fun y ↦ (ϕ y (v y))) x X - ϕ x (cov₁ v x X)

variable {cov₁ cov₂}

private theorem homBundleAux_tensorial
    (hcov₁ : IsCovariantDerivativeOn F₁ cov₁ s) (hcov₂ : IsCovariantDerivativeOn F₂ cov₂ s)
    (x : M) (hϕ : MDiffAt T% ϕ x) (X : TangentSpace I x)
    (hx : x ∈ s := by trivial) :
    TensorialAt I F₁ (homBundleAux cov₁ cov₂ ϕ x X) x where
  smul hf hv := by
    simp [homBundleAux, ← Pi.smul_def', hcov₁.leibniz hv hf, hcov₂.leibniz
      (MDifferentiableAt.clm_bundle_apply hϕ hv) hf, smul_sub]
  add hv hv' := by
    rename_i hϕ _ _
    simp [homBundleAux, ← Pi.add_def, hcov₂.add
      (MDifferentiableAt.clm_bundle_apply hϕ hv) (MDifferentiableAt.clm_bundle_apply hϕ hv'),
      hcov₁.add hv hv']
    abel

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [ContMDiffVectorBundle 1 F₁ V₁ I]

open Classical in
/--
The induced covariant derivative on the Hom-bundle `Hom(V₁, V₂)` evaluated at a single point `x`.

For a section `ϕ` that is differentiable at `x`, this returns a continuous linear map from the
tangent space to `V₁ x →L[𝕜] V₂ x`, mapping a tangent vector `X` to `∇_X ϕ`.
If `ϕ` is not differentiable at `x`, it returns `0` as a junk value.
-/
def homBundleAt
    (hcov₁ : IsCovariantDerivativeOn F₁ cov₁ s) (hcov₂ : IsCovariantDerivativeOn F₂ cov₂ s)
    (ϕ : (x : M) → V₁ x →L[𝕜] V₂ x) (x : M) :
    TangentSpace I x →L[𝕜] V₁ x →L[𝕜] V₂ x where
  toFun X :=
    if hϕ : MDiffAt (T% ϕ) x then
      if hx : x ∈ s then
        TensorialAt.mkHom
          (homBundleAux cov₁ cov₂ ϕ x X) x (homBundleAux_tensorial hcov₁ hcov₂ x hϕ X)
      else 0
    else 0
  map_add' X X' := by
    split_ifs
    · ext
      simp [TensorialAt.mkHom_apply_eq_extend, homBundleAux]
      abel
    · simp only [add_zero]
    · simp only [add_zero]
  map_smul' m X := by
    split_ifs
    · ext
      simp [TensorialAt.mkHom_apply_eq_extend, homBundleAux, smul_sub]
    · simp only [RingHom.id_apply, smul_zero]
    · simp only [RingHom.id_apply, smul_zero]
  cont := by
    split_ifs
    · let e₁ := VectorBundle.continuousLinearEquivAt 𝕜 F₁ V₁ x
      let e₂ := VectorBundle.continuousLinearEquivAt 𝕜 F₂ V₂ x
      apply (e₁.arrowCongrSL e₂).toHomeomorph.comp_continuous_iff.mp
      apply continuous_clm_apply.mpr
      intro v
      simp only [ContinuousLinearEquiv.coe_toHomeomorph, Function.comp_apply,
        ContinuousLinearEquiv.arrowCongrSL_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, TensorialAt.mkHom_apply_eq_extend, homBundleAux, map_sub]
      fun_prop
    · exact continuous_const
    · exact continuous_const

theorem homBundleAt_apply
    (hcov₁ : IsCovariantDerivativeOn F₁ cov₁ s) (hcov₂ : IsCovariantDerivativeOn F₂ cov₂ s)
    {ϕ : (x : M) → V₁ x →L[𝕜] V₂ x}
    {x : M} (hϕ : MDiffAt (T% ϕ) x)
    {v : (x : M) → V₁ x} (hv : MDiffAt (T% v) x)
    (X : TangentSpace I x) (hx : x ∈ s := by trivial) :
    (hcov₁.homBundleAt hcov₂) ϕ x X (v x) = cov₂ (fun y ↦ (ϕ y (v y))) x X - ϕ x (cov₁ v x X) := by
  simp [homBundleAt, dite_eq_left hϕ, dite_eq_left hx,
    (homBundleAux_tensorial hcov₁ hcov₂ x hϕ X hx).mkHom_apply hv, homBundleAux]

theorem homBundleAt_apply_eq_extend
    (hcov₁ : IsCovariantDerivativeOn F₁ cov₁ s) (hcov₂ : IsCovariantDerivativeOn F₂ cov₂ s)
    {ϕ : (x : M) → V₁ x →L[𝕜] V₂ x}
    {x : M} (hϕ : MDiffAt (T% ϕ) x)
    {v : V₁ x}
    (X : TangentSpace I x) (hx : x ∈ s := by trivial) :
    (hcov₁.homBundleAt hcov₂) ϕ x X v = (cov₂ (fun y ↦ (ϕ y) (FiberBundle.extend F₁ v y)) x) X
      - (ϕ x) ((cov₁ (FiberBundle.extend F₁ v) x) X) := by
  simp [homBundleAt, dite_eq_left hϕ, dite_eq_left hx,
    (homBundleAux_tensorial hcov₁ hcov₂ x hϕ X hx).mkHom_apply_eq_extend, homBundleAux]

/--
The proposition that the induced covariant derivative on a Hom-bundle `Hom(V₁, V₂)`,
defined through the Leibniz rule, locally satisfies the properties of a covariant derivative.
-/
theorem homBundle
    (hcov₁ : IsCovariantDerivativeOn F₁ cov₁ s) (hcov₂ : IsCovariantDerivativeOn F₂ cov₂ s) :
    IsCovariantDerivativeOn (F₁ →L[𝕜] F₂) (hcov₁.homBundleAt hcov₂) s where
  add  := by
    intro ϕ ϕ' x hϕ hϕ' hx
    ext X v
    simp [homBundleAt]
    have h_add : (MDiffAt fun x ↦ (⟨x, ϕ x + ϕ' x⟩ :
      TotalSpace (F₁ →L[𝕜] F₂) fun x ↦ V₁ x →L[𝕜] V₂ x)) x:=
      mdifferentiableAt_add_section hϕ hϕ'
    simp [dite_eq_left hϕ, dite_eq_left hϕ', dite_eq_left h_add, dite_eq_left hx]
    simp [TensorialAt.mkHom_apply_eq_extend, homBundleAux]
    simp [← Pi.add_def]
    simp [hcov₂.add
        (MDifferentiableAt.clm_bundle_apply hϕ (FiberBundle.mdifferentiableAt_extend I F₁ v))
        (MDifferentiableAt.clm_bundle_apply hϕ' (FiberBundle.mdifferentiableAt_extend I F₁ v)),
      add_apply]
    abel
  leibniz := by
    intro ϕ g x hϕ hg hx
    ext X v
    simp [homBundleAt]
    have h_smul : (MDiffAt fun x ↦ (⟨x, g x • ϕ x⟩ :
      TotalSpace (F₁ →L[𝕜] F₂) fun x ↦ V₁ x →L[𝕜] V₂ x
    )) x := MDifferentiableAt.smul_section hg hϕ
    simp [dite_eq_left hϕ, dite_eq_left h_smul]
    simp [TensorialAt.mkHom_apply_eq_extend, homBundleAux, dite_eq_left hx]
    simp [← Pi.smul_def']
    simp [hcov₂.leibniz
      (MDifferentiableAt.clm_bundle_apply hϕ (FiberBundle.mdifferentiableAt_extend I F₁ v)) hg]
    simp [smul_sub]
    abel

end IsCovariantDerivativeOn

namespace CovariantDerivative

-- Global covariant derivatives on the two fiber bundles as bundled objects
variable (cov₁ : CovariantDerivative I F₁ V₁) (cov₂ : CovariantDerivative I F₂ V₂)

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [ContMDiffVectorBundle 1 F₁ V₁ I]

/--
The global induced covariant derivative on a Hom-bundle `Hom(V₁, V₂)` as a bundled object.

When acting at point `x` on a section `ϕ` that is not differentiable at that point, it returns
a junk value.
-/
def homBundle :
    CovariantDerivative I (F₁ →L[𝕜] F₂) (fun x ↦ V₁ x →L[𝕜] V₂ x) where
  toFun ϕ x := cov₁.isCovariantDerivativeOnUniv.homBundleAt cov₂.isCovariantDerivativeOnUniv ϕ x
  isCovariantDerivativeOnUniv := IsCovariantDerivativeOn.homBundle cov₁.isCovariantDerivativeOnUniv
        cov₂.isCovariantDerivativeOnUniv

theorem homBundle_apply
    {ϕ : (x : M) → V₁ x →L[𝕜] V₂ x}
    {x : M} (hϕ : MDiffAt (T% ϕ) x)
    {v : (x : M) → V₁ x} (hv : MDiffAt (T% v) x)
    (X : TangentSpace I x) :
    (cov₁.homBundle cov₂) ϕ x X (v x) = cov₂ (fun y ↦ (ϕ y (v y))) x X - ϕ x (cov₁ v x X) := by
  simp [homBundle,
    cov₁.isCovariantDerivativeOnUniv.homBundleAt_apply cov₂.isCovariantDerivativeOnUniv hϕ hv]


theorem homBundle_apply_eq_extend
    {ϕ : (x : M) → V₁ x →L[𝕜] V₂ x}
    {x : M} (hϕ : MDiffAt (T% ϕ) x)
    {v : V₁ x}
    (X : TangentSpace I x) :
    (cov₁.homBundle cov₂) ϕ x X v = (cov₂ (fun y ↦ (ϕ y) (FiberBundle.extend F₁ v y)) x) X
      - (ϕ x) ((cov₁ (FiberBundle.extend F₁ v) x) X) := by
  simp [homBundle, cov₁.isCovariantDerivativeOnUniv.homBundleAt_apply_eq_extend
    cov₂.isCovariantDerivativeOnUniv hϕ]

end CovariantDerivative
