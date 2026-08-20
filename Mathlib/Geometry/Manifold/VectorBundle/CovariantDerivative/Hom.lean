/-
Copyright (c) 2026 Michał Pacholski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Pacholski
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-! # The induced connection on a Hom-bundle

Given covariant derivatives `cov₁` on a vector bundle `V₁` and `cov₂` on a vector bundle `V₂`
over the same manifold `M`, we build the induced covariant derivative on the bundle
`Hom(V₁, V₂)`, characterized by the Leibniz rule

`(∇_X σ)(s) = ∇₂_X (σ s) - σ (∇₁_X s)`.

## Main definitions and results

*

-/

public noncomputable section

open Bundle Filter Topology

open scoped Manifold ContDiff

section HomBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-! ### Vector Bundle Setup -/

-- First vector bundle (Domain of the Hom-bundle)
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
variable {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
variable [∀ x, AddCommGroup (V₁ x)] [∀ x, Module 𝕜 (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
variable [∀ x, IsTopologicalAddGroup (V₁ x)] [∀ x, ContinuousSMul 𝕜 (V₁ x)]
variable [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁] [ContMDiffVectorBundle 1 F₁ V₁ I]

-- Second vector bundle (Codomain of the Hom-bundle)
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
variable {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
variable [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
variable [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul 𝕜 (V₂ x)]
variable [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂] [ContMDiffVectorBundle 1 F₂ V₂ I]

-- Require completeness and finite dimensions to use the `TensorialAt` machinery
variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁]

-- Input covariant derivatives
variable (cov₁ : CovariantDerivative I F₁ V₁)
variable (cov₂ : CovariantDerivative I F₂ V₂)

/-! ### Differentiable sections of the Hom-bundle -/

omit [∀ (x : M), IsTopologicalAddGroup (V₁ x)] [∀ (x : M), ContinuousSMul 𝕜 (V₁ x)]
  [ContMDiffVectorBundle 1 F₁ V₁ I] [ContMDiffVectorBundle 1 F₂ V₂ I] [CompleteSpace 𝕜]
  [FiniteDimensional 𝕜 F₁] in
/-- Applying a differentiable section of the Hom-bundle to a differentiable section of `V₁`
yields a differentiable section of `V₂`. -/
lemma mdifferentiableAt_hom_section_apply {σ : Π y : M, V₁ y →L[𝕜] V₂ y} {x : M}
    (hσ : MDiffAt T% σ x)
    {s : Π y : M, V₁ y} (hs : MDiffAt (T% s) x) :
    MDiffAt (T% fun y ↦ σ y (s y)) x :=
  MDifferentiableAt.clm_bundle_apply (b := id) hσ hs

/-! ### Induced Hom-Bundle Connection -/

/--
The unbundled operator on global sections representing the Leibniz rule for the Hom-connection
in the direction `X`. Mathematically, this computes `∇_X (σ(s₁)) - σ(∇_X s₁)`.
-/
def homBundleOp (σ : Π y : M, V₁ y →L[𝕜] V₂ y) (x : M) (X : TangentSpace I x) :
    (Π y, V₁ y) → V₂ x :=
  fun s₁ => cov₂ (fun y => σ y (s₁ y)) x X - σ x (cov₁ s₁ x X)

omit [ContMDiffVectorBundle 1 F₁ V₁ I] [ContMDiffVectorBundle 1 F₂ V₂ I] [CompleteSpace 𝕜]
  [FiniteDimensional 𝕜 F₁] in
/--
Proof that `homBundleOp` is tensorial at `x` with respect to the input section `s₁`, for `σ`
a section of the Hom-bundle which is differentiable at `x`.
Because the difference cancels the derivative of the section, this operator depends only
on the pointwise value `s₁ x`, allowing us to project it down to the fiber.
-/
lemma homBundleOp_isTensorialAt (σ : Π y : M, V₁ y →L[𝕜] V₂ y) (x : M) (X : TangentSpace I x)
    (hσ : MDiffAt T% σ x) :
    TensorialAt I F₁ (homBundleOp cov₁ cov₂ σ x X) x := by
  constructor
  · intro f s hf hs
    have hτ : MDiffAt (T% fun y ↦ σ y (s y)) x := mdifferentiableAt_hom_section_apply hσ hs
    have hfs : (fun y ↦ σ y ((f • s) y)) = f • (fun y ↦ σ y (s y)) := by
      funext y; simp
    simp only [homBundleOp, hfs,
      cov₂.isCovariantDerivativeOnUniv.leibniz hτ hf (Set.mem_univ x),
      cov₁.isCovariantDerivativeOnUniv.leibniz hs hf (Set.mem_univ x)]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply,
      smul_apply, map_add, map_smul, smul_sub]
    abel
  · intro s s' hs hs'
    have hτ : MDiffAt (T% fun y ↦ σ y (s y)) x := mdifferentiableAt_hom_section_apply hσ hs
    have hτ' : MDiffAt (T% fun y ↦ σ y (s' y)) x := mdifferentiableAt_hom_section_apply hσ hs'
    have hadd : (fun y ↦ σ y ((s + s') y))
        = (fun y ↦ σ y (s y)) + (fun y ↦ σ y (s' y)) := by
      funext y; simp
    simp only [homBundleOp, hadd,
      cov₂.isCovariantDerivativeOnUniv.add hτ hτ' (Set.mem_univ x),
      cov₁.isCovariantDerivativeOnUniv.add hs hs' (Set.mem_univ x)]
    simp only [add_apply, map_add]
    abel

/-- The value of `homBundleOp` on the canonical extension of a vector `v` of the fibre `V₁ x`,
packaged as a continuous linear map in the direction `X`. -/
def homBundleFiberOp (σ : Π y : M, V₁ y →L[𝕜] V₂ y) (x : M) (v : V₁ x) :
    TangentSpace I x →L[𝕜] V₂ x :=
  cov₂ (fun y ↦ σ y (FiberBundle.extend F₁ v y)) x -
    (σ x).comp (cov₁ (FiberBundle.extend F₁ v) x)

omit [VectorBundle 𝕜 F₁ V₁] [ContMDiffVectorBundle 1 F₁ V₁ I] [VectorBundle 𝕜 F₂ V₂]
  [ContMDiffVectorBundle 1 F₂ V₂ I] [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] in
lemma homBundleOp_extend (σ : Π y : M, V₁ y →L[𝕜] V₂ y) (x : M) (X : TangentSpace I x)
    (v : V₁ x) :
    homBundleOp cov₁ cov₂ σ x X (FiberBundle.extend F₁ v) = homBundleFiberOp cov₁ cov₂ σ x v X := by
  unfold homBundleOp
  rfl

/--
The induced covariant derivative on the Hom-bundle, evaluated point-wise, for a section `σ` of
the Hom-bundle which is differentiable at `x`.
By using `TensorialAt.mkHom`, this projects the global differential operator down to a
continuous linear map `V₁ x →L[𝕜] V₂ x`.
-/
def homBundlePointwiseAux (σ : Π y : M, V₁ y →L[𝕜] V₂ y) (x : M)
    (hσ : MDiffAt T% σ x) :
    TangentSpace I x →L[𝕜] (V₁ x →L[𝕜] V₂ x) where
  toFun := fun X => TensorialAt.mkHom _ x (homBundleOp_isTensorialAt cov₁ cov₂ σ x X hσ)
  map_add' X Y := by
    ext v
    simp only [add_apply, TensorialAt.mkHom_apply_eq_extend,
      homBundleOp_extend, map_add]
  map_smul' c X := by
    ext v
    simp only [RingHom.id_apply, smul_apply,
      TensorialAt.mkHom_apply_eq_extend, homBundleOp_extend, map_smul]
  cont := by
    have he₁ : V₁ x ≃L[𝕜] F₁ := (trivializationAt F₁ V₁ x).continuousLinearEquivAt 𝕜 x
      (FiberBundle.mem_baseSet_trivializationAt F₁ V₁ x)
    have he₂ : V₂ x ≃L[𝕜] F₂ := (trivializationAt F₂ V₂ x).continuousLinearEquivAt 𝕜 x
      (FiberBundle.mem_baseSet_trivializationAt F₂ V₂ x)
    set Θ : (V₁ x →L[𝕜] V₂ x) ≃L[𝕜] (F₁ →L[𝕜] F₂) := he₁.arrowCongrSL he₂ with hΘ
    change Continuous fun X ↦ TensorialAt.mkHom _ x (homBundleOp_isTensorialAt cov₁ cov₂ σ x X hσ)
    rw [← Θ.toHomeomorph.comp_continuous_iff, continuous_clm_apply]
    intro w
    have key : ∀ X : TangentSpace I x,
        (Θ.toHomeomorph ∘ fun X ↦ TensorialAt.mkHom (homBundleOp cov₁ cov₂ σ x X) x
            (homBundleOp_isTensorialAt cov₁ cov₂ σ x X hσ)) X w
          = he₂ (homBundleFiberOp cov₁ cov₂ σ x (he₁.symm w) X) := by
      intro X
      simp [hΘ, TensorialAt.mkHom_apply_eq_extend, homBundleOp_extend]
    simp only [key]
    exact he₂.continuous.comp (homBundleFiberOp cov₁ cov₂ σ x (he₁.symm w)).continuous

open scoped Classical in
/-- The induced covariant derivative on the Hom-bundle, evaluated point-wise; the junk value `0`
is used at points where `σ` is not differentiable. -/
def homBundlePointwise (σ : Π y : M, V₁ y →L[𝕜] V₂ y) (x : M) :
    TangentSpace I x →L[𝕜] (V₁ x →L[𝕜] V₂ x) :=
  if hσ : MDiffAt T% σ x then homBundlePointwiseAux cov₁ cov₂ σ x hσ else 0

omit [ContMDiffVectorBundle 1 F₂ V₂ I] in
/-- On the canonical extension of a vector of the fibre, the Hom-bundle connection is given by
`homBundleFiberOp`. -/
lemma homBundlePointwise_apply_extend {σ : Π y : M, V₁ y →L[𝕜] V₂ y} {x : M}
    (hσ : MDiffAt T% σ x) (X : TangentSpace I x) (v : V₁ x) :
    homBundlePointwise cov₁ cov₂ σ x X v = homBundleFiberOp cov₁ cov₂ σ x v X := by
  rw [homBundlePointwise, dite_eq_left hσ]
  rfl

omit [ContMDiffVectorBundle 1 F₂ V₂ I] in
/-- The defining property of the Hom-bundle connection. -/
lemma homBundlePointwise_apply {σ : Π y : M, V₁ y →L[𝕜] V₂ y} {x : M}
    (hσ : MDiffAt T% σ x) (X : TangentSpace I x)
    {s : Π y : M, V₁ y} (hs : MDiffAt (T% s) x) :
    homBundlePointwise cov₁ cov₂ σ x X (s x)
      = cov₂ (fun y ↦ σ y (s y)) x X - σ x (cov₁ s x X) := by
  rw [homBundlePointwise, dite_eq_left hσ]
  exact TensorialAt.mkHom_apply (homBundleOp_isTensorialAt cov₁ cov₂ σ x X hσ) hs

/-! ### Global Bundling of the Hom-Connection -/

omit [ContMDiffVectorBundle 1 F₂ V₂ I] in
/--
Proof that the pointwise induced Hom-connection satisfies the unbundled local covariant
derivative rules (additivity and the Leibniz rule over scalar multiplication).
-/
lemma isCovariantDerivativeOn_homBundle :
    IsCovariantDerivativeOn (F₁ →L[𝕜] F₂) (homBundlePointwise cov₁ cov₂) Set.univ := by
  constructor
  · intro σ σ' x hσ hσ' _
    ext X v
    have hE : MDiffAt (T% (FiberBundle.extend F₁ v)) x :=
      FiberBundle.mdifferentiableAt_extend I F₁ v
    have hσσ' : MDiffAt T% (σ + σ') x :=
      mdifferentiableAt_add_section hσ hσ'
    rw [add_apply, add_apply,
      homBundlePointwise_apply_extend cov₁ cov₂ hσσ',
      homBundlePointwise_apply_extend cov₁ cov₂ hσ,
      homBundlePointwise_apply_extend cov₁ cov₂ hσ']
    have hsplit : (fun y ↦ (σ + σ') y (FiberBundle.extend F₁ v y))
        = (fun y ↦ σ y (FiberBundle.extend F₁ v y))
          + (fun y ↦ σ' y (FiberBundle.extend F₁ v y)) := by
      funext y; simp
    simp only [homBundleFiberOp, sub_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply]
    rw [hsplit, cov₂.isCovariantDerivativeOnUniv.add (mdifferentiableAt_hom_section_apply hσ hE)
        (mdifferentiableAt_hom_section_apply hσ' hE) (Set.mem_univ x)]
    simp only [add_apply, Pi.add_apply]
    abel
  · intro σ g x hσ hg _
    ext X v
    have hE : MDiffAt (T% (FiberBundle.extend F₁ v)) x :=
      FiberBundle.mdifferentiableAt_extend I F₁ v
    have hgσ : MDiffAt T% (g • σ) x := hg.smul_section hσ
    rw [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, add_apply,
      smul_apply, smul_apply,
      homBundlePointwise_apply_extend cov₁ cov₂ hgσ,
      homBundlePointwise_apply_extend cov₁ cov₂ hσ]
    have hsplit : (fun y ↦ (g • σ) y (FiberBundle.extend F₁ v y))
        = g • (fun y ↦ σ y (FiberBundle.extend F₁ v y)) := by
      funext y; simp
    simp only [homBundleFiberOp, sub_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, hsplit,
      cov₂.isCovariantDerivativeOnUniv.leibniz (mdifferentiableAt_hom_section_apply hσ hE) hg
        (Set.mem_univ x),
      add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, FiberBundle.extend_apply_self, smul_sub]
    abel

/--
The globally bundled covariant derivative on the `Hom`-bundle.
This provides the connection `∇^{Hom}` acting on sections of `Hom(V₁, V₂)`.
-/
def CovariantDerivative.homBundle :
    CovariantDerivative I (F₁ →L[𝕜] F₂) (fun x ↦ V₁ x →L[𝕜] V₂ x) where
  toFun := homBundlePointwise cov₁ cov₂
  isCovariantDerivativeOnUniv := isCovariantDerivativeOn_homBundle cov₁ cov₂

end HomBundle
