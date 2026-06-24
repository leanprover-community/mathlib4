/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang, Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.LinearAlgebra.Trace

/-! # Curvature of an affine connection

We define the curvature tensor of an affine connection, i.e. a covariant derivative on the tangent
bundle `TM` of some manifold `M`.

## Main definitions and results

TODO!

-/

@[expose] public section

open Bundle Set NormedSpace
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}

/-! A preliminary lemma about -/
section prelim

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V]

-- FIXME: does this require real bundles?
lemma exists_contMDiff_of_one_form {k : WithTop ℕ∞}
    {σ : Π x : M, V x} (hσ : CMDiffAt k (T% σ) x) :
    ∃ σ' : (Π x : M, V x),
      CMDiff k (T% σ') ∧ σ' x = σ x ∧ mfderiv% (T% σ') x = mfderiv% (T% σ) x := by
  /- proof idea: assuming smooth bump functions, this becomes a local question
  locally, convolve σ with a bump function of small support; should preserve σ x and mfderiv
  does mathlib have this already? (Moritz Doll proved something similar, I think!)
  -/
  sorry

-- We need one level more of agreement!

-- TODO: this ought to be true (possibly after improving `[IsManifold I 1 M]` to higher regularity),
-- but maybe the definition of smoothness (i.e. `ContMDiffCovariantDerivativeOn`) needs to be
-- adjusted to get it -- the current definition is potentially very weak if the space of sections of
-- `V` over `u` is small.
-- TODO: move this to `CovariantDerivative.Basic`
variable {F} in
lemma ContMDiffCovariantDerivativeOn.contMDiff' [IsManifold I 1 M] [VectorBundle 𝕜 F V]
    {k : WithTop ℕ∞} {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    (hcov : IsCovariantDerivativeOn F cov) [hcov' : ContMDiffCovariantDerivativeOn F k cov univ]
    {σ : Π x : M, V x} (hσ :CMDiffAt (k + 1) (T% σ) x) :
    letI covσ (x : M) : TotalSpace (E →L[𝕜] F) fun x ↦ TangentSpace I x →L[𝕜] V x := ⟨x, cov σ x⟩
    ContMDiffAt I (I.prod 𝓘(𝕜, E →L[𝕜] F)) k covσ x := by
  obtain ⟨σ', hσ', heqs, hdiffx⟩ := exists_contMDiff_of_one_form F hσ
  have aux := contMDiffOn_univ.mp (hcov'.contMDiff hσ'.contMDiffOn)
  -- know: ∇ σ and ∇ σ' agree at x
  have aux' := hcov.congr_of_eq_one_jet (Filter.univ_mem)
    (hσ.mdifferentiableAt (by simp)) (hσ'.mdifferentiableAt (by simp))
    heqs.symm hdiffx.symm -- TODO: choose direction for both equalities!
  -- we need one more level, though!
  sorry

end prelim

variable
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-! ## The Riemannian curvature tensor of an unbundled covariant derivative on `TM` on a set `s`

TODO: generalise this discussion to any vector bundle E
-/
namespace IsCovariantDerivativeOn

variable (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))

variable {X X' Y : (Π x : M, TangentSpace I x)} (σ : Π x, V x)

/-- Local notation for a covariant derivative on a vector bundle acting on a vector field and a
section. -/
local syntax "∇" term:arg term : term
local macro_rules | `(∇ $X $σ) => `(fun (x : M) ↦ cov $σ x ($X x))

example {x} : (∇ X σ) x = cov σ x (X x) := by rfl

/-- The Riemannian curvature endomorphism of a covariant derivative on the tangent bundle `TM`,
as a bare function. Prefer to use `IsCovariantDerivativeOn.curvatureTensor`
(which is a (3,1)-tensor) instead. -/
noncomputable def curvatureTensorAux :
    (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) →
      (Π x : M, V x) → (Π x : M, V x) :=
  fun X Y σ ↦ (∇ X (∇ Y σ)) - (∇ Y (∇ X σ)) - ∇ (VectorField.mlieBracket I X Y) σ

variable [IsManifold I 2 M]
  {cov cov' : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
  {X X' Y Z : Π x : M, TangentSpace I x}

-- TODO: generalise to C^(k + 1) (not just C^2), and move to `CovariantDerivative.Basic`
lemma temp
    {cov : ((x : M) → V x) → (x : M) → TangentSpace I x →L[𝕜] V x}
    (hcov : IsCovariantDerivativeOn F cov)
    [hcov' : ContMDiffCovariantDerivativeOn F 1 cov univ] -- is this the right regularity?
    {x : M} {σ : Π x, V x} {X : (x : M) → TangentSpace I x}
    (hσ : CMDiffAt 2 (T% σ) x) (hX : CMDiffAt 1 (T% X) x) :
    CMDiffAt 1 (T% (fun x ↦ (cov σ x) (X x))) x :=
  (hcov'.contMDiff' hcov hσ).clm_bundle_apply hX

lemma temp_mdiff
    {cov : ((x : M) → V x) → (x : M) → TangentSpace I x →L[𝕜] V x}
    (hcov : IsCovariantDerivativeOn F cov)
    [hcov' : ContMDiffCovariantDerivativeOn F 1 cov univ] -- is this the right regularity?
    {x : M} {σ : Π x, V x} {X : (x : M) → TangentSpace I x}
    (hσ : CMDiffAt 2 (T% σ) x) (hX : MDiffAt (T% X) x) :
    MDiffAt (T% (fun x ↦ (cov σ x) (X x))) x :=
  -- requires adapting `ContMDiffAt.clm_bundle_apply` to `MDifferentiableAt` hypotheses
  sorry

-- HM: looks false to me
-- lemma temp' -- I suspect this one will also work!
--     {cov : ((x : M) → V x) → (x : M) → TangentSpace I x →L[𝕜] V x}
--     (hcov : IsCovariantDerivativeOn F cov)
--     {x : M} {σ : Π x, V x} {X : (x : M) → TangentSpace I x}
--     -- XXX: I suspect σ being C¹ will suffice, and no extra hypotheses on X are necessary
--     (hσ : CMDiffAt 1 (T% σ) x)
--     (aux : ContMDiffAt I (I.prod 𝓘(𝕜, E →L[𝕜] F)) 1
--       (fun x ↦ TotalSpace.mk' (E →L[𝕜] F) x (cov σ x)) x) :
--     ContMDiffAt I (I.prod 𝓘(𝕜, F)) 1 (T% (fun x ↦ (cov σ x) (X x))) x := by
--   sorry

/- Lessons learned from the experiment below:
- we need the lemma temp (or perhaps just temp'); is this in mathlib already?
- the curvature tensor needs a C¹ connection, and a manifold of order 3 and minSmoothness k 2 or so
- we can only prove tensoriality for C² sections (at a point, I hope! to be confirmed),
  so need new tensoriality lemmas
- `mdifferentiableAt` lemmas for C^k covariant derivatives would be nice API addition
-/

-- HM: don't think this one is needed (or perhaps even true)
-- lemma aux
--     (hcov : IsCovariantDerivativeOn F cov) [hcov' : ContMDiffCovariantDerivativeOn F 1 cov univ]
--     {x : M} {Y Z : (x : M) → TangentSpace I x} {τ : Π x, V x}
--     (hτ : CMDiffAt 2 (T% τ) x) :
--     (MDiffAt (T% (fun x ↦ (cov τ x) (VectorField.mlieBracket I Z Y x)))) x := by
--   apply ContMDiffAt.mdifferentiableAt _ one_ne_zero
--   apply temp' F hcov ?_ (hcov'.contMDiff' hcov hτ)
--   apply hτ.of_le
--   norm_num

variable [CompleteSpace E]

theorem curvatureTensorAux_tensorial₁ (hcov : IsCovariantDerivativeOn F cov) (x : M)
    [hcov' : ContMDiffCovariantDerivativeOn F 1 cov univ]
    (Y : (Π x : M, TangentSpace I x)) (τ : Π x, V x)
    (hY : MDiffAt (T% Y) x)
    (hτ : CMDiffAt 2 (T% τ) x) :
    TensorialAt I E (curvatureTensorAux cov · Y τ x) x where
  smul {f X} hf hX := by
    unfold curvatureTensorAux
    dsimp
    sorry
  add {X X'} hX hX' := by
    unfold curvatureTensorAux
    simp only [Pi.add_apply, map_add, Pi.sub_apply]
    rw [VectorField.mlieBracket_add_left hX hX']
    simp only [map_add]
    set A := cov (fun x ↦ (cov τ x) (Y x)) x (X x)
    set B := cov (fun x ↦ (cov τ x) (Y x)) x (X' x)
    set C := cov (fun x ↦ (cov τ x) (X x)) x
    set D := cov (fun x ↦ (cov τ x) (X' x)) x
    have hτX : MDiffAt (T% (fun x ↦ cov τ x (X x))) x := temp_mdiff F hcov hτ hX
    have hτX' : MDiffAt (T% (fun x ↦ cov τ x (X' x))) x := temp_mdiff F hcov hτ hX'
    conv =>
      enter [1, 1, 2]
      equals (cov (fun x ↦ (cov τ x) (X x)) x) (Y x)
          + (cov (fun x ↦ (cov τ x) (X' x)) x) (Y x) =>
        have H := hcov.add hτX hτX'
        exact congr($H (Y x))
    abel

-- update hypotheses to match lemma above, once proven!
theorem curvatureTensorAux_tensorial₂ (hcov : IsCovariantDerivativeOn F cov) (x : M)
    [hcov' : ContMDiffCovariantDerivativeOn F 1 cov univ]
    (X : (Π x : M, TangentSpace I x)) (σ : Π x, V x) :
    TensorialAt I E (curvatureTensorAux cov X · σ x) x :=
  -- proof is analogous to the version in X
  sorry

-- update hypotheses to match lemma above, once proven!
theorem curvatureTensorAux_tensorial₃ (hcov : IsCovariantDerivativeOn F cov) (x : M)
    [hcov' : ContMDiffCovariantDerivativeOn F 1 cov univ]
    (X Y : (Π x : M, TangentSpace I x)) :
    TensorialAt I F (curvatureTensorAux cov X Y · x) x :=
  -- linearity should be "easy" also, scalar multiplication is a different proof
  sorry

noncomputable section

/-- The Riemannian curvature endomorphism `R`, as a (3,1)-tensor field: for vector fields `X`, `Y`
and `Z`, it is defined as `R(X, Y)Z = ∇_X (∇_Y Z) - ∇_Y (∇_X Z) - ∇_[X,Y] Z`. -/
-- This definition follows Lee's sign conventions.
-- TODO: decide if we want this one, and add a comment accordingly!
def curvatureEndomorphismTensor (hcov : IsCovariantDerivativeOn F cov) (x : M)
    [ContMDiffCovariantDerivativeOn F 1 cov univ] :
    TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] V x →L[𝕜] V x :=
  TensorialAt.mkHom₃ (curvatureTensorAux cov · · · x) x
    (fun X τ hX hτ ↦ hcov.curvatureTensorAux_tensorial₁ F x X τ hX sorry)
    -- `hτ` not good enough for the `sorry` above
    -- HM: looks like we may need a version of `TensorialAt.mkHom₃` in which the tensoriality
    -- conditions are only proved for C^2 (or C^k) sections
    (fun X τ _ _ ↦ hcov.curvatureTensorAux_tensorial₂ F x X τ)
    (fun X Y _ _ ↦ hcov.curvatureTensorAux_tensorial₃ F x X Y)

variable [ContMDiffCovariantDerivativeOn F 1 cov univ]

-- lemmas: curvatureEndomorphismTensor_apply and curvatureEndomorphismTensor_apply_extend

variable (X) in
@[simp]
lemma curvatureEndomorphismTensor_self (hcov : IsCovariantDerivativeOn F cov)
    (X₀ : TangentSpace I x) :
    hcov.curvatureEndomorphismTensor F x X₀ X₀ = 0 := by
  sorry

variable (X Y) in
lemma curvatureEndomorphismTensor_swap (hcov : IsCovariantDerivativeOn F cov)
    (X₀ Y₀ : TangentSpace I x) :
    hcov.curvatureEndomorphismTensor F x X₀ Y₀ = - hcov.curvatureEndomorphismTensor F x Y₀ X₀ := by
  sorry

-- lemma: if cov is the Levi-Civita connection, we have <V, R(X, Y)Z> + <R(X, Y)V, Z> = 0
-- for all vector fields V, X, Y and Z.

-- this is the thing whose cohomology class gives a definition of characteristic classes
-- do something similar (but swap the argument order of the full curvature tensor) for the
-- Levi-Civita connection to get Ricci curvature
def traceCurvature [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 E]
    (hcov : IsCovariantDerivativeOn F cov) (x : M) :
    TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] 𝕜 :=
  have : T2Space (V x) := (VectorBundle.continuousLinearEquivAt 𝕜 F V x).toHomeomorph.symm.t2Space
  have : T2Space (TangentSpace% x) := inferInstanceAs <| T2Space E
  have : FiniteDimensional 𝕜 (V x) := VectorBundle.finiteDimensional 𝕜 F V x
  have : FiniteDimensional 𝕜 (TangentSpace I x) :=
    VectorBundle.finiteDimensional 𝕜 E (TangentSpace I) x
  let tr : (TangentSpace I x →ₗ[𝕜] V x →L[𝕜] V x) →ₗ[𝕜] TangentSpace I x →ₗ[𝕜] 𝕜 :=
    LinearMap.llcomp 𝕜 (TangentSpace I x) _ _
      (LinearMap.trace 𝕜 (V x) ∘ₗ ContinuousLinearMap.coeLM 𝕜)
  let Tr : (TangentSpace I x →L[𝕜] V x →L[𝕜] V x) →L[𝕜] TangentSpace I x →L[𝕜] 𝕜 :=
    (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
      (tr ∘ₗ ContinuousLinearMap.coeLM 𝕜)).toContinuousLinearMap
  Tr ∘L curvatureEndomorphismTensor F hcov x

-- scalar curvature left to the reader
-- (for this construction need to set up the typeclasses for a Riemannian manifold)

end

end IsCovariantDerivativeOn
