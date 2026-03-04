/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.BumpFunction
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# Extending an element of a vector bundle to a smooth section

-/

public section

open Bundle Filter Module Topology Set
open scoped Manifold ContDiff

section extend
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  -- `V` vector bundle

-- TODO: either change `localFrame` to make sure it is everywhere smooth
-- or introduce a cut-off here. First option is probaly better.
-- TODO: comment why we chose the second option in the end, and adapt the definition accordingly
-- new definition: smooth a bump function, then smul with localExtensionOn
/-- Extend a vector `v ∈ V x` to a section of the bundle `V`, whose value at `x` is `v`.
The details of the extension are mostly unspecified: for covariant derivatives, the value of
`s` at points other than `x` will not matter (except for shorter proofs).
Thus, we choose `s` to be somewhat nice: our chosen construction is linear in `v`.
-/
noncomputable def extend [FiniteDimensional ℝ F] [T2Space M] {x : M} (v : V x) :
    (x' : M) → V x' :=
  letI b := Basis.ofVectorSpace ℝ F
  letI t := trivializationAt F V x
  -- Choose a smooth bump function ψ near `x`, supported within t.baseSet
  -- and return ψ • V₀ instead.
  letI ht := t.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
  let ψ := Classical.choose <| (SmoothBumpFunction.nhds_basis_support (I := I) ht).mem_iff.1 ht
  ψ.toFun • localExtensionOn b t v

variable {I F}

-- NB. These two lemmas don't hold for *any* choice of extension of `v`, but they hold for
-- *well-chosen* extensions (such as ours).
-- so, one may argue this is mathematically wrong, but it encodes the "choice some extension
-- with this and that property" nicely
-- a different proof would be to argue only the value at a point matters for cov
@[simp]
lemma extend_add [FiniteDimensional ℝ F] [T2Space M] {x : M} (v v' : V x) :
    extend I F (v + v') = extend I F v + extend I F v' := by
  simp [extend]

@[simp]
lemma extend_smul [FiniteDimensional ℝ F] [T2Space M] {a : ℝ} {x : M} (v : V x) :
  extend I F (a • v) = a • extend I F v := by simp [extend]; module

@[simp]
lemma extend_zero [FiniteDimensional ℝ F] [T2Space M] (x : M) :
  extend I F (0 : V x) = 0 := by simp [extend]

@[simp] lemma extend_apply_self [FiniteDimensional ℝ F] [T2Space M] {x : M} (v : V x) :
    extend I F v x = v := by
  simpa [extend] using
    localExtensionOn_apply_self _ _ (FiberBundle.mem_baseSet_trivializationAt' x) v

variable (I F)

lemma contMDiff_extend [IsManifold I ∞ M] [FiniteDimensional ℝ F] [T2Space M]
    [ContMDiffVectorBundle ∞ F V I] {x : M} (σ₀ : V x) :
    CMDiff ∞ (T% (extend I F σ₀)) := by
  letI t := trivializationAt F V x
  letI ht := t.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let ψ := Classical.choose <| (SmoothBumpFunction.nhds_basis_support (I := I) ht).mem_iff.1 ht
  let hψ :=
    Classical.choose_spec <| (SmoothBumpFunction.nhds_basis_support (I := I) ht).mem_iff.1 ht
  exact ContMDiffOn.smul_section_of_tsupport ψ.contMDiff.contMDiffOn t.open_baseSet hψ.1
    (contMDiffOn_localExtensionOn _ hx _)

-- TODO weaken regularity condition on `IsManifold` and `ContMDiffVectorBundle` hypotheses
lemma mdifferentiable_extend [IsManifold I ∞ M] [FiniteDimensional ℝ F] [T2Space M]
    [ContMDiffVectorBundle ∞ F V I] {x : M} (σ₀ : V x) :
    MDiff (T% (extend I F σ₀)) :=
  contMDiff_extend I F σ₀ |>.mdifferentiable (by simp)

lemma mdifferentiableAt_extend [IsManifold I ∞ M] [FiniteDimensional ℝ F] [T2Space M]
    [ContMDiffVectorBundle ∞ F V I] {x : M} (σ₀ : V x) (x' : M) :
    MDiffAt (T% (extend I F σ₀)) x' :=
  mdifferentiable_extend I F σ₀ |>.mdifferentiableAt

theorem contDiff_extend
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    (x : E) (y : E') : ContDiff ℝ ∞ (extend 𝓘(ℝ, E) E' y (x := x)) := by
  rw [contDiff_iff_contDiffAt]
  intro x'
  rw [← contMDiffAt_iff_contDiffAt]
  simpa [contMDiffAt_section] using contMDiff_extend (V := Trivial E E') _ _ y x'

end extend
