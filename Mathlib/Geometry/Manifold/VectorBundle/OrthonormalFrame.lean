/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
import Mathlib.Geometry.Manifold.VectorBundle.GramSchmidtOrtho
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# Existence of orthonormal frames on Riemannian vector bundles

In this file, we prove that a Riemannian vector bundle has orthonormal frames near each point.
These are constructed by taking any local frame, and applying Gram-Schmidt orthonormalisation
to it (point-wise). If the bundle metric is `C^k`, the resulting orthonormal frame also is.

TODO: add main results, etc

## Implementation note

Like local frames, orthonormal frames use the junk value pattern: their value is meaningless
outside of the `baseSet` of the trivialisation used to define them.

## Tags
vector bundle, local frame, smoothness

-/

open Manifold Bundle ContinuousLinearMap ENat Bornology
open scoped ContDiff Topology

-- Let `V` be a smooth vector bundle with a `C^n` Riemannian structure over a `C^k` manifold `B`.
variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsManifold IB n B] [ContMDiffVectorBundle n F E IB]
  [IsContMDiffRiemannianBundle IB n F E]

variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

-- bad, for prototyping
variable {b : Basis ι ℝ F}
    {e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B)}
    [MemTrivializationAtlas e] {x : B} -- (hx : x ∈ e.baseSet)
namespace Basis

-- noncomputable def orthonormalFrame_toBasis_at : Basis ι ℝ (E x) :=
--   sorry -- b.map (e.linearEquivAt (R := 𝕜) x hx).symm

variable (b e) in
/-- The orthonormal frame associated to the basis `b` and the trivialisation `e`:
this is obtained by applying the Gram-Schmidt orthonormalisation procedure to `b.localFrame e`.
In particular, if x is outside of `e.baseSet`, this returns the junk value 0. -/
noncomputable def orthonormalFrame : ι → (x : B) → E x :=
  VectorBundle.gramSchmidt (b.localFrame e)

variable (b e) in
/-- Each orthonormal frame `s^i ∈ Γ(E)` of a `C^k` vector bundle, defined by a local
trivialisation `e`, is `C^k` on `e.baseSet`. -/
lemma contMDiffOn_orthonormalFrame_baseSet (i : ι) :
    CMDiff[e.baseSet] n (T% b.orthonormalFrame e i) := by
  apply gramSchmidt_contMDiffOn _ _ (fun i ↦ b.contMDiffOn_localFrame_baseSet n e _)
  intro x hx
  sorry -- missing lemma: localFrame is linearly independent at each point in the baseSet

variable (b e) in
lemma _root_.contMDiffAt_orthonormalFrame_of_mem (i : ι) {x : B} (hx : x ∈ e.baseSet) :
    CMDiffAt n (T% b.orthonormalFrame e i) x :=
  -- bug: if I change this to a by apply, and put #check after the `by`, it works, but #check' fails
  -- #check' contMDiffOn_orthonormalFrame_baseSet
  (contMDiffOn_orthonormalFrame_baseSet b e i).contMDiffAt <| e.open_baseSet.mem_nhds hx

-- variable (b e) in
-- @[simp]
-- lemma orthonormalFrame_apply_of_mem_baseSet {i : ι} (hx : x ∈ e.baseSet) :
--     b.orthonormalFrame e i x = b.orthonormalFrame_toBasis_at e hx i := by
--   simp [orthonormalFrame, hx]

@[simp]
lemma orthonormalFrame_apply_of_notMem {i : ι} (hx : x ∉ e.baseSet) :
    b.orthonormalFrame e i x = 0 := by
  simp only [orthonormalFrame, VectorBundle.gramSchmidt_apply]
  convert InnerProductSpace.gramSchmidt_zero ℝ i
  apply localFrame_apply_of_notMem e b hx

end Basis
