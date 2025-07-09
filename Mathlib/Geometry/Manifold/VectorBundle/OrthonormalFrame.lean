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

variable {s : ι → (x : B) → E x} {u : Set B}

-- also: monotonicity? will see if useful, at all...

/-- Applying the Gram-Schmidt procedure to a local frame yields another local frame. -/
def IsLocalFrameOn.gramSchmidt (hs : IsLocalFrameOn IB F n s u) :
    IsLocalFrameOn IB F n (VectorBundle.gramSchmidt s) u where
  linearIndependent := by
    intro x hx
    exact VectorBundle.gramSchmidt_linearIndependent (hs.linearIndependent hx)
  generating := by
    intro x hx
    sorry -- lemma about Gram-Schmidt...
  contMDiffOn i := gramSchmidt_contMDiffOn i u (fun i ↦ hs.contMDiffOn i) <|
      fun x hx ↦ (hs.linearIndependent hx).comp _ Subtype.val_injective

namespace Basis

-- bad, for prototyping
variable {b : Basis ι ℝ F}
    {e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B)}
    [MemTrivializationAtlas e] {x : B} -- (hx : x ∈ e.baseSet)

-- noncomputable def orthonormalFrame_toBasis_at : Basis ι ℝ (E x) := sorry

variable (b e) in
/-- The orthonormal frame associated to the basis `b` and the trivialisation `e`:
this is obtained by applying the Gram-Schmidt orthonormalisation procedure to `b.localFrame e`.
In particular, if x is outside of `e.baseSet`, this returns the junk value 0. -/
noncomputable def orthonormalFrame : ι → (x : B) → E x :=
  VectorBundle.gramSchmidt (b.localFrame e)

omit [IsManifold IB n B] in
/-- An orthonormal frame w.r.t. a local trivialisation is a local frame. -/
lemma orthonormalFrame_isLocalFrameOn : IsLocalFrameOn IB F n (b.orthonormalFrame e) e.baseSet :=
  (b.localFrame_isLocalFrameOn_baseSet IB n e).gramSchmidt

omit [IsManifold IB n B] in
variable (b e) in
/-- Each orthonormal frame `s^i ∈ Γ(E)` of a `C^k` vector bundle, defined by a local
trivialisation `e`, is `C^k` on `e.baseSet`. -/
lemma contMDiffOn_orthonormalFrame_baseSet (i : ι) :
    CMDiff[e.baseSet] n (T% b.orthonormalFrame e i) :=
  orthonormalFrame_isLocalFrameOn.contMDiffOn _

omit [IsManifold IB n B] in
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

/- next steps:

lemma: local frame coefficients (in the same way),
a section is C^k iff its coefficients are
(prove for IsLocalFrameOn first!)

lemma: frame coefficient of s_i is the product with that local section
  (only true here, by orthogonality)

cor: section t is smooth iff each product <t, si> is (just rewrite twice)

lemma: uniqueness (what I need for torsion) -/
