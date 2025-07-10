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
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E] {n : WithTop ℕ∞}
  [IsManifold IB n B] [ContMDiffVectorBundle n F E IB]
  [IsContMDiffRiemannianBundle IB n F E]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

variable {s : ι → (x : B) → E x} {u u' : Set B}

variable (IB F n) in
structure IsOrthogonalFrameOn (s : ι → (x : B) → E x) (u : Set B)
    extends IsLocalFrameOn IB F n s u where
  /-- Any two distinct sections are point-wise orthogonal on `u`. -/
  orthogonal {i j : ι} {x : B} : i ≠ j → x ∈ u → ⟪s i x, s j x⟫ = 0

omit [VectorBundle ℝ F E] [IsManifold IB n B] [ContMDiffVectorBundle n F E IB]
  [IsContMDiffRiemannianBundle IB n F E]
  [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι] in
lemma IsOrthogonalFrameOn.mono (hs : IsOrthogonalFrameOn IB F n s u) (huu' : u' ⊆ u) :
    IsOrthogonalFrameOn IB F n s u' where
  toIsLocalFrameOn := hs.toIsLocalFrameOn.mono huu'
  orthogonal hij hx := hs.orthogonal hij (huu' hx)

/-- Applying the Gram-Schmidt procedure to a local frame yields another local frame. -/
def IsLocalFrameOn.gramSchmidt (hs : IsLocalFrameOn IB F n s u) :
    IsLocalFrameOn IB F n (VectorBundle.gramSchmidt s) u where
  linearIndependent := by
    intro x hx
    exact VectorBundle.gramSchmidt_linearIndependent (hs.linearIndependent hx)
  generating := by
    intro x hx
    simpa only [VectorBundle.gramSchmidt_apply, InnerProductSpace.span_gramSchmidt ℝ (s · x)]
      using hs.generating hx
  contMDiffOn i := gramSchmidt_contMDiffOn i u (fun i ↦ hs.contMDiffOn i) <|
      fun x hx ↦ (hs.linearIndependent hx).comp _ Subtype.val_injective

/-- Applying the Gram-Schmidt procedure to an orthogonal local frame yields
another orthogonal local frame. -/
def IsOrthogonalFrameOn.gramSchmidt (hs : IsOrthogonalFrameOn IB F n s u) :
    IsOrthogonalFrameOn IB F n (VectorBundle.gramSchmidt s) u where
  toIsLocalFrameOn := hs.toIsLocalFrameOn.gramSchmidt
  orthogonal {_ _ x} hij _hx := VectorBundle.gramSchmidt_orthogonal s hij x


/-! # Determining smoothness of a section via its local frame coefficients

We show that for any orthogonal local frame `{s i}` on `u ⊆ B`, a section `t` is smooth on `u`
if and only if its coefficients in `{s i}` are. This argument crucially depends on the existence of
a smooth bundle metric on `V` (which always holds in finite dimensions, and in certain important
infinite-dimensional cases).

See `LocalFrame.lean` for a similar statement, about local frames induced by a local trivialisation
on finite rank bundles over any complete field.

The orthogonality requirement can be removed, with additional technical effort: see the comment
below for details. It simplifies the proofs as the local frame coefficients take a particularly
simple form in orthgonal frames.
-/

section smoothness

namespace IsOrthogonalFrameOn

variable (hs : IsOrthogonalFrameOn IB F n s u) {t : (x : B) → E x} {x : B}

set_option linter.style.commandStart false

variable (t) in
lemma repr_eq_inner (hs : IsOrthogonalFrameOn IB F n s u)
    {x} (hx : x ∈ u) (i : ι) :
    hs.repr i t x = ⟪s i x, t x⟫ / (‖s i x‖ ^ 2) := by
  -- should be a general lemma: orthogonal basis, have this identity
  sorry

/-- If `t` is `C^k` at `x`, so is its coefficient `hs.repr i t` in a local frame s near `x` -/
lemma contMDiffWithinAt_repr (ht : CMDiffAt[u] n (T% t) x) (hx : x ∈ u) (i : ι) :
    CMDiffAt[u] n (hs.repr i t) x := by
  have aux : CMDiffAt[u] n (fun x ↦ ⟪s i x, t x⟫ / (‖s i x‖ ^ 2)) x := by
    apply contMDiffWithinAt_aux ((hs.contMDiffOn i) x hx) ht
    have := hs.linearIndependent hx
    sorry
  exact aux.congr_of_mem (fun y hy ↦ hs.repr_eq_inner _ hy _) hx

/-- If `t` is `C^k` at `x`, so is its coefficient `hs.repr i t` in a local frame s near `x` -/
lemma contMDiffAt_repr (hu : u ∈ 𝓝 x) (ht : CMDiffAt n (T% t) x) (i : ι) :
    CMDiffAt n (hs.repr i t) x := by
  have aux : CMDiffAt n (fun x ↦ ⟪s i x, t x⟫ / (‖s i x‖ ^ 2)) x := by
    apply contMDiffAt_aux ((hs.contMDiffOn i).contMDiffAt hu) ht
    have := hs.linearIndependent (mem_of_mem_nhds hu)
    sorry
  exact aux.congr_of_eventuallyEq <|
    Filter.eventually_of_mem hu fun x hx ↦ hs.repr_eq_inner _ hx _

-- Future: prove the same result for all local frames
-- if `{s i}` is a local frame on `u`, and `{s' i}` are the corresponding orthogonalised frame,
-- for each `x ∈ u` the vectors `{s i x}` and `{s' i x}` are bases of `E x`,
-- and the coefficients w.r.t. `s i` and `s' i x` are related by the base change matrix.
-- This matrix depends smoothly on `x`, hence the frame coefficients w.r.t. `{s i}` are smooth iff
-- those w.r.t. `{s' i}` are.

/-- If `{s i}` is an orthogonal local frame on a neighbourhood `u` of `x` and `t` is `C^k` on `u`,
so is its coefficient in the frame `{s i}`. -/
lemma contMDiffOn_repr (ht : CMDiff[u] n (T% t)) (i : ι) : CMDiff[u] n (hs.repr i t) :=
  fun x' hx ↦ hs.contMDiffWithinAt_repr (ht x' hx) hx _

/-- A section `s` of `V` is `C^k` at `x` iff each of its coefficients in an orthogonal
local frame near `x` is. -/
lemma contMDiffAt_iff_repr [Fintype ι]
    (hu : u ∈ 𝓝 x) : CMDiffAt n (T% t) x ↔ ∀ i, CMDiffAt n (hs.repr i t) x :=
  ⟨fun h i ↦ hs.contMDiffAt_repr hu h i, fun h ↦ hs.contMDiffAt_of_repr h hu⟩

/-- If `{s i}` is an orthogonal local frame on `s`, a section `s` of `V` is `C^k` on `u` iff
each of its coefficients `hs.repr i s` w.r.t. the local frame `{s i}` is. -/
lemma contMDiffOn_iff_repr [Fintype ι] :
    CMDiff[u] n (T% t) ↔ ∀ i, CMDiff[u] n (hs.repr i t) :=
  ⟨fun h i ↦ hs.contMDiffOn_repr h i, fun hi ↦ hs.contMDiffOn_of_repr hi⟩

-- unused, just stating for convenience/nice API
include hs in
lemma contMDiffAt_iff_repr' [Fintype ι]
    (hu : u ∈ 𝓝 x) : CMDiffAt n (T% t) x ↔ ∀ i, CMDiffAt n (fun x ↦ ⟪s i x, t x⟫) x := by
  trans ∀ i, CMDiffAt n (fun x ↦ ⟪s i x, t x⟫/ (‖s i x‖ ^ 2)) x
  · rw [hs.contMDiffAt_iff_repr hu]
    have (i : ι) := Filter.eventually_of_mem hu fun x hx ↦ (hs.repr_eq_inner t hx i)
    exact ⟨fun h i ↦ (h i).congr_of_eventuallyEq <| Filter.EventuallyEq.symm (this i),
      fun h i ↦ (h i).congr_of_eventuallyEq (this i)⟩
  · peel with i
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · sorry -- similar to other direction below
    · apply h.smul
      refine ContMDiffAt.inv₀ ?_ ?_
      · sorry -- rewrite ‖ ‖² = ⟨s, s⟩
      · sorry -- neq 0

-- unused, just stating for convenience/nice API
lemma contMDiffOn_iff_repr' [Fintype ι] :
    CMDiff[u] n (T% t) ↔ ∀ i, CMDiff[u] n (fun x ↦ ⟪s i x, t x⟫) :=
  sorry -- similar to the above lemma

end IsOrthogonalFrameOn

end smoothness

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

/- next lemma: uniqueness (what I need for torsion) -/
