/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.GramSchmidtOrtho
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

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

@[expose] public section -- FIXME: think if expose is desired!

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

variable {s : ι → (x : B) → E x} {u u' : Set B}

variable (IB F n) in
structure IsOrthonormalFrameOn (s : ι → (x : B) → E x) (u : Set B)
    extends IsLocalFrameOn IB F n s u where
  orthonormal {x} : x ∈ u → Orthonormal ℝ (s · x)
  -- /-- Any two distinct sections are point-wise orthogonal on `u`. -/
  -- orthogonal {i j : ι} {x : B} : i ≠ j → x ∈ u → ⟪s i x, s j x⟫ = 0
  -- normalised {i : ι} {x : B} : x ∈ u → ‖s i x‖ = 1

omit [VectorBundle ℝ F E] [IsManifold IB n B] [ContMDiffVectorBundle n F E IB]
  [IsContMDiffRiemannianBundle IB n F E]
  [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι] in
lemma IsOrthonormalFrameOn.mono (hs : IsOrthonormalFrameOn IB F n s u) (huu' : u' ⊆ u) :
    IsOrthonormalFrameOn IB F n s u' where
  toIsLocalFrameOn := hs.toIsLocalFrameOn.mono huu'
  orthonormal hx := hs.orthonormal (huu' hx)

/-- Applying the Gram-Schmidt procedure to a local frame yields an orthonormal local frame. -/
def IsLocalFrameOn.gramSchmidtNormed (hs : IsLocalFrameOn IB F n s u) :
    IsOrthonormalFrameOn IB F n (VectorBundle.gramSchmidtNormed s) u where
  linearIndependent := by
    intro x hx
    exact VectorBundle.gramSchmidtNormed_linearIndependent <| hs.linearIndependent hx
  generating := by
    intro x hx
    simpa only [VectorBundle.span_gramSchmidtNormed_range, VectorBundle.gramSchmidt_apply,
      InnerProductSpace.span_gramSchmidt] using hs.generating hx
  contMDiffOn i := gramSchmidtNormed_contMDiffOn (fun i ↦ hs.contMDiffOn i) <|
      fun x hx ↦ (hs.linearIndependent hx).comp _ Subtype.val_injective
  orthonormal hx := (VectorBundle.gramSchmidtNormed_orthonormal (hs.linearIndependent hx))

-- XXX: is this one necessary?
/-- Applying the normalised Gram-Schmidt procedure to an orthonormal local frame yields
another orthonormal local frame. -/
def IsOrthonormalFrameOn.gramSchmidtNormed (hs : IsOrthonormalFrameOn IB F n s u) :
    IsOrthonormalFrameOn IB F n (VectorBundle.gramSchmidtNormed s) u :=
  hs.toIsLocalFrameOn.gramSchmidtNormed

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

namespace IsOrthonormalFrameOn

omit [IsManifold IB n B] [ContMDiffVectorBundle n F E IB]

variable [Finite ι] (hs : IsOrthonormalFrameOn IB F n s u) {t : (x : B) → E x} {x : B}

omit [VectorBundle ℝ F E] [IsManifold IB n B] [ContMDiffVectorBundle n F E IB]
  [IsContMDiffRiemannianBundle IB n F E] in
variable (t) in
lemma coeff_eq_inner' (hs : IsOrthonormalFrameOn IB F n s u) (hx : x ∈ u) (i : ι) :
    hs.coeff i x (t x) = ⟪s i x, t x⟫ := by
  let := Fintype.ofFinite ι
  let b := VectorBundle.gramSchmidtOrthonormalBasis (hs.linearIndependent hx) (hs.generating hx)
  have beq (i : ι) : b i = s i x := by
    simp [b, VectorBundle.gramSchmidtNormed_apply_of_orthonormal (hs.orthonormal hx) i]
  have heq' : b.toBasis = hs.toBasisAt hx := by
    ext i
    simp [b, VectorBundle.gramSchmidtNormed_apply_of_orthonormal (hs.orthonormal hx) i]
  have aux := b.repr_apply_apply (t x) i
  rw [beq] at aux
  simp [← aux, IsLocalFrameOn.coeff, hx, ← heq']

-- This lemma would hold more generally for an *orthogonal frame*.
-- variable (t) in
-- lemma coeff_eq_inner (hs : IsOrthonormalFrameOn IB F n s u) (hx : x ∈ u) (i : ι) :
--     hs.coeff i t x = ⟪s i x, t x⟫ / (‖s i x‖ ^ 2) := by
--   sorry -- need a version of b.repr_apply_apply for *orthogonal* bases

/-- If `t` is `C^k` at `x`, so is its coefficient `hs.coeff i t` in a local frame s near `x` -/
lemma contMDiffWithinAt_coeff (ht : CMDiffAt[u] n (T% t) x) (hx : x ∈ u) (i : ι) :
    CMDiffAt[u] n (LinearMap.piApply (hs.coeff i) t) x :=
  ((hs.contMDiffOn i x hx).inner_bundle ht).congr_of_mem (fun _ hy ↦ hs.coeff_eq_inner' _ hy _) hx

omit [IsManifold IB n B] [ContMDiffVectorBundle n F E IB] in
/-- If `t` is `C^k` at `x`, so is its coefficient `hs.coeff i t` in a local frame s near `x` -/
lemma contMDiffAt_coeff (hu : u ∈ 𝓝 x) (ht : CMDiffAt n (T% t) x) (i : ι) :
    CMDiffAt n (LinearMap.piApply (hs.coeff i) t) x :=
  (((hs.contMDiffOn i).contMDiffAt hu).inner_bundle ht).congr_of_eventuallyEq <|
    Filter.eventually_of_mem hu fun _ hx ↦ hs.coeff_eq_inner' _ hx _

-- Future: prove the same result for all local frames
-- if `{s i}` is a local frame on `u`, and `{s' i}` are the corresponding orthogonalised frame,
-- for each `x ∈ u` the vectors `{s i x}` and `{s' i x}` are bases of `E x`,
-- and the coefficients w.r.t. `s i` and `s' i x` are related by the base change matrix.
-- This matrix depends smoothly on `x`, hence the frame coefficients w.r.t. `{s i}` are smooth iff
-- those w.r.t. `{s' i}` are.

/-- If `{s i}` is an orthogonal local frame on a neighbourhood `u` of `x` and `t` is `C^k` on `u`,
so is its coefficient in the frame `{s i}`. -/
lemma contMDiffOn_coeff (ht : CMDiff[u] n (T% t)) (i : ι) :
    CMDiff[u] n (LinearMap.piApply (hs.coeff i) t) :=
  fun x' hx ↦ hs.contMDiffWithinAt_coeff (ht x' hx) hx _

/-- A section `s` of `V` is `C^k` at `x` iff each of its coefficients in an orthogonal
local frame near `x` is. -/
lemma contMDiffAt_iff_coeff [FiniteDimensional ℝ F] (hu : u ∈ 𝓝 x) :
    CMDiffAt n (T% t) x ↔ ∀ i, CMDiffAt n (LinearMap.piApply (hs.coeff i) t) x :=
  ⟨fun h i ↦ hs.contMDiffAt_coeff hu h i, fun h ↦ hs.contMDiffAt_of_coeff h hu⟩

/-- If `{s i}` is an orthogonal local frame on `s`, a section `s` of `V` is `C^k` on `u` iff
each of its coefficients `hs.coeff i s` w.r.t. the local frame `{s i}` is. -/
lemma contMDiffOn_iff_coeff [FiniteDimensional ℝ F] :
    CMDiff[u] n (T% t) ↔ ∀ i, CMDiff[u] n (LinearMap.piApply (hs.coeff i) t) :=
  ⟨fun h i ↦ hs.contMDiffOn_coeff h i, fun hi ↦ hs.contMDiffOn_of_coeff hi⟩

-- unused, just stating for convenience/nice API
include hs in
lemma contMDiffAt_iff_coeff' [FiniteDimensional ℝ F] (hu : u ∈ 𝓝 x) :
    CMDiffAt n (T% t) x ↔ ∀ i, CMDiffAt n (fun x ↦ ⟪s i x, t x⟫) x := by
  rw [hs.contMDiffAt_iff_coeff hu]
  have (i : ι) := Filter.eventually_of_mem hu fun x hx ↦ (hs.coeff_eq_inner' t hx i)
  exact ⟨fun h i ↦ (h i).congr_of_eventuallyEq <| Filter.EventuallyEq.symm (this i),
    fun h i ↦ (h i).congr_of_eventuallyEq (this i)⟩

-- unused, just stating for convenience/nice API
lemma contMDiffOn_iff_coeff' :
    CMDiff[u] n (T% t) ↔ ∀ i, CMDiff[u] n (fun x ↦ ⟪s i x, t x⟫) :=
  sorry -- similar to the above lemma

end IsOrthonormalFrameOn

end smoothness

namespace Module.Basis

variable {b : Basis ι ℝ F}
    {e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F E → B)}
    [MemTrivializationAtlas e] {x : B}

variable (b e) in
/-- The orthonormal frame associated to the basis `b` and the trivialisation `e`:
this is obtained by applying the Gram-Schmidt orthonormalisation procedure to `b.localFrame e`.
In particular, if x is outside of `e.baseSet`, this returns the junk value 0. -/
noncomputable def orthonormalFrame : ι → (x : B) → E x :=
  VectorBundle.gramSchmidtNormed (e.localFrame b)

omit [IsManifold IB n B] in
variable (b e) in
/-- An orthonormal frame w.r.t. a local trivialisation is an orthonormal local frame. -/
lemma orthonormalFrame_isOrthonormalFrameOn :
    IsOrthonormalFrameOn IB F n (b.orthonormalFrame e) e.baseSet :=
  (e.isLocalFrameOn_localFrame_baseSet IB n b).gramSchmidtNormed

omit [IsManifold IB n B] in
variable (b e) in
/-- Each orthonormal frame `s^i ∈ Γ(E)` of a `C^k` vector bundle, defined by a local
trivialisation `e`, is `C^k` on `e.baseSet`. -/
lemma contMDiffOn_orthonormalFrame_baseSet (i : ι) :
    CMDiff[e.baseSet] n (T% (b.orthonormalFrame e i)) := by
  apply IsLocalFrameOn.contMDiffOn
  exact (b.orthonormalFrame_isOrthonormalFrameOn e).toIsLocalFrameOn

omit [IsManifold IB n B] in
variable (b e) in
lemma _root_.contMDiffAt_orthonormalFrame_of_mem (i : ι) {x : B} (hx : x ∈ e.baseSet) :
    CMDiffAt n (T% (b.orthonormalFrame e i)) x :=
  -- bug: if I change this to a by apply, and put #check after the `by`, it works, but #check' fails
  -- #check' contMDiffOn_orthonormalFrame_baseSet
  (contMDiffOn_orthonormalFrame_baseSet b e i).contMDiffAt <| e.open_baseSet.mem_nhds hx

-- TODO: add more variants with mdifferentiable!
omit [ContMDiffVectorBundle n F E IB] [IsContMDiffRiemannianBundle IB n F E] in
variable [ContMDiffVectorBundle 1 F E IB] [IsContMDiffRiemannianBundle IB 1 F E] in
variable (b e) in
lemma _root_.mdifferentiableAt_orthonormalFrame_of_mem (i : ι) {x : B} (hx : x ∈ e.baseSet) :
    MDiffAt (T% (b.orthonormalFrame e i)) x := by
  apply ContMDiffAt.mdifferentiableAt _ one_ne_zero
  exact (contMDiffOn_orthonormalFrame_baseSet b e i).contMDiffAt <| e.open_baseSet.mem_nhds hx

@[simp]
lemma orthonormalFrame_apply_of_notMem {i : ι} (hx : x ∉ e.baseSet) :
    b.orthonormalFrame e i x = 0 := by
  simp only [orthonormalFrame, VectorBundle.gramSchmidtNormed, InnerProductSpace.gramSchmidtNormed,
    RCLike.ofReal_real_eq_id, id_eq, smul_eq_zero, inv_eq_zero, norm_eq_zero, or_self]
  convert InnerProductSpace.gramSchmidt_zero ℝ i
  exact e.localFrame_apply_of_notMem b hx

end Module.Basis
