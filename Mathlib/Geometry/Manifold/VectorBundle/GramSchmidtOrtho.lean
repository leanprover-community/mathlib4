/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
public import Mathlib.Geometry.Manifold.Notation

/-!
# Gram-Schmidt orthonormalisation on sections of Riemannian vector bundles

In this file, we provide a version of the Gram-Schmidt orthonormalisation procedure
for sections of Riemannian vector bundles: this produces a system of sections which orthogonal
with respect to the bundle metric. If the initial sections were linearly independent resp.
formed a basis at the point, so do the normalised sections.

If the bundle metric is `C^k`, then the procedure preserves regularity of sections:
if all sections are `C^k`, so are their normalised versions.

This is used in `OrthonormalFrame.lean` to convert a local frame to a local orthonormal frame.

## Implementation note


## Tags
vector bundle, bundle metric, orthonormal frame, Gram-Schmidt

-/

open Manifold Bundle ContinuousLinearMap ENat Bornology
open scoped ContDiff Topology

@[expose] public section -- FIXME: re-consider if we really want to expose all definitions

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

attribute [local instance] IsWellOrder.toHasWellFounded

local notation "⟪" x ", " y "⟫" => inner ℝ x y

open Finset

namespace VectorBundle

open Submodule

/-- The Gram-Schmidt process takes a set of sections as input
and outputs a set of sections which are point-wise orthogonal with the same span.
Basically, we apply the Gram-Schmidt algorithm point-wise. -/
noncomputable def gramSchmidt [WellFoundedLT ι]
    (s : ι → (x : B) → E x) (n : ι) : (x : B) → E x := fun x ↦
  InnerProductSpace.gramSchmidt ℝ (s · x) n

-- Let `s i` be a collection of sections in `E`, indexed by `ι`.
variable {s : ι → (x : B) → E x}

omit [TopologicalSpace B]

variable (s) in
/-- This lemma uses `∑ i in` instead of `∑ i :`. -/
theorem gramSchmidt_def (n : ι) (x) :
    gramSchmidt s n x = s n x - ∑ i ∈ Iio n, (ℝ ∙ gramSchmidt s i x).starProjection (s n x) := by
  rw [gramSchmidt, InnerProductSpace.gramSchmidt_def]
  congr

variable (s) in
theorem gramSchmidt_def' (n : ι) (x) :
    s n x = gramSchmidt s n x + ∑ i ∈ Iio n, (ℝ ∙ gramSchmidt s i x).starProjection (s n x) := by
  rw [gramSchmidt_def, sub_add_cancel]

variable (s) in
theorem gramSchmidt_def'' (n : ι) (x) :
    s n x = gramSchmidt s n x + ∑ i ∈ Iio n,
      (⟪gramSchmidt s i x, s n x⟫ / (‖gramSchmidt s i x‖) ^ 2) • gramSchmidt s i x :=
  InnerProductSpace.gramSchmidt_def'' ℝ (s · x) n

variable (s) in
@[simp]
lemma gramSchmidt_apply (n : ι) (x) :
    gramSchmidt s n x = InnerProductSpace.gramSchmidt ℝ (s · x) n := rfl

variable (s) in
@[simp]
theorem gramSchmidt_bot {ι : Type*} [LinearOrder ι] [LocallyFiniteOrder ι] [OrderBot ι]
    [WellFoundedLT ι] (s : ι → (x : B) → E x) : gramSchmidt s ⊥ = s ⊥ := by
  ext x
  apply InnerProductSpace.gramSchmidt_bot

@[simp]
theorem gramSchmidt_zero (n : ι) : gramSchmidt (0 : ι → (x : B) → E x) n = 0 := by
  ext x
  simpa using InnerProductSpace.gramSchmidt_zero ..

variable (s) in
/-- **Gram-Schmidt Orthogonalisation**: `gramSchmidt` produces a point-wise orthogonal system
of sections. -/
theorem gramSchmidt_orthogonal {a b : ι} (h₀ : a ≠ b) (x) :
    ⟪gramSchmidt s a x, gramSchmidt s b x⟫ = 0 :=
  InnerProductSpace.gramSchmidt_orthogonal _ _ h₀

variable (s) in
/-- This is another version of `gramSchmidt_orthogonal` using `Pairwise` instead. -/
theorem gramSchmidt_pairwise_orthogonal (x) :
    Pairwise fun a b ↦ ⟪gramSchmidt s a x, gramSchmidt s b x⟫ = 0 :=
  fun _ _ h ↦ gramSchmidt_orthogonal s h _

variable (s) in
theorem gramSchmidt_inv_triangular {i j : ι} (hij : i < j) (x) :
    ⟪gramSchmidt s j x, s i x⟫ = 0 :=
  InnerProductSpace.gramSchmidt_inv_triangular _ _ hij

open Submodule Set Order

variable (s) in
theorem mem_span_gramSchmidt {i j : ι} (hij : i ≤ j) (x) :
    s i x ∈ span ℝ ((gramSchmidt s · x) '' Set.Iic j) :=
  InnerProductSpace.mem_span_gramSchmidt _ _ hij

variable (s) in
theorem gramSchmidt_mem_span (x) :
    ∀ {j i}, i ≤ j → gramSchmidt s i x ∈ span ℝ ((s · x) '' Set.Iic j) :=
  InnerProductSpace.gramSchmidt_mem_span _ _

variable (s) in
theorem span_gramSchmidt_Iic (c : ι) (x) :
    span ℝ ((gramSchmidt s · x) '' Set.Iic c) = span ℝ ((s · x) '' Set.Iic c) :=
  InnerProductSpace.span_gramSchmidt_Iic ..

variable (s) in
theorem span_gramSchmidt_Iio (c : ι) (x) :
    span ℝ ((gramSchmidt s · x) '' Set.Iio c) = span ℝ ((s · x) '' Set.Iio c) :=
  InnerProductSpace.span_gramSchmidt_Iio _ _ _

variable (s) in
/-- `gramSchmidt` preserves the point-wise span of sections. -/
theorem span_gramSchmidt (x : B) :
    span ℝ (range (gramSchmidt s · x)) = Submodule.span ℝ (range (s · x)) :=
  InnerProductSpace.span_gramSchmidt ℝ (s · x)

/-- If the section values `s i x` are orthogonal, `gramSchmidt` yields the same values at `x`. -/
theorem gramSchmidt_of_orthogonal {x} (hs : Pairwise fun i j ↦ ⟪s i x, s j x⟫ = 0) :
    ∀ i₀, gramSchmidt s i₀ x = s i₀ x:= by
  simp_rw [gramSchmidt]
  exact fun i ↦ congrFun (InnerProductSpace.gramSchmidt_of_orthogonal ℝ hs) i

theorem gramSchmidt_ne_zero_coe (n : ι) (x)
    (h₀ : LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic n → ι))) : gramSchmidt s n x ≠ 0 :=
  InnerProductSpace.gramSchmidt_ne_zero_coe _ h₀

variable (s) in
/-- If the input sections of `gramSchmidt` are point-wise linearly independent,
the resulting sections are non-zero. -/
theorem gramSchmidt_ne_zero (n : ι) {x} (h₀ : LinearIndependent ℝ (s · x)) :
    gramSchmidt s n x ≠ 0 :=
  InnerProductSpace.gramSchmidt_ne_zero _ h₀

-- No version of `gramSchmidt_triangular` at the moment, for technical reasons: it would expect a
-- `Basis` (of vectors in `E x`) as input, whereas we would want a hypothesis "the section values
-- `s i x` form a basis" instead.

/-- `gramSchmidt` produces point-wise linearly independent sections when given linearly
independent sections. -/
theorem gramSchmidt_linearIndependent {x} (h₀ : LinearIndependent ℝ (s · x)) :
    LinearIndependent ℝ (gramSchmidt s · x) :=
  InnerProductSpace.gramSchmidt_linearIndependent h₀

/-- When the sections `s` form a basis at `x`, so do the sections `gramSchmidt s`. -/
noncomputable def gramSchmidtBasis {x} (hs : LinearIndependent ℝ (s · x))
    (hs' : ⊤ ≤ Submodule.span ℝ (Set.range (s · x))) :
    Module.Basis ι ℝ (E x) :=
  Module.Basis.mk (gramSchmidt_linearIndependent hs)
    ((span_gramSchmidt s x).trans (eq_top_iff'.mpr fun _ ↦ hs' trivial)).ge

theorem coe_gramSchmidtBasis {x} (hs : LinearIndependent ℝ (s · x))
    (hs' : ⊤ ≤ Submodule.span ℝ (Set.range (s · x))) :
    (gramSchmidtBasis hs hs') = (gramSchmidt s · x) :=
  Module.Basis.coe_mk _ _

noncomputable def gramSchmidtNormed [WellFoundedLT ι]
    (s : ι → (x : B) → E x) (n : ι) : (x : B) → E x := fun x ↦
  InnerProductSpace.gramSchmidtNormed ℝ (s · x) n

lemma gramSchmidtNormed_coe {n : ι} {x} :
    gramSchmidtNormed s n x = ‖gramSchmidt s n x‖⁻¹ • gramSchmidt s n x := by
  simp [gramSchmidtNormed, InnerProductSpace.gramSchmidtNormed]

variable {x}

theorem gramSchmidtNormed_unit_length_coe (n : ι)
    (h₀ : LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic n → ι))) :
    ‖gramSchmidtNormed s n x‖ = 1 :=
  InnerProductSpace.gramSchmidtNormed_unit_length_coe n h₀

theorem gramSchmidtNormed_unit_length (n : ι) (h₀ : LinearIndependent ℝ (s · x)) :
    ‖gramSchmidtNormed s n x‖ = 1 :=
  InnerProductSpace.gramSchmidtNormed_unit_length n h₀

theorem gramSchmidtNormed_unit_length' {n : ι} (hn : gramSchmidtNormed s n x ≠ 0) :
    ‖gramSchmidtNormed s n x‖ = 1 :=
  InnerProductSpace.gramSchmidtNormed_unit_length' hn

/-- **Gram-Schmidt Orthonormalization**: `gramSchmidtNormed` applied to a point-wise linearly
independent set of sections produces a point-wise orthornormal system of sections. -/
theorem gramSchmidtNormed_orthonormal (h₀ : LinearIndependent ℝ (s · x)) :
    Orthonormal ℝ (gramSchmidtNormed s · x) :=
  InnerProductSpace.gramSchmidtNormed_orthonormal h₀

variable (s) in
/-- **Gram-Schmidt Orthonormalization**: `gramSchmidtNormed` produces a point-wise orthornormal
system of sections after removing the sections which become zero in the process. -/
theorem gramSchmidtNormed_orthonormal' (x) :
    Orthonormal ℝ fun i : { i | gramSchmidtNormed s i x ≠ 0 } => gramSchmidtNormed s i x :=
  InnerProductSpace.gramSchmidtNormed_orthonormal' _

open Submodule Set Order

variable (s) in
theorem span_gramSchmidtNormed (t : Set ι) (x) :
    span ℝ ((gramSchmidtNormed s · x) '' t) = span ℝ ((gramSchmidt s · x) '' t) :=
  InnerProductSpace.span_gramSchmidtNormed (s · x) t

variable (s) in
theorem span_gramSchmidtNormed_range (x) :
    span ℝ (range (gramSchmidtNormed s · x)) = span ℝ (range (gramSchmidt s · x)) := by
  simpa only [image_univ.symm] using span_gramSchmidtNormed s Set.univ x

/-- `gramSchmidtNormed` applied to linearly independent sections at a point `x` produces
sections which are linearly independent at `x`. -/
theorem gramSchmidtNormed_linearIndependent (h₀ : LinearIndependent ℝ (s · x)) :
    LinearIndependent ℝ (gramSchmidtNormed s · x) := by
  simp [gramSchmidtNormed, InnerProductSpace.gramSchmidtNormed_linearIndependent h₀]

lemma gramSchmidtNormed_apply_of_orthogonal (hs : Pairwise fun i j ↦ ⟪s i x, s j x⟫ = 0) {i : ι} :
    gramSchmidtNormed s i x = (‖s i x‖⁻¹ : ℝ) • s i x := by
  simp_rw [gramSchmidtNormed_coe, gramSchmidt_of_orthogonal hs i]

/-- If the section values `s i x` are orthonormal, applying `gramSchmidtNormed` yields the same
values at `x`. -/
lemma gramSchmidtNormed_apply_of_orthonormal {x} (hs : Orthonormal ℝ (s · x)) (i : ι) :
    gramSchmidtNormed s i x = s i x := by
  simp [gramSchmidtNormed_apply_of_orthogonal hs.2, hs.1 i]

-- TODO: comment on the different design compared to `InnerProductSpace.gramSchmidtOrthonormalBasis`

/-- When the sections `s` form a basis at `x`, so do the sections `gramSchmidtNormed s`.

Prefer using `gramSchmidtOrthonormalBasis` over this declaration. -/
noncomputable def gramSchmidtNormedBasis {x} (hs : LinearIndependent ℝ (s · x))
    (hs' : ⊤ ≤ Submodule.span ℝ (Set.range (s · x))) :
    Module.Basis ι ℝ (E x) :=
  Module.Basis.mk (v := fun i ↦ gramSchmidtNormed s i x) (gramSchmidtNormed_linearIndependent hs)
    (by rw [span_gramSchmidtNormed_range s x, span_gramSchmidt s x]; exact hs')

/-- Prefer using `gramSchmidtOrthonormalBasis` over this declaration. -/
@[simp]
theorem coe_gramSchmidtNormedBasis {x} (hs : LinearIndependent ℝ (s · x))
    (hs' : ⊤ ≤ Submodule.span ℝ (Set.range (s · x))) :
    (gramSchmidtNormedBasis hs hs' : ι → E x) = (gramSchmidtNormed s · x) :=
  Module.Basis.coe_mk _ _

noncomputable def gramSchmidtOrthonormalBasis {x} [Fintype ι]
    (hs : LinearIndependent ℝ (s · x)) (hs' : ⊤ ≤ Submodule.span ℝ (Set.range (s · x))) :
    OrthonormalBasis ι ℝ (E x) := by
  apply (gramSchmidtNormedBasis hs hs').toOrthonormalBasis
  simp [gramSchmidtNormed_orthonormal hs]

@[simp]
theorem gramSchmidtOrthonormalBasis_coe [Fintype ι] {x} (hs : LinearIndependent ℝ (s · x))
    (hs' : ⊤ ≤ Submodule.span ℝ (Set.range (s · x))) :
    (gramSchmidtOrthonormalBasis hs hs' : ι → E x) = (gramSchmidtNormed s · x) := by
  simp [gramSchmidtOrthonormalBasis]

theorem gramSchmidtOrthonormalBasis_apply_of_orthonormal [Fintype ι] {x}
    (hs : Orthonormal ℝ (s · x)) (hs' : ⊤ ≤ Submodule.span ℝ (Set.range (s · x))) :
    (gramSchmidtOrthonormalBasis hs.linearIndependent hs') = (s · x) := by
  simp [gramSchmidtNormed_apply_of_orthonormal hs]

end VectorBundle

/-! The Gram-Schmidt process preserves smoothness of sections -/

variable {n : WithTop ℕ∞}

variable [IsContMDiffRiemannianBundle IB n F E]

section helper

variable {s t : (x : B) → E x} {u : Set B} {x : B}

-- TODO: give a much better name!
lemma contMDiffWithinAt_aux
    (hs : CMDiffAt[u] n (T% s) x) (ht : CMDiffAt[u] n (T% t) x) (hs' : s x ≠ 0) :
    CMDiffAt[u] n (fun x ↦ ⟪s x, t x⟫ / (‖s x‖ ^ 2)) x := by
  have := (hs.inner_bundle ht).smul ((hs.inner_bundle hs).inv₀ (inner_self_ne_zero.mpr hs'))
  apply this.congr
  · intro y hy
    congr
    simp [inner_self_eq_norm_sq_to_K]
  · congr
    rw [← real_inner_self_eq_norm_sq]

lemma contMDiffAt_aux (hs : CMDiffAt n (T% s) x) (ht : CMDiffAt n (T% t) x) (hs' : s x ≠ 0) :
    CMDiffAt n (fun x ↦ ⟪s x, t x⟫ / (‖s x‖ ^ 2)) x := by
  rw [← contMDiffWithinAt_univ] at hs ht ⊢
  exact contMDiffWithinAt_aux hs ht hs'

def ContMDiffWithinAt.orthogonalProjection
    (hs : CMDiffAt[u] n (T% s) x) (ht : CMDiffAt[u] n (T% t) x) (hs' : s x ≠ 0) :
    CMDiffAt[u] n (T% (fun x ↦ (Submodule.span ℝ {s x}).starProjection (t x))) x := by
  simp_rw [Submodule.starProjection_singleton]
  exact (contMDiffWithinAt_aux hs ht hs').smul_section hs

lemma contMDiffWithinAt_inner (hs : CMDiffAt[u] n (T% s) x) (hs' : s x ≠ 0) :
    CMDiffAt[u] n (‖s ·‖) x := by
  let F (x) := ⟪s x, s x⟫
  have aux : CMDiffAt[u] n (Real.sqrt ∘ F) x := by
    have h1 : CMDiffAt[(F '' u)] n (Real.sqrt) (F x) := by
      apply ContMDiffAt.contMDiffWithinAt
      rw [contMDiffAt_iff_contDiffAt]
      exact Real.contDiffAt_sqrt (by simp [F, hs'])
    exact h1.comp x (hs.inner_bundle hs) (Set.mapsTo_image _ u)
  convert aux
  simp [F]

end helper

variable {s : ι → (x : B) → E x} {u : Set B} {x : B} {i : ι}

lemma gramSchmidt_contMDiffWithinAt (hs : ∀ i, CMDiffAt[u] n (T% (s i)) x)
    {i : ι} (hs' : LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic i → ι))) :
    CMDiffAt[u] n (T% (VectorBundle.gramSchmidt s i)) x := by
  -- XXX: this `suffices` used to be just `simp only [VectorBundle.gramSchmidt_def]`
  suffices CMDiffAt[u] n (T% (fun x ↦ s i x - ∑ j ∈ Iio i,
      (ℝ ∙ VectorBundle.gramSchmidt s j x).starProjection (s i x))) x by
    simp_rw [VectorBundle.gramSchmidt]
    apply this.congr
    · intro x hx
      rw [InnerProductSpace.gramSchmidt_def]; simp
    · rw [InnerProductSpace.gramSchmidt_def]; simp
  apply (hs i).sub_section
  apply ContMDiffWithinAt.sum_section
  intro i' hi'
  let aux : { x // x ∈ Set.Iic i' } → { x // x ∈ Set.Iic i } :=
    fun ⟨x, hx⟩ ↦ ⟨x, hx.trans (Finset.mem_Iio.mp hi').le⟩
  have : LinearIndependent ℝ ((fun x_1 ↦ s x_1 x) ∘ @Subtype.val ι fun x ↦ x ∈ Set.Iic i') := by
    apply hs'.comp aux
    intro ⟨x, hx⟩ ⟨x', hx'⟩ h
    simp_all only [Subtype.mk.injEq, aux]
  apply ContMDiffWithinAt.orthogonalProjection (gramSchmidt_contMDiffWithinAt hs this) (hs i)
  apply VectorBundle.gramSchmidt_ne_zero_coe _ _ this
termination_by i
decreasing_by exact (LocallyFiniteOrderBot.finset_mem_Iio i i').mp hi'

lemma gramSchmidt_contMDiffAt (hs : ∀ i, CMDiffAt n (T% (s i)) x)
    (hs' : LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic i → ι))) :
    CMDiffAt n (T% (VectorBundle.gramSchmidt s i)) x :=
  contMDiffWithinAt_univ.mpr <| gramSchmidt_contMDiffWithinAt (fun i ↦ hs i) hs'

lemma gramSchmidt_contMDiffOn (hs : ∀ i, CMDiff[u] n (T% (s i)))
    (hs' : ∀ x ∈ u, LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic i → ι))) :
    CMDiff[u] n (T% (VectorBundle.gramSchmidt s i)) :=
  fun x hx ↦ gramSchmidt_contMDiffWithinAt (fun i ↦ hs i x hx) (hs' _ hx)

lemma gramSchmidt_contMDiff (hs : ∀ i, CMDiff n (T% (s i)))
    (hs' : ∀ x, LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic i → ι))) :
    CMDiff n (T% (VectorBundle.gramSchmidt s i)) :=
  fun x ↦ gramSchmidt_contMDiffAt (fun i ↦ hs i x) (hs' x)

lemma gramSchmidtNormed_contMDiffWithinAt (hs : ∀ i, CMDiffAt[u] n (T% (s i)) x)
    (hs' : LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic i → ι))) :
    CMDiffAt[u] n (T% (VectorBundle.gramSchmidtNormed s i)) x := by
  have : CMDiffAt[u] n (T%
      (fun x ↦ ‖VectorBundle.gramSchmidt s i x‖⁻¹ • VectorBundle.gramSchmidt s i x)) x := by
    refine ContMDiffWithinAt.smul_section ?_ (gramSchmidt_contMDiffWithinAt hs hs')
    refine ContMDiffWithinAt.inv₀ ?_ ?_
    · refine contMDiffWithinAt_inner (gramSchmidt_contMDiffWithinAt hs hs') ?_
      simpa using InnerProductSpace.gramSchmidt_ne_zero_coe i hs'
    · simpa using InnerProductSpace.gramSchmidt_ne_zero_coe i hs'
  exact this.congr (fun y hy ↦ by congr) (by congr)

lemma gramSchmidtNormed_contMDiffAt (hs : ∀ i, CMDiffAt n (T% (s i)) x)
    (hs' : LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic i → ι)))
    : CMDiffAt n (T% (VectorBundle.gramSchmidtNormed s i)) x :=
  contMDiffWithinAt_univ.mpr <| gramSchmidtNormed_contMDiffWithinAt (fun i ↦ hs i) hs'

lemma gramSchmidtNormed_contMDiffOn (hs : ∀ i, CMDiff[u] n (T% (s i)))
    (hs' : ∀ x ∈ u, LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic i → ι))) :
    CMDiff[u] n (T% (VectorBundle.gramSchmidtNormed s i)) :=
  fun x hx ↦ gramSchmidtNormed_contMDiffWithinAt (fun i ↦ hs i x hx) (hs' _ hx)

lemma gramSchmidtNormed_contMDiff (hs : ∀ i, CMDiff n (T% (s i)))
    (hs' : ∀ x, LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic i → ι))) :
    CMDiff n (T% (VectorBundle.gramSchmidtNormed s i)) :=
  fun x ↦ gramSchmidtNormed_contMDiffAt (fun i ↦ hs i x) (hs' x)
