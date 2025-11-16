/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Gram-Schmidt orthonormalization on sections of Riemannian vector bundles

In this file, we provide a version of the Gram-Schmidt orthonormalization procedure
for sections of Riemannian vector bundles: this produces a system of sections which are orthogonal
with respect to the bundle metric. If the initial sections were linearly independent (resp.
formed a basis) at the point, so do the normalized sections.

# TODO
If the bundle metric is `C^k`, then the procedure preserves regularity of sections:
if all sections are `C^k`, so are their normalized versions.

This will be used in `OrthonormalFrame.lean` to convert a local frame to a local orthonormal frame.

## Tags
vector bundle, bundle metric, orthonormal frame, Gram-Schmidt

-/

open Manifold Bundle Module
open scoped ContDiff Topology

-- Let `E` be a topological vector bundle over a topological space `B`,
-- with a continuous Riemannian structure.
-- (Continuity is only used for proving that Gram-Schmidt preserves continuity of sections.)
variable {B F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)]
variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

open Finset Submodule

namespace VectorBundle

/-- The Gram-Schmidt process takes a set of sections as input
and outputs a set of sections which are point-wise orthogonal and have the same span.
Basically, we apply the Gram-Schmidt algorithm point-wise. -/
noncomputable def gramSchmidt (s : ι → (x : B) → E x) (n : ι) : (x : B) → E x :=
  fun x ↦ InnerProductSpace.gramSchmidt ℝ (s · x) n

-- Let `s i` be a collection of sections in `E`, indexed by `ι`.
variable {s : ι → (x : B) → E x}

/-- This lemma uses `∑ i in` instead of `∑ i :`. -/
theorem gramSchmidt_def (s : ι → (x : B) → E x) (n : ι) (x) :
    gramSchmidt s n x =
      s n x - ∑ i ∈ Iio n, (ℝ ∙ gramSchmidt s i x).starProjection (s n x) := by
  rw [gramSchmidt, InnerProductSpace.gramSchmidt_def]
  congr

theorem gramSchmidt_def' (s : ι → (x : B) → E x) (n : ι) (x) :
    s n x = gramSchmidt s n x +
      ∑ i ∈ Iio n, (ℝ ∙ gramSchmidt s i x).starProjection (s n x) := by
  rw [gramSchmidt_def, sub_add_cancel]

theorem gramSchmidt_def'' (s : ι → (x : B) → E x) (n : ι) (x) :
    s n x = gramSchmidt s n x + ∑ i ∈ Iio n,
      (⟪gramSchmidt s i x, s n x⟫ / (‖gramSchmidt s i x‖) ^ 2) • gramSchmidt s i x :=
  InnerProductSpace.gramSchmidt_def'' ℝ (s · x) n

@[simp]
lemma gramSchmidt_apply (s : ι → (x : B) → E x) (n : ι) (x) :
    gramSchmidt s n x = InnerProductSpace.gramSchmidt ℝ (s · x) n := rfl

@[simp]
theorem gramSchmidt_bot {ι : Type*} [LinearOrder ι] [LocallyFiniteOrder ι] [OrderBot ι]
    [WellFoundedLT ι] (s : ι → (x : B) → E x) : gramSchmidt s ⊥ = s ⊥ := by
  ext x
  apply InnerProductSpace.gramSchmidt_bot

@[simp]
theorem gramSchmidt_zero (n : ι) :
    gramSchmidt (0 : ι → (x : B) → E x) n = 0 := by
  ext x
  simpa using InnerProductSpace.gramSchmidt_zero ..

/-- **Gram-Schmidt Orthogonalisation**: `gramSchmidt` produces a point-wise orthogonal system
of sections. -/
theorem gramSchmidt_orthogonal (s : ι → (x : B) → E x) {a b : ι} (h₀ : a ≠ b) (x) :
    ⟪gramSchmidt s a x, gramSchmidt s b x⟫ = 0 :=
  InnerProductSpace.gramSchmidt_orthogonal _ _ h₀

/-- This is another version of `gramSchmidt_orthogonal` using `Pairwise` instead. -/
theorem gramSchmidt_pairwise_orthogonal (s : ι → (x : B) → E x) (x) :
    Pairwise fun a b ↦ ⟪gramSchmidt s a x, gramSchmidt s b x⟫ = 0 :=
  fun _ _ h ↦ gramSchmidt_orthogonal s h _

theorem gramSchmidt_inv_triangular (s : ι → (x : B) → E x) {i j : ι} (hij : i < j) (x) :
    ⟪gramSchmidt s j x, s i x⟫ = 0 :=
  InnerProductSpace.gramSchmidt_inv_triangular _ _ hij

open Set

theorem mem_span_gramSchmidt (s : ι → (x : B) → E x) {i j : ι} (hij : i ≤ j) (x) :
    s i x ∈ span ℝ ((gramSchmidt s · x) '' Set.Iic j) :=
  InnerProductSpace.mem_span_gramSchmidt _ _ hij

theorem gramSchmidt_mem_span (s : ι → (x : B) → E x) (x) :
    ∀ {j i}, i ≤ j → gramSchmidt s i x ∈ span ℝ ((s · x) '' Set.Iic j) :=
  InnerProductSpace.gramSchmidt_mem_span _ _

theorem span_gramSchmidt_Iic (s : ι → (x : B) → E x) (c : ι) (x) :
    span ℝ ((gramSchmidt s · x) '' Set.Iic c) = span ℝ ((s · x) '' Set.Iic c) :=
  InnerProductSpace.span_gramSchmidt_Iic ..

theorem span_gramSchmidt_Iio (s : ι → (x : B) → E x) (c : ι) (x) :
    span ℝ ((gramSchmidt s · x) '' Set.Iio c) = span ℝ ((s · x) '' Set.Iio c) :=
  InnerProductSpace.span_gramSchmidt_Iio _ _ _

/-- `gramSchmidt` preserves the point-wise span of sections. -/
theorem span_gramSchmidt (s : ι → (x : B) → E x) (x) :
    span ℝ (range (gramSchmidt s · x)) = span ℝ (range (s · x)) :=
  InnerProductSpace.span_gramSchmidt ℝ (s · x)

variable {x : B}

/-- If the section values `s i x` are orthogonal, `gramSchmidt` yields the same values at `x`. -/
theorem gramSchmidt_of_orthogonal (hs : Pairwise fun i j ↦ ⟪s i x, s j x⟫ = 0) :
    ∀ i₀, gramSchmidt s i₀ x = s i₀ x := by
  simp_rw [gramSchmidt]
  exact fun i ↦ congrFun (InnerProductSpace.gramSchmidt_of_orthogonal ℝ hs) i

theorem gramSchmidt_ne_zero_coe (n : ι)
    (h₀ : LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic n → ι))) : gramSchmidt s n x ≠ 0 :=
  InnerProductSpace.gramSchmidt_ne_zero_coe _ h₀

/-- If the input sections of `gramSchmidt` are point-wise linearly independent,
the resulting sections are non-zero. -/
theorem gramSchmidt_ne_zero (s : ι → (x : B) → E x) (n : ι) (h₀ : LinearIndependent ℝ (s · x)) :
    gramSchmidt s n x ≠ 0 :=
  InnerProductSpace.gramSchmidt_ne_zero _ h₀

-- For technical reasons, no version of `gramSchmidt_triangular` is provided so far:
-- it would expect a `Basis` (of vectors in `E x`) as input, whereas we would want a hypothesis
-- "the section values `s i x` form a basis" instead.

/-- `gramSchmidt` produces point-wise linearly independent sections when given linearly
independent sections. -/
theorem gramSchmidt_linearIndependent (h₀ : LinearIndependent ℝ (s · x)) :
    LinearIndependent ℝ (gramSchmidt s · x) :=
  InnerProductSpace.gramSchmidt_linearIndependent h₀

/-- When the sections `s` form a basis at `x`, so do the sections `gramSchmidt s`. -/
noncomputable def gramSchmidtBasis (hs : LinearIndependent ℝ (s · x))
    (hs' : ⊤ ≤ span ℝ (Set.range (s · x))) :
    Basis ι ℝ (E x) :=
  Basis.mk (gramSchmidt_linearIndependent hs)
    ((span_gramSchmidt s x).trans (eq_top_iff'.mpr fun _ ↦ hs' trivial)).ge

theorem coe_gramSchmidtBasis (hs : LinearIndependent ℝ (s · x))
    (hs' : ⊤ ≤ span ℝ (Set.range (s · x))) :
    (gramSchmidtBasis hs hs') = (gramSchmidt s · x) :=
  Basis.coe_mk _ _

/-- The normalized `gramSchmidt`, i.e. each resulting section has unit length (or vanishes)
at each point -/
noncomputable def gramSchmidtNormed
    (s : ι → (x : B) → E x) (n : ι) : (x : B) → E x := fun x ↦
  InnerProductSpace.gramSchmidtNormed ℝ (s · x) n

lemma gramSchmidtNormed_coe {n : ι} :
    gramSchmidtNormed s n x = ‖gramSchmidt s n x‖⁻¹ • gramSchmidt s n x := by
  simp [gramSchmidtNormed, InnerProductSpace.gramSchmidtNormed]

theorem gramSchmidtNormed_unit_length_coe {n : ι}
    (h₀ : LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic n → ι))) :
    ‖gramSchmidtNormed s n x‖ = 1 :=
  InnerProductSpace.gramSchmidtNormed_unit_length_coe h₀

theorem gramSchmidtNormed_unit_length {n : ι} (h₀ : LinearIndependent ℝ (s · x)) :
    ‖gramSchmidtNormed s n x‖ = 1 :=
  InnerProductSpace.gramSchmidtNormed_unit_length h₀

theorem gramSchmidtNormed_unit_length' {n : ι} (hn : gramSchmidtNormed s n x ≠ 0) :
    ‖gramSchmidtNormed s n x‖ = 1 :=
  InnerProductSpace.gramSchmidtNormed_unit_length' hn

/-- **Gram-Schmidt Orthonormalization**: `gramSchmidtNormed` applied to a point-wise linearly
independent set of sections produces a point-wise orthornormal system of sections. -/
theorem gramSchmidtNormed_orthonormal (h₀ : LinearIndependent ℝ (s · x)) :
    Orthonormal ℝ (gramSchmidtNormed s · x) :=
  InnerProductSpace.gramSchmidtNormed_orthonormal h₀

/-- **Gram-Schmidt Orthonormalization**: `gramSchmidtNormed` produces a point-wise orthornormal
system of sections after removing the sections which become zero in the process. -/
theorem gramSchmidtNormed_orthonormal' (s : ι → (x : B) → E x) (x) :
    Orthonormal ℝ fun i : { i | gramSchmidtNormed s i x ≠ 0 } => gramSchmidtNormed s i x :=
  InnerProductSpace.gramSchmidtNormed_orthonormal' _

theorem span_gramSchmidtNormed (s : ι → (x : B) → E x) (t : Set ι) :
    span ℝ ((gramSchmidtNormed s · x) '' t) = span ℝ ((gramSchmidt s · x) '' t) :=
  InnerProductSpace.span_gramSchmidtNormed (s · x) t

theorem span_gramSchmidtNormed_range (s : ι → (x : B) → E x) :
    span ℝ (range (gramSchmidtNormed s · x)) = span ℝ (range (gramSchmidt s · x)) := by
  simpa only [image_univ.symm] using span_gramSchmidtNormed ..

/-- `gramSchmidtNormed` applied to linearly independent sections at a point `x` produces
sections which are linearly independent at `x`. -/
theorem gramSchmidtNormed_linearIndependent (h₀ : LinearIndependent ℝ (s · x)) :
    LinearIndependent ℝ (gramSchmidtNormed s · x) := by
  simp [gramSchmidtNormed, InnerProductSpace.gramSchmidtNormed_linearIndependent h₀]

lemma gramSchmidtNormed_apply_of_orthogonal (hs : Pairwise (⟪s · x, s · x⟫ = 0)) {i : ι} :
    gramSchmidtNormed s i x = ‖s i x‖⁻¹ • s i x := by
  simp_rw [gramSchmidtNormed_coe, gramSchmidt_of_orthogonal hs i]

/-- If the section values `s i x` are orthonormal, applying `gramSchmidtNormed` yields the same
values at `x`. -/
lemma gramSchmidtNormed_apply_of_orthonormal (hs : Orthonormal ℝ (s · x)) {i : ι} :
    gramSchmidtNormed s i x = s i x := by
  simp [gramSchmidtNormed_apply_of_orthogonal hs.2, hs.1 i]

/-- When the sections `s` form a basis at `x`, so do the sections `gramSchmidtNormed s`.

Note that `gramSchmidtOrthonormalBasis` proves a strictly stronger statement. -/
noncomputable def gramSchmidtNormedBasis (hs : LinearIndependent ℝ (s · x))
    (hs' : ⊤ ≤ span ℝ (Set.range (s · x))) :
    Basis ι ℝ (E x) :=
  Basis.mk (v := fun i ↦ gramSchmidtNormed s i x) (gramSchmidtNormed_linearIndependent hs)
    (by rw [span_gramSchmidtNormed_range s, span_gramSchmidt s x]; exact hs')

@[simp]
theorem coe_gramSchmidtNormedBasis (hs : LinearIndependent ℝ (s · x))
    (hs' : ⊤ ≤ span ℝ (Set.range (s · x))) :
    (gramSchmidtNormedBasis hs hs' : ι → E x) = (gramSchmidtNormed s · x) :=
  Basis.coe_mk _ _

/-- If the sections `s` form a basis at `x`, the resulting sections form an orthonormal basis
at `x`.

We intentionally choose a different design from `InnerProductSpace.gramSchmidtOrthonormalBasis`,
as this is more convenient to work with in the application to local frames:
in this case, we know the sections form a basis, so linear independence and generating conditions
are easy to apply. Having to prove something about the cardinality of the indexing set would
be more tedious.
As we always obtain a basis, we need not consider the case of some resulting vector being zero.
-/
noncomputable def gramSchmidtOrthonormalBasis [Fintype ι]
    (hs : LinearIndependent ℝ (s · x)) (hs' : ⊤ ≤ span ℝ (Set.range (s · x))) :
    OrthonormalBasis ι ℝ (E x) := by
  apply (gramSchmidtNormedBasis hs hs').toOrthonormalBasis
  simp [gramSchmidtNormed_orthonormal hs]

@[simp]
theorem gramSchmidtOrthonormalBasis_coe [Fintype ι] (hs : LinearIndependent ℝ (s · x))
    (hs' : ⊤ ≤ span ℝ (Set.range (s · x))) :
    gramSchmidtOrthonormalBasis hs hs' = (gramSchmidtNormed s · x) := by
  simp [gramSchmidtOrthonormalBasis]

theorem gramSchmidtOrthonormalBasis_apply_of_orthonormal [Fintype ι]
    (hs : Orthonormal ℝ (s · x)) (hs' : ⊤ ≤ span ℝ (Set.range (s · x))) :
    (gramSchmidtOrthonormalBasis hs.linearIndependent hs') = (s · x) := by
  simp [gramSchmidtNormed_apply_of_orthonormal hs]

end VectorBundle

/-! The Gram-Schmidt process preserves continuity of sections -/
section continuity

variable [TopologicalSpace B]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]

-- TODO: need continuity analogues of ContMDiff.{smul_section,sub_section}

section helper

variable {s t : (x : B) → E x} {u : Set B} {x : B}

-- TODO: give a much better name!
lemma continuousWithinAt_aux
    (hs : ContinuousWithinAt (T% s) u x) (ht : ContinuousWithinAt (T% t) u x) (hs' : s x ≠ 0) :
    ContinuousWithinAt (fun x ↦ ⟪s x, t x⟫ / (‖s x‖ ^ 2)) u x := by
  have := (hs.inner_bundle ht).smul ((hs.inner_bundle hs).inv₀ (inner_self_ne_zero.mpr hs'))
  apply this.congr
  · intro y hy
    congr
    simp [inner_self_eq_norm_sq_to_K]
  · congr
    rw [← real_inner_self_eq_norm_sq]

lemma continuousAt_aux (hs : ContinuousAt (T% s) x) (ht : ContinuousAt (T% t) x) (hs' : s x ≠ 0) :
    ContinuousAt (fun x ↦ ⟪s x, t x⟫ / (‖s x‖ ^ 2)) x := by
  rw [← continuousWithinAt_univ] at hs ht ⊢
  exact continuousWithinAt_aux hs ht hs'

def ContinuousWithinAt.starProjection
    (hs : ContinuousWithinAt (T% s) u x) (ht : ContinuousWithinAt (T% t) u x) (hs' : s x ≠ 0) :
    -- TODO: leaving out the type ascription yields a horrible error message, add test and fix!
    letI S : (x : B) → E x := fun x ↦ (Submodule.span ℝ {s x}).orthogonalProjection (t x);
    ContinuousWithinAt (T% S) u x := by
  simp [Submodule.starProjection_singleton]
  sorry -- missing API! exact (continuousWithinAt_aux hs ht hs').smul_section hs

lemma continuousWithinAt_inner (hs : ContinuousWithinAt (T% s) u x) :
    ContinuousWithinAt (‖s ·‖) u x := by
  convert (Real.continuous_sqrt.continuousWithinAt).comp (hs.inner_bundle hs) (Set.mapsTo_image _ u)
  simp [← norm_eq_sqrt_real_inner]

end helper

variable {s : ι → (x : B) → E x} {u : Set B} {x : B} {i : ι}

attribute [local instance] IsWellOrder.toHasWellFounded

lemma gramSchmidt_continuousWithinAt (hs : ∀ i, ContinuousWithinAt (T% (s i)) u x)
    {i : ι} (hs' : LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic i → ι))) :
    ContinuousWithinAt (T% (VectorBundle.gramSchmidt s i)) u x := by
  sorry /- simp_rw [VectorBundle.gramSchmidt_def]
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
  apply VectorBundle.gramSchmidt_ne_zero_coe _ this -/
-- termination_by i
-- decreasing_by exact (LocallyFiniteOrderBot.finset_mem_Iio i i').mp hi'

lemma gramSchmidt_continuousAt (hs : ∀ i, ContinuousAt (T% (s i)) x)
    (hs' : LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic i → ι))) :
    ContinuousAt (T% (VectorBundle.gramSchmidt s i)) x := by
  simp_rw [← continuousWithinAt_univ] at hs ⊢
  exact gramSchmidt_continuousWithinAt (fun i ↦ hs i) hs'

lemma gramSchmidt_continuousOn (hs : ∀ i, ContinuousOn (T% (s i)) u)
    (hs' : ∀ x ∈ u, LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic i → ι))) :
    ContinuousOn (T% (VectorBundle.gramSchmidt s i)) u :=
  fun x hx ↦ gramSchmidt_continuousWithinAt (fun i ↦ hs i x hx) (hs' _ hx)

lemma gramSchmidt_continuous (hs : ∀ i, Continuous (T% (s i)))
    (hs' : ∀ x, LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic i → ι))) :
    Continuous (T% (VectorBundle.gramSchmidt s i)) := by
  simp_rw [continuous_iff_continuousAt] at hs ⊢
  exact fun x ↦ gramSchmidt_continuousAt (fun i ↦ hs i x) (hs' x)

lemma gramSchmidtNormed_continuousWithinAt (hs : ∀ i, ContinuousWithinAt (T% (s i)) u x)
    (hs' : LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic i → ι))) :
    ContinuousWithinAt (T% (VectorBundle.gramSchmidtNormed s i)) u x := by
  have : ContinuousWithinAt (T%
      (fun x ↦ ‖VectorBundle.gramSchmidt s i x‖⁻¹ • VectorBundle.gramSchmidt s i x)) u x := by
    sorry
  --   refine ContMDiffWithinAt.smul_section ?_ (gramSchmidt_contMDiffWithinAt hs hs')
  --   refine ContMDiffWithinAt.inv₀ ?_ ?_
  --   · refine contMDiffWithinAt_inner (gramSchmidt_contMDiffWithinAt hs hs') ?_
  --     simpa using InnerProductSpace.gramSchmidt_ne_zero_coe i hs'
  --   · simpa using InnerProductSpace.gramSchmidt_ne_zero_coe i hs'
  exact this.congr (fun y hy ↦ by congr) (by congr)

lemma gramSchmidtNormed_continuousAt (hs : ∀ i, ContinuousAt (T% (s i)) x)
    (hs' : LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic i → ι))) :
    ContinuousAt (T% (VectorBundle.gramSchmidtNormed s i)) x := by
  simp_rw [← continuousWithinAt_univ] at hs ⊢
  exact gramSchmidtNormed_continuousWithinAt (fun i ↦ hs i) hs'

lemma gramSchmidtNormed_continuousOn (hs : ∀ i, ContinuousOn (T% (s i)) u)
    (hs' : ∀ x ∈ u, LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic i → ι))) :
    ContinuousOn (T% (VectorBundle.gramSchmidtNormed s i)) u :=
  fun x hx ↦ gramSchmidtNormed_continuousWithinAt (fun i ↦ hs i x hx) (hs' _ hx)

lemma gramSchmidtNormed_continuous (hs : ∀ i, Continuous (T% (s i)))
    (hs' : ∀ x, LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic i → ι))) :
    Continuous (T% (VectorBundle.gramSchmidtNormed s i)) := by
  simp_rw [continuous_iff_continuousAt] at hs ⊢
  exact fun x ↦ gramSchmidtNormed_continuousAt (fun i ↦ hs i x) (hs' x)

end continuity
