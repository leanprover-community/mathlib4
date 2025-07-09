/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.Elaborators

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
    gramSchmidt s n x =
      s n x - ∑ i ∈ Iio n, (ℝ ∙ gramSchmidt s i x).orthogonalProjection (s n x) := by
  simp only [gramSchmidt, InnerProductSpace.gramSchmidt_def]

variable (s) in
theorem gramSchmidt_def' (n : ι) (x) :
    s n x = gramSchmidt s n x +
      ∑ i ∈ Iio n, (ℝ ∙ gramSchmidt s i x).orthogonalProjection (s n x) := by
  rw [gramSchmidt_def, sub_add_cancel]

variable (s) in
theorem gramSchmidt_def'' (n : ι) (x) :
    s n x = gramSchmidt s n x + ∑ i ∈ Iio n,
      (⟪gramSchmidt s i x, s n x⟫ / (‖gramSchmidt s i x‖) ^ 2) • gramSchmidt s i x := by
  convert gramSchmidt_def' s n x
  rw [orthogonalProjection_singleton, RCLike.ofReal_pow]
  rfl

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
/-- **Gram-Schmidt Orthogonalisation**:
`gramSchmidt` produces an orthogonal system of vectors. -/
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

-- variable (s) in
-- /-- `gramSchmidt` preserves span of vectors. -/
-- theorem span_gramSchmidt (x) : span ℝ (range (gramSchmidt ℝ (s · x))) = span ℝ (range (s · x)) :=
--   span_eq_span (range_subset_iff.2 fun _ ↦
--     span_mono (image_subset_range _ _) <| gramSchmidt_mem_span _ _ le_rfl) <|
--       range_subset_iff.2 fun _ ↦
--         span_mono (image_subset_range _ _) <| mem_span_gramSchmidt _ _ le_rfl

theorem gramSchmidt_of_orthogonal {x} (hs : Pairwise fun i j ↦ ⟪s i x, s j x⟫ = 0) :
    ∀ i₀, gramSchmidt s i₀ x = s i₀ x:= by
  intro i
  rw [gramSchmidt_def]
  trans s i x - 0
  · congr
    apply Finset.sum_eq_zero
    intro j hj
    rw [Submodule.coe_eq_zero]
    suffices span ℝ ((s · x) '' Set.Iic j) ⟂ ℝ ∙ s i x by
      apply orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero
      rw [mem_orthogonal_singleton_iff_inner_left, ← mem_orthogonal_singleton_iff_inner_right]
      exact this <| gramSchmidt_mem_span _ _ le_rfl
    rw [isOrtho_span]
    rintro u ⟨k, hk, rfl⟩ v (rfl : v = s i x)
    apply hs
    exact (lt_of_le_of_lt hk (Finset.mem_Iio.mp hj)).ne
  · simp

theorem gramSchmidt_ne_zero_coe (n : ι) (x)
    (h₀ : LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic n → ι))) : gramSchmidt s n x ≠ 0 :=
  InnerProductSpace.gramSchmidt_ne_zero_coe _ h₀

variable (s) in
/-- If the input vectors of `gramSchmidt` are linearly independent,
then the output vectors are non-zero. -/
theorem gramSchmidt_ne_zero (n : ι) {x} (h₀ : LinearIndependent ℝ (s · x)) :
    gramSchmidt s n x ≠ 0 :=
  InnerProductSpace.gramSchmidt_ne_zero _ h₀

-- not needed at the moment: I want a point-wise version, along the lines
-- "if s i x is a basis, then gramSchmidt s i x is a triangular matrix"
/-
/-- `gramSchmidt` produces a triangular matrix of vectors when given a basis. -/
theorem gramSchmidt_triangular {x} {i j : ι} (hij : i < j) (b : Basis ι ℝ (E x)) :
    b.repr (gramSchmidt b i x) j = 0 := sorry
     b.repr (gramSchmidt b i) j = 0 := by
   have : gramSchmidt ℝ b i ∈ span ℝ (gramSchmidt ℝ b '' Set.Iio j) :=
     subset_span ((Set.mem_image _ _ _).2 ⟨i, hij, rfl⟩)
   have : gramSchmidt ℝ b i ∈ span ℝ (b '' Set.Iio j) := by rwa [← span_gramSchmidt_Iio ℝ b j]
   have : ↑(b.repr (gramSchmidt ℝ b i)).support ⊆ Set.Iio j :=
     Basis.repr_support_subset_of_mem_span b (Set.Iio j) this
   exact (Finsupp.mem_supported' _ _).1 ((Finsupp.mem_supported ℝ _).2 this) j Set.notMem_Iio_self-/

/-- `gramSchmidt` produces linearly independent vectors when given linearly independent vectors. -/
theorem gramSchmidt_linearIndependent {x} (h₀ : LinearIndependent ℝ (s · x)) :
    LinearIndependent ℝ (gramSchmidt s · x) :=
  InnerProductSpace.gramSchmidt_linearIndependent h₀

end VectorBundle

-- When given a local frame, this produces an orthonormal local frame...
-- nothing new to prove; will prove in the frames file

-- Continuity and smoothness.

variable {n : WithTop ℕ∞}

-- TODO: fix pretty-printing of my new elaborators!
set_option linter.style.commandStart false

variable [IsContMDiffRiemannianBundle IB n F E]

def contMDiffWithinAt_myproj {s t : (x : B) → E x} {u : Set B} {x : B}
    (hs : CMDiffAt[u] n (T% s) x) (ht : CMDiffAt[u] n (T% t) x) (hs' : s x ≠ 0) :
    -- TODO: leaving out the type ascription yields a horrible error message, add test and fix!
    letI S : (x : B) → E x := fun x ↦ (Submodule.span ℝ {s x}).orthogonalProjection (t x);
    CMDiffAt[u] n (T% S) x := by
  simp_rw [Submodule.orthogonalProjection_singleton]
  apply ContMDiffWithinAt.smul_section ?_ hs
  suffices ContMDiffWithinAt IB 𝓘(ℝ, ℝ) n (fun x ↦ ⟪s x, t x⟫ / ⟪s x, s x⟫) u x by
    apply this.congr
    · intro y hy
      rw [RCLike.ofReal_pow, ← inner_self_eq_norm_sq_to_K]
    · rw [RCLike.ofReal_pow, ← inner_self_eq_norm_sq_to_K]
  exact (hs.inner_bundle ht).smul ((hs.inner_bundle hs).inv₀ (inner_self_ne_zero.mpr hs'))

lemma gramSchmidt_contMDiffWithinAt {s : ι → (x : B) → E x} (i : ι) {u : Set B} {x : B}
    (hs : ∀ i, CMDiffAt[u] n (T% (s i)) x)
    (hs' : LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic i → ι))) :
    CMDiffAt[u] n (T% (VectorBundle.gramSchmidt s i)) x := by
  simp_rw [VectorBundle.gramSchmidt_def]
  apply (hs i).sub_section
  apply ContMDiffWithinAt.sum_section
  intro i' hi'
  let aux : { x // x ∈ Set.Iic i' } → { x // x ∈ Set.Iic i } :=
    fun ⟨x, hx⟩ ↦ ⟨x, hx.trans (Finset.mem_Iio.mp hi').le⟩
  have : LinearIndependent ℝ ((fun x_1 ↦ s x_1 x) ∘ @Subtype.val ι fun x ↦ x ∈ Set.Iic i') := by
    apply hs'.comp aux
    intro ⟨x, hx⟩ ⟨x', hx'⟩ h
    simp_all only [Subtype.mk.injEq, aux]
  apply contMDiffWithinAt_myproj (gramSchmidt_contMDiffWithinAt i' hs this) (hs i)
  apply VectorBundle.gramSchmidt_ne_zero_coe _ _ this
termination_by i
decreasing_by
  exact (LocallyFiniteOrderBot.finset_mem_Iio i i').mp hi'

lemma gramSchmidt_contMDiffAt {s : ι → (x : B) → E x} (i : ι) {x : B}
    (hs : ∀ i, CMDiffAt n (T% (s i)) x)
    (hs' : LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic i → ι)))
    : CMDiffAt n (T% (VectorBundle.gramSchmidt s i)) x :=
  contMDiffWithinAt_univ.mpr <| gramSchmidt_contMDiffWithinAt _ (fun i ↦ hs i) hs'

lemma gramSchmidt_contMDiffOn {s : ι → (x : B) → E x} (i : ι) (u : Set B)
    (hs : ∀ i, CMDiff[u] n (T% (s i)))
    (hs' : ∀ x ∈ u, LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic i → ι))) :
    CMDiff[u] n (T% (VectorBundle.gramSchmidt s i)) :=
  fun x hx ↦ gramSchmidt_contMDiffWithinAt _ (fun i ↦ hs i x hx) (hs' _ hx)

lemma gramSchmidt_contMDiff {s : ι → (x : B) → E x} (i : ι)
    (hs : ∀ i, CMDiff n (T% (s i)))
    (hs' : ∀ x, LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic i → ι))) :
    CMDiff n (T% (VectorBundle.gramSchmidt s i)) :=
  fun x ↦ gramSchmidt_contMDiffAt _ (fun i ↦ hs i x) (hs' x)
