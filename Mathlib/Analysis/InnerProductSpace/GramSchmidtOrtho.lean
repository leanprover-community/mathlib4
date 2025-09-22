/-
Copyright (c) 2022 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao, Kevin Buzzard, Alexander Bentkamp
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Gram-Schmidt Orthogonalization and Orthonormalization

In this file we introduce Gram-Schmidt Orthogonalization and Orthonormalization.

The Gram-Schmidt process takes a set of vectors as input
and outputs a set of orthogonal vectors which have the same span.

## Main results

- `gramSchmidt`: the Gram-Schmidt process
- `gramSchmidt_orthogonal`: `gramSchmidt` produces an orthogonal system of vectors.
- `span_gramSchmidt`: `gramSchmidt` preserves span of vectors.
- `gramSchmidt_linearIndependent`: if the input vectors of `gramSchmidt` are linearly independent,
  then so are the output vectors.
- `gramSchmidt_ne_zero`: if the input vectors of `gramSchmidt` are linearly independent,
  then the output vectors are non-zero.
- `gramSchmidtBasis`: the basis produced by the Gram-Schmidt process when given a basis as input
- `gramSchmidtNormed`:
  the normalized `gramSchmidt` process, i.e each vector in `gramSchmidtNormed` has unit length
- `gramSchmidt_orthonormal`: `gramSchmidtNormed` produces an orthornormal system of vectors.
- `gramSchmidtOrthonormalBasis`: orthonormal basis constructed by the Gram-Schmidt process from
  an indexed set of vectors of the right size
-/


open Finset Submodule Module

variable (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

attribute [local instance] IsWellOrder.toHasWellFounded

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace InnerProductSpace

/-- The Gram-Schmidt process takes a set of vectors as input
and outputs a set of orthogonal vectors which have the same span. -/
noncomputable def gramSchmidt [WellFoundedLT ι] (f : ι → E) (n : ι) : E :=
  f n - ∑ i : Iio n, (𝕜 ∙ gramSchmidt f i).starProjection (f n)
termination_by n
decreasing_by exact mem_Iio.1 i.2

/-- This lemma uses `∑ i in` instead of `∑ i :`. -/
theorem gramSchmidt_def (f : ι → E) (n : ι) :
    gramSchmidt 𝕜 f n = f n - ∑ i ∈ Iio n, (𝕜 ∙ gramSchmidt 𝕜 f i).starProjection (f n) := by
  rw [← sum_attach, attach_eq_univ, gramSchmidt]

theorem gramSchmidt_def' (f : ι → E) (n : ι) :
    f n = gramSchmidt 𝕜 f n + ∑ i ∈ Iio n, (𝕜 ∙ gramSchmidt 𝕜 f i).starProjection (f n) := by
  rw [gramSchmidt_def, sub_add_cancel]

theorem gramSchmidt_def'' (f : ι → E) (n : ι) :
    f n = gramSchmidt 𝕜 f n + ∑ i ∈ Iio n,
      (⟪gramSchmidt 𝕜 f i, f n⟫ / (‖gramSchmidt 𝕜 f i‖ : 𝕜) ^ 2) • gramSchmidt 𝕜 f i := by
  simp only [← map_pow, ← starProjection_singleton, ← gramSchmidt_def' 𝕜 f n]

@[simp]
theorem gramSchmidt_bot {ι : Type*} [LinearOrder ι] [LocallyFiniteOrder ι] [OrderBot ι]
    [WellFoundedLT ι] (f : ι → E) : gramSchmidt 𝕜 f ⊥ = f ⊥ := by
  rw [gramSchmidt_def, Iio_eq_Ico, Finset.Ico_self, Finset.sum_empty, sub_zero]

@[simp]
theorem gramSchmidt_zero (n : ι) : gramSchmidt 𝕜 (0 : ι → E) n = 0 := by rw [gramSchmidt_def]; simp

/-- **Gram-Schmidt Orthogonalisation**:
`gramSchmidt` produces an orthogonal system of vectors. -/
theorem gramSchmidt_orthogonal (f : ι → E) {a b : ι} (h₀ : a ≠ b) :
    ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 := by
  suffices ∀ a b : ι, a < b → ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 by
    rcases h₀.lt_or_gt with ha | hb
    · exact this _ _ ha
    · rw [inner_eq_zero_symm]
      exact this _ _ hb
  clear h₀ a b
  intro a b h₀
  revert a
  apply wellFounded_lt.induction b
  intro b ih a h₀
  simp only [gramSchmidt_def 𝕜 f b, inner_sub_right, inner_sum,
    starProjection_singleton, inner_smul_right]
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_Iio.mpr h₀)]
  · by_cases h : gramSchmidt 𝕜 f a = 0
    · simp only [h, inner_zero_left, zero_div, zero_mul, sub_zero]
    · rw [RCLike.ofReal_pow, ← inner_self_eq_norm_sq_to_K, div_mul_cancel₀, sub_self]
      rwa [inner_self_ne_zero]
  intro i hi hia
  simp only [mul_eq_zero, div_eq_zero_iff]
  right
  rcases hia.lt_or_gt with hia₁ | hia₂
  · rw [inner_eq_zero_symm]
    exact ih a h₀ i hia₁
  · exact ih i (mem_Iio.1 hi) a hia₂

/-- This is another version of `gramSchmidt_orthogonal` using `Pairwise` instead. -/
theorem gramSchmidt_pairwise_orthogonal (f : ι → E) :
    Pairwise fun a b => ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 := fun _ _ =>
  gramSchmidt_orthogonal 𝕜 f

theorem gramSchmidt_inv_triangular (v : ι → E) {i j : ι} (hij : i < j) :
    ⟪gramSchmidt 𝕜 v j, v i⟫ = 0 := by
  rw [gramSchmidt_def'' 𝕜 v]
  simp only [inner_add_right, inner_sum, inner_smul_right]
  set b : ι → E := gramSchmidt 𝕜 v
  convert zero_add (0 : 𝕜)
  · exact gramSchmidt_orthogonal 𝕜 v hij.ne'
  apply Finset.sum_eq_zero
  rintro k hki'
  have hki : k < i := by simpa using hki'
  have : ⟪b j, b k⟫ = 0 := gramSchmidt_orthogonal 𝕜 v (hki.trans hij).ne'
  simp [this]

open Submodule Set Order

theorem mem_span_gramSchmidt (f : ι → E) {i j : ι} (hij : i ≤ j) :
    f i ∈ span 𝕜 (gramSchmidt 𝕜 f '' Set.Iic j) := by
  rw [gramSchmidt_def' 𝕜 f i]
  simp_rw [starProjection_singleton]
  exact Submodule.add_mem _ (subset_span <| mem_image_of_mem _ hij)
    (Submodule.sum_mem _ fun k hk => smul_mem (span 𝕜 (gramSchmidt 𝕜 f '' Set.Iic j)) _ <|
      subset_span <| mem_image_of_mem (gramSchmidt 𝕜 f) <| (Finset.mem_Iio.1 hk).le.trans hij)

theorem gramSchmidt_mem_span (f : ι → E) :
    ∀ {j i}, i ≤ j → gramSchmidt 𝕜 f i ∈ span 𝕜 (f '' Set.Iic j) := by
  intro j i hij
  rw [gramSchmidt_def 𝕜 f i]
  simp_rw [starProjection_singleton]
  refine Submodule.sub_mem _ (subset_span (mem_image_of_mem _ hij))
    (Submodule.sum_mem _ fun k hk => ?_)
  let hkj : k < j := (Finset.mem_Iio.1 hk).trans_le hij
  exact smul_mem _ _
    (span_mono (image_mono <| Set.Iic_subset_Iic.2 hkj.le) <| gramSchmidt_mem_span _ le_rfl)
termination_by j => j

theorem span_gramSchmidt_Iic (f : ι → E) (c : ι) :
    span 𝕜 (gramSchmidt 𝕜 f '' Set.Iic c) = span 𝕜 (f '' Set.Iic c) :=
  span_eq_span (Set.image_subset_iff.2 fun _ => gramSchmidt_mem_span _ _) <|
    Set.image_subset_iff.2 fun _ => mem_span_gramSchmidt _ _

theorem span_gramSchmidt_Iio (f : ι → E) (c : ι) :
    span 𝕜 (gramSchmidt 𝕜 f '' Set.Iio c) = span 𝕜 (f '' Set.Iio c) :=
  span_eq_span (Set.image_subset_iff.2 fun _ hi =>
    span_mono (image_mono <| Iic_subset_Iio.2 hi) <| gramSchmidt_mem_span _ _ le_rfl) <|
      Set.image_subset_iff.2 fun _ hi =>
        span_mono (image_mono <| Iic_subset_Iio.2 hi) <| mem_span_gramSchmidt _ _ le_rfl

/-- `gramSchmidt` preserves span of vectors. -/
theorem span_gramSchmidt (f : ι → E) : span 𝕜 (range (gramSchmidt 𝕜 f)) = span 𝕜 (range f) :=
  span_eq_span (range_subset_iff.2 fun _ =>
    span_mono (image_subset_range _ _) <| gramSchmidt_mem_span _ _ le_rfl) <|
      range_subset_iff.2 fun _ =>
        span_mono (image_subset_range _ _) <| mem_span_gramSchmidt _ _ le_rfl

/-- If given an orthogonal set of vectors, `gramSchmidt` fixes its input. -/
theorem gramSchmidt_of_orthogonal {f : ι → E} (hf : Pairwise (⟪f ·, f ·⟫ = 0)) :
    gramSchmidt 𝕜 f = f := by
  ext i
  rw [gramSchmidt_def]
  trans f i - 0
  · congr
    apply Finset.sum_eq_zero
    intro j hj
    rw [Submodule.starProjection_apply, Submodule.coe_eq_zero]
    suffices span 𝕜 (f '' Set.Iic j) ⟂ 𝕜 ∙ f i by
      apply orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero
      rw [mem_orthogonal_singleton_iff_inner_left, ← mem_orthogonal_singleton_iff_inner_right]
      exact this (gramSchmidt_mem_span 𝕜 f (le_refl j))
    rw [isOrtho_span]
    rintro u ⟨k, hk, rfl⟩ v (rfl : v = f i)
    apply hf
    exact (lt_of_le_of_lt hk (Finset.mem_Iio.mp hj)).ne
  · simp

variable {𝕜}

theorem gramSchmidt_ne_zero_coe {f : ι → E} (n : ι)
    (h₀ : LinearIndependent 𝕜 (f ∘ ((↑) : Set.Iic n → ι))) : gramSchmidt 𝕜 f n ≠ 0 := by
  by_contra h
  have h₁ : f n ∈ span 𝕜 (f '' Set.Iio n) := by
    rw [← span_gramSchmidt_Iio 𝕜 f n, gramSchmidt_def' 𝕜 f, h, zero_add]
    apply Submodule.sum_mem _ _
    intro a ha
    simp only [starProjection_singleton]
    apply Submodule.smul_mem _ _ _
    rw [Finset.mem_Iio] at ha
    exact subset_span ⟨a, ha, by rfl⟩
  have h₂ : (f ∘ ((↑) : Set.Iic n → ι)) ⟨n, le_refl n⟩ ∈
      span 𝕜 (f ∘ ((↑) : Set.Iic n → ι) '' Set.Iio ⟨n, le_refl n⟩) := by
    rw [image_comp]
    simpa using h₁
  apply LinearIndependent.notMem_span_image h₀ _ h₂
  simp only [Set.mem_Iio, lt_self_iff_false, not_false_iff]

/-- If the input vectors of `gramSchmidt` are linearly independent,
then the output vectors are non-zero. -/
theorem gramSchmidt_ne_zero {f : ι → E} (n : ι) (h₀ : LinearIndependent 𝕜 f) :
    gramSchmidt 𝕜 f n ≠ 0 :=
  gramSchmidt_ne_zero_coe _ (LinearIndependent.comp h₀ _ Subtype.coe_injective)

/-- `gramSchmidt` produces a triangular matrix of vectors when given a basis. -/
theorem gramSchmidt_triangular {i j : ι} (hij : i < j) (b : Basis ι 𝕜 E) :
    b.repr (gramSchmidt 𝕜 b i) j = 0 := by
  have : gramSchmidt 𝕜 b i ∈ span 𝕜 (gramSchmidt 𝕜 b '' Set.Iio j) :=
    subset_span ((Set.mem_image _ _ _).2 ⟨i, hij, rfl⟩)
  have : gramSchmidt 𝕜 b i ∈ span 𝕜 (b '' Set.Iio j) := by rwa [← span_gramSchmidt_Iio 𝕜 b j]
  have : ↑(b.repr (gramSchmidt 𝕜 b i)).support ⊆ Set.Iio j :=
    Basis.repr_support_subset_of_mem_span b (Set.Iio j) this
  exact (Finsupp.mem_supported' _ _).1 ((Finsupp.mem_supported 𝕜 _).2 this) j Set.notMem_Iio_self

/-- `gramSchmidt` produces linearly independent vectors when given linearly independent vectors. -/
theorem gramSchmidt_linearIndependent {f : ι → E} (h₀ : LinearIndependent 𝕜 f) :
    LinearIndependent 𝕜 (gramSchmidt 𝕜 f) :=
  linearIndependent_of_ne_zero_of_inner_eq_zero (fun _ => gramSchmidt_ne_zero _ h₀) fun _ _ =>
    gramSchmidt_orthogonal 𝕜 f

/-- When given a basis, `gramSchmidt` produces a basis. -/
noncomputable def gramSchmidtBasis (b : Basis ι 𝕜 E) : Basis ι 𝕜 E :=
  Basis.mk (gramSchmidt_linearIndependent b.linearIndependent)
    ((span_gramSchmidt 𝕜 b).trans b.span_eq).ge

theorem coe_gramSchmidtBasis (b : Basis ι 𝕜 E) : (gramSchmidtBasis b : ι → E) = gramSchmidt 𝕜 b :=
  Basis.coe_mk _ _

variable (𝕜) in
/-- the normalized `gramSchmidt` (i.e each vector in `gramSchmidtNormed` has unit length.) -/
noncomputable def gramSchmidtNormed (f : ι → E) (n : ι) : E :=
  (‖gramSchmidt 𝕜 f n‖ : 𝕜)⁻¹ • gramSchmidt 𝕜 f n

theorem gramSchmidtNormed_unit_length_coe {f : ι → E} (n : ι)
    (h₀ : LinearIndependent 𝕜 (f ∘ ((↑) : Set.Iic n → ι))) : ‖gramSchmidtNormed 𝕜 f n‖ = 1 := by
  simp only [gramSchmidt_ne_zero_coe n h₀, gramSchmidtNormed, norm_smul_inv_norm, Ne,
    not_false_iff]

theorem gramSchmidtNormed_unit_length {f : ι → E} (n : ι) (h₀ : LinearIndependent 𝕜 f) :
    ‖gramSchmidtNormed 𝕜 f n‖ = 1 :=
  gramSchmidtNormed_unit_length_coe _ (LinearIndependent.comp h₀ _ Subtype.coe_injective)

theorem gramSchmidtNormed_unit_length' {f : ι → E} {n : ι} (hn : gramSchmidtNormed 𝕜 f n ≠ 0) :
    ‖gramSchmidtNormed 𝕜 f n‖ = 1 := by
  rw [gramSchmidtNormed] at *
  rw [norm_smul_inv_norm]
  simpa using hn

/-- **Gram-Schmidt Orthonormalization**:
`gramSchmidtNormed` applied to a linearly independent set of vectors produces an orthornormal
system of vectors. -/
theorem gramSchmidtNormed_orthonormal {f : ι → E} (h₀ : LinearIndependent 𝕜 f) :
    Orthonormal 𝕜 (gramSchmidtNormed 𝕜 f) := by
  unfold Orthonormal
  constructor
  · simp only [gramSchmidtNormed_unit_length, h₀, imp_true_iff]
  · intro i j hij
    simp only [gramSchmidtNormed, inner_smul_left, inner_smul_right, RCLike.conj_inv,
      RCLike.conj_ofReal, mul_eq_zero, inv_eq_zero, RCLike.ofReal_eq_zero, norm_eq_zero]
    repeat' right
    exact gramSchmidt_orthogonal 𝕜 f hij

@[deprecated (since := "2025-07-10")] alias gramSchmidt_orthonormal := gramSchmidtNormed_orthonormal

/-- **Gram-Schmidt Orthonormalization**:
`gramSchmidtNormed` produces an orthornormal system of vectors after removing the vectors which
become zero in the process. -/
theorem gramSchmidtNormed_orthonormal' (f : ι → E) :
    Orthonormal 𝕜 fun i : { i | gramSchmidtNormed 𝕜 f i ≠ 0 } => gramSchmidtNormed 𝕜 f i := by
  refine ⟨fun i => gramSchmidtNormed_unit_length' i.prop, ?_⟩
  rintro i j (hij : ¬_)
  rw [Subtype.ext_iff] at hij
  simp [gramSchmidtNormed, inner_smul_left, inner_smul_right, gramSchmidt_orthogonal 𝕜 f hij]

@[deprecated (since := "2025-07-10")]
alias gramSchmidt_orthonormal' := gramSchmidtNormed_orthonormal'

open Submodule Set Order

theorem span_gramSchmidtNormed (f : ι → E) (s : Set ι) :
    span 𝕜 (gramSchmidtNormed 𝕜 f '' s) = span 𝕜 (gramSchmidt 𝕜 f '' s) := by
  refine span_eq_span
    (Set.image_subset_iff.2 fun i hi => smul_mem _ _ <| subset_span <| mem_image_of_mem _ hi)
    (Set.image_subset_iff.2 fun i hi =>
      span_mono (image_mono <| singleton_subset_set_iff.2 hi) ?_)
  simp only [coe_singleton, Set.image_singleton]
  by_cases h : gramSchmidt 𝕜 f i = 0
  · simp [h]
  · refine mem_span_singleton.2 ⟨‖gramSchmidt 𝕜 f i‖, smul_inv_smul₀ ?_ _⟩
    exact mod_cast norm_ne_zero_iff.2 h

theorem span_gramSchmidtNormed_range (f : ι → E) :
    span 𝕜 (range (gramSchmidtNormed 𝕜 f)) = span 𝕜 (range (gramSchmidt 𝕜 f)) := by
  simpa only [image_univ.symm] using span_gramSchmidtNormed f univ

/-- `gramSchmidtNormed` produces linearly independent vectors when given linearly independent
vectors. -/
theorem gramSchmidtNormed_linearIndependent {f : ι → E} (h₀ : LinearIndependent 𝕜 f) :
    LinearIndependent 𝕜 (gramSchmidtNormed 𝕜 f) := by
  unfold gramSchmidtNormed
  have (i : ι) : IsUnit (‖gramSchmidt 𝕜 f i‖⁻¹ : 𝕜) :=
    isUnit_iff_ne_zero.mpr (by simp [gramSchmidt_ne_zero i h₀])
  let w : ι → 𝕜ˣ := fun i ↦ (this i).unit
  apply (gramSchmidt_linearIndependent h₀).units_smul (w := fun i ↦ (this i).unit)

section OrthonormalBasis

variable [Fintype ι] [FiniteDimensional 𝕜 E] (h : finrank 𝕜 E = Fintype.card ι) (f : ι → E)

/-- Given an indexed family `f : ι → E` of vectors in an inner product space `E`, for which the
size of the index set is the dimension of `E`, produce an orthonormal basis for `E` which agrees
with the orthonormal set produced by the Gram-Schmidt orthonormalization process on the elements of
`ι` for which this process gives a nonzero number. -/
noncomputable def gramSchmidtOrthonormalBasis : OrthonormalBasis ι 𝕜 E :=
  ((gramSchmidtNormed_orthonormal' f).exists_orthonormalBasis_extension_of_card_eq
    (v := gramSchmidtNormed 𝕜 f) h).choose

theorem gramSchmidtOrthonormalBasis_apply {f : ι → E} {i : ι} (hi : gramSchmidtNormed 𝕜 f i ≠ 0) :
    gramSchmidtOrthonormalBasis h f i = gramSchmidtNormed 𝕜 f i :=
  ((gramSchmidtNormed_orthonormal' f).exists_orthonormalBasis_extension_of_card_eq
    (v := gramSchmidtNormed 𝕜 f) h).choose_spec i hi

theorem gramSchmidtOrthonormalBasis_apply_of_orthogonal {f : ι → E}
    (hf : Pairwise fun i j => ⟪f i, f j⟫ = 0) {i : ι} (hi : f i ≠ 0) :
    gramSchmidtOrthonormalBasis h f i = (‖f i‖⁻¹ : 𝕜) • f i := by
  have H : gramSchmidtNormed 𝕜 f i = (‖f i‖⁻¹ : 𝕜) • f i := by
    rw [gramSchmidtNormed, gramSchmidt_of_orthogonal 𝕜 hf]
  rw [gramSchmidtOrthonormalBasis_apply h, H]
  simpa [H] using hi

theorem inner_gramSchmidtOrthonormalBasis_eq_zero {f : ι → E} {i : ι}
    (hi : gramSchmidtNormed 𝕜 f i = 0) (j : ι) : ⟪gramSchmidtOrthonormalBasis h f i, f j⟫ = 0 := by
  rw [← mem_orthogonal_singleton_iff_inner_right]
  suffices span 𝕜 (gramSchmidtNormed 𝕜 f '' Set.Iic j) ⟂ 𝕜 ∙ gramSchmidtOrthonormalBasis h f i by
    apply this
    rw [span_gramSchmidtNormed]
    exact mem_span_gramSchmidt 𝕜 f le_rfl
  rw [isOrtho_span]
  rintro u ⟨k, _, rfl⟩ v (rfl : v = _)
  by_cases hk : gramSchmidtNormed 𝕜 f k = 0
  · rw [hk, inner_zero_left]
  rw [← gramSchmidtOrthonormalBasis_apply h hk]
  have : k ≠ i := by
    rintro rfl
    exact hk hi
  exact (gramSchmidtOrthonormalBasis h f).orthonormal.2 this

theorem gramSchmidtOrthonormalBasis_inv_triangular {i j : ι} (hij : i < j) :
    ⟪gramSchmidtOrthonormalBasis h f j, f i⟫ = 0 := by
  by_cases hi : gramSchmidtNormed 𝕜 f j = 0
  · rw [inner_gramSchmidtOrthonormalBasis_eq_zero h hi]
  · simp [gramSchmidtOrthonormalBasis_apply h hi, gramSchmidtNormed, inner_smul_left,
      gramSchmidt_inv_triangular 𝕜 f hij]

theorem gramSchmidtOrthonormalBasis_inv_triangular' {i j : ι} (hij : i < j) :
    (gramSchmidtOrthonormalBasis h f).repr (f i) j = 0 := by
  simpa [OrthonormalBasis.repr_apply_apply] using gramSchmidtOrthonormalBasis_inv_triangular h f hij

/-- Given an indexed family `f : ι → E` of vectors in an inner product space `E`, for which the
size of the index set is the dimension of `E`, the matrix of coefficients of `f` with respect to the
orthonormal basis `gramSchmidtOrthonormalBasis` constructed from `f` is upper-triangular. -/
theorem gramSchmidtOrthonormalBasis_inv_blockTriangular :
    ((gramSchmidtOrthonormalBasis h f).toBasis.toMatrix f).BlockTriangular id := fun _ _ =>
  gramSchmidtOrthonormalBasis_inv_triangular' h f

theorem gramSchmidtOrthonormalBasis_det [DecidableEq ι] :
    (gramSchmidtOrthonormalBasis h f).toBasis.det f =
      ∏ i, ⟪gramSchmidtOrthonormalBasis h f i, f i⟫ := by
  convert Matrix.det_of_upperTriangular (gramSchmidtOrthonormalBasis_inv_blockTriangular h f)
  exact ((gramSchmidtOrthonormalBasis h f).repr_apply_apply (f _) _).symm

end OrthonormalBasis

end InnerProductSpace
