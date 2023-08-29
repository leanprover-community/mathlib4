/-
Copyright (c) 2022 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao, Kevin Buzzard, Alexander Bentkamp
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Block

#align_import analysis.inner_product_space.gram_schmidt_ortho from "leanprover-community/mathlib"@"1a4df69ca1a9a0e5e26bfe12e2b92814216016d0"

/-!
# Gram-Schmidt Orthogonalization and Orthonormalization

In this file we introduce Gram-Schmidt Orthogonalization and Orthonormalization.

The Gram-Schmidt process takes a set of vectors as input
and outputs a set of orthogonal vectors which have the same span.

## Main results

- `gramSchmidt` : the Gram-Schmidt process
- `gramSchmidt_orthogonal` :
  `gramSchmidt` produces an orthogonal system of vectors.
- `span_gramSchmidt` :
  `gramSchmidt` preserves span of vectors.
- `gramSchmidt_ne_zero` :
  If the input vectors of `gramSchmidt` are linearly independent,
  then the output vectors are non-zero.
- `gramSchmidt_basis` :
  The basis produced by the Gram-Schmidt process when given a basis as input.
- `gramSchmidtNormed` :
  the normalized `gramSchmidt` (i.e each vector in `gramSchmidtNormed` has unit length.)
- `gramSchmidt_orthonormal` :
  `gramSchmidtNormed` produces an orthornormal system of vectors.
- `gramSchmidtOrthonormalBasis`: orthonormal basis constructed by the Gram-Schmidt process from
  an indexed set of vectors of the right size
-/


open scoped BigOperators

open Finset Submodule FiniteDimensional

variable (𝕜 : Type*) {E : Type*} [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [IsWellOrder ι (· < ·)]

attribute [local instance] IsWellOrder.toHasWellFounded

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-- The Gram-Schmidt process takes a set of vectors as input
and outputs a set of orthogonal vectors which have the same span. -/
noncomputable def gramSchmidt [IsWellOrder ι (· < ·)] (f : ι → E) (n : ι) : E :=
  f n - ∑ i : Iio n, orthogonalProjection (𝕜 ∙ gramSchmidt f i) (f n)
termination_by _ n => n
decreasing_by exact mem_Iio.1 i.2
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
#align gram_schmidt gramSchmidt

/-- This lemma uses `∑ i in` instead of `∑ i :`.-/
theorem gramSchmidt_def (f : ι → E) (n : ι) :
    gramSchmidt 𝕜 f n = f n - ∑ i in Iio n, orthogonalProjection (𝕜 ∙ gramSchmidt 𝕜 f i) (f n) := by
  rw [← sum_attach, attach_eq_univ, gramSchmidt]
  -- 🎉 no goals
#align gram_schmidt_def gramSchmidt_def

theorem gramSchmidt_def' (f : ι → E) (n : ι) :
    f n = gramSchmidt 𝕜 f n + ∑ i in Iio n, orthogonalProjection (𝕜 ∙ gramSchmidt 𝕜 f i) (f n) := by
  rw [gramSchmidt_def, sub_add_cancel]
  -- 🎉 no goals
#align gram_schmidt_def' gramSchmidt_def'

theorem gramSchmidt_def'' (f : ι → E) (n : ι) :
    f n = gramSchmidt 𝕜 f n + ∑ i in Iio n,
      (⟪gramSchmidt 𝕜 f i, f n⟫ / (‖gramSchmidt 𝕜 f i‖ : 𝕜) ^ 2) • gramSchmidt 𝕜 f i := by
  convert gramSchmidt_def' 𝕜 f n
  -- ⊢ (inner (gramSchmidt 𝕜 f x✝) (f n) / ↑‖gramSchmidt 𝕜 f x✝‖ ^ 2) • gramSchmidt …
  rw [orthogonalProjection_singleton, IsROrC.ofReal_pow]
  -- 🎉 no goals
#align gram_schmidt_def'' gramSchmidt_def''

@[simp]
theorem gramSchmidt_zero {ι : Type*} [LinearOrder ι] [LocallyFiniteOrder ι] [OrderBot ι]
    [IsWellOrder ι (· < ·)] (f : ι → E) : gramSchmidt 𝕜 f ⊥ = f ⊥ := by
  rw [gramSchmidt_def, Iio_eq_Ico, Finset.Ico_self, Finset.sum_empty, sub_zero]
  -- 🎉 no goals
#align gram_schmidt_zero gramSchmidt_zero

/-- **Gram-Schmidt Orthogonalisation**:
`gramSchmidt` produces an orthogonal system of vectors. -/
theorem gramSchmidt_orthogonal (f : ι → E) {a b : ι} (h₀ : a ≠ b) :
    ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 := by
  suffices ∀ a b : ι, a < b → ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 by
    cases' h₀.lt_or_lt with ha hb
    · exact this _ _ ha
    · rw [inner_eq_zero_symm]
      exact this _ _ hb
  clear h₀ a b
  -- ⊢ ∀ (a b : ι), a < b → inner (gramSchmidt 𝕜 f a) (gramSchmidt 𝕜 f b) = 0
  intro a b h₀
  -- ⊢ inner (gramSchmidt 𝕜 f a) (gramSchmidt 𝕜 f b) = 0
  revert a
  -- ⊢ ∀ (a : ι), a < b → inner (gramSchmidt 𝕜 f a) (gramSchmidt 𝕜 f b) = 0
  apply WellFounded.induction (@IsWellFounded.wf ι (· < ·) _) b
  -- ⊢ ∀ (x : ι), (∀ (y : ι), y < x → ∀ (a : ι), a < y → inner (gramSchmidt 𝕜 f a)  …
  intro b ih a h₀
  -- ⊢ inner (gramSchmidt 𝕜 f a) (gramSchmidt 𝕜 f b) = 0
  simp only [gramSchmidt_def 𝕜 f b, inner_sub_right, inner_sum, orthogonalProjection_singleton,
    inner_smul_right]
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_Iio.mpr h₀)]
  -- ⊢ inner (gramSchmidt 𝕜 f a) (f b) - inner (gramSchmidt 𝕜 f a) (f b) / ↑(‖gramS …
  · by_cases h : gramSchmidt 𝕜 f a = 0
    -- ⊢ inner (gramSchmidt 𝕜 f a) (f b) - inner (gramSchmidt 𝕜 f a) (f b) / ↑(‖gramS …
    · simp only [h, inner_zero_left, zero_div, zero_mul, sub_zero]
      -- 🎉 no goals
    · rw [IsROrC.ofReal_pow, ← inner_self_eq_norm_sq_to_K, div_mul_cancel, sub_self]
      -- ⊢ inner (gramSchmidt 𝕜 f a) (gramSchmidt 𝕜 f a) ≠ 0
      rwa [inner_self_ne_zero]
      -- 🎉 no goals
  intro i hi hia
  -- ⊢ inner (gramSchmidt 𝕜 f i) (f b) / ↑(‖gramSchmidt 𝕜 f i‖ ^ 2) * inner (gramSc …
  simp only [mul_eq_zero, div_eq_zero_iff, inner_self_eq_zero]
  -- ⊢ (inner (gramSchmidt 𝕜 f i) (f b) = 0 ∨ ↑(‖gramSchmidt 𝕜 f i‖ ^ 2) = 0) ∨ inn …
  right
  -- ⊢ inner (gramSchmidt 𝕜 f a) (gramSchmidt 𝕜 f i) = 0
  cases' hia.lt_or_lt with hia₁ hia₂
  -- ⊢ inner (gramSchmidt 𝕜 f a) (gramSchmidt 𝕜 f i) = 0
  · rw [inner_eq_zero_symm]
    -- ⊢ inner (gramSchmidt 𝕜 f i) (gramSchmidt 𝕜 f a) = 0
    exact ih a h₀ i hia₁
    -- 🎉 no goals
  · exact ih i (mem_Iio.1 hi) a hia₂
    -- 🎉 no goals
#align gram_schmidt_orthogonal gramSchmidt_orthogonal

/-- This is another version of `gramSchmidt_orthogonal` using `pairwise` instead. -/
theorem gramSchmidt_pairwise_orthogonal (f : ι → E) :
    Pairwise fun a b => ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 := fun _ _ =>
  gramSchmidt_orthogonal 𝕜 f
#align gram_schmidt_pairwise_orthogonal gramSchmidt_pairwise_orthogonal

theorem gramSchmidt_inv_triangular (v : ι → E) {i j : ι} (hij : i < j) :
    ⟪gramSchmidt 𝕜 v j, v i⟫ = 0 := by
  rw [gramSchmidt_def'' 𝕜 v]
  -- ⊢ inner (gramSchmidt 𝕜 v j) (gramSchmidt 𝕜 v i + ∑ i_1 in Iio i, (inner (gramS …
  simp only [inner_add_right, inner_sum, inner_smul_right]
  -- ⊢ inner (gramSchmidt 𝕜 v j) (gramSchmidt 𝕜 v i) + ∑ x in Iio i, inner (gramSch …
  set b : ι → E := gramSchmidt 𝕜 v
  -- ⊢ inner (b j) (b i) + ∑ x in Iio i, inner (b x) (v i) / ↑‖b x‖ ^ 2 * inner (b  …
  convert zero_add (0 : 𝕜)
  -- ⊢ inner (b j) (b i) = 0
  · exact gramSchmidt_orthogonal 𝕜 v hij.ne'
    -- 🎉 no goals
  apply Finset.sum_eq_zero
  -- ⊢ ∀ (x : ι), x ∈ Iio i → inner (b x) (v i) / ↑‖b x‖ ^ 2 * inner (b j) (b x) = 0
  rintro k hki'
  -- ⊢ inner (b k) (v i) / ↑‖b k‖ ^ 2 * inner (b j) (b k) = 0
  have hki : k < i := by simpa using hki'
  -- ⊢ inner (b k) (v i) / ↑‖b k‖ ^ 2 * inner (b j) (b k) = 0
  have : ⟪b j, b k⟫ = 0 := gramSchmidt_orthogonal 𝕜 v (hki.trans hij).ne'
  -- ⊢ inner (b k) (v i) / ↑‖b k‖ ^ 2 * inner (b j) (b k) = 0
  simp [this]
  -- 🎉 no goals
#align gram_schmidt_inv_triangular gramSchmidt_inv_triangular

open Submodule Set Order

theorem mem_span_gramSchmidt (f : ι → E) {i j : ι} (hij : i ≤ j) :
    f i ∈ span 𝕜 (gramSchmidt 𝕜 f '' Set.Iic j) := by
  rw [gramSchmidt_def' 𝕜 f i]
  -- ⊢ gramSchmidt 𝕜 f i + ∑ i_1 in Finset.Iio i, ↑(↑(orthogonalProjection (span 𝕜  …
  simp_rw [orthogonalProjection_singleton]
  -- ⊢ gramSchmidt 𝕜 f i + ∑ x in Finset.Iio i, (inner (gramSchmidt 𝕜 f x) (f i) /  …
  exact Submodule.add_mem _ (subset_span <| mem_image_of_mem _ hij)
    (Submodule.sum_mem _ fun k hk => smul_mem (span 𝕜 (gramSchmidt 𝕜 f '' Set.Iic j)) _ <|
      subset_span <| mem_image_of_mem (gramSchmidt 𝕜 f) <| (Finset.mem_Iio.1 hk).le.trans hij)
#align mem_span_gram_schmidt mem_span_gramSchmidt

theorem gramSchmidt_mem_span (f : ι → E) :
    ∀ {j i}, i ≤ j → gramSchmidt 𝕜 f i ∈ span 𝕜 (f '' Set.Iic j) := by
  intro j i hij
  -- ⊢ gramSchmidt 𝕜 f i ∈ span 𝕜 (f '' Set.Iic j)
  rw [gramSchmidt_def 𝕜 f i]
  -- ⊢ f i - ∑ i_1 in Finset.Iio i, ↑(↑(orthogonalProjection (span 𝕜 {gramSchmidt 𝕜 …
  simp_rw [orthogonalProjection_singleton]
  -- ⊢ f i - ∑ x in Finset.Iio i, (inner (gramSchmidt 𝕜 f x) (f i) / ↑(‖gramSchmidt …
  refine' Submodule.sub_mem _ (subset_span (mem_image_of_mem _ hij))
    (Submodule.sum_mem _ fun k hk => _)
  let hkj : k < j := (Finset.mem_Iio.1 hk).trans_le hij
  -- ⊢ (inner (gramSchmidt 𝕜 f k) (f i) / ↑(‖gramSchmidt 𝕜 f k‖ ^ 2)) • gramSchmidt …
  exact smul_mem _ _
    (span_mono (image_subset f <| Iic_subset_Iic.2 hkj.le) <| gramSchmidt_mem_span _ le_rfl)
termination_by _ => j
decreasing_by exact hkj
              -- 🎉 no goals
#align gram_schmidt_mem_span gramSchmidt_mem_span

theorem span_gramSchmidt_Iic (f : ι → E) (c : ι) :
    span 𝕜 (gramSchmidt 𝕜 f '' Set.Iic c) = span 𝕜 (f '' Set.Iic c) :=
  span_eq_span (Set.image_subset_iff.2 fun _ => gramSchmidt_mem_span _ _) <|
    Set.image_subset_iff.2 fun _ => mem_span_gramSchmidt _ _
#align span_gram_schmidt_Iic span_gramSchmidt_Iic

theorem span_gramSchmidt_Iio (f : ι → E) (c : ι) :
    span 𝕜 (gramSchmidt 𝕜 f '' Set.Iio c) = span 𝕜 (f '' Set.Iio c) :=
  span_eq_span (Set.image_subset_iff.2 fun _ hi =>
    span_mono (image_subset _ <| Iic_subset_Iio.2 hi) <| gramSchmidt_mem_span _ _ le_rfl) <|
      Set.image_subset_iff.2 fun _ hi =>
        span_mono (image_subset _ <| Iic_subset_Iio.2 hi) <| mem_span_gramSchmidt _ _ le_rfl
#align span_gram_schmidt_Iio span_gramSchmidt_Iio

/-- `gramSchmidt` preserves span of vectors. -/
theorem span_gramSchmidt (f : ι → E) : span 𝕜 (range (gramSchmidt 𝕜 f)) = span 𝕜 (range f) :=
  span_eq_span (range_subset_iff.2 fun _ =>
    span_mono (image_subset_range _ _) <| gramSchmidt_mem_span _ _ le_rfl) <|
      range_subset_iff.2 fun _ =>
        span_mono (image_subset_range _ _) <| mem_span_gramSchmidt _ _ le_rfl
#align span_gram_schmidt span_gramSchmidt

theorem gramSchmidt_of_orthogonal {f : ι → E} (hf : Pairwise fun i j => ⟪f i, f j⟫ = 0) :
    gramSchmidt 𝕜 f = f := by
  ext i
  -- ⊢ gramSchmidt 𝕜 f i = f i
  rw [gramSchmidt_def]
  -- ⊢ f i - ∑ i_1 in Finset.Iio i, ↑(↑(orthogonalProjection (span 𝕜 {gramSchmidt 𝕜 …
  trans f i - 0
  -- ⊢ f i - ∑ i_1 in Finset.Iio i, ↑(↑(orthogonalProjection (span 𝕜 {gramSchmidt 𝕜 …
  · congr
    -- ⊢ ∑ i_1 in Finset.Iio i, ↑(↑(orthogonalProjection (span 𝕜 {gramSchmidt 𝕜 f i_1 …
    apply Finset.sum_eq_zero
    -- ⊢ ∀ (x : ι), x ∈ Finset.Iio i → ↑(↑(orthogonalProjection (span 𝕜 {gramSchmidt  …
    intro j hj
    -- ⊢ ↑(↑(orthogonalProjection (span 𝕜 {gramSchmidt 𝕜 f j})) (f i)) = 0
    rw [coe_eq_zero]
    -- ⊢ ↑(orthogonalProjection (span 𝕜 {gramSchmidt 𝕜 f j})) (f i) = 0
    suffices span 𝕜 (f '' Set.Iic j) ⟂ 𝕜 ∙ f i by
      apply orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero
      rw [mem_orthogonal_singleton_iff_inner_left]
      rw [← mem_orthogonal_singleton_iff_inner_right]
      exact this (gramSchmidt_mem_span 𝕜 f (le_refl j))
    rw [isOrtho_span]
    -- ⊢ ∀ ⦃u : E⦄, u ∈ f '' Set.Iic j → ∀ ⦃v : E⦄, v ∈ {f i} → inner u v = 0
    rintro u ⟨k, hk, rfl⟩ v (rfl : v = f i)
    -- ⊢ inner (f k) (f i) = 0
    apply hf
    -- ⊢ k ≠ i
    exact (lt_of_le_of_lt hk (Finset.mem_Iio.mp hj)).ne
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
#align gram_schmidt_of_orthogonal gramSchmidt_of_orthogonal

variable {𝕜}

theorem gramSchmidt_ne_zero_coe {f : ι → E} (n : ι)
    (h₀ : LinearIndependent 𝕜 (f ∘ ((↑) : Set.Iic n → ι))) : gramSchmidt 𝕜 f n ≠ 0 := by
  by_contra h
  -- ⊢ False
  have h₁ : f n ∈ span 𝕜 (f '' Set.Iio n) := by
    rw [← span_gramSchmidt_Iio 𝕜 f n, gramSchmidt_def' 𝕜 f, h, zero_add]
    apply Submodule.sum_mem _ _
    intro a ha
    simp only [Set.mem_image, Set.mem_Iio, orthogonalProjection_singleton]
    apply Submodule.smul_mem _ _ _
    rw [Finset.mem_Iio] at ha
    refine' subset_span ⟨a, ha, by rfl⟩
  have h₂ : (f ∘ ((↑) : Set.Iic n → ι)) ⟨n, le_refl n⟩ ∈
      span 𝕜 (f ∘ ((↑) : Set.Iic n → ι) '' Set.Iio ⟨n, le_refl n⟩) := by
    rw [image_comp]
    convert h₁ using 3
    ext i
    apply Iff.intro <;> simp -- Porting note: was `simpa using @le_of_lt _ _ i n`
    · intros; simp_all only
    · intros q; use i; exact ⟨q, le_of_lt q, rfl⟩
  apply LinearIndependent.not_mem_span_image h₀ _ h₂
  -- ⊢ ¬{ val := n, property := (_ : n ≤ n) } ∈ Set.Iio { val := n, property := (_  …
  simp only [Set.mem_Iio, lt_self_iff_false, not_false_iff]
  -- 🎉 no goals
#align gram_schmidt_ne_zero_coe gramSchmidt_ne_zero_coe

/-- If the input vectors of `gramSchmidt` are linearly independent,
then the output vectors are non-zero. -/
theorem gramSchmidt_ne_zero {f : ι → E} (n : ι) (h₀ : LinearIndependent 𝕜 f) :
    gramSchmidt 𝕜 f n ≠ 0 :=
  gramSchmidt_ne_zero_coe _ (LinearIndependent.comp h₀ _ Subtype.coe_injective)
#align gram_schmidt_ne_zero gramSchmidt_ne_zero

/-- `gramSchmidt` produces a triangular matrix of vectors when given a basis. -/
theorem gramSchmidt_triangular {i j : ι} (hij : i < j) (b : Basis ι 𝕜 E) :
    b.repr (gramSchmidt 𝕜 b i) j = 0 := by
  have : gramSchmidt 𝕜 b i ∈ span 𝕜 (gramSchmidt 𝕜 b '' Set.Iio j) :=
    subset_span ((Set.mem_image _ _ _).2 ⟨i, hij, rfl⟩)
  have : gramSchmidt 𝕜 b i ∈ span 𝕜 (b '' Set.Iio j) := by rwa [← span_gramSchmidt_Iio 𝕜 b j]
  -- ⊢ ↑(↑b.repr (gramSchmidt 𝕜 (↑b) i)) j = 0
  have : ↑(b.repr (gramSchmidt 𝕜 b i)).support ⊆ Set.Iio j :=
    Basis.repr_support_subset_of_mem_span b (Set.Iio j) this
  exact (Finsupp.mem_supported' _ _).1 ((Finsupp.mem_supported 𝕜 _).2 this) j Set.not_mem_Iio_self
  -- 🎉 no goals
#align gram_schmidt_triangular gramSchmidt_triangular

/-- `gramSchmidt` produces linearly independent vectors when given linearly independent vectors. -/
theorem gramSchmidt_linearIndependent {f : ι → E} (h₀ : LinearIndependent 𝕜 f) :
    LinearIndependent 𝕜 (gramSchmidt 𝕜 f) :=
  linearIndependent_of_ne_zero_of_inner_eq_zero (fun _ => gramSchmidt_ne_zero _ h₀) fun _ _ =>
    gramSchmidt_orthogonal 𝕜 f
#align gram_schmidt_linear_independent gramSchmidt_linearIndependent

/-- When given a basis, `gramSchmidt` produces a basis. -/
noncomputable def gramSchmidtBasis (b : Basis ι 𝕜 E) : Basis ι 𝕜 E :=
  Basis.mk (gramSchmidt_linearIndependent b.linearIndependent)
    ((span_gramSchmidt 𝕜 b).trans b.span_eq).ge
#align gram_schmidt_basis gramSchmidtBasis

theorem coe_gramSchmidtBasis (b : Basis ι 𝕜 E) : (gramSchmidtBasis b : ι → E) = gramSchmidt 𝕜 b :=
  Basis.coe_mk _ _
#align coe_gram_schmidt_basis coe_gramSchmidtBasis

variable (𝕜)

/-- the normalized `gramSchmidt`
(i.e each vector in `gramSchmidtNormed` has unit length.) -/
noncomputable def gramSchmidtNormed (f : ι → E) (n : ι) : E :=
  (‖gramSchmidt 𝕜 f n‖ : 𝕜)⁻¹ • gramSchmidt 𝕜 f n
#align gram_schmidt_normed gramSchmidtNormed

variable {𝕜}

theorem gramSchmidtNormed_unit_length_coe {f : ι → E} (n : ι)
    (h₀ : LinearIndependent 𝕜 (f ∘ ((↑) : Set.Iic n → ι))) : ‖gramSchmidtNormed 𝕜 f n‖ = 1 := by
  simp only [gramSchmidt_ne_zero_coe n h₀, gramSchmidtNormed, norm_smul_inv_norm, Ne.def,
    not_false_iff]
#align gram_schmidt_normed_unit_length_coe gramSchmidtNormed_unit_length_coe

theorem gramSchmidtNormed_unit_length {f : ι → E} (n : ι) (h₀ : LinearIndependent 𝕜 f) :
    ‖gramSchmidtNormed 𝕜 f n‖ = 1 :=
  gramSchmidtNormed_unit_length_coe _ (LinearIndependent.comp h₀ _ Subtype.coe_injective)
#align gram_schmidt_normed_unit_length gramSchmidtNormed_unit_length

theorem gramSchmidtNormed_unit_length' {f : ι → E} {n : ι} (hn : gramSchmidtNormed 𝕜 f n ≠ 0) :
    ‖gramSchmidtNormed 𝕜 f n‖ = 1 := by
  rw [gramSchmidtNormed] at *
  -- ⊢ ‖(↑‖gramSchmidt 𝕜 f n‖)⁻¹ • gramSchmidt 𝕜 f n‖ = 1
  rw [norm_smul_inv_norm]
  -- ⊢ gramSchmidt 𝕜 f n ≠ 0
  simpa using hn
  -- 🎉 no goals
#align gram_schmidt_normed_unit_length' gramSchmidtNormed_unit_length'

/-- **Gram-Schmidt Orthonormalization**:
`gramSchmidtNormed` applied to a linearly independent set of vectors produces an orthornormal
system of vectors. -/
theorem gramSchmidt_orthonormal {f : ι → E} (h₀ : LinearIndependent 𝕜 f) :
    Orthonormal 𝕜 (gramSchmidtNormed 𝕜 f) := by
  unfold Orthonormal
  -- ⊢ (∀ (i : ι), ‖gramSchmidtNormed 𝕜 f i‖ = 1) ∧ ∀ {i j : ι}, i ≠ j → inner (gra …
  constructor
  -- ⊢ ∀ (i : ι), ‖gramSchmidtNormed 𝕜 f i‖ = 1
  · simp only [gramSchmidtNormed_unit_length, h₀, eq_self_iff_true, imp_true_iff]
    -- 🎉 no goals
  · intro i j hij
    -- ⊢ inner (gramSchmidtNormed 𝕜 f i) (gramSchmidtNormed 𝕜 f j) = 0
    simp only [gramSchmidtNormed, inner_smul_left, inner_smul_right, IsROrC.conj_inv,
      IsROrC.conj_ofReal, mul_eq_zero, inv_eq_zero, IsROrC.ofReal_eq_zero, norm_eq_zero]
    repeat' right
    -- ⊢ inner (gramSchmidt 𝕜 f i) (gramSchmidt 𝕜 f j) = 0
    exact gramSchmidt_orthogonal 𝕜 f hij
    -- 🎉 no goals
#align gram_schmidt_orthonormal gramSchmidt_orthonormal

/-- **Gram-Schmidt Orthonormalization**:
`gramSchmidtNormed` produces an orthornormal system of vectors after removing the vectors which
become zero in the process. -/
theorem gramSchmidt_orthonormal' (f : ι → E) :
    Orthonormal 𝕜 fun i : { i | gramSchmidtNormed 𝕜 f i ≠ 0 } => gramSchmidtNormed 𝕜 f i := by
  refine' ⟨fun i => gramSchmidtNormed_unit_length' i.prop, _⟩
  -- ⊢ ∀ {i j : ↑{i | gramSchmidtNormed 𝕜 f i ≠ 0}}, i ≠ j → inner ((fun i => gramS …
  rintro i j (hij : ¬_)
  -- ⊢ inner ((fun i => gramSchmidtNormed 𝕜 f ↑i) i) ((fun i => gramSchmidtNormed 𝕜 …
  rw [Subtype.ext_iff] at hij
  -- ⊢ inner ((fun i => gramSchmidtNormed 𝕜 f ↑i) i) ((fun i => gramSchmidtNormed 𝕜 …
  simp [gramSchmidtNormed, inner_smul_left, inner_smul_right, gramSchmidt_orthogonal 𝕜 f hij]
  -- 🎉 no goals
#align gram_schmidt_orthonormal' gramSchmidt_orthonormal'

theorem span_gramSchmidtNormed (f : ι → E) (s : Set ι) :
    span 𝕜 (gramSchmidtNormed 𝕜 f '' s) = span 𝕜 (gramSchmidt 𝕜 f '' s) := by
  refine' span_eq_span
    (Set.image_subset_iff.2 fun i hi => smul_mem _ _ <| subset_span <| mem_image_of_mem _ hi)
    (Set.image_subset_iff.2 fun i hi =>
      span_mono (image_subset _ <| singleton_subset_set_iff.2 hi) _)
  simp only [coe_singleton, Set.image_singleton]
  -- ⊢ gramSchmidt 𝕜 f i ∈ span 𝕜 {gramSchmidtNormed 𝕜 f i}
  by_cases h : gramSchmidt 𝕜 f i = 0
  -- ⊢ gramSchmidt 𝕜 f i ∈ span 𝕜 {gramSchmidtNormed 𝕜 f i}
  · simp [h]
    -- 🎉 no goals
  · refine' mem_span_singleton.2 ⟨‖gramSchmidt 𝕜 f i‖, smul_inv_smul₀ _ _⟩
    -- ⊢ ↑‖gramSchmidt 𝕜 f i‖ ≠ 0
    exact_mod_cast norm_ne_zero_iff.2 h
    -- 🎉 no goals
#align span_gram_schmidt_normed span_gramSchmidtNormed

theorem span_gramSchmidtNormed_range (f : ι → E) :
    span 𝕜 (range (gramSchmidtNormed 𝕜 f)) = span 𝕜 (range (gramSchmidt 𝕜 f)) := by
  simpa only [image_univ.symm] using span_gramSchmidtNormed f univ
  -- 🎉 no goals
#align span_gram_schmidt_normed_range span_gramSchmidtNormed_range

section OrthonormalBasis

variable [Fintype ι] [FiniteDimensional 𝕜 E] (h : finrank 𝕜 E = Fintype.card ι) (f : ι → E)

/-- Given an indexed family `f : ι → E` of vectors in an inner product space `E`, for which the
size of the index set is the dimension of `E`, produce an orthonormal basis for `E` which agrees
with the orthonormal set produced by the Gram-Schmidt orthonormalization process on the elements of
`ι` for which this process gives a nonzero number. -/
noncomputable def gramSchmidtOrthonormalBasis : OrthonormalBasis ι 𝕜 E :=
  ((gramSchmidt_orthonormal' f).exists_orthonormalBasis_extension_of_card_eq
    (v := gramSchmidtNormed 𝕜 f) h).choose
#align gram_schmidt_orthonormal_basis gramSchmidtOrthonormalBasis

theorem gramSchmidtOrthonormalBasis_apply {f : ι → E} {i : ι} (hi : gramSchmidtNormed 𝕜 f i ≠ 0) :
    gramSchmidtOrthonormalBasis h f i = gramSchmidtNormed 𝕜 f i :=
  ((gramSchmidt_orthonormal' f).exists_orthonormalBasis_extension_of_card_eq
    (v := gramSchmidtNormed 𝕜 f) h).choose_spec i hi
#align gram_schmidt_orthonormal_basis_apply gramSchmidtOrthonormalBasis_apply

theorem gramSchmidtOrthonormalBasis_apply_of_orthogonal {f : ι → E}
    (hf : Pairwise fun i j => ⟪f i, f j⟫ = 0) {i : ι} (hi : f i ≠ 0) :
    gramSchmidtOrthonormalBasis h f i = (‖f i‖⁻¹ : 𝕜) • f i := by
  have H : gramSchmidtNormed 𝕜 f i = (‖f i‖⁻¹ : 𝕜) • f i := by
    rw [gramSchmidtNormed, gramSchmidt_of_orthogonal 𝕜 hf]
  rw [gramSchmidtOrthonormalBasis_apply h, H]
  -- ⊢ gramSchmidtNormed 𝕜 f i ≠ 0
  simpa [H] using hi
  -- 🎉 no goals
#align gram_schmidt_orthonormal_basis_apply_of_orthogonal gramSchmidtOrthonormalBasis_apply_of_orthogonal

theorem inner_gramSchmidtOrthonormalBasis_eq_zero {f : ι → E} {i : ι}
    (hi : gramSchmidtNormed 𝕜 f i = 0) (j : ι) : ⟪gramSchmidtOrthonormalBasis h f i, f j⟫ = 0 := by
  rw [← mem_orthogonal_singleton_iff_inner_right]
  -- ⊢ f j ∈ (span 𝕜 {↑(gramSchmidtOrthonormalBasis h f) i})ᗮ
  suffices span 𝕜 (gramSchmidtNormed 𝕜 f '' Set.Iic j) ⟂ 𝕜 ∙ gramSchmidtOrthonormalBasis h f i by
    apply this
    rw [span_gramSchmidtNormed]
    exact mem_span_gramSchmidt 𝕜 f le_rfl
  rw [isOrtho_span]
  -- ⊢ ∀ ⦃u : E⦄, u ∈ gramSchmidtNormed 𝕜 f '' Set.Iic j → ∀ ⦃v : E⦄, v ∈ {↑(gramSc …
  rintro u ⟨k, _, rfl⟩ v (rfl : v = _)
  -- ⊢ inner (gramSchmidtNormed 𝕜 f k) (↑(gramSchmidtOrthonormalBasis h f) i) = 0
  by_cases hk : gramSchmidtNormed 𝕜 f k = 0
  -- ⊢ inner (gramSchmidtNormed 𝕜 f k) (↑(gramSchmidtOrthonormalBasis h f) i) = 0
  · rw [hk, inner_zero_left]
    -- 🎉 no goals
  rw [← gramSchmidtOrthonormalBasis_apply h hk]
  -- ⊢ inner (↑(gramSchmidtOrthonormalBasis h f) k) (↑(gramSchmidtOrthonormalBasis  …
  have : k ≠ i := by
    rintro rfl
    exact hk hi
  exact (gramSchmidtOrthonormalBasis h f).orthonormal.2 this
  -- 🎉 no goals
#align inner_gram_schmidt_orthonormal_basis_eq_zero inner_gramSchmidtOrthonormalBasis_eq_zero

theorem gramSchmidtOrthonormalBasis_inv_triangular {i j : ι} (hij : i < j) :
    ⟪gramSchmidtOrthonormalBasis h f j, f i⟫ = 0 := by
  by_cases hi : gramSchmidtNormed 𝕜 f j = 0
  -- ⊢ inner (↑(gramSchmidtOrthonormalBasis h f) j) (f i) = 0
  · rw [inner_gramSchmidtOrthonormalBasis_eq_zero h hi]
    -- 🎉 no goals
  · simp [gramSchmidtOrthonormalBasis_apply h hi, gramSchmidtNormed, inner_smul_left,
      gramSchmidt_inv_triangular 𝕜 f hij]
#align gram_schmidt_orthonormal_basis_inv_triangular gramSchmidtOrthonormalBasis_inv_triangular

theorem gramSchmidtOrthonormalBasis_inv_triangular' {i j : ι} (hij : i < j) :
    (gramSchmidtOrthonormalBasis h f).repr (f i) j = 0 := by
  simpa [OrthonormalBasis.repr_apply_apply] using gramSchmidtOrthonormalBasis_inv_triangular h f hij
  -- 🎉 no goals
#align gram_schmidt_orthonormal_basis_inv_triangular' gramSchmidtOrthonormalBasis_inv_triangular'

/-- Given an indexed family `f : ι → E` of vectors in an inner product space `E`, for which the
size of the index set is the dimension of `E`, the matrix of coefficients of `f` with respect to the
orthonormal basis `gramSchmidtOrthonormalBasis` constructed from `f` is upper-triangular. -/
theorem gramSchmidtOrthonormalBasis_inv_blockTriangular :
    ((gramSchmidtOrthonormalBasis h f).toBasis.toMatrix f).BlockTriangular id := fun _ _ =>
  gramSchmidtOrthonormalBasis_inv_triangular' h f
#align gram_schmidt_orthonormal_basis_inv_block_triangular gramSchmidtOrthonormalBasis_inv_blockTriangular

-- Porting note: added a `DecidableEq` argument to help with timeouts in
-- `Mathlib/Analysis/InnerProductSpace/Orientation.lean`
theorem gramSchmidtOrthonormalBasis_det [DecidableEq ι] :
    (gramSchmidtOrthonormalBasis h f).toBasis.det f =
      ∏ i, ⟪gramSchmidtOrthonormalBasis h f i, f i⟫ := by
  convert Matrix.det_of_upperTriangular (gramSchmidtOrthonormalBasis_inv_blockTriangular h f)
  -- ⊢ inner (↑(gramSchmidtOrthonormalBasis h f) x✝) (f x✝) = Basis.toMatrix (Ortho …
  exact ((gramSchmidtOrthonormalBasis h f).repr_apply_apply (f _) _).symm
  -- 🎉 no goals
#align gram_schmidt_orthonormal_basis_det gramSchmidtOrthonormalBasis_det

end OrthonormalBasis
