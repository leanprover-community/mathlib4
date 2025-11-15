/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-!
# The completion of a number field at an infinite place

This file contains the completion of a number field at an infinite place. This is ultimately
achieved by applying the `UniformSpace.Completion` functor, however each infinite place induces
its own `UniformSpace` instance on the number field, so the inference system cannot automatically
infer these. A common approach to handle the ambiguity that arises from having multiple sources
of instances is through the use of type synonyms. In this case, we use the type synonym `WithAbs`
of a semiring. In particular this type synonym depends on an absolute value, which provides a
systematic way of assigning and inferring instances of the semiring that also depend on an absolute
value. The completion of a field at multiple absolute values is defined in
`Mathlib/Algebra/Ring/WithAbs.lean` as `AbsoluteValue.Completion`. The completion of a number
field at an infinite place is then derived in this file, as `InfinitePlace` is a subtype of
`AbsoluteValue`.

## Main definitions
- `NumberField.InfinitePlace.Completion` : the completion of a number field `K` at an infinite
  place, obtained by completing `K` with respect to the absolute value associated to the infinite
  place.
- `NumberField.InfinitePlace.Completion.extensionEmbedding` : the embedding `v.embedding : K →+* ℂ`
  extended to `v.Completion →+* ℂ`.
- `NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal` : if the infinite place `v`
  is real, then this extends the embedding `v.embedding_of_isReal : K →+* ℝ` to
  `v.Completion →+* ℝ`.
- `NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal` : the ring isomorphism
  `v.Completion ≃+* ℝ` when `v` is a real infinite place; the forward direction of this is
  `extensionEmbeddingOfIsReal`.
- `NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex` : the ring isomorphism
  `v.Completion ≃+* ℂ` when `v` is a complex infinite place; the forward direction of this is
  `extensionEmbedding`.

## Main results
- `NumberField.Completion.locallyCompactSpace` : the completion of a number field at
  an infinite place is locally compact.
- `NumberField.Completion.isometry_extensionEmbedding` : the embedding `v.Completion →+* ℂ` is
  an isometry. See also `isometry_extensionEmbeddingOfIsReal` for the corresponding result on
  `v.Completion →+* ℝ` when `v` is real.
- `NumberField.Completion.bijective_extensionEmbedding_of_isComplex` : the embedding
  `v.Completion →+* ℂ` is bijective when `v` is complex. See also
  `bijective_extensionEmbeddingOfIsReal` for the corresponding result for `v.Completion →+* ℝ`
  when `v` is real.

## Tags
number field, embeddings, infinite places, completion, absolute value
-/
noncomputable section

namespace NumberField.InfinitePlace

open AbsoluteValue.Completion

variable {K : Type*} [Field K] (v : InfinitePlace K)

/-- The completion of a number field at an infinite place. -/
abbrev Completion := v.1.Completion

namespace Completion

instance : NormedField v.Completion :=
  letI := (WithAbs.isUniformInducing_of_comp v.norm_embedding_eq).completableTopField
  UniformSpace.Completion.instNormedFieldOfCompletableTopField (WithAbs v.1)

lemma norm_coe (x : WithAbs v.1) :
    ‖(x : v.Completion)‖ = v (WithAbs.equiv v.1 x) :=
  UniformSpace.Completion.norm_coe x

instance : Algebra K v.Completion :=
  inferInstanceAs <| Algebra (WithAbs v.1) v.1.Completion

/-- The coercion from the rationals to its completion along an infinite place is `Rat.cast`. -/
lemma WithAbs.ratCast_equiv (v : InfinitePlace ℚ) (x : WithAbs v.1) :
    Rat.cast (WithAbs.equiv _ x) = (x : v.Completion) :=
  (eq_ratCast (UniformSpace.Completion.coeRingHom.comp
    (WithAbs.equiv v.1).symm.toRingHom) x).symm

lemma Rat.norm_infinitePlace_completion (v : InfinitePlace ℚ) (x : ℚ) :
    ‖(x : v.Completion)‖ = |x| := by
  rw [← (WithAbs.equiv v.1).apply_symm_apply x, WithAbs.ratCast_equiv,
    norm_coe, (WithAbs.equiv v.1).apply_symm_apply,
    Rat.infinitePlace_apply]

/-- The completion of a number field at an infinite place is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace (v.Completion) :=
  AbsoluteValue.Completion.locallyCompactSpace v.norm_embedding_eq

/-- The embedding associated to an infinite place extended to an embedding `v.Completion →+* ℂ`. -/
def extensionEmbedding : v.Completion →+* ℂ := extensionEmbedding_of_comp v.norm_embedding_eq

/-- The embedding `K →+* ℝ` associated to a real infinite place extended to `v.Completion →+* ℝ`. -/
def extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) : v.Completion →+* ℝ :=
  extensionEmbedding_of_comp <| v.norm_embedding_of_isReal hv

@[simp]
theorem extensionEmbedding_coe (x : K) : extensionEmbedding v x = v.embedding x :=
  extensionEmbedding_of_comp_coe v.norm_embedding_eq x

@[simp]
theorem extensionEmbeddingOfIsReal_coe {v : InfinitePlace K} (hv : IsReal v) (x : K) :
    extensionEmbeddingOfIsReal hv x = embedding_of_isReal hv x :=
  extensionEmbedding_of_comp_coe (v.norm_embedding_of_isReal hv) x

open UniformSpace.Completion in
@[simp]
theorem extensionEmbeddingOfIsReal_apply {v : InfinitePlace K} (hv : IsReal v) (x : v.Completion) :
    (extensionEmbeddingOfIsReal hv x : ℂ) = extensionEmbedding v x := by
  refine UniformSpace.Completion.induction_on x ?_ (fun x => by simp)
  exact isClosed_eq (Continuous.comp' (by fun_prop) continuous_extension) continuous_extension

@[deprecated (since := "2025-09-24")]
alias extensionEmbedding_of_isReal_coe := extensionEmbeddingOfIsReal_coe

/-- The embedding `v.Completion →+* ℂ` is an isometry. -/
theorem isometry_extensionEmbedding : Isometry (extensionEmbedding v) :=
  Isometry.of_dist_eq (extensionEmbedding_dist_eq_of_comp v.norm_embedding_eq)

/-- The embedding `v.Completion →+* ℝ` at a real infinite place is an isometry. -/
theorem isometry_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) :
    Isometry (extensionEmbeddingOfIsReal hv) :=
  Isometry.of_dist_eq (extensionEmbedding_dist_eq_of_comp <| v.norm_embedding_of_isReal hv)

@[deprecated (since := "2025-09-24")]
alias isometry_extensionEmbedding_of_isReal := isometry_extensionEmbeddingOfIsReal

/-- The embedding `v.Completion →+* ℂ` has closed image inside `ℂ`. -/
theorem isClosed_image_extensionEmbedding : IsClosed (Set.range (extensionEmbedding v)) :=
  (isClosedEmbedding_extensionEmbedding_of_comp v.norm_embedding_eq).isClosed_range

/-- The embedding `v.Completion →+* ℝ` associated to a real infinite place has closed image
inside `ℝ`. -/
theorem isClosed_image_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) :
    IsClosed (Set.range (extensionEmbeddingOfIsReal hv)) :=
  (isClosedEmbedding_extensionEmbedding_of_comp <| v.norm_embedding_of_isReal hv).isClosed_range

@[deprecated (since := "2025-09-24")]
alias isClosed_image_extensionEmbedding_of_isReal := isClosed_image_extensionEmbeddingOfIsReal

theorem subfield_ne_real_of_isComplex {v : InfinitePlace K} (hv : IsComplex v) :
    (extensionEmbedding v).fieldRange ≠ Complex.ofRealHom.fieldRange := by
  contrapose! hv
  simp only [not_isComplex_iff_isReal, isReal_iff]
  ext x
  obtain ⟨r, hr⟩ := hv ▸ extensionEmbedding_coe v x ▸ RingHom.mem_fieldRange_self _ _
  simp only [ComplexEmbedding.conjugate_coe_eq, ← hr, Complex.ofRealHom_eq_coe, Complex.conj_ofReal]

/-- If `v` is a complex infinite place, then the embedding `v.Completion →+* ℂ` is surjective. -/
theorem surjective_extensionEmbedding_of_isComplex {v : InfinitePlace K} (hv : IsComplex v) :
    Function.Surjective (extensionEmbedding v) := by
  rw [← RingHom.fieldRange_eq_top_iff]
  exact (Complex.subfield_eq_of_closed <| isClosed_image_extensionEmbedding v).resolve_left <|
    subfield_ne_real_of_isComplex hv

/-- If `v` is a complex infinite place, then the embedding `v.Completion →+* ℂ` is bijective. -/
theorem bijective_extensionEmbedding_of_isComplex {v : InfinitePlace K} (hv : IsComplex v) :
    Function.Bijective (extensionEmbedding v) :=
  ⟨(extensionEmbedding v).injective, surjective_extensionEmbedding_of_isComplex hv⟩

/-- The ring isomorphism `v.Completion ≃+* ℂ`, when `v` is complex, given by the bijection
`v.Completion →+* ℂ`. -/
def ringEquivComplexOfIsComplex {v : InfinitePlace K} (hv : IsComplex v) :
    v.Completion ≃+* ℂ :=
  RingEquiv.ofBijective _ (bijective_extensionEmbedding_of_isComplex hv)

/-- If the infinite place `v` is complex, then `v.Completion` is isometric to `ℂ`. -/
def isometryEquivComplexOfIsComplex {v : InfinitePlace K} (hv : IsComplex v) :
    v.Completion ≃ᵢ ℂ where
  toEquiv := ringEquivComplexOfIsComplex hv
  isometry_toFun := isometry_extensionEmbedding v

@[simp]
theorem ringEquivComplexOfIsComplex_apply {v : InfinitePlace K} (hv : IsComplex v)
    (x : v.Completion) : ringEquivComplexOfIsComplex hv x = extensionEmbedding v x :=
  RingEquiv.ofBijective_apply _ _ _

/-- If `v` is a real infinite place, then the embedding `v.Completion →+* ℝ` is surjective. -/
theorem surjective_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) :
    Function.Surjective (extensionEmbeddingOfIsReal hv) := by
  rw [← RingHom.fieldRange_eq_top_iff, ← Real.subfield_eq_of_closed]
  exact isClosed_image_extensionEmbeddingOfIsReal hv

@[deprecated (since := "2025-09-24")]
alias surjective_extensionEmbedding_of_isReal := surjective_extensionEmbeddingOfIsReal

/-- If `v` is a real infinite place, then the embedding `v.Completion →+* ℝ` is bijective. -/
theorem bijective_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) :
    Function.Bijective (extensionEmbeddingOfIsReal hv) :=
  ⟨(extensionEmbeddingOfIsReal hv).injective, surjective_extensionEmbeddingOfIsReal hv⟩

@[deprecated (since := "2025-09-24")]
alias bijective_extensionEmbedding_of_isReal := bijective_extensionEmbeddingOfIsReal

/-- The ring isomorphism `v.Completion ≃+* ℝ`, when `v` is real, given by the bijection
`v.Completion →+* ℝ`. -/
def ringEquivRealOfIsReal {v : InfinitePlace K} (hv : IsReal v) : v.Completion ≃+* ℝ :=
  RingEquiv.ofBijective _ (bijective_extensionEmbeddingOfIsReal hv)

@[simp]
theorem ringEquivRealOfIsReal_apply {v : InfinitePlace K} (hv : IsReal v) (x : v.Completion) :
    ringEquivRealOfIsReal hv x = extensionEmbeddingOfIsReal hv x :=
  RingEquiv.ofBijective_apply _ _ _

/-- If the infinite place `v` is real, then `v.Completion` is isometric to `ℝ`. -/
def isometryEquivRealOfIsReal {v : InfinitePlace K} (hv : IsReal v) : v.Completion ≃ᵢ ℝ where
  toEquiv := ringEquivRealOfIsReal hv
  isometry_toFun := isometry_extensionEmbeddingOfIsReal hv

end Completion

namespace LiesOver

open Completion

variable {L : Type*} [Field L] [Algebra K L] (w : InfinitePlace L) {v} [w.1.LiesOver v.1]

instance : Algebra v.Completion w.Completion :=
  mapOfComp (L := WithAbs w.1)
    (comp_of_comap_eq (f := algebraMap (WithAbs v.1) (WithAbs w.1)) (LiesOver.comap_eq w v))
      |>.toAlgebra

-- shortcut required because of low priority of GroupWithZero.toNoZeroSMulDivisors
instance [w.1.LiesOver v.1] : NoZeroSMulDivisors v.Completion w.Completion :=
  GroupWithZero.toNoZeroSMulDivisors

@[simp]
theorem algebraMap_coe (x : WithAbs v.1) :
    algebraMap v.Completion w.Completion x = algebraMap (WithAbs v.1) (WithAbs w.1) x := by
  rw [RingHom.algebraMap_toAlgebra, mapOfComp_coe]

open UniformSpace.Completion NumberField.ComplexEmbedding in
theorem extensionEmbedding_algebraMap
    (h : w.embedding.comp (algebraMap K L) = v.embedding) (x : v.Completion) :
    extensionEmbedding w (algebraMap v.Completion w.Completion x) =
      extensionEmbedding v x := by
  induction x using induction_on
  · exact isClosed_eq (Continuous.comp continuous_extension continuous_map) continuous_extension
  · rw [RingHom.algebraMap_toAlgebra, mapOfComp_coe]
    simp only [extensionEmbedding_coe, ← h]
    rfl

open UniformSpace.Completion NumberField.ComplexEmbedding in
theorem conjugate_extensionEmbedding_algebraMap
    (h : (conjugate w.embedding).comp (algebraMap K L) = v.embedding) (x : v.Completion) :
    conjugate (extensionEmbedding w) (algebraMap v.Completion w.Completion x) =
      extensionEmbedding v x := by
  induction x using induction_on
  · exact isClosed_eq (Continuous.comp (by
        change Continuous (starRingEnd ℂ ∘ extensionEmbedding w);
        exact Continuous.comp Complex.continuous_conj continuous_extension) continuous_map)
      continuous_extension
  · rw [RingHom.algebraMap_toAlgebra, mapOfComp_coe]
    simp only [extensionEmbedding_coe, conjugate_coe_eq, ← h]
    rfl

open UniformSpace.Completion in
theorem extensionEmbedding_algebraMap_of_isReal (h : v.IsReal) (x : v.Completion) :
    extensionEmbedding w (algebraMap v.Completion w.Completion x) =
      extensionEmbedding v x :=
  extensionEmbedding_algebraMap w
    (LiesOver.comap_eq w v ▸ comap_embedding_of_isReal _ (LiesOver.comap_eq w v ▸ h) |>.symm) _

end LiesOver

end NumberField.InfinitePlace
