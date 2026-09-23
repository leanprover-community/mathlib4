/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

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
`Mathlib/Analysis/Normed/Field/WithAbs.lean` as `AbsoluteValue.Completion`. The completion of a
number field at an infinite place is then derived in this file, as `InfinitePlace` is a subtype of
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

@[expose] public section
noncomputable section

namespace NumberField.InfinitePlace

open AbsoluteValue.Completion UniformSpace.Completion NumberField.ComplexEmbedding

variable {K : Type*} [Field K] (v : InfinitePlace K)

theorem isometry_embedding : Isometry (v.embedding.comp (WithAbs.equiv v.1).toRingHom) :=
  AddMonoidHomClass.isometry_of_norm _ fun x ↦ by
    simpa using v.norm_embedding_eq (WithAbs.equiv v.1 x)

theorem isometry_embedding_of_isReal (hv : v.IsReal) :
    Isometry ((v.embedding_of_isReal hv).comp (WithAbs.equiv v.1).toRingHom) :=
  AddMonoidHomClass.isometry_of_norm _ fun x ↦ by
    simpa using v.norm_embedding_of_isReal hv (WithAbs.equiv v.1 x)

/-- The completion of a number field at an infinite place. -/
abbrev Completion := v.1.Completion

namespace Completion


lemma norm_coe (x : WithAbs v.1) :
    ‖(x : v.Completion)‖ = v (WithAbs.equiv v.1 x) :=
  UniformSpace.Completion.norm_coe x

instance : CompletableTopField (WithAbs v.1) :=
  v.isometry_embedding.isUniformInducing.completableTopField

example : NormedField v.Completion := inferInstance
example : Algebra K v.Completion := inferInstance
example : IsTopologicalRing v.Completion := inferInstance

/-- The coercion from the rationals to its completion along an infinite place is `Rat.cast`. -/
lemma WithAbs.ratCast_equiv (v : InfinitePlace ℚ) (x : WithAbs v.1) :
    Rat.cast (WithAbs.equiv _ x) = (x : v.Completion) :=
  (eq_ratCast (UniformSpace.Completion.coeRingHom.comp
    (WithAbs.equiv v.1).symm.toRingHom) _).symm

lemma Rat.norm_infinitePlace_completion (v : InfinitePlace ℚ) (x : ℚ) :
    ‖(x : v.Completion)‖ = |x| := by
  rw [← (WithAbs.equiv v.1).apply_symm_apply x, WithAbs.ratCast_equiv,
    norm_coe, (WithAbs.equiv v.1).apply_symm_apply,
    Rat.infinitePlace_apply]

/-- The completion of a number field at an infinite place is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace (v.Completion) :=
  AbsoluteValue.Completion.locallyCompactSpace v.isometry_embedding

/-- The embedding associated to an infinite place extended to an embedding `v.Completion →+* ℂ`. -/
def extensionEmbedding : v.Completion →+* ℂ := v.isometry_embedding.extensionHom

/-- The embedding `K →+* ℝ` associated to a real infinite place extended to `v.Completion →+* ℝ`. -/
def extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) : v.Completion →+* ℝ :=
  (v.isometry_embedding_of_isReal hv).extensionHom

@[simp]
theorem extensionEmbedding_coe (x : WithAbs v.1) :
    extensionEmbedding v x = v.embedding (WithAbs.equiv v.1 x) :=
  v.isometry_embedding.extensionHom_coe _

@[simp]
theorem extensionEmbeddingOfIsReal_coe {v : InfinitePlace K} (hv : IsReal v) (x : WithAbs v.1) :
    extensionEmbeddingOfIsReal hv x = embedding_of_isReal hv (WithAbs.equiv v.1 x) :=
  (v.isometry_embedding_of_isReal hv).extensionHom_coe _

open UniformSpace.Completion in
@[simp]
theorem extensionEmbeddingOfIsReal_apply {v : InfinitePlace K} (hv : IsReal v) (x : v.Completion) :
    (extensionEmbeddingOfIsReal hv x : ℂ) = extensionEmbedding v x := by
  refine UniformSpace.Completion.induction_on x ?_ (by simp)
  exact isClosed_eq (Continuous.comp' (by fun_prop) continuous_extension) continuous_extension

/-- The embedding `v.Completion →+* ℂ` is an isometry. -/
theorem isometry_extensionEmbedding : Isometry (extensionEmbedding v) :=
  v.isometry_embedding.completion_extension

/-- The embedding `v.Completion →+* ℝ` at a real infinite place is an isometry. -/
theorem isometry_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) :
    Isometry (extensionEmbeddingOfIsReal hv) :=
  (v.isometry_embedding_of_isReal hv).completion_extension

/-- The embedding `v.Completion →+* ℂ` has closed image inside `ℂ`. -/
theorem isClosed_image_extensionEmbedding : IsClosed (Set.range (extensionEmbedding v)) :=
  v.isometry_embedding.completion_extension.isClosedEmbedding.isClosed_range

/-- The embedding `v.Completion →+* ℝ` associated to a real infinite place has closed image
inside `ℝ`. -/
theorem isClosed_image_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) :
    IsClosed (Set.range (extensionEmbeddingOfIsReal hv)) :=
  (v.isometry_embedding_of_isReal hv).completion_extension.isClosedEmbedding.isClosed_range

theorem subfield_ne_real_of_isComplex {v : InfinitePlace K} (hv : IsComplex v) :
    (extensionEmbedding v).fieldRange ≠ Complex.ofRealHom.fieldRange := by
  contrapose hv
  simp only [not_isComplex_iff_isReal, isReal_iff]
  ext x
  obtain ⟨r, hr⟩ := hv ▸ RingHom.mem_fieldRange_self (extensionEmbedding v) (x : v.Completion)
  rw [extensionEmbedding_coe, ← WithAbs.equiv_symm_apply, RingEquiv.apply_symm_apply] at hr
  simp [ComplexEmbedding.conjugate_coe_eq, ← hr, Complex.conj_ofReal]

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
    v.Completion ≃+* ℂ := RingEquiv.ofBijective _ (bijective_extensionEmbedding_of_isComplex hv)

@[simp] theorem ringEquivComplexOfIsComplex_apply {v : InfinitePlace K} (hv : IsComplex v)
    (x : v.Completion) : ringEquivComplexOfIsComplex hv x = extensionEmbedding v x := rfl

/-- If the infinite place `v` is complex, then `v.Completion` is isometric to `ℂ`. -/
def isometryEquivComplexOfIsComplex {v : InfinitePlace K} (hv : IsComplex v) :
    v.Completion ≃ᵢ ℂ where
  toEquiv := ringEquivComplexOfIsComplex hv
  isometry_toFun := isometry_extensionEmbedding v

/-- If `v` is a real infinite place, then the embedding `v.Completion →+* ℝ` is surjective. -/
theorem surjective_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) :
    Function.Surjective (extensionEmbeddingOfIsReal hv) := by
  rw [← RingHom.fieldRange_eq_top_iff, ← Real.subfield_eq_of_closed]
  exact isClosed_image_extensionEmbeddingOfIsReal hv

/-- If `v` is a real infinite place, then the embedding `v.Completion →+* ℝ` is bijective. -/
theorem bijective_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) :
    Function.Bijective (extensionEmbeddingOfIsReal hv) :=
  ⟨(extensionEmbeddingOfIsReal hv).injective, surjective_extensionEmbeddingOfIsReal hv⟩

/-- The ring isomorphism `v.Completion ≃+* ℝ`, when `v` is real, given by the bijection
`v.Completion →+* ℝ`. -/
def ringEquivRealOfIsReal {v : InfinitePlace K} (hv : IsReal v) : v.Completion ≃+* ℝ :=
  RingEquiv.ofBijective _ (bijective_extensionEmbeddingOfIsReal hv)

@[simp] theorem ringEquivRealOfIsReal_apply {v : InfinitePlace K} (hv : IsReal v)
    (x : v.Completion) : ringEquivRealOfIsReal hv x = extensionEmbeddingOfIsReal hv x := rfl

/-- If the infinite place `v` is real, then `v.Completion` is isometric to `ℝ`. -/
def isometryEquivRealOfIsReal {v : InfinitePlace K} (hv : IsReal v) : v.Completion ≃ᵢ ℝ where
  toEquiv := ringEquivRealOfIsReal hv
  isometry_toFun := isometry_extensionEmbeddingOfIsReal hv

variable {L : Type*} [Field L] [Algebra K L] (w : InfinitePlace L) {v}
  [Algebra v.Completion w.Completion] [IsScalarTower K v.Completion w.Completion]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem algebraMap_coe (x : WithAbs v.1) :
    algebraMap v.Completion w.Completion x = algebraMap (WithAbs v.1) (WithAbs w.1) x := by
  have := IsScalarTower.algebraMap_apply (WithAbs v.1) v.Completion w.Completion x
  rw [algebraMap_def] at this
  simp [this, algebraMap_def, Algebra.algebraMap_self]

end Completion

section LiesOver

variable {L : Type*} [Field L] [Algebra K L] (w : InfinitePlace L) (v : InfinitePlace K)

namespace Completion

variable [Algebra v.Completion w.Completion] [IsScalarTower K v.Completion w.Completion]

/-- Assume that `w.Completion` forms an algebra over `v.Completion` with continuous scalar action,
such that `IsScalarTower K v.Completion w.Completion`.
If `w.embedding : L →+* ℂ` extends `v.embedding : K →+* ℂ`, then the corresponding embeddings
to completions are also extensions. -/
theorem liesOver_extensionEmbedding [ContinuousSMul v.Completion w.Completion]
    [ComplexEmbedding.LiesOver w.embedding v.embedding] :
    ComplexEmbedding.LiesOver (extensionEmbedding w) (extensionEmbedding v) where
  over := by
    ext x
    induction x using induction_on
    · exact isClosed_eq
        (continuous_extension.comp (continuous_algebraMap v.Completion w.Completion))
        continuous_extension
    · simp [WithAbs.algebraMap_left_apply, WithAbs.algebraMap_right_apply,
        ← ComplexEmbedding.LiesOver.over w.embedding v.embedding]

theorem liesOver_conjugate_extensionEmbedding [ContinuousSMul v.Completion w.Completion]
    [ComplexEmbedding.LiesOver (conjugate w.embedding) v.embedding] :
    ComplexEmbedding.LiesOver (conjugate (extensionEmbedding w)) (extensionEmbedding v) where
  over := by
    ext x
    induction x using induction_on
    · simpa using isClosed_eq (.comp (by fun_prop)
        (continuous_extension.comp <| continuous_algebraMap v.Completion w.Completion))
        continuous_extension
    · simp [WithAbs.algebraMap_left_apply, WithAbs.algebraMap_right_apply,
        ← ComplexEmbedding.LiesOver.over (conjugate w.embedding) v.embedding]

omit [Algebra K L] in
@[simp]
theorem liesOver_extensionEmbedding_apply {φ : w.Completion →+* ℂ}
    [ComplexEmbedding.LiesOver φ (extensionEmbedding v)] {x : v.Completion} :
    φ (algebraMap v.Completion w.Completion x) = (extensionEmbedding v) x := by
  simp_all [liesOver_iff, RingHom.ext_iff]

end Completion

namespace LiesOver

open Completion

variable [w.1.LiesOver v.1]

theorem isometry_algebraMap : Isometry (algebraMap (WithAbs v.1) (WithAbs w.1)) :=
  AddMonoidHomClass.isometry_of_norm _ fun x ↦ by
    simpa [WithAbs.norm_eq_apply_ofAbs] using
      WithAbs.ofAbs_algebraMap v.1 w.1 x ▸ comp_of_comap_eq (comap_eq w v) x.ofAbs

variable {v}

theorem embedding_liesOver_of_isReal (h : v.IsReal) :
    ComplexEmbedding.LiesOver w.embedding v.embedding where
  over := (comap_eq w v ▸ comap_embedding_of_isReal _ (comap_eq w v ▸ h)).symm

variable [Algebra v.Completion w.Completion] [IsScalarTower K v.Completion w.Completion]
  [ContinuousSMul v.Completion w.Completion]

theorem extensionEmbedding_liesOver_of_isReal (h : v.IsReal) :
    ComplexEmbedding.LiesOver (extensionEmbedding w) (extensionEmbedding v) :=
  let := embedding_liesOver_of_isReal w h; liesOver_extensionEmbedding w v

end LiesOver

end NumberField.InfinitePlace.LiesOver
