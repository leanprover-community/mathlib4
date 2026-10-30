/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

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

open NumberField.ComplexEmbedding AbsoluteValue.Completion

variable {K : Type*} [Field K] (v : InfinitePlace K)

theorem isometry_embedding : Isometry (v.embedding.comp (WithAbs.equiv v.1).toRingHom) :=
  AddMonoidHomClass.isometry_of_norm _ fun x ↦ by
    simpa using! v.norm_embedding_eq (WithAbs.equiv v.1 x)

theorem isometry_embedding_of_isReal (hv : v.IsReal) :
    Isometry ((v.embedding_of_isReal hv).comp (WithAbs.equiv v.1).toRingHom) :=
  AddMonoidHomClass.isometry_of_norm _ fun x ↦ by
    simpa using! v.norm_embedding_of_isReal hv (WithAbs.equiv v.1 x)

instance : CompletableTopField (WithAbs v.1) :=
  v.isometry_embedding.isUniformInducing.completableTopField

/-- The completion of a number field at an infinite place. -/
abbrev Completion : Type _ := v.1.Completion

namespace Completion

/-- Coercion of an element of `K` into the completion. -/
instance : Coe K v.Completion where
  coe k := (WithAbs.toAbs v.1 k : v.1.Completion)

section Deprecated

/-! ### Deprecated API from when `InfinitePlace.Completion` was a one-field structure -/

set_option linter.deprecated false

@[deprecated "`v.Completion` is now an abbreviation for `v.1.Completion`" (since := "2026-10-30")]
def ofCompletion {v : InfinitePlace K} (x : v.1.Completion) : v.Completion := x

@[deprecated "`v.Completion` is now an abbreviation for `v.1.Completion`" (since := "2026-10-30")]
def toCompletion {v : InfinitePlace K} (x : v.Completion) : v.1.Completion := x

@[deprecated Equiv.refl (since := "2026-10-30")]
def equivCompletion : v.Completion ≃ v.1.Completion := Equiv.refl _

@[deprecated "`v.Completion` is now an abbreviation for `v.1.Completion`" (since := "2026-10-30")]
theorem equivCompletion_apply (x : v.Completion) : equivCompletion v x = toCompletion x := rfl

@[deprecated "`v.Completion` is now an abbreviation for `v.1.Completion`" (since := "2026-10-30")]
theorem equivCompletion_symm_apply (x : v.1.Completion) :
    (equivCompletion v).symm x = ofCompletion x := rfl

@[deprecated RingEquiv.refl (since := "2026-10-30")]
def equiv : v.Completion ≃+* v.1.Completion := RingEquiv.refl _

@[deprecated "`v.Completion` is now an abbreviation for `v.1.Completion`" (since := "2026-10-30")]
theorem equiv_apply (x : v.Completion) : equiv v x = toCompletion x := rfl

@[deprecated "`v.Completion` is now an abbreviation for `v.1.Completion`" (since := "2026-10-30")]
theorem toCompletion_ofCompletion (x : v.1.Completion) :
    toCompletion (ofCompletion x : v.Completion) = x := rfl

@[deprecated "`v.Completion` is now an abbreviation for `v.1.Completion`" (since := "2026-10-30")]
theorem ofCompletion_toCompletion (x : v.Completion) : ofCompletion (toCompletion x) = x := rfl

@[deprecated "`v.Completion` is now an abbreviation for `v.1.Completion`" (since := "2026-10-30")]
theorem toCompletion_zero : toCompletion (0 : v.Completion) = 0 := rfl

@[deprecated "`v.Completion` is now an abbreviation for `v.1.Completion`" (since := "2026-10-30")]
theorem toCompletion_one : toCompletion (1 : v.Completion) = 1 := rfl

@[deprecated "`v.Completion` is now an abbreviation for `v.1.Completion`" (since := "2026-10-30")]
theorem toCompletion_add (x y : v.Completion) :
    toCompletion (x + y) = toCompletion x + toCompletion y := rfl

@[deprecated "`v.Completion` is now an abbreviation for `v.1.Completion`" (since := "2026-10-30")]
theorem toCompletion_mul (x y : v.Completion) :
    toCompletion (x * y) = toCompletion x * toCompletion y := rfl

@[deprecated "`v.Completion` is now an abbreviation for `v.1.Completion`" (since := "2026-10-30")]
theorem ext {v : InfinitePlace K} {x y : v.Completion} (h : toCompletion x = toCompletion y) :
    x = y := h

@[deprecated Function.surjective_id (since := "2026-10-30")]
theorem toCompletion_surjective : Function.Surjective (toCompletion (v := v)) :=
  Function.surjective_id

@[deprecated Function.surjective_id (since := "2026-10-30")]
theorem ofCompletion_surjective : Function.Surjective (ofCompletion (v := v)) :=
  Function.surjective_id

@[deprecated "`v.Completion` is now an abbreviation for `v.1.Completion`" (since := "2026-10-30")]
theorem norm_toCompletion (x : v.Completion) : ‖toCompletion x‖ = ‖x‖ := rfl

@[deprecated "`v.Completion` is now an abbreviation for `v.1.Completion`" (since := "2026-10-30")]
theorem norm_ofCompletion (x : v.1.Completion) : ‖(ofCompletion x : v.Completion)‖ = ‖x‖ := rfl

@[deprecated isometry_id (since := "2026-10-30")]
theorem isometry_toCompletion : Isometry (toCompletion (v := v)) := isometry_id

@[deprecated IsometryEquiv.refl (since := "2026-10-30")]
def isometryEquivCompletion : v.Completion ≃ᵢ v.1.Completion := IsometryEquiv.refl _

@[deprecated continuous_id (since := "2026-10-30")]
theorem continuous_toCompletion : Continuous (toCompletion (v := v)) := continuous_id

@[deprecated continuous_id (since := "2026-10-30")]
theorem continuous_ofCompletion : Continuous (ofCompletion (v := v)) := continuous_id

@[deprecated "`v.Completion` is now an abbreviation for `v.1.Completion`" (since := "2026-10-30")]
theorem coe_toCompletion (x : WithAbs v.1) :
    toCompletion (x : v.Completion) = (x : v.1.Completion) := rfl

@[deprecated AbsoluteValue.Completion.coe_zero (since := "2026-10-30")]
theorem coe_zero : ((0 : K) : v.Completion) = 0 := by simp

@[deprecated AbsoluteValue.Completion.coe_one (since := "2026-10-30")]
theorem coe_one : ((1 : K) : v.Completion) = 1 := by simp

@[deprecated AbsoluteValue.Completion.coe_add (since := "2026-10-30")]
theorem coe_add (x y : K) : ((x + y : K) : v.Completion) = ↑x + ↑y := by simp

@[deprecated AbsoluteValue.Completion.coe_mul (since := "2026-10-30")]
theorem coe_mul (x y : K) : ((x * y : K) : v.Completion) = ↑x * ↑y := by simp

@[deprecated (since := "2026-10-30")]
alias continuous_coe := AbsoluteValue.Completion.continuous_coe

@[deprecated (since := "2026-10-30")]
alias denseRange_coe := AbsoluteValue.Completion.denseRange_coe

@[deprecated (since := "2026-10-30")]
alias induction_on := AbsoluteValue.Completion.induction_on

@[deprecated "`v.Completion` is now an abbreviation for `v.1.Completion`" (since := "2026-10-30")]
theorem algebraMap_toCompletion (R : Type*) [CommSemiring R] [Algebra R (WithAbs v.1)]
    [UniformContinuousConstSMul R (WithAbs v.1)] (r : R) :
    toCompletion (algebraMap R v.Completion r) = algebraMap R v.1.Completion r := rfl

@[deprecated AbsoluteValue.Completion.algebraMap_def (since := "2026-10-30")]
theorem algebraMap_apply (k : K) :
    algebraMap K v.Completion k = (k : v.Completion) := by
  rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
    Algebra.algebraMap_self_apply]

@[deprecated (since := "2026-10-30")]
alias norm_coe := AbsoluteValue.Completion.norm_coe

end Deprecated

example : NormedField v.Completion := inferInstance
example : Algebra K v.Completion := inferInstance
example : IsTopologicalRing v.Completion := inferInstance

/-- The coercion from the rationals to its completion along an infinite place is `Rat.cast`. -/
lemma WithAbs.ratCast_equiv (v : InfinitePlace ℚ) (x : WithAbs v.1) :
    Rat.cast (WithAbs.equiv _ x) = (x : v.Completion) :=
  (eq_ratCast (AbsoluteValue.Completion.ofCompletion.comp <|
    UniformSpace.Completion.coeRingHom.comp (WithAbs.equiv v.1).symm.toRingHom) _).symm.trans <| by
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
    exact AbsoluteValue.Completion.ofCompletion_coe x

lemma Rat.norm_infinitePlace_completion (v : InfinitePlace ℚ) (x : ℚ) :
    ‖(x : v.Completion)‖ = |x| := by
  rw [← (WithAbs.equiv v.1).apply_symm_apply x, WithAbs.ratCast_equiv,
    AbsoluteValue.Completion.norm_coe]
  exact Rat.infinitePlace_apply v x

/-- The completion of a number field at an infinite place is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace (v.Completion) :=
  AbsoluteValue.Completion.locallyCompactSpace v.isometry_embedding

/-- The embedding associated to an infinite place extended to an embedding `v.Completion →+* ℂ`. -/
def extensionEmbedding : v.Completion →+* ℂ :=
  UniformSpace.Completion.extensionHom _ v.isometry_embedding.continuous |>.comp
    AbsoluteValue.Completion.toCompletion

/-- The embedding `K →+* ℝ` associated to a real infinite place extended to `v.Completion →+* ℝ`. -/
def extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) : v.Completion →+* ℝ :=
  UniformSpace.Completion.extensionHom _ (v.isometry_embedding_of_isReal hv).continuous |>.comp
    AbsoluteValue.Completion.toCompletion

@[simp]
theorem extensionEmbedding_coe (x : WithAbs v.1) :
    extensionEmbedding v x = v.embedding (WithAbs.equiv v.1 x) := by
  simp [extensionEmbedding, UniformSpace.Completion.extensionHom_coe]

@[simp]
theorem extensionEmbeddingOfIsReal_coe {v : InfinitePlace K} (hv : IsReal v) (x : WithAbs v.1) :
    extensionEmbeddingOfIsReal hv x = embedding_of_isReal hv (WithAbs.equiv v.1 x) := by
  simp [extensionEmbeddingOfIsReal, UniformSpace.Completion.extensionHom_coe]

/-- The embedding `v.Completion →+* ℂ` is an isometry. -/
theorem isometry_extensionEmbedding : Isometry (extensionEmbedding v) :=
  v.isometry_embedding.completion_extension.comp
    (AbsoluteValue.Completion.isometry_toCompletion v.1)

/-- The embedding `v.Completion →+* ℝ` at a real infinite place is an isometry. -/
theorem isometry_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) :
    Isometry (extensionEmbeddingOfIsReal hv) :=
  (v.isometry_embedding_of_isReal hv).completion_extension.comp
    (AbsoluteValue.Completion.isometry_toCompletion v.1)

@[simp]
theorem extensionEmbeddingOfIsReal_apply {v : InfinitePlace K} (hv : IsReal v) (x : v.Completion) :
    (extensionEmbeddingOfIsReal hv x : ℂ) = extensionEmbedding v x := by
  induction x using AbsoluteValue.Completion.induction_on with
  | hp =>
    exact isClosed_eq
      (Complex.continuous_ofReal.comp (isometry_extensionEmbeddingOfIsReal hv).continuous)
      (isometry_extensionEmbedding v).continuous
  | ih a => simp

/-- The embedding `v.Completion →+* ℂ` has closed image inside `ℂ`. -/
theorem isClosed_image_extensionEmbedding : IsClosed (Set.range (extensionEmbedding v)) :=
  (isometry_extensionEmbedding v).isClosedEmbedding.isClosed_range

/-- The embedding `v.Completion →+* ℝ` associated to a real infinite place has closed image
inside `ℝ`. -/
theorem isClosed_image_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) :
    IsClosed (Set.range (extensionEmbeddingOfIsReal hv)) :=
  (isometry_extensionEmbeddingOfIsReal hv).isClosedEmbedding.isClosed_range

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

theorem algebraMap_eq_coe (x : WithAbs v.1) :
    algebraMap (WithAbs v.1) w.Completion x = (algebraMap (WithAbs v.1) (WithAbs w.1) x) := by
  rw [WithAbs.algebraMap_left_apply, AbsoluteValue.Completion.algebraMap_def,
    WithAbs.algebraMap_left_apply]

variable [Algebra v.Completion w.Completion] [IsScalarTower K v.Completion w.Completion]

@[simp]
theorem algebraMap_coe (x : WithAbs v.1) :
    algebraMap v.Completion w.Completion x = algebraMap (WithAbs v.1) (WithAbs w.1) x := by
  have := IsScalarTower.algebraMap_apply K v.Completion w.Completion x.ofAbs
  simp only [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
    Algebra.algebraMap_self_apply, WithAbs.toAbs_ofAbs] at this
  rw [← this, WithAbs.algebraMap_left_apply, WithAbs.algebraMap_right_apply]

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
    induction x using AbsoluteValue.Completion.induction_on
    · exact isClosed_eq
        ((isometry_extensionEmbedding w).continuous.comp
          (continuous_algebraMap v.Completion w.Completion))
        (isometry_extensionEmbedding v).continuous
    · simp [WithAbs.algebraMap_left_apply, WithAbs.algebraMap_right_apply,
        ← ComplexEmbedding.LiesOver.over w.embedding v.embedding]

theorem liesOver_conjugate_extensionEmbedding [ContinuousSMul v.Completion w.Completion]
    [ComplexEmbedding.LiesOver (conjugate w.embedding) v.embedding] :
    ComplexEmbedding.LiesOver (conjugate (extensionEmbedding w)) (extensionEmbedding v) where
  over := by
    ext x
    induction x using AbsoluteValue.Completion.induction_on
    · simpa using! isClosed_eq (.comp (by fun_prop)
          ((isometry_extensionEmbedding w).continuous.comp <|
            continuous_algebraMap v.Completion w.Completion))
        (isometry_extensionEmbedding v).continuous
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

variable [w.LiesOver v]

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
