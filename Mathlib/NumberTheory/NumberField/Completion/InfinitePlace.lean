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
    simpa using! v.norm_embedding_eq (WithAbs.equiv v.1 x)

theorem isometry_embedding_of_isReal (hv : v.IsReal) :
    Isometry ((v.embedding_of_isReal hv).comp (WithAbs.equiv v.1).toRingHom) :=
  AddMonoidHomClass.isometry_of_norm _ fun x ↦ by
    simpa using! v.norm_embedding_of_isReal hv (WithAbs.equiv v.1 x)

instance : CompletableTopField (WithAbs v.1) :=
  v.isometry_embedding.isUniformInducing.completableTopField

/-- The completion of a number field at an infinite place, as a one-field structure wrapping the
completion `v.1.Completion` of `K` at the underlying absolute value. -/
structure Completion where
  /-- Wrap an element of `v.1.Completion` into `v.Completion`. -/
  ofCompletion ::
  /-- The underlying element of `v.1.Completion`. -/
  toCompletion : v.1.Completion

namespace Completion

/-- `Completion.toCompletion` and `Completion.ofCompletion` as an equivalence. -/
@[simps]
def equivCompletion : v.Completion ≃ v.1.Completion where
  toFun := toCompletion
  invFun := ofCompletion
  left_inv _ := rfl
  right_inv _ := rfl

instance : NormedField v.Completion := fast_instance% (equivCompletion v).normedField

/-- `Completion.toCompletion` as a ring isomorphism onto the underlying completion. -/
@[simps! apply]
def equiv : v.Completion ≃+* v.1.Completion where
  toEquiv := equivCompletion v
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp] lemma toCompletion_ofCompletion (x : v.1.Completion) :
    toCompletion (ofCompletion x : v.Completion) = x := rfl
@[simp] lemma ofCompletion_toCompletion (x : v.Completion) :
    ofCompletion x.toCompletion = x := rfl

@[simp] lemma toCompletion_zero : (0 : v.Completion).toCompletion = 0 := rfl
@[simp] lemma toCompletion_one : (1 : v.Completion).toCompletion = 1 := rfl
@[simp] lemma toCompletion_add (x y : v.Completion) :
    (x + y).toCompletion = x.toCompletion + y.toCompletion := rfl
@[simp] lemma toCompletion_mul (x y : v.Completion) :
    (x * y).toCompletion = x.toCompletion * y.toCompletion := rfl

@[ext] theorem ext {v : InfinitePlace K} {x y : v.Completion}
    (h : x.toCompletion = y.toCompletion) : x = y := by
  cases x; cases y; exact congrArg ofCompletion h

theorem toCompletion_surjective : Function.Surjective (toCompletion (v := v)) :=
  (equivCompletion v).surjective

theorem ofCompletion_surjective : Function.Surjective (ofCompletion (v := v)) :=
  (equivCompletion v).symm.surjective

@[simp] lemma norm_toCompletion (x : v.Completion) : ‖x.toCompletion‖ = ‖x‖ := rfl

@[simp] lemma norm_ofCompletion (x : v.1.Completion) :
    ‖(ofCompletion x : v.Completion)‖ = ‖x‖ := rfl

theorem isometry_toCompletion : Isometry (toCompletion (v := v)) :=
  Isometry.of_dist_eq fun _ _ ↦ rfl

/-- `Completion.toCompletion` as an isometry equivalence onto the underlying completion. -/
def isometryEquivCompletion : v.Completion ≃ᵢ v.1.Completion where
  toEquiv := equivCompletion v
  isometry_toFun := isometry_toCompletion v

theorem continuous_toCompletion : Continuous (toCompletion (v := v)) :=
  (isometry_toCompletion v).continuous

theorem continuous_ofCompletion : Continuous (ofCompletion (v := v)) :=
  (isometryEquivCompletion v).symm.continuous

instance : CompleteSpace v.Completion :=
  ((isometry_toCompletion v).isUniformInducing.completeSpace_congr
    (toCompletion_surjective v)).mpr inferInstance

instance : Inhabited v.Completion := ⟨0⟩

/-- Coercion of an element of `WithAbs v.1` into the completion. -/
instance : Coe (WithAbs v.1) v.Completion where
  coe x := ofCompletion (x : v.1.Completion)

/-- Coercion of an element of `K` into the completion. -/
instance : Coe K v.Completion where
  coe k := ofCompletion (k : v.1.Completion)

@[simp] lemma coe_toCompletion (x : WithAbs v.1) :
    (x : v.Completion).toCompletion = (x : v.1.Completion) := rfl

@[norm_cast] lemma coe_zero : ((0 : K) : v.Completion) = 0 := by ext; simp
@[norm_cast] lemma coe_one : ((1 : K) : v.Completion) = 1 := by ext; simp
@[norm_cast] lemma coe_add (x y : K) : ((x + y : K) : v.Completion) = ↑x + ↑y := by
  ext; simp [UniformSpace.Completion.coe_add]
@[norm_cast] lemma coe_mul (x y : K) : ((x * y : K) : v.Completion) = ↑x * ↑y := by
  ext; simp [UniformSpace.Completion.coe_mul]

theorem continuous_coe : Continuous ((↑) : WithAbs v.1 → v.Completion) :=
  (continuous_ofCompletion v).comp (UniformSpace.Completion.continuous_coe _)

theorem denseRange_coe : DenseRange ((↑) : WithAbs v.1 → v.Completion) :=
  (ofCompletion_surjective v).denseRange.comp UniformSpace.Completion.denseRange_coe
    (continuous_ofCompletion v)

/-- Induction on the completion of a number field at an infinite place: a closed property that
holds on the image of `K` holds everywhere. -/
@[elab_as_elim]
theorem induction_on {p : v.Completion → Prop} (x : v.Completion) (hp : IsClosed {x | p x})
    (ih : ∀ a : WithAbs v.1, p a) : p x :=
  UniformSpace.Completion.induction_on (p := fun y ↦ p (ofCompletion y)) x.toCompletion
    (hp.preimage (continuous_ofCompletion v)) ih

section Algebra

variable (R : Type*) [CommSemiring R] [Algebra R (WithAbs v.1)]
  [UniformContinuousConstSMul R (WithAbs v.1)]

instance : Algebra R v.Completion := fast_instance% (equivCompletion v).algebra R

theorem algebraMap_toCompletion (r : R) :
    (algebraMap R v.Completion r).toCompletion = algebraMap R v.1.Completion r := rfl

end Algebra

@[simp] theorem algebraMap_apply (k : K) : algebraMap K v.Completion k = (k : v.Completion) := rfl

lemma norm_coe (x : WithAbs v.1) :
    ‖(x : v.Completion)‖ = v (WithAbs.equiv v.1 x) :=
  UniformSpace.Completion.norm_coe x

example : NormedField v.Completion := inferInstance
example : Algebra K v.Completion := inferInstance
example : IsTopologicalRing v.Completion := inferInstance

/-- The coercion from the rationals to its completion along an infinite place is `Rat.cast`. -/
lemma WithAbs.ratCast_equiv (v : InfinitePlace ℚ) (x : WithAbs v.1) :
    Rat.cast (WithAbs.equiv _ x) = (x : v.Completion) :=
  (eq_ratCast ((equiv v).symm.toRingHom.comp (UniformSpace.Completion.coeRingHom.comp
    (WithAbs.equiv v.1).symm.toRingHom)) _).symm

lemma Rat.norm_infinitePlace_completion (v : InfinitePlace ℚ) (x : ℚ) :
    ‖(x : v.Completion)‖ = |x| := by
  rw [← (WithAbs.equiv v.1).apply_symm_apply x, WithAbs.ratCast_equiv,
    norm_coe, (WithAbs.equiv v.1).apply_symm_apply,
    Rat.infinitePlace_apply]

/-- The completion of a number field at an infinite place is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace (v.Completion) :=
  letI := AbsoluteValue.Completion.locallyCompactSpace v.isometry_embedding
  (isometryEquivCompletion v).toHomeomorph.isClosedEmbedding.locallyCompactSpace

/-- The embedding associated to an infinite place extended to an embedding `v.Completion →+* ℂ`. -/
def extensionEmbedding : v.Completion →+* ℂ :=
  v.isometry_embedding.extensionHom.comp (equiv v).toRingHom

/-- The embedding `K →+* ℝ` associated to a real infinite place extended to `v.Completion →+* ℝ`. -/
def extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) : v.Completion →+* ℝ :=
  (v.isometry_embedding_of_isReal hv).extensionHom.comp (equiv v).toRingHom

@[simp]
theorem extensionEmbedding_coe (x : WithAbs v.1) :
    extensionEmbedding v x = v.embedding (WithAbs.equiv v.1 x) :=
  v.isometry_embedding.extensionHom_coe _

@[simp]
theorem extensionEmbeddingOfIsReal_coe {v : InfinitePlace K} (hv : IsReal v) (x : WithAbs v.1) :
    extensionEmbeddingOfIsReal hv x = embedding_of_isReal hv (WithAbs.equiv v.1 x) :=
  (v.isometry_embedding_of_isReal hv).extensionHom_coe _

/-- The embedding `v.Completion →+* ℂ` is an isometry. -/
theorem isometry_extensionEmbedding : Isometry (extensionEmbedding v) :=
  v.isometry_embedding.completion_extension.comp (isometry_toCompletion v)

/-- The embedding `v.Completion →+* ℝ` at a real infinite place is an isometry. -/
theorem isometry_extensionEmbeddingOfIsReal {v : InfinitePlace K} (hv : IsReal v) :
    Isometry (extensionEmbeddingOfIsReal hv) :=
  (v.isometry_embedding_of_isReal hv).completion_extension.comp (isometry_toCompletion v)

@[simp]
theorem extensionEmbeddingOfIsReal_apply {v : InfinitePlace K} (hv : IsReal v) (x : v.Completion) :
    (extensionEmbeddingOfIsReal hv x : ℂ) = extensionEmbedding v x := by
  induction x using induction_on with
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
  apply ext
  rw [algebraMap_toCompletion]
  exact UniformSpace.Completion.algebraMap_def (WithAbs w.1) (WithAbs v.1) x

variable [Algebra v.Completion w.Completion] [IsScalarTower K v.Completion w.Completion]

@[simp]
theorem algebraMap_coe (x : WithAbs v.1) :
    algebraMap v.Completion w.Completion x = algebraMap (WithAbs v.1) (WithAbs w.1) x :=
  (IsScalarTower.algebraMap_apply (WithAbs v.1) v.Completion w.Completion x).symm.trans
    (algebraMap_eq_coe w x)

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
    induction x using induction_on
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
