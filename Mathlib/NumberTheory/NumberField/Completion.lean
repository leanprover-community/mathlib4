/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Analysis.NormedSpace.Completion
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Embeddings
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.Instances.Real

/-!
# Completions of a number field at an infinite place

This file contains the completion of a number field at its infinite places.

We first define abstractly the uniform structure associated to a (semi)ring with an associated
absolute value, derived from a `NormedRing` instance. Let `v` be an infinite place, to which
is associated an absolute value; the abstract uniform structure of this absolute value is
used to define a `NormedField` instance, and therefore a uniform structure. We complete `K`
at `v` using the `UniformSpace.Completion` functor with respect to this uniform structure to
obtain `v.completion`.

The embedding `v.embedding : K →+* ℂ` associated to an infinite place enjoys useful properties
within the uniform structure defined by `v`; namely, it is a uniform embedding and an isometry.
This is because the absolute value associated to `v` factors through `v.embedding`. This allows
us to show that the completion of `K` at an infinite place is locally compact. Moreover, we can
extend `v.embedding` to a embedding `v.completion →+* ℂ`. We show that if `v` is real (i.e.,
`v.embedding (K) ⊆ ℝ`) then the extended embedding gives an isomorphism `v.completion ≃+* ℝ`,
else the extended embedding gives an isomorphism `v.completion ≃+* ℂ`.

## Main definitions
 - `WithAbs` : type synonym equipping a semiring with an absolute value.
 - `AbsoluteValue.completion` : the uniform space completion of a field `K` equipped with real
  absolute value.
 - `NumberField.InfinitePlace.completion` : the completion of a number field `K` at an infinite
  place, obtained by completing `K` with respect to the absolute value associated to the infinite
  place.
 - `NumberField.InfinitePlace.Completion.extensionEmbedding` : the embedding `v.embedding : K →+* ℂ`
  extended to `v.completion →+* ℂ`.
 - `NumberField.InfinitePlace.Completion.extensionEmbedding_of_isReal` : if the infinite place `v`
  is real, then this extends the embedding `v.embedding_of_isReal : K →+* ℝ` to
  `v.completion →+* ℝ`.
 - `NumberField.InfinitePlace.Completion.equivReal_of_isReal` : the ring isomorphism
  `v.completion ≃+* ℝ` when `v` is a real infinite place; the forward direction of this is
  `extensionEmbedding_of_isReal`.
 - `NumberField.InfinitePlace.Completion.equivComplex_of_isComplex` : the ring isomorphism
  `v.completion ≃+* ℂ` when `v` is a complex infinite place; the forward direction of this is
  `extensionEmbedding`.

## Main results
 - `NumberField.Completion.locallyCompactSpace` : the completion of a number field at
  an infinite place is locally compact.
 - `NumberField.Completion.isometry_extensionEmbedding` : the embedding `v.completion →+* ℂ` is
  an isometry. See also `isometry_extensionEmbedding_of_isReal` for the corresponding result on
  `v.completion →+* ℝ` when `v` is real.
 - `NumberField.Completion.bijective_extensionEmbedding_of_isComplex` : the embedding
  `v.completion →+* ℂ` is bijective when `v` is complex. See also
  `bijective_extensionEmebdding_of_isReal` for the corresponding result for `v.completion →+* ℝ`
  when `v` is real.

## Tags
number field, embeddings, infinite places, completion
-/
noncomputable section

/-- Type synonym equipping a semiring with an absolute value. -/
def WithAbs {R S} [Semiring R] [OrderedSemiring S] : AbsoluteValue R S → Type _ := fun _ => R

namespace WithAbs

instance {R} [Ring R] (v : AbsoluteValue R ℝ) : NormedRing (WithAbs v) where
  toRing := inferInstanceAs (Ring R)
  norm := v
  dist_eq _ _ := rfl
  dist_self x := by simp only [sub_self, MulHom.toFun_eq_coe, AbsoluteValue.coe_toMulHom, map_zero]
  dist_comm := v.map_sub
  dist_triangle := v.sub_le
  edist_dist x y := rfl
  norm_mul x y := (v.map_mul x y).le
  eq_of_dist_eq_zero := by simp only [MulHom.toFun_eq_coe, AbsoluteValue.coe_toMulHom,
    AbsoluteValue.map_sub_eq_zero_iff, imp_self, implies_true]

instance {R} [Ring R] [Nontrivial R] (v : AbsoluteValue R ℝ) : NormOneClass (WithAbs v) where
  norm_one := v.map_one

variable {K} [Field K] (v : AbsoluteValue K ℝ)

instance instNormedFieldWithAbs : NormedField (WithAbs v) where
  toField := inferInstanceAs (Field K)
  __ := inferInstanceAs (NormedRing (WithAbs v))
  norm_mul' := v.map_mul

variable {A : Type*} [NormedField A] {f : WithAbs v →+* A} {v}

/-- If the absolute value `v` factors through an embedding `f` into a normed field, then
the distance associated to the absolute value also factors through `f`. -/
theorem dist_of_comp
    (h : v = (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp f.injective)
    (x y : WithAbs v) :
    dist x y = dist (f x) (f y) := by
  rw [(instNormedFieldWithAbs v).dist_eq, (inferInstanceAs <| NormedField A).dist_eq,
    ← f.map_sub, h]; rfl

instance : Inhabited (WithAbs v) := ⟨0⟩

/-- If the absolute value `v` factors through an embedding `f` into a normed field, then
the pseudo metric space associated to the absolute value is the same as the pseudo metric space
induced by `f`. -/
theorem pseudoMetricSpace_induced_of_comp
    (h : v = (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp f.injective) :
    (instNormedFieldWithAbs v).toPseudoMetricSpace = PseudoMetricSpace.induced f inferInstance := by
  ext; exact dist_of_comp h _ _

/-- If the absolute value `v` factors through an embedding `f` into a normed field, then
the uniform structure associated to the absolute value is the same as the uniform structure
induced by `f`. -/
theorem uniformSpace_eq_comap_of_comp
    (h : v = (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp f.injective) :
    (instNormedFieldWithAbs v).toUniformSpace = UniformSpace.comap f inferInstance := by
  rw [pseudoMetricSpace_induced_of_comp h]; rfl

/-- If the absolute value `v` factors through an embedding `f` into a normed field, then
`f` is uniform inducing. -/
theorem uniformInducing_of_comp
    (h : v = (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp f.injective) :
    UniformInducing f :=
  uniformInducing_iff_uniformSpace.2 (Eq.symm (uniformSpace_eq_comap_of_comp h))

/-- If the absolute value `v` factors through an embedding `f` into a normed field, then
`f` is an isometry. -/
theorem isometry_of_comp
    (h : v = (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp f.injective) :
    Isometry f :=
  Isometry.of_dist_eq <| fun x y => by rw [pseudoMetricSpace_induced_of_comp h]; rfl

end WithAbs

namespace AbsoluteValue

open WithAbs

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ)

/-- The completion of a field with respect to a real absolute value. -/
def completion := UniformSpace.Completion (WithAbs v)

namespace Completion

instance : NormedRing v.completion :=
  UniformSpace.Completion.instNormedRing _

instance [CompletableTopField (WithAbs v)] : NormedField v.completion :=
  UniformSpace.Completion.instNormedField (WithAbs v)

instance : CompleteSpace v.completion :=
  UniformSpace.Completion.completeSpace (WithAbs v)

instance : Inhabited v.completion :=
  UniformSpace.Completion.inhabited _

instance : Coe K v.completion :=
  inferInstanceAs (Coe (WithAbs v) (UniformSpace.Completion (WithAbs v)))

instance : Algebra (WithAbs v) v.completion :=
  UniformSpace.Completion.algebra (WithAbs v) _

variable {A : Type*} [NormedField A] [CompleteSpace A] {f : WithAbs v →+* A} {v}

/-- If the absolute value of a normed field factors through an embedding into another normed field
`A`, then this extends that embedding to `v.completion →+* A`. -/
def extensionEmbedding_of_comp
    (h : v = (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp f.injective) :
    v.completion →+* A :=
  UniformSpace.Completion.extensionHom _
    (WithAbs.uniformInducing_of_comp h).uniformContinuous.continuous

/-- If the absolute value of a normed field factors through a normed embedding, then the extended
embedding `v.completion →+* A` preserves distances. -/
theorem extensionEmbedding_dist_eq_of_comp
    (h : v = (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp f.injective)
    (x y : v.completion) :
    dist (extensionEmbedding_of_comp h x) (extensionEmbedding_of_comp h y) =
      dist x y := by
  refine (UniformSpace.Completion.induction_on₂ x y ?_ (fun x y => ?_))
  · refine isClosed_eq ?_ continuous_dist
    · exact (continuous_iff_continuous_dist.1 (UniformSpace.Completion.continuous_extension))
  · rw [extensionEmbedding_of_comp, UniformSpace.Completion.extensionHom, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk, UniformSpace.Completion.dist_eq]
    simp only [UniformSpace.Completion.extension_coe
      (WithAbs.uniformInducing_of_comp h).uniformContinuous]
    exact Isometry.dist_eq (WithAbs.isometry_of_comp h) _ _

/-- If the absolute value of a normed field factors through a normed embedding, then the
extended embedding `v.completion →+* A` is an isometry. -/
theorem isometry_extensionEmbedding_of_comp
    (h : v = (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp f.injective) :
    Isometry (extensionEmbedding_of_comp h) :=
  Isometry.of_dist_eq <| extensionEmbedding_dist_eq_of_comp h

/-- If the absolute value of a normed field factors through a normed embedding, then the
extended embedding `v.completion →+* A` is a closed embedding. -/
theorem closedEmbedding_extensionEmbedding_of_comp
    (h : v = (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp f.injective) :
    ClosedEmbedding (extensionEmbedding_of_comp h) :=
  (isometry_extensionEmbedding_of_comp h).closedEmbedding

/-- The completion of any normed field with an absolute value, such that the absolute value
factors through an embedding into a normed locally compact field, is also locally compact. -/
theorem locallyCompactSpace [LocallyCompactSpace A]
    (h : v = (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp f.injective)  :
    LocallyCompactSpace (v.completion) :=
  (closedEmbedding_extensionEmbedding_of_comp h).locallyCompactSpace

end AbsoluteValue.Completion

namespace NumberField.InfinitePlace

open AbsoluteValue.Completion

variable {K : Type*} [Field K] [NumberField K] (v : InfinitePlace K)

/-- The normed field structure of a number field coming from the absolute value associated to
an infinite place. -/
def normedField : NormedField K :=
  inferInstanceAs (NormedField (WithAbs v.1))

/-- The absolute value of an infinite place is the composition of the complex norm with the
place's associated embedding. -/
theorem abs_eq_comp :
    v.1 = (IsAbsoluteValue.toAbsoluteValue (norm : ℂ → ℝ)).comp v.embedding.injective := by
  rw [← v.2.choose_spec]
  rfl

/-- The absolute value of a real infinite place is the composition of the real norm with the
place's associated real embedding. -/
theorem abs_of_isReal_eq_comp {v : InfinitePlace K} (hv : IsReal v) :
    v.1 = (IsAbsoluteValue.toAbsoluteValue (norm : ℝ → ℝ)).comp
      (v.embedding_of_isReal hv).injective := by
  ext x
  rw [(show v.1 x = v x by rfl), ← v.norm_embedding_of_isReal hv x]
  rfl

/-- The completion of a number field at an infinite place. -/
def completion := v.1.completion

namespace Completion

instance : NormedField v.completion :=
  letI := (WithAbs.uniformInducing_of_comp v.abs_eq_comp).completableTopField
  UniformSpace.Completion.instNormedField (WithAbs v.1)

instance : CompleteSpace v.completion :=
  inferInstanceAs (CompleteSpace v.1.completion)

instance : Inhabited v.completion :=
  inferInstanceAs (Inhabited v.1.completion)

instance : Coe K v.completion :=
  inferInstanceAs (Coe (WithAbs v.1) v.1.completion)

instance : Algebra K v.completion :=
  inferInstanceAs (Algebra (WithAbs v.1) v.1.completion)

/-- The embedding associated to an infinite place extended to an embedding `v.completion →+* ℂ`. -/
def extensionEmbedding :=
  extensionEmbedding_of_comp v.abs_eq_comp

/-- The embedding `K →+* ℝ` associated to a real infinite place extended to `v.completion →+* ℝ`. -/
def extensionEmbedding_of_isReal {v : InfinitePlace K} (hv : IsReal v) :=
  extensionEmbedding_of_comp <| abs_of_isReal_eq_comp hv

/-- The embedding `v.completion →+* ℂ` is an isometry. -/
theorem isometry_extensionEmbedding : Isometry (extensionEmbedding v) :=
  Isometry.of_dist_eq (extensionEmbedding_dist_eq_of_comp v.abs_eq_comp)

/-- The embedding `v.completion →+* ℝ` at a real infinite palce is an isometry. -/
theorem isometry_extensionEmbedding_of_isReal {v : InfinitePlace K} (hv : IsReal v) :
    Isometry (extensionEmbedding_of_isReal hv) :=
  Isometry.of_dist_eq (extensionEmbedding_dist_eq_of_comp <| abs_of_isReal_eq_comp hv)

theorem injective_extensionEmbedding : Function.Injective (extensionEmbedding v) := by
  letI : DivisionRing v.1.completion := (instNormedFieldCompletion v).toDivisionRing
  exact (extensionEmbedding v).injective

theorem injective_extensionEmbedding_of_isReal {v : InfinitePlace K} (hv : IsReal v) :
    Function.Injective (extensionEmbedding_of_isReal hv) := by
  letI : DivisionRing v.1.completion := (instNormedFieldCompletion v).toDivisionRing
  exact (extensionEmbedding_of_isReal hv).injective

/-- The completion of a number field at an infinite place is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace (v.completion) :=
  AbsoluteValue.Completion.locallyCompactSpace v.abs_eq_comp

/-- The embedding `v.completion →+* ℂ` has closed image inside `ℂ`. -/
theorem isClosed_image_extensionEmbedding : IsClosed (Set.range (extensionEmbedding v)) := by
  exact ((closedEmbedding_iff _).1 <| closedEmbedding_extensionEmbedding_of_comp v.abs_eq_comp).2

/-- The embedding `v.completion →+* ℝ` associated to a real infinite place has closed image
inside `ℝ`. -/
theorem isClosed_image_extensionEmbedding_of_isReal {v : InfinitePlace K} (hv : IsReal v) :
    IsClosed (Set.range (extensionEmbedding_of_isReal hv)) :=
  ((closedEmbedding_iff _).1 <|
    closedEmbedding_extensionEmbedding_of_comp (abs_of_isReal_eq_comp hv)).2

private def subfield_of_isReal {v : InfinitePlace K} (hv : IsReal v) : Subfield ℝ where
  toSubring := (extensionEmbedding_of_isReal hv).range
  inv_mem' := by
    letI : NormedField (AbsoluteValue.completion v.1) := instNormedFieldCompletion v
    exact fun _ ⟨x, hx⟩ => ⟨x⁻¹, by simp only [map_inv₀, hx]⟩

private def subfield : Subfield ℂ where
  toSubring := (extensionEmbedding v).range
  inv_mem' := by
    letI : NormedField (AbsoluteValue.completion v.1) := instNormedFieldCompletion v
    exact fun _ ⟨x, hx⟩ => ⟨x⁻¹, by simp only [map_inv₀, hx]⟩

private theorem isClosed_subfield : IsClosed (subfield v : Set ℂ) :=
  isClosed_image_extensionEmbedding v

private theorem isClosed_subfield_of_isReal {v : InfinitePlace K} (hv : IsReal v) :
    IsClosed (subfield_of_isReal hv : Set ℝ) :=
  isClosed_image_extensionEmbedding_of_isReal hv

private theorem subfield_ne_real_of_isComplex {v : InfinitePlace K} (hv : IsComplex v) :
    subfield v ≠ Complex.ofReal.fieldRange := by
  contrapose! hv
  simp only [not_isComplex_iff_isReal, isReal_iff, ComplexEmbedding.isReal_iff]
  ext x
  have h : v.embedding x ∈ subfield v := by
    simp only [subfield, Subfield.mem_mk, RingHom.mem_range, extensionEmbedding,
      extensionEmbedding_of_comp, UniformSpace.Completion.extensionHom, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk]
    refine ⟨x, ?_⟩
    rw [UniformSpace.Completion.extension_coe
        (WithAbs.uniformInducing_of_comp (abs_eq_comp v)).uniformContinuous]
    rfl
  simp only [hv, RingHom.mem_fieldRange, Complex.ofReal_eq_coe] at h
  obtain ⟨r, hr⟩ := h
  simp only [ComplexEmbedding.conjugate_coe_eq, ← hr, Complex.conj_ofReal]

/-- If `v` is a complex infinite place, then the embedding `v.completion →+* ℂ` is surjective. -/
theorem surjective_extensionEmbedding_of_isComplex {v : InfinitePlace K} (hv : IsComplex v) :
    Function.Surjective (extensionEmbedding v) := by
  rw [← RingHom.range_top_iff_surjective, (show ⊤ = (⊤ : Subfield ℂ).toSubring by rfl),
    ← (Complex.subfield_eq_of_closed <| isClosed_subfield v).resolve_left <|
      subfield_ne_real_of_isComplex hv]
  rfl

/-- If `v` is a complex infinite place, then the embedding `v.completion →+* ℂ` is bijective. -/
theorem bijective_extensionEmbedding_of_isComplex {v : InfinitePlace K} (hv : IsComplex v) :
    Function.Bijective (extensionEmbedding v) :=
  ⟨injective_extensionEmbedding v, surjective_extensionEmbedding_of_isComplex hv⟩

/-- The ring isomorphism `v.completion ≃+* ℂ`, when `v` is complex, given by the bijection
`v.completion →+* ℂ`. -/
def equivComplex_of_isComplex {v : InfinitePlace K} (hv : IsComplex v) :
    v.completion ≃+* ℂ :=
  RingEquiv.ofBijective _ (bijective_extensionEmbedding_of_isComplex hv)

/-- If `v` is a real infinite place, then the embedding `v.completion →+* ℝ` is surjective. -/
theorem surjective_extensionEmbedding_of_isReal {v : InfinitePlace K} (hv : IsReal v) :
    Function.Surjective (extensionEmbedding_of_isReal hv) := by
  rw [← RingHom.range_top_iff_surjective, (show ⊤ = (⊤ : Subfield ℝ).toSubring by rfl),
    ← Real.subfield_eq_of_closed <| isClosed_subfield_of_isReal hv]
  rfl

/-- If `v` is a real infinite place, then the embedding `v.completion →+* ℝ` is bijective. -/
theorem bijective_extensionEmbedding_of_isReal {v : InfinitePlace K} (hv : IsReal v) :
    Function.Bijective (extensionEmbedding_of_isReal hv) :=
  ⟨injective_extensionEmbedding_of_isReal hv, surjective_extensionEmbedding_of_isReal hv⟩

/-- The ring isomorphism `v.completion ≃+* ℝ`, when `v` is real, given by the bijection
`v.completion →+* ℝ`. -/
def equivReal_of_isReal {v : InfinitePlace K} (hv : IsReal v) : v.completion ≃+* ℝ :=
  RingEquiv.ofBijective _ (bijective_extensionEmbedding_of_isReal hv)

end NumberField.InfinitePlace.Completion
