/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Xavier Roblot
-/
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Norm
import Mathlib.Topology.Instances.Complex

#align_import number_theory.number_field.embeddings from "leanprover-community/mathlib"@"caa58cbf5bfb7f81ccbaca4e8b8ac4bc2b39cc1c"

/-!
# Embeddings of number fields
This file defines the embeddings of a number field into an algebraic closed field.

## Main Definitions and Results
* `NumberField.Embeddings.range_eval_eq_rootSet_minpoly`: let `x ∈ K` with `K` number field and
  let `A` be an algebraic closed field of char. 0, then the images of `x` by the embeddings of `K`
   in `A` are exactly the roots in `A` of the minimal polynomial of `x` over `ℚ`.
* `NumberField.Embeddings.pow_eq_one_of_norm_eq_one`: an algebraic integer whose conjugates are
  all of norm one is a root of unity.
* `NumberField.InfinitePlace`: the type of infinite places of a number field `K`.
* `NumberField.InfinitePlace.mk_eq_iff`: two complex embeddings define the same infinite place iff
they are equal or complex conjugates.
* `NumberField.InfinitePlace.prod_eq_abs_norm`: the infinite part of the product formula, that is
for `x ∈ K`, we have `Π_w ‖x‖_w = |norm(x)|` where the product is over the infinite place `w` and
`‖·‖_w` is the normalized absolute value for `w`.

## Tags
number field, embeddings, places, infinite places
-/

open scoped Classical

namespace NumberField.Embeddings

section Fintype

open FiniteDimensional

variable (K : Type*) [Field K] [NumberField K]

variable (A : Type*) [Field A] [CharZero A]

/-- There are finitely many embeddings of a number field. -/
noncomputable instance : Fintype (K →+* A) :=
  Fintype.ofEquiv (K →ₐ[ℚ] A) RingHom.equivRatAlgHom.symm

variable [IsAlgClosed A]

/-- The number of embeddings of a number field is equal to its finrank. -/
theorem card : Fintype.card (K →+* A) = finrank ℚ K := by
  rw [Fintype.ofEquiv_card RingHom.equivRatAlgHom.symm, AlgHom.card]
#align number_field.embeddings.card NumberField.Embeddings.card

instance : Nonempty (K →+* A) := by
  rw [← Fintype.card_pos_iff, NumberField.Embeddings.card K A]
  exact FiniteDimensional.finrank_pos

end Fintype

section Roots

open Set Polynomial

variable (K A : Type*) [Field K] [NumberField K] [Field A] [Algebra ℚ A] [IsAlgClosed A] (x : K)

/-- Let `A` be an algebraically closed field and let `x ∈ K`, with `K` a number field.
The images of `x` by the embeddings of `K` in `A` are exactly the roots in `A` of
the minimal polynomial of `x` over `ℚ`. -/
theorem range_eval_eq_rootSet_minpoly :
    (range fun φ : K →+* A => φ x) = (minpoly ℚ x).rootSet A := by
  convert (NumberField.isAlgebraic K).range_eval_eq_rootSet_minpoly A x using 1
  ext a
  exact ⟨fun ⟨φ, hφ⟩ => ⟨φ.toRatAlgHom, hφ⟩, fun ⟨φ, hφ⟩ => ⟨φ.toRingHom, hφ⟩⟩
#align number_field.embeddings.range_eval_eq_root_set_minpoly NumberField.Embeddings.range_eval_eq_rootSet_minpoly

end Roots

section Bounded

open FiniteDimensional Polynomial Set

variable {K : Type*} [Field K] [NumberField K]

variable {A : Type*} [NormedField A] [IsAlgClosed A] [NormedAlgebra ℚ A]

theorem coeff_bdd_of_norm_le {B : ℝ} {x : K} (h : ∀ φ : K →+* A, ‖φ x‖ ≤ B) (i : ℕ) :
    ‖(minpoly ℚ x).coeff i‖ ≤ max B 1 ^ finrank ℚ K * (finrank ℚ K).choose (finrank ℚ K / 2) := by
  have hx := IsSeparable.isIntegral ℚ x
  rw [← norm_algebraMap' A, ← coeff_map (algebraMap ℚ A)]
  refine coeff_bdd_of_roots_le _ (minpoly.monic hx)
      (IsAlgClosed.splits_codomain _) (minpoly.natDegree_le x) (fun z hz => ?_) i
  classical
  rw [← Multiset.mem_toFinset] at hz
  obtain ⟨φ, rfl⟩ := (range_eval_eq_rootSet_minpoly K A x).symm.subset hz
  exact h φ
#align number_field.embeddings.coeff_bdd_of_norm_le NumberField.Embeddings.coeff_bdd_of_norm_le

variable (K A)

/-- Let `B` be a real number. The set of algebraic integers in `K` whose conjugates are all
smaller in norm than `B` is finite. -/
theorem finite_of_norm_le (B : ℝ) : {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* A, ‖φ x‖ ≤ B}.Finite := by
  let C := Nat.ceil (max B 1 ^ finrank ℚ K * (finrank ℚ K).choose (finrank ℚ K / 2))
  have := bUnion_roots_finite (algebraMap ℤ K) (finrank ℚ K) (finite_Icc (-C : ℤ) C)
  refine this.subset fun x hx => ?_; simp_rw [mem_iUnion]
  have h_map_ℚ_minpoly := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hx.1
  refine ⟨_, ⟨?_, fun i => ?_⟩, mem_rootSet.2 ⟨minpoly.ne_zero hx.1, minpoly.aeval ℤ x⟩⟩
  · rw [← (minpoly.monic hx.1).natDegree_map (algebraMap ℤ ℚ), ← h_map_ℚ_minpoly]
    exact minpoly.natDegree_le x
  rw [mem_Icc, ← abs_le, ← @Int.cast_le ℝ]
  refine (Eq.trans_le ?_ <| coeff_bdd_of_norm_le hx.2 i).trans (Nat.le_ceil _)
  rw [h_map_ℚ_minpoly, coeff_map, eq_intCast, Int.norm_cast_rat, Int.norm_eq_abs, Int.cast_abs]
#align number_field.embeddings.finite_of_norm_le NumberField.Embeddings.finite_of_norm_le

/-- An algebraic integer whose conjugates are all of norm one is a root of unity. -/
theorem pow_eq_one_of_norm_eq_one {x : K} (hxi : IsIntegral ℤ x) (hx : ∀ φ : K →+* A, ‖φ x‖ = 1) :
    ∃ (n : ℕ) (_ : 0 < n), x ^ n = 1 := by
  obtain ⟨a, -, b, -, habne, h⟩ :=
    @Set.Infinite.exists_ne_map_eq_of_mapsTo _ _ _ _ (x ^ · : ℕ → K) Set.infinite_univ
      (by exact fun a _ => ⟨hxi.pow a, fun φ => by simp [hx φ]⟩) (finite_of_norm_le K A (1 : ℝ))
  · wlog hlt : b < a
    · exact this K A hxi hx b a habne.symm h.symm (habne.lt_or_lt.resolve_right hlt)
    refine ⟨a - b, tsub_pos_of_lt hlt, ?_⟩
    rw [← Nat.sub_add_cancel hlt.le, pow_add, mul_left_eq_self₀] at h
    refine h.resolve_right fun hp => ?_
    specialize hx (IsAlgClosed.lift (NumberField.isAlgebraic K)).toRingHom
    rw [pow_eq_zero hp, map_zero, norm_zero] at hx; norm_num at hx
#align number_field.embeddings.pow_eq_one_of_norm_eq_one NumberField.Embeddings.pow_eq_one_of_norm_eq_one

end Bounded

end NumberField.Embeddings

section Place

variable {K : Type*} [Field K] {A : Type*} [NormedDivisionRing A] [Nontrivial A] (φ : K →+* A)

/-- An embedding into a normed division ring defines a place of `K` -/
def NumberField.place : AbsoluteValue K ℝ :=
  (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp φ.injective
#align number_field.place NumberField.place

@[simp]
theorem NumberField.place_apply (x : K) : (NumberField.place φ) x = norm (φ x) := rfl
#align number_field.place_apply NumberField.place_apply

end Place

namespace NumberField.ComplexEmbedding

open Complex NumberField

open scoped ComplexConjugate

variable {K : Type*} [Field K] {k : Type*} [Field k]

/-- The conjugate of a complex embedding as a complex embedding. -/
@[reducible]
def conjugate (φ : K →+* ℂ) : K →+* ℂ := star φ
#align number_field.complex_embedding.conjugate NumberField.ComplexEmbedding.conjugate

@[simp]
theorem conjugate_coe_eq (φ : K →+* ℂ) (x : K) : (conjugate φ) x = conj (φ x) := rfl
#align number_field.complex_embedding.conjugate_coe_eq NumberField.ComplexEmbedding.conjugate_coe_eq

theorem place_conjugate (φ : K →+* ℂ) : place (conjugate φ) = place φ := by
  ext; simp only [place_apply, norm_eq_abs, abs_conj, conjugate_coe_eq]
#align number_field.complex_embedding.place_conjugate NumberField.ComplexEmbedding.place_conjugate

/-- An embedding into `ℂ` is real if it is fixed by complex conjugation. -/
@[reducible]
def IsReal (φ : K →+* ℂ) : Prop := IsSelfAdjoint φ
#align number_field.complex_embedding.is_real NumberField.ComplexEmbedding.IsReal

theorem isReal_iff {φ : K →+* ℂ} : IsReal φ ↔ conjugate φ = φ := isSelfAdjoint_iff
#align number_field.complex_embedding.is_real_iff NumberField.ComplexEmbedding.isReal_iff

theorem isReal_conjugate_iff {φ : K →+* ℂ} : IsReal (conjugate φ) ↔ IsReal φ :=
  IsSelfAdjoint.star_iff
#align number_field.complex_embedding.is_real_conjugate_iff NumberField.ComplexEmbedding.isReal_conjugate_iff

/-- A real embedding as a ring homomorphism from `K` to `ℝ` . -/
def IsReal.embedding {φ : K →+* ℂ} (hφ : IsReal φ) : K →+* ℝ where
  toFun x := (φ x).re
  map_one' := by simp only [map_one, one_re]
  map_mul' := by
    simp only [Complex.conj_eq_iff_im.mp (RingHom.congr_fun hφ _), map_mul, mul_re,
      mul_zero, tsub_zero, eq_self_iff_true, forall_const]
  map_zero' := by simp only [map_zero, zero_re]
  map_add' := by simp only [map_add, add_re, eq_self_iff_true, forall_const]
#align number_field.complex_embedding.is_real.embedding NumberField.ComplexEmbedding.IsReal.embedding

@[simp]
theorem IsReal.coe_embedding_apply {φ : K →+* ℂ} (hφ : IsReal φ) (x : K) :
    (hφ.embedding x : ℂ) = φ x := by
  apply Complex.ext
  · rfl
  · rw [ofReal_im, eq_comm, ← Complex.conj_eq_iff_im]
    exact RingHom.congr_fun hφ x
#align number_field.complex_embedding.is_real.coe_embedding_apply NumberField.ComplexEmbedding.IsReal.coe_embedding_apply

lemma IsReal.comp (f : k →+* K) {φ : K →+* ℂ} (hφ : IsReal φ) :
    IsReal (φ.comp f) := by ext1 x; simpa using RingHom.congr_fun hφ (f x)

lemma isReal_comp_iff {f : k ≃+* K} {φ : K →+* ℂ} :
    IsReal (φ.comp (f : k →+* K)) ↔ IsReal φ :=
  ⟨fun H ↦ by convert H.comp f.symm.toRingHom; ext1; simp, IsReal.comp _⟩

lemma exists_comp_symm_eq_of_comp_eq [Algebra k K] [IsGalois k K] (φ ψ : K →+* ℂ)
    (h : φ.comp (algebraMap k K) = ψ.comp (algebraMap k K)) :
    ∃ σ : K ≃ₐ[k] K, φ.comp σ.symm = ψ := by
  letI := (φ.comp (algebraMap k K)).toAlgebra
  letI := φ.toAlgebra
  have : IsScalarTower k K ℂ := IsScalarTower.of_algebraMap_eq' rfl
  let ψ' : K →ₐ[k] ℂ := { ψ with commutes' := fun r ↦ (RingHom.congr_fun h r).symm }
  use (AlgHom.restrictNormal' ψ' K).symm
  ext1 x
  exact AlgHom.restrictNormal_commutes ψ' K x

variable [Algebra k K] (φ : K →+* ℂ) (σ : K ≃ₐ[k] K)

/--
`IsConj φ σ` states that `σ : K ≃ₐ[k] K` is the conjugation under the embedding `φ : K →+* ℂ`.
-/
def IsConj : Prop := conjugate φ = φ.comp σ

variable {φ σ}

lemma IsConj.eq (h : IsConj φ σ) (x) : φ (σ x) = star (φ x) := RingHom.congr_fun h.symm x

lemma IsConj.ext {σ₁ σ₂ : K ≃ₐ[k] K} (h₁ : IsConj φ σ₁) (h₂ : IsConj φ σ₂) : σ₁ = σ₂ :=
  AlgEquiv.ext fun x ↦ φ.injective ((h₁.eq x).trans (h₂.eq x).symm)

lemma IsConj.ext_iff {σ₁ σ₂ : K ≃ₐ[k] K} (h₁ : IsConj φ σ₁) : σ₁ = σ₂ ↔ IsConj φ σ₂ :=
  ⟨fun e ↦ e ▸ h₁, h₁.ext⟩

lemma IsConj.isReal_comp (h : IsConj φ σ) : IsReal (φ.comp (algebraMap k K)) := by
  ext1 x
  simp only [conjugate_coe_eq, RingHom.coe_comp, Function.comp_apply, ← h.eq,
    starRingEnd_apply, AlgEquiv.commutes]

lemma isConj_one_iff : IsConj φ (1 : K ≃ₐ[k] K) ↔ IsReal φ := Iff.rfl

alias ⟨_, IsReal.isConjGal_one⟩ := ComplexEmbedding.isConj_one_iff

lemma IsConj.symm (hσ : IsConj φ σ) :
    IsConj φ σ.symm := RingHom.ext fun x ↦ by simpa using congr_arg star (hσ.eq (σ.symm x))

lemma isConj_symm : IsConj φ σ.symm ↔ IsConj φ σ :=
  ⟨IsConj.symm, IsConj.symm⟩

end NumberField.ComplexEmbedding

section InfinitePlace

open NumberField

variable {k : Type*} [Field k] (K : Type*) [Field K] {F : Type*} [Field F]

/-- An infinite place of a number field `K` is a place associated to a complex embedding. -/
def NumberField.InfinitePlace := { w : AbsoluteValue K ℝ // ∃ φ : K →+* ℂ, place φ = w }
#align number_field.infinite_place NumberField.InfinitePlace

instance [NumberField K] : Nonempty (NumberField.InfinitePlace K) := Set.instNonemptyRange _

variable {K}

/-- Return the infinite place defined by a complex embedding `φ`. -/
noncomputable def NumberField.InfinitePlace.mk (φ : K →+* ℂ) : NumberField.InfinitePlace K :=
  ⟨place φ, ⟨φ, rfl⟩⟩
#align number_field.infinite_place.mk NumberField.InfinitePlace.mk

namespace NumberField.InfinitePlace

open NumberField

instance {K : Type*} [Field K] : FunLike (InfinitePlace K) K (fun _ => ℝ) :=
{ coe := fun w x => w.1 x
  coe_injective' := fun _ _ h => Subtype.eq (AbsoluteValue.ext fun x => congr_fun h x)}

instance : MonoidWithZeroHomClass (InfinitePlace K) K ℝ where
  coe w x := w.1 x
  coe_injective' _ _ h := Subtype.eq (AbsoluteValue.ext fun x => congr_fun h x)
  map_mul w _ _ := w.1.map_mul _ _
  map_one w := w.1.map_one
  map_zero w := w.1.map_zero

instance : NonnegHomClass (InfinitePlace K) K ℝ where
  coe w x := w x
  coe_injective' _ _ h := Subtype.eq (AbsoluteValue.ext fun x => congr_fun h x)
  map_nonneg w _ := w.1.nonneg _

@[simp]
theorem apply (φ : K →+* ℂ) (x : K) : (mk φ) x = Complex.abs (φ x) := rfl
#align number_field.infinite_place.apply NumberField.InfinitePlace.apply

/-- For an infinite place `w`, return an embedding `φ` such that `w = infinite_place φ` . -/
noncomputable def embedding (w : InfinitePlace K) : K →+* ℂ := w.2.choose
#align number_field.infinite_place.embedding NumberField.InfinitePlace.embedding

@[simp]
theorem mk_embedding (w : InfinitePlace K) : mk (embedding w) = w := Subtype.ext w.2.choose_spec
#align number_field.infinite_place.mk_embedding NumberField.InfinitePlace.mk_embedding

@[simp]
theorem mk_conjugate_eq (φ : K →+* ℂ) : mk (ComplexEmbedding.conjugate φ) = mk φ := by
  refine FunLike.ext _ _ (fun x => ?_)
  rw [apply, apply, ComplexEmbedding.conjugate_coe_eq, Complex.abs_conj]
#align number_field.infinite_place.mk_conjugate_eq NumberField.InfinitePlace.mk_conjugate_eq

theorem norm_embedding_eq (w : InfinitePlace K) (x : K) :
    ‖(embedding w) x‖ = w x := by
  nth_rewrite 2 [← mk_embedding w]
  rfl

theorem eq_iff_eq (x : K) (r : ℝ) : (∀ w : InfinitePlace K, w x = r) ↔ ∀ φ : K →+* ℂ, ‖φ x‖ = r :=
  ⟨fun hw φ => hw (mk φ), by rintro hφ ⟨w, ⟨φ, rfl⟩⟩; exact hφ φ⟩
#align number_field.infinite_place.eq_iff_eq NumberField.InfinitePlace.eq_iff_eq

theorem le_iff_le (x : K) (r : ℝ) : (∀ w : InfinitePlace K, w x ≤ r) ↔ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ r :=
  ⟨fun hw φ => hw (mk φ), by rintro hφ ⟨w, ⟨φ, rfl⟩⟩; exact hφ φ⟩
#align number_field.infinite_place.le_iff_le NumberField.InfinitePlace.le_iff_le

theorem pos_iff {w : InfinitePlace K} {x : K} : 0 < w x ↔ x ≠ 0 := AbsoluteValue.pos_iff w.1
#align number_field.infinite_place.pos_iff NumberField.InfinitePlace.pos_iff

@[simp]
theorem mk_eq_iff {φ ψ : K →+* ℂ} : mk φ = mk ψ ↔ φ = ψ ∨ ComplexEmbedding.conjugate φ = ψ := by
  constructor
  · -- We prove that the map ψ ∘ φ⁻¹ between φ(K) and ℂ is uniform continuous, thus it is either the
    -- inclusion or the complex conjugation using `Complex.uniformContinuous_ringHom_eq_id_or_conj`
    intro h₀
    obtain ⟨j, hiφ⟩ := (φ.injective).hasLeftInverse
    let ι := RingEquiv.ofLeftInverse hiφ
    have hlip : LipschitzWith 1 (RingHom.comp ψ ι.symm.toRingHom) := by
      change LipschitzWith 1 (ψ ∘ ι.symm)
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [NNReal.coe_one, one_mul, NormedField.dist_eq, Function.comp_apply, Function.comp_apply,
        ← map_sub, ← map_sub]
      apply le_of_eq
      suffices ‖φ (ι.symm (x - y))‖ = ‖ψ (ι.symm (x - y))‖ by
        rw [← this, ← RingEquiv.ofLeftInverse_apply hiφ _, RingEquiv.apply_symm_apply ι _]
        rfl
      exact congrFun (congrArg (↑) h₀) _
    cases
      Complex.uniformContinuous_ringHom_eq_id_or_conj φ.fieldRange hlip.uniformContinuous with
    | inl h =>
        left; ext1 x
        conv_rhs => rw [← hiφ x]
        exact (congrFun h (ι x)).symm
    | inr h =>
        right; ext1 x
        conv_rhs => rw [← hiφ x]
        exact (congrFun h (ι x)).symm
  · rintro (⟨h⟩ | ⟨h⟩)
    · exact congr_arg mk h
    · rw [← mk_conjugate_eq]
      exact congr_arg mk h
#align number_field.infinite_place.mk_eq_iff NumberField.InfinitePlace.mk_eq_iff

/-- An infinite place is real if it is defined by a real embedding. -/
def IsReal (w : InfinitePlace K) : Prop := ∃ φ : K →+* ℂ, ComplexEmbedding.IsReal φ ∧ mk φ = w
#align number_field.infinite_place.is_real NumberField.InfinitePlace.IsReal

/-- An infinite place is complex if it is defined by a complex (ie. not real) embedding. -/
def IsComplex (w : InfinitePlace K) : Prop := ∃ φ : K →+* ℂ, ¬ComplexEmbedding.IsReal φ ∧ mk φ = w
#align number_field.infinite_place.is_complex NumberField.InfinitePlace.IsComplex

theorem embedding_mk_eq (φ : K →+* ℂ) :
    embedding (mk φ) = φ ∨ embedding (mk φ) = ComplexEmbedding.conjugate φ := by
  rw [@eq_comm _ _ φ, @eq_comm _ _ (ComplexEmbedding.conjugate φ), ← mk_eq_iff, mk_embedding]

@[simp]
theorem embedding_mk_eq_of_isReal {φ : K →+* ℂ} (h : ComplexEmbedding.IsReal φ) :
    embedding (mk φ) = φ := by
  have := embedding_mk_eq φ
  rwa [ComplexEmbedding.isReal_iff.mp h, or_self] at this
#align number_field.complex_embeddings.is_real.embedding_mk NumberField.InfinitePlace.embedding_mk_eq_of_isReal

theorem isReal_iff {w : InfinitePlace K} :
    IsReal w ↔ ComplexEmbedding.IsReal (embedding w) := by
  refine ⟨?_, fun h => ⟨embedding w, h, mk_embedding w⟩⟩
  rintro ⟨φ, ⟨hφ, rfl⟩⟩
  rwa [embedding_mk_eq_of_isReal hφ]
#align number_field.infinite_place.is_real_iff NumberField.InfinitePlace.isReal_iff

theorem isComplex_iff {w : InfinitePlace K} :
    IsComplex w ↔ ¬ComplexEmbedding.IsReal (embedding w) := by
  refine ⟨?_, fun h => ⟨embedding w, h, mk_embedding w⟩⟩
  rintro ⟨φ, ⟨hφ, rfl⟩⟩
  contrapose! hφ
  cases mk_eq_iff.mp (mk_embedding (mk φ)) with
  | inl h => rwa [h] at hφ
  | inr h => rwa [← ComplexEmbedding.isReal_conjugate_iff, h] at hφ
#align number_field.infinite_place.is_complex_iff NumberField.InfinitePlace.isComplex_iff

@[simp]
theorem conjugate_embedding_eq_of_isReal {w : InfinitePlace K} (h : IsReal w) :
    ComplexEmbedding.conjugate (embedding w) = embedding w :=
  ComplexEmbedding.isReal_iff.mpr (isReal_iff.mp h)

@[simp]
theorem not_isReal_iff_isComplex {w : InfinitePlace K} : ¬IsReal w ↔ IsComplex w := by
  rw [isComplex_iff, isReal_iff]
#align number_field.infinite_place.not_is_real_iff_is_complex NumberField.InfinitePlace.not_isReal_iff_isComplex

@[simp]
theorem not_isComplex_iff_isReal {w : InfinitePlace K} : ¬IsComplex w ↔ IsReal w := by
  rw [isComplex_iff, isReal_iff, not_not]

theorem isReal_or_isComplex (w : InfinitePlace K) : IsReal w ∨ IsComplex w := by
  rw [← not_isReal_iff_isComplex]; exact em _
#align number_field.infinite_place.is_real_or_is_complex NumberField.InfinitePlace.isReal_or_isComplex

/-- The real embedding associated to a real infinite place. -/
noncomputable def embedding_of_isReal {w : InfinitePlace K} (hw : IsReal w) : K →+* ℝ :=
  ComplexEmbedding.IsReal.embedding (isReal_iff.mp hw)
#align number_field.infinite_place.is_real.embedding NumberField.InfinitePlace.embedding_of_isReal

@[simp]
theorem embedding_of_isReal_apply {w : InfinitePlace K} (hw : IsReal w) (x : K) :
    ((embedding_of_isReal hw) x : ℂ) = (embedding w) x :=
  ComplexEmbedding.IsReal.coe_embedding_apply (isReal_iff.mp hw) x

@[simp]
theorem isReal_of_mk_isReal {φ : K →+* ℂ} (h : IsReal (mk φ)) :
    ComplexEmbedding.IsReal φ := by
  contrapose! h
  rw [not_isReal_iff_isComplex]
  exact ⟨φ, h, rfl⟩

lemma isReal_mk_iff {φ : K →+* ℂ} :
    IsReal (mk φ) ↔ ComplexEmbedding.IsReal φ :=
  ⟨isReal_of_mk_isReal, fun H ↦ ⟨_, H, rfl⟩⟩

lemma isComplex_mk_iff {φ : K →+* ℂ} :
    IsComplex (mk φ) ↔ ¬ ComplexEmbedding.IsReal φ :=
  not_isReal_iff_isComplex.symm.trans isReal_mk_iff.not

@[simp]
theorem not_isReal_of_mk_isComplex {φ : K →+* ℂ} (h : IsComplex (mk φ)) :
    ¬ ComplexEmbedding.IsReal φ := by rwa [← isComplex_mk_iff]

/-- The multiplicity of an infinite place, that is the number of distinct complex embeddings that
define it, see `card_filter_mk_eq`. -/
noncomputable def mult (w : InfinitePlace K) : ℕ := if (IsReal w) then 1 else 2

theorem card_filter_mk_eq [NumberField K] (w : InfinitePlace K) :
    (Finset.univ.filter fun φ => mk φ = w).card = mult w := by
  conv_lhs =>
    congr; congr; ext
    rw [← mk_embedding w, mk_eq_iff, ComplexEmbedding.conjugate, star_involutive.eq_iff]
  simp_rw [Finset.filter_or, Finset.filter_eq' _ (embedding w),
    Finset.filter_eq' _ (ComplexEmbedding.conjugate (embedding w)),
    Finset.mem_univ, ite_true, mult]
  split_ifs with hw
  · rw [ComplexEmbedding.isReal_iff.mp (isReal_iff.mp hw), Finset.union_idempotent,
      Finset.card_singleton]
  · refine Finset.card_pair ?_
    rwa [Ne.def, eq_comm, ← ComplexEmbedding.isReal_iff, ← isReal_iff]

open scoped BigOperators

noncomputable instance NumberField.InfinitePlace.fintype [NumberField K] :
    Fintype (InfinitePlace K) := Set.fintypeRange _
#align number_field.infinite_place.number_field.infinite_place.fintype NumberField.InfinitePlace.NumberField.InfinitePlace.fintype

theorem sum_mult_eq [NumberField K] :
    ∑ w : InfinitePlace K, mult w = FiniteDimensional.finrank ℚ K := by
  rw [← Embeddings.card K ℂ, Fintype.card, Finset.card_eq_sum_ones, ← Finset.univ.sum_fiberwise
    (fun φ => InfinitePlace.mk φ)]
  exact Finset.sum_congr rfl
    (fun _ _ => by rw [Finset.sum_const, smul_eq_mul, mul_one, card_filter_mk_eq])

/-- The map from real embeddings to real infinite places as an equiv -/
noncomputable def mkReal :
    { φ : K →+* ℂ // ComplexEmbedding.IsReal φ } ≃ { w : InfinitePlace K // IsReal w } := by
  refine (Equiv.ofBijective (fun φ => ⟨mk φ, ?_⟩) ⟨fun φ ψ h => ?_, fun w => ?_⟩)
  · exact ⟨φ, φ.prop, rfl⟩
  · rwa [Subtype.mk.injEq, mk_eq_iff, ComplexEmbedding.isReal_iff.mp φ.prop, or_self,
      ← Subtype.ext_iff] at h
  · exact ⟨⟨embedding w, isReal_iff.mp w.prop⟩, by simp⟩

/-- The map from nonreal embeddings to complex infinite places -/
noncomputable def mkComplex :
    { φ : K →+* ℂ // ¬ComplexEmbedding.IsReal φ } → { w : InfinitePlace K // IsComplex w } :=
  Subtype.map mk fun φ hφ => ⟨φ, hφ, rfl⟩
#align number_field.infinite_place.mk_complex NumberField.InfinitePlace.mkComplex

@[simp]
theorem mkReal_coe (φ : { φ : K →+* ℂ // ComplexEmbedding.IsReal φ }) :
    (mkReal φ : InfinitePlace K) = mk (φ : K →+* ℂ) := rfl
#align number_field.infinite_place.mk_real_coe NumberField.InfinitePlace.mkReal_coe

@[simp]
theorem mkComplex_coe (φ : { φ : K →+* ℂ // ¬ComplexEmbedding.IsReal φ }) :
    (mkComplex φ : InfinitePlace K) = mk (φ : K →+* ℂ) := rfl
#align number_field.infinite_place.mk_complex_coe NumberField.InfinitePlace.mkComplex_coe

variable [NumberField K]

open scoped BigOperators

/-- The infinite part of the product formula : for `x ∈ K`, we have `Π_w ‖x‖_w = |norm(x)|` where
`‖·‖_w` is the normalized absolute value for `w`.  -/
theorem prod_eq_abs_norm (x : K) :
    ∏ w : InfinitePlace K, w x ^ mult w = abs (Algebra.norm ℚ x) := by
  convert (congr_arg Complex.abs (@Algebra.norm_eq_prod_embeddings ℚ _ _ _ _ ℂ _ _ _ _ _ x)).symm
  · rw [map_prod, ← Fintype.prod_equiv RingHom.equivRatAlgHom (fun f => Complex.abs (f x))
      (fun φ => Complex.abs (φ x)) fun _ => by simp [RingHom.equivRatAlgHom_apply]; rfl]
    rw [← Finset.prod_fiberwise Finset.univ (fun φ => mk φ) (fun φ => Complex.abs (φ x))]
    have : ∀ w : InfinitePlace K, ∀ φ ∈ Finset.filter (fun a ↦ mk a = w) Finset.univ,
        Complex.abs (φ x) = w x := by
      intro _ _ hφ
      rw [← (Finset.mem_filter.mp hφ).2]
      rfl
    simp_rw [Finset.prod_congr rfl (this _), Finset.prod_const, card_filter_mk_eq]
  · rw [eq_ratCast, Rat.cast_abs, ← Complex.abs_ofReal, Complex.ofReal_rat_cast]
#align number_field.infinite_place.prod_eq_abs_norm NumberField.InfinitePlace.prod_eq_abs_norm

open Fintype FiniteDimensional

variable (K)

/-- The number of infinite real places of the number field `K`. -/
noncomputable abbrev NrRealPlaces := card { w : InfinitePlace K // IsReal w }

/-- The number of infinite complex places of the number field `K`. -/
noncomputable abbrev NrComplexPlaces := card { w : InfinitePlace K // IsComplex w }

theorem card_real_embeddings :
    card { φ : K →+* ℂ // ComplexEmbedding.IsReal φ } = NrRealPlaces K := Fintype.card_congr mkReal
#align number_field.infinite_place.card_real_embeddings NumberField.InfinitePlace.card_real_embeddings

theorem card_complex_embeddings :
    card { φ : K →+* ℂ // ¬ComplexEmbedding.IsReal φ } = 2 * NrComplexPlaces K := by
  suffices ∀ w : { w : InfinitePlace K // IsComplex w }, (Finset.univ.filter
      fun φ : { φ // ¬ ComplexEmbedding.IsReal φ } => mkComplex φ = w).card = 2 by
    rw [Fintype.card, Finset.card_eq_sum_ones, ← Finset.sum_fiberwise _ (fun φ => mkComplex φ)]
    simp_rw [Finset.sum_const, this, smul_eq_mul, mul_one, Fintype.card, Finset.card_eq_sum_ones,
      Finset.mul_sum]
  rintro ⟨w, hw⟩
  convert card_filter_mk_eq w
  · rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    refine Fintype.card_congr (Equiv.ofBijective ?_ ⟨fun _ _ h => ?_, fun ⟨φ, hφ⟩ => ?_⟩)
    · exact fun ⟨φ, hφ⟩ => ⟨φ.val, by rwa [Subtype.ext_iff] at hφ⟩
    · rwa [Subtype.mk_eq_mk, ← Subtype.ext_iff, ← Subtype.ext_iff] at h
    · refine ⟨⟨⟨φ, not_isReal_of_mk_isComplex (hφ.symm ▸ hw)⟩, ?_⟩, rfl⟩
      rwa [Subtype.ext_iff, mkComplex_coe]
  · simp_rw [mult, not_isReal_iff_isComplex.mpr hw, ite_false]
#align number_field.infinite_place.card_complex_embeddings NumberField.InfinitePlace.card_complex_embeddings

theorem card_add_two_mul_card_eq_rank :
    NrRealPlaces K + 2 * NrComplexPlaces K = finrank ℚ K := by
  rw [← card_real_embeddings, ← card_complex_embeddings, Fintype.card_subtype_compl,
    ← Embeddings.card K ℂ, Nat.add_sub_of_le]
  exact Fintype.card_subtype_le _

variable {K}

/-- The restriction of an infinite place along an embedding. -/
def comap (w : InfinitePlace K) (f : k →+* K) : InfinitePlace k :=
  ⟨w.1.comp f.injective, w.embedding.comp f,
    by { ext x; show _ = w.1 (f x); rw [← w.2.choose_spec]; rfl }⟩

@[simp]
lemma comap_mk (φ : K →+* ℂ) (f : k →+* K) : (mk φ).comap f = mk (φ.comp f) := rfl

lemma comap_comp (w : InfinitePlace K) (f : F →+* K) (g : k →+* F) :
    w.comap (f.comp g) = (w.comap f).comap g := rfl

lemma IsReal.comap (f : k →+* K) {w : InfinitePlace K} (hφ : IsReal w) :
    IsReal (w.comap f) := by
  rw [← mk_embedding w, comap_mk, isReal_mk_iff]
  rw [← mk_embedding w, isReal_mk_iff] at hφ
  exact hφ.comp f

lemma isReal_comap_iff (f : k ≃+* K) {w : InfinitePlace K} :
    IsReal (w.comap (f : k →+* K)) ↔ IsReal w := by
  rw [← mk_embedding w, comap_mk, isReal_mk_iff, isReal_mk_iff, ComplexEmbedding.isReal_comp_iff]

lemma comap_surjective [Algebra k K] (h : Algebra.IsAlgebraic k K) :
    Function.Surjective (comap · (algebraMap k K)) := fun w ↦
  letI := w.embedding.toAlgebra
  ⟨mk (IsAlgClosed.lift (M := ℂ) h), by simp [comap_mk, RingHom.algebraMap_toAlgebra]⟩

variable [Algebra k K] (σ : K ≃ₐ[k] K) (w : InfinitePlace K)

/-- The action of the galois group on infinite places. -/
@[simps! smul_coe_apply]
instance : MulAction (K ≃ₐ[k] K) (InfinitePlace K) where
  smul := fun σ w ↦ w.comap σ.symm
  one_smul := fun _ ↦ rfl
  mul_smul := fun _ _ _ ↦ rfl

lemma smul_eq_comap : σ • w = w.comap σ.symm := rfl

@[simp] lemma smul_apply (x) : (σ • w) x = w (σ.symm x) := rfl

@[simp] lemma smul_mk (φ : K →+* ℂ) : σ • mk φ = mk (φ.comp σ.symm) := rfl

lemma comap_smul {f : F →+* K} : (σ • w).comap f = w.comap (RingHom.comp σ.symm f) := rfl

variable {σ w}

lemma isReal_smul_iff : IsReal (σ • w) ↔ IsReal w := isReal_comap_iff (f := σ.symm.toRingEquiv)

lemma isComplex_smul_iff : IsComplex (σ • w) ↔ IsComplex w := by
  rw [← not_isReal_iff_isComplex, ← not_isReal_iff_isComplex, isReal_smul_iff]

lemma ComplexEmbedding.exists_comp_symm_eq_of_comp_eq [Algebra k K] [IsGalois k K] (φ ψ : K →+* ℂ)
    (h : φ.comp (algebraMap k K) = ψ.comp (algebraMap k K)) :
    ∃ σ : K ≃ₐ[k] K, φ.comp σ.symm = ψ := by
  letI := (φ.comp (algebraMap k K)).toAlgebra
  letI := φ.toAlgebra
  have : IsScalarTower k K ℂ := IsScalarTower.of_algebraMap_eq' rfl
  let ψ' : K →ₐ[k] ℂ := { ψ with commutes' := fun r ↦ (RingHom.congr_fun h r).symm }
  use (AlgHom.restrictNormal' ψ' K).symm
  ext1 x
  exact AlgHom.restrictNormal_commutes ψ' K x

lemma exists_smul_eq_of_comap_eq [Algebra k K] [IsGalois k K] {w w' : InfinitePlace K}
    (h : w.comap (algebraMap k K) = w'.comap (algebraMap k K)) : ∃ σ : K ≃ₐ[k] K, σ • w = w' := by
  rw [← mk_embedding w, ← mk_embedding w', comap_mk, comap_mk, mk_eq_iff] at h
  cases h with
  | inl h =>
    obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq w.embedding w'.embedding h
    use σ
    rw [← mk_embedding w, ← mk_embedding w', smul_mk, hσ]
  | inr h =>
    obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq
      ((starRingEnd ℂ).comp (embedding w)) w'.embedding h
    use σ
    rw [← mk_embedding w, ← mk_embedding w', smul_mk, mk_eq_iff]
    exact Or.inr hσ

lemma mem_orbit_iff [IsGalois k K] {w w' : InfinitePlace K} :
    w' ∈ MulAction.orbit (K ≃ₐ[k] K) w ↔ w.comap (algebraMap k K) = w'.comap (algebraMap k K) := by
  refine ⟨?_, exists_smul_eq_of_comap_eq⟩
  rintro ⟨σ, rfl : σ • w = w'⟩
  rw [← mk_embedding w, comap_mk, smul_mk, comap_mk]
  congr 1; ext1; simp

/-- The orbits of infinite places under the action of the galois group are indexed by
the infinite places of the base field. -/
noncomputable
def orbitRelEquiv [IsGalois k K] :
    Quotient (MulAction.orbitRel (K ≃ₐ[k] K) (InfinitePlace K)) ≃ InfinitePlace k := by
  refine Equiv.ofBijective (Quotient.lift (comap · (algebraMap k K))
    fun _ _ e ↦ (mem_orbit_iff.mp e).symm) ⟨?_, ?_⟩
  · rintro ⟨w⟩ ⟨w'⟩ e
    exact Quotient.sound (mem_orbit_iff.mpr e.symm)
  · intro w
    obtain ⟨w', hw⟩ := comap_surjective (Normal.isAlgebraic' (K := K)) w
    exact ⟨⟦w'⟧, hw⟩

lemma orbitRelEquiv_apply_mk'' [IsGalois k K] (w : InfinitePlace K) :
    orbitRelEquiv (Quotient.mk'' w) = comap w (algebraMap k K) := rfl

variable (k w)

/--
An infinite place is unramified in a field extension if the restriction has the same multiplicity.
-/
def IsUnramified : Prop := mult (w.comap (algebraMap k K)) = mult w

variable {k w}

lemma not_isUnramified_iff :
    ¬ IsUnramified k w ↔ IsComplex w ∧ IsReal (w.comap (algebraMap k K)) := by
  rw [IsUnramified, mult, mult, ← not_isReal_iff_isComplex]
  split_ifs with h₁ h₂ h₂ <;>
    simp only [not_true_eq_false, false_iff, and_self, forall_true_left, IsEmpty.forall_iff,
      not_and, OfNat.one_ne_ofNat, not_false_eq_true, true_iff, OfNat.ofNat_ne_one, h₁, h₂]
  exact h₁ (h₂.comap _)

lemma isUnramified_iff :
    IsUnramified k w ↔ IsReal w ∨ IsComplex (w.comap (algebraMap k K)) := by
  rw [← not_iff_not, not_isUnramified_iff, not_or,
    not_isReal_iff_isComplex, not_isComplex_iff_isReal]

variable (k)

lemma IsReal.isUnramified (h : IsReal w) : IsUnramified k w := isUnramified_iff.mpr (Or.inl h)

variable {k}

lemma _root_.NumberField.ComplexEmbedding.IsConj.isUnramified_mk_iff
    {φ : K →+* ℂ} (h : ComplexEmbedding.IsConj φ σ) :
    IsUnramified k (mk φ) ↔ σ = 1 := by
  rw [h.ext_iff, ComplexEmbedding.isConj_one_iff, ← not_iff_not, not_isUnramified_iff,
    ← not_isReal_iff_isComplex, comap_mk, isReal_mk_iff, isReal_mk_iff, eq_true h.isReal_comp,
    and_true]

lemma isUnramified_mk_iff_forall_isConj [IsGalois k K] {φ : K →+* ℂ} :
    IsUnramified k (mk φ) ↔ ∀ σ : K ≃ₐ[k] K, ComplexEmbedding.IsConj φ σ → σ = 1 := by
  refine ⟨fun H σ hσ ↦ hσ.isUnramified_mk_iff.mp H,
    fun H ↦ ?_⟩
  by_contra hφ
  rw [not_isUnramified_iff] at hφ
  rw [comap_mk, isReal_mk_iff, ← not_isReal_iff_isComplex, isReal_mk_iff,
    ← ComplexEmbedding.isConj_one_iff (k := k)] at hφ
  letI := (φ.comp (algebraMap k K)).toAlgebra
  letI := φ.toAlgebra
  have : IsScalarTower k K ℂ := IsScalarTower.of_algebraMap_eq' rfl
  let φ' : K →ₐ[k] ℂ := { star φ with commutes' := fun r ↦ by simpa using RingHom.congr_fun hφ.2 r }
  have : ComplexEmbedding.IsConj φ (AlgHom.restrictNormal' φ' K) :=
    (RingHom.ext <| AlgHom.restrictNormal_commutes φ' K).symm
  exact hφ.1 (H _ this ▸ this)

local notation "Stab" => MulAction.stabilizer (K ≃ₐ[k] K)

lemma mem_stabilizer_mk_iff (φ : K →+* ℂ) (σ : K ≃ₐ[k] K) :
    σ ∈ Stab (mk φ) ↔ σ = 1 ∨ ComplexEmbedding.IsConj φ σ := by
  simp only [MulAction.mem_stabilizer_iff, smul_mk, mk_eq_iff]
  rw [← ComplexEmbedding.isConj_symm, ComplexEmbedding.conjugate, star_eq_iff_star_eq]
  refine or_congr ⟨fun H ↦ ?_, fun H ↦ H ▸ rfl⟩ Iff.rfl
  exact congr_arg AlgEquiv.symm
    (AlgEquiv.ext (g := AlgEquiv.refl) fun x ↦ φ.injective (RingHom.congr_fun H x))

lemma IsUnramified.stabilizer_eq_bot (h : IsUnramified k w) : Stab w = ⊥ := by
  rw [eq_bot_iff, ← mk_embedding w, SetLike.le_def]
  simp only [mem_stabilizer_mk_iff, Subgroup.mem_bot, forall_eq_or_imp, true_and]
  exact fun σ hσ ↦ hσ.isUnramified_mk_iff.mp ((mk_embedding w).symm ▸ h)

lemma _root_.NumberField.ComplexEmbedding.IsConj.coe_stabilzer_mk
    {φ : K →+* ℂ} (h : ComplexEmbedding.IsConj φ σ) :
    (Stab (mk φ) : Set (K ≃ₐ[k] K)) = {1, σ} := by
  ext
  rw [SetLike.mem_coe, mem_stabilizer_mk_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    ← h.ext_iff, eq_comm (a := σ)]

variable (k w)

lemma nat_card_stabilizer_eq_one_or_two :
    Nat.card (Stab w) = 1 ∨ Nat.card (Stab w) = 2 := by
  rw [← SetLike.coe_sort_coe, ← mk_embedding w]
  by_cases h : ∃ σ, ComplexEmbedding.IsConj (k := k) (embedding w) σ
  · obtain ⟨σ, hσ⟩ := h
    simp only [hσ.coe_stabilzer_mk, Nat.card_eq_fintype_card, card_ofFinset, Set.toFinset_singleton]
    by_cases 1 = σ
    · left; simp [*]
    · right; simp [*]
  · push_neg at h
    left
    convert show Nat.card ({1} : Set (K ≃ₐ[k] K)) = 1 by simp
    ext
    simp only [SetLike.mem_coe, mem_stabilizer_mk_iff, Set.mem_singleton_iff, or_iff_left_iff_imp]
    exact fun x ↦ (h _ x).elim

variable {k w}

lemma isUnramified_iff_stabilizer_eq_bot [IsGalois k K] : IsUnramified k w ↔ Stab w = ⊥ := by
  rw [← mk_embedding w, isUnramified_mk_iff_forall_isConj]
  simp only [eq_bot_iff, SetLike.le_def, mem_stabilizer_mk_iff,
    Subgroup.mem_bot, forall_eq_or_imp, true_and]

lemma isUnramified_iff_card_stabilizer_eq_one [IsGalois k K] :
    IsUnramified k w ↔ Nat.card (Stab w) = 1 := by
  rw [isUnramified_iff_stabilizer_eq_bot, Subgroup.card_eq_one]

lemma not_isUnramified_iff_card_stabilizer_eq_two [IsGalois k K] :
    ¬ IsUnramified k w ↔ Nat.card (Stab w) = 2 := by
  rw [isUnramified_iff_card_stabilizer_eq_one]
  obtain (e|e) := nat_card_stabilizer_eq_one_or_two k w <;> rw [e] <;> decide

lemma card_stabilizer [IsGalois k K] :
    Nat.card (Stab w) = if IsUnramified k w then 1 else 2 := by
  split
  · rwa [← isUnramified_iff_card_stabilizer_eq_one]
  · rwa [← not_isUnramified_iff_card_stabilizer_eq_two]

lemma even_nat_card_aut_of_not_isUnramified [IsGalois k K] (hw : ¬ IsUnramified k w) :
    Even (Nat.card <| K ≃ₐ[k] K) := by
  by_cases H : Finite (K ≃ₐ[k] K)
  · cases nonempty_fintype (K ≃ₐ[k] K)
    rw [even_iff_two_dvd, Nat.card_eq_fintype_card,
      ← not_isUnramified_iff_card_stabilizer_eq_two.mp hw, Nat.card_eq_fintype_card]
    exact Subgroup.card_subgroup_dvd_card (Stab w)
  · convert even_zero
    by_contra e
    exact H (Nat.finite_of_card_ne_zero e)

lemma even_card_aut_of_not_isUnramified [IsGalois k K] [FiniteDimensional k K]
    (hw : ¬ IsUnramified k w) :
    Even (Fintype.card <| K ≃ₐ[k] K) :=
  Nat.card_eq_fintype_card (α := K ≃ₐ[k] K) ▸ even_nat_card_aut_of_not_isUnramified hw

lemma even_finrank_of_not_isUnramified [IsGalois k K]
    (hw : ¬ IsUnramified k w) : Even (finrank k K) := by
  by_cases FiniteDimensional k K
  · exact IsGalois.card_aut_eq_finrank k K ▸ even_card_aut_of_not_isUnramified hw
  · exact finrank_of_not_finite ‹_› ▸ even_zero

lemma isUnramified_smul_iff :
    IsUnramified k (σ • w) ↔ IsUnramified k w := by
  rw [isUnramified_iff, isUnramified_iff, isReal_smul_iff, comap_smul,
    ← AlgEquiv.toAlgHom_toRingHom, AlgHom.comp_algebraMap]

variable (K)

/-- A infinite place of the base field is unramified in a field extension if every
infinite place over it is unramified. -/
def IsUnramifiedIn (w : InfinitePlace k) : Prop :=
  ∀ v, comap v (algebraMap k K) = w → IsUnramified k v

variable {K}

lemma isUnramifiedIn_comap [IsGalois k K] {w : InfinitePlace K} :
    (w.comap (algebraMap k K)).IsUnramifiedIn K ↔ w.IsUnramified k := by
  refine ⟨fun H ↦ H _ rfl, fun H v hv ↦ ?_⟩
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_comap_eq hv
  rwa [isUnramified_smul_iff] at H

lemma even_card_aut_of_not_isUnramifiedIn [IsGalois k K] [FiniteDimensional k K]
    {w : InfinitePlace k} (hw : ¬ w.IsUnramifiedIn K) :
    Even (Fintype.card <| K ≃ₐ[k] K) := by
  obtain ⟨v, rfl⟩ := comap_surjective (Normal.isAlgebraic' (K := K)) w
  rw [isUnramifiedIn_comap] at hw
  exact even_card_aut_of_not_isUnramified hw

lemma even_finrank_of_not_isUnramifiedIn
    [IsGalois k K] {w : InfinitePlace k} (hw : ¬ w.IsUnramifiedIn K) :
    Even (finrank k K) := by
  obtain ⟨v, rfl⟩ := comap_surjective (Normal.isAlgebraic' (K := K)) w
  rw [isUnramifiedIn_comap] at hw
  exact even_finrank_of_not_isUnramified hw

variable (k K)

open Finset BigOperators in
lemma card_isUnramified [NumberField k] [IsGalois k K] :
    Finset.card (univ.filter <| IsUnramified k (K := K)) =
      Finset.card (univ.filter <| IsUnramifiedIn K (k := k)) * (finrank k K) := by
  letI := Module.Finite.of_restrictScalars_finite ℚ k K
  rw [← IsGalois.card_aut_eq_finrank,
    Finset.card_eq_sum_card_fiberwise (f := (comap · (algebraMap k K)))
    (t := (univ.filter <| IsUnramifiedIn K (k := k))), ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl (fun w hw ↦ ?_)
  obtain ⟨w, rfl⟩ := comap_surjective (Normal.isAlgebraic' (K := K)) w
  simp only [mem_univ, forall_true_left, mem_filter, true_and] at hw
  trans Finset.card (MulAction.orbit (K ≃ₐ[k] K) w).toFinset
  · congr; ext w'
    simp only [mem_univ, forall_true_left, filter_congr_decidable, mem_filter, true_and,
      Set.mem_toFinset, mem_orbit_iff, @eq_comm _ (comap w' _), and_iff_right_iff_imp]
    intro e; rwa [← isUnramifiedIn_comap, ← e]
  · rw [← MulAction.card_orbit_mul_card_stabilizer_eq_card_group _ w,
      ← Nat.card_eq_fintype_card (α := Stab w), card_stabilizer, if_pos,
      mul_one, Set.toFinset_card]
    rwa [← isUnramifiedIn_comap]
  · simp [isUnramifiedIn_comap]

open Finset BigOperators in
lemma card_isUnramified_compl [NumberField k] [IsGalois k K] :
    Finset.card (univ.filter <| IsUnramified k (K := K))ᶜ =
      Finset.card (univ.filter <| IsUnramifiedIn K (k := k))ᶜ * (finrank k K / 2) := by
  letI := Module.Finite.of_restrictScalars_finite ℚ k K
  rw [← IsGalois.card_aut_eq_finrank,
    Finset.card_eq_sum_card_fiberwise (f := (comap · (algebraMap k K)))
    (t := (univ.filter <| IsUnramifiedIn K (k := k))ᶜ), ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl (fun w hw ↦ ?_)
  obtain ⟨w, rfl⟩ := comap_surjective (Normal.isAlgebraic' (K := K)) w
  simp only [mem_univ, forall_true_left, compl_filter, not_not, mem_filter, true_and] at hw
  trans Finset.card (MulAction.orbit (K ≃ₐ[k] K) w).toFinset
  · congr; ext w'
    simp only [compl_filter, filter_congr_decidable, mem_filter, mem_univ, true_and,
      @eq_comm _ (comap w' _), Set.mem_toFinset, mem_orbit_iff, and_iff_right_iff_imp]
    intro e; rwa [← isUnramifiedIn_comap, ← e]
  · rw [← MulAction.card_orbit_mul_card_stabilizer_eq_card_group _ w,
      ← Nat.card_eq_fintype_card (α := Stab w), InfinitePlace.card_stabilizer, if_neg,
      Nat.mul_div_cancel _ zero_lt_two, Set.toFinset_card]
    rwa [← isUnramifiedIn_comap]
  · simp [isUnramifiedIn_comap]

lemma card_eq_card_isUnramifiedIn [NumberField k] [IsGalois k K] :
    Fintype.card (InfinitePlace K) =
      Finset.card (Finset.univ.filter <| IsUnramifiedIn K (k := k)) * finrank k K +
      Finset.card (Finset.univ.filter <| IsUnramifiedIn K (k := k))ᶜ * (finrank k K / 2) := by
  rw [← card_isUnramified, ← card_isUnramified_compl, Finset.card_add_card_compl]

end NumberField.InfinitePlace

end InfinitePlace
