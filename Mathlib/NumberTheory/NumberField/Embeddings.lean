/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Xavier Roblot
-/
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Topology.Instances.Complex

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

open scoped Finset Topology

namespace NumberField.Embeddings

section Fintype

open Module

variable (K : Type*) [Field K] [NumberField K]
variable (A : Type*) [Field A] [CharZero A]

/-- There are finitely many embeddings of a number field. -/
noncomputable instance : Fintype (K →+* A) :=
  Fintype.ofEquiv (K →ₐ[ℚ] A) RingHom.equivRatAlgHom.symm

variable [IsAlgClosed A]

/-- The number of embeddings of a number field is equal to its finrank. -/
theorem card : Fintype.card (K →+* A) = finrank ℚ K := by
  rw [Fintype.ofEquiv_card RingHom.equivRatAlgHom.symm, AlgHom.card]

instance : Nonempty (K →+* A) := by
  rw [← Fintype.card_pos_iff, NumberField.Embeddings.card K A]
  exact Module.finrank_pos

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

end Roots

section Bounded

open Module Polynomial Set

variable {K : Type*} [Field K] [NumberField K]
variable {A : Type*} [NormedField A] [IsAlgClosed A] [NormedAlgebra ℚ A]

theorem coeff_bdd_of_norm_le {B : ℝ} {x : K} (h : ∀ φ : K →+* A, ‖φ x‖ ≤ B) (i : ℕ) :
    ‖(minpoly ℚ x).coeff i‖ ≤ max B 1 ^ finrank ℚ K * (finrank ℚ K).choose (finrank ℚ K / 2) := by
  have hx := Algebra.IsSeparable.isIntegral ℚ x
  rw [← norm_algebraMap' A, ← coeff_map (algebraMap ℚ A)]
  refine coeff_bdd_of_roots_le _ (minpoly.monic hx)
      (IsAlgClosed.splits_codomain _) (minpoly.natDegree_le x) (fun z hz => ?_) i
  classical
  rw [← Multiset.mem_toFinset] at hz
  obtain ⟨φ, rfl⟩ := (range_eval_eq_rootSet_minpoly K A x).symm.subset hz
  exact h φ

variable (K A)

/-- Let `B` be a real number. The set of algebraic integers in `K` whose conjugates are all
smaller in norm than `B` is finite. -/
theorem finite_of_norm_le (B : ℝ) : {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* A, ‖φ x‖ ≤ B}.Finite := by
  classical
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

/-- An algebraic integer whose conjugates are all of norm one is a root of unity. -/
theorem pow_eq_one_of_norm_eq_one {x : K} (hxi : IsIntegral ℤ x) (hx : ∀ φ : K →+* A, ‖φ x‖ = 1) :
    ∃ (n : ℕ) (_ : 0 < n), x ^ n = 1 := by
  obtain ⟨a, -, b, -, habne, h⟩ :=
    @Set.Infinite.exists_ne_map_eq_of_mapsTo _ _ _ _ (x ^ · : ℕ → K) Set.infinite_univ
      (by exact fun a _ => ⟨hxi.pow a, fun φ => by simp [hx φ]⟩) (finite_of_norm_le K A (1 : ℝ))
  wlog hlt : b < a
  · exact this K A hxi hx b a habne.symm h.symm (habne.lt_or_lt.resolve_right hlt)
  refine ⟨a - b, tsub_pos_of_lt hlt, ?_⟩
  rw [← Nat.sub_add_cancel hlt.le, pow_add, mul_left_eq_self₀] at h
  refine h.resolve_right fun hp => ?_
  specialize hx (IsAlgClosed.lift (R := ℚ)).toRingHom
  rw [pow_eq_zero hp, map_zero, norm_zero] at hx; norm_num at hx

end Bounded

end NumberField.Embeddings

section Place

variable {K : Type*} [Field K] {A : Type*} [NormedDivisionRing A] [Nontrivial A] (φ : K →+* A)

/-- An embedding into a normed division ring defines a place of `K` -/
def NumberField.place : AbsoluteValue K ℝ :=
  (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp φ.injective

@[simp]
theorem NumberField.place_apply (x : K) : (NumberField.place φ) x = norm (φ x) := rfl

end Place

namespace NumberField.ComplexEmbedding

open Complex NumberField

open scoped ComplexConjugate

variable {K : Type*} [Field K] {k : Type*} [Field k]

/-- The conjugate of a complex embedding as a complex embedding. -/
abbrev conjugate (φ : K →+* ℂ) : K →+* ℂ := star φ

@[simp]
theorem conjugate_coe_eq (φ : K →+* ℂ) (x : K) : (conjugate φ) x = conj (φ x) := rfl

theorem place_conjugate (φ : K →+* ℂ) : place (conjugate φ) = place φ := by
  ext; simp only [place_apply, norm_conj, conjugate_coe_eq]

/-- An embedding into `ℂ` is real if it is fixed by complex conjugation. -/
abbrev IsReal (φ : K →+* ℂ) : Prop := IsSelfAdjoint φ

theorem isReal_iff {φ : K →+* ℂ} : IsReal φ ↔ conjugate φ = φ := isSelfAdjoint_iff

theorem isReal_conjugate_iff {φ : K →+* ℂ} : IsReal (conjugate φ) ↔ IsReal φ :=
  IsSelfAdjoint.star_iff

/-- A real embedding as a ring homomorphism from `K` to `ℝ` . -/
def IsReal.embedding {φ : K →+* ℂ} (hφ : IsReal φ) : K →+* ℝ where
  toFun x := (φ x).re
  map_one' := by simp only [map_one, one_re]
  map_mul' := by
    simp only [Complex.conj_eq_iff_im.mp (RingHom.congr_fun hφ _), map_mul, mul_re,
      mul_zero, tsub_zero, eq_self_iff_true, forall_const]
  map_zero' := by simp only [map_zero, zero_re]
  map_add' := by simp only [map_add, add_re, eq_self_iff_true, forall_const]

@[simp]
theorem IsReal.coe_embedding_apply {φ : K →+* ℂ} (hφ : IsReal φ) (x : K) :
    (hφ.embedding x : ℂ) = φ x := by
  apply Complex.ext
  · rfl
  · rw [ofReal_im, eq_comm, ← Complex.conj_eq_iff_im]
    exact RingHom.congr_fun hφ x

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

instance [NumberField K] : Nonempty (NumberField.InfinitePlace K) := Set.instNonemptyRange _

variable {K}

/-- Return the infinite place defined by a complex embedding `φ`. -/
noncomputable def NumberField.InfinitePlace.mk (φ : K →+* ℂ) : NumberField.InfinitePlace K :=
  ⟨place φ, ⟨φ, rfl⟩⟩

namespace NumberField.InfinitePlace

open NumberField

instance {K : Type*} [Field K] : FunLike (InfinitePlace K) K ℝ where
  coe w x := w.1 x
  coe_injective' _ _ h := Subtype.eq (AbsoluteValue.ext fun x => congr_fun h x)

lemma coe_apply {K : Type*} [Field K] (v : InfinitePlace K) (x : K) :
  v x = v.1 x := rfl

@[ext]
lemma ext {K : Type*} [Field K] (v₁ v₂ : InfinitePlace K) (h : ∀ k, v₁ k = v₂ k) : v₁ = v₂ :=
  Subtype.ext <| AbsoluteValue.ext h

instance : MonoidWithZeroHomClass (InfinitePlace K) K ℝ where
  map_mul w _ _ := w.1.map_mul _ _
  map_one w := w.1.map_one
  map_zero w := w.1.map_zero

instance : NonnegHomClass (InfinitePlace K) K ℝ where
  apply_nonneg w _ := w.1.nonneg _

@[simp]
theorem apply (φ : K →+* ℂ) (x : K) : (mk φ) x = ‖φ x‖ := rfl

/-- For an infinite place `w`, return an embedding `φ` such that `w = infinite_place φ` . -/
noncomputable def embedding (w : InfinitePlace K) : K →+* ℂ := w.2.choose

@[simp]
theorem mk_embedding (w : InfinitePlace K) : mk (embedding w) = w := Subtype.ext w.2.choose_spec

@[simp]
theorem mk_conjugate_eq (φ : K →+* ℂ) : mk (ComplexEmbedding.conjugate φ) = mk φ := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [apply, apply, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]

theorem norm_embedding_eq (w : InfinitePlace K) (x : K) :
    ‖(embedding w) x‖ = w x := by
  nth_rewrite 2 [← mk_embedding w]
  rfl

theorem eq_iff_eq (x : K) (r : ℝ) : (∀ w : InfinitePlace K, w x = r) ↔ ∀ φ : K →+* ℂ, ‖φ x‖ = r :=
  ⟨fun hw φ => hw (mk φ), by rintro hφ ⟨w, ⟨φ, rfl⟩⟩; exact hφ φ⟩

theorem le_iff_le (x : K) (r : ℝ) : (∀ w : InfinitePlace K, w x ≤ r) ↔ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ r :=
  ⟨fun hw φ => hw (mk φ), by rintro hφ ⟨w, ⟨φ, rfl⟩⟩; exact hφ φ⟩

theorem pos_iff {w : InfinitePlace K} {x : K} : 0 < w x ↔ x ≠ 0 := AbsoluteValue.pos_iff w.1

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

/-- An infinite place is real if it is defined by a real embedding. -/
def IsReal (w : InfinitePlace K) : Prop := ∃ φ : K →+* ℂ, ComplexEmbedding.IsReal φ ∧ mk φ = w

/-- An infinite place is complex if it is defined by a complex (ie. not real) embedding. -/
def IsComplex (w : InfinitePlace K) : Prop := ∃ φ : K →+* ℂ, ¬ComplexEmbedding.IsReal φ ∧ mk φ = w

theorem embedding_mk_eq (φ : K →+* ℂ) :
    embedding (mk φ) = φ ∨ embedding (mk φ) = ComplexEmbedding.conjugate φ := by
  rw [@eq_comm _ _ φ, @eq_comm _ _ (ComplexEmbedding.conjugate φ), ← mk_eq_iff, mk_embedding]

@[simp]
theorem embedding_mk_eq_of_isReal {φ : K →+* ℂ} (h : ComplexEmbedding.IsReal φ) :
    embedding (mk φ) = φ := by
  have := embedding_mk_eq φ
  rwa [ComplexEmbedding.isReal_iff.mp h, or_self] at this

theorem isReal_iff {w : InfinitePlace K} :
    IsReal w ↔ ComplexEmbedding.IsReal (embedding w) := by
  refine ⟨?_, fun h => ⟨embedding w, h, mk_embedding w⟩⟩
  rintro ⟨φ, ⟨hφ, rfl⟩⟩
  rwa [embedding_mk_eq_of_isReal hφ]

theorem isComplex_iff {w : InfinitePlace K} :
    IsComplex w ↔ ¬ComplexEmbedding.IsReal (embedding w) := by
  refine ⟨?_, fun h => ⟨embedding w, h, mk_embedding w⟩⟩
  rintro ⟨φ, ⟨hφ, rfl⟩⟩
  contrapose! hφ
  cases mk_eq_iff.mp (mk_embedding (mk φ)) with
  | inl h => rwa [h] at hφ
  | inr h => rwa [← ComplexEmbedding.isReal_conjugate_iff, h] at hφ

@[simp]
theorem conjugate_embedding_eq_of_isReal {w : InfinitePlace K} (h : IsReal w) :
    ComplexEmbedding.conjugate (embedding w) = embedding w :=
  ComplexEmbedding.isReal_iff.mpr (isReal_iff.mp h)

@[simp]
theorem not_isReal_iff_isComplex {w : InfinitePlace K} : ¬IsReal w ↔ IsComplex w := by
  rw [isComplex_iff, isReal_iff]

@[simp]
theorem not_isComplex_iff_isReal {w : InfinitePlace K} : ¬IsComplex w ↔ IsReal w := by
  rw [isComplex_iff, isReal_iff, not_not]

theorem isReal_or_isComplex (w : InfinitePlace K) : IsReal w ∨ IsComplex w := by
  rw [← not_isReal_iff_isComplex]; exact em _

theorem ne_of_isReal_isComplex {w w' : InfinitePlace K} (h : IsReal w) (h' : IsComplex w') :
    w ≠ w' := fun h_eq ↦ not_isReal_iff_isComplex.mpr h' (h_eq ▸ h)

variable (K) in
theorem disjoint_isReal_isComplex :
    Disjoint {(w : InfinitePlace K) | IsReal w} {(w : InfinitePlace K) | IsComplex w} :=
  Set.disjoint_iff.2 <| fun _ hw ↦ not_isReal_iff_isComplex.2 hw.2 hw.1

/-- The real embedding associated to a real infinite place. -/
noncomputable def embedding_of_isReal {w : InfinitePlace K} (hw : IsReal w) : K →+* ℝ :=
  ComplexEmbedding.IsReal.embedding (isReal_iff.mp hw)

@[simp]
theorem embedding_of_isReal_apply {w : InfinitePlace K} (hw : IsReal w) (x : K) :
    ((embedding_of_isReal hw) x : ℂ) = (embedding w) x :=
  ComplexEmbedding.IsReal.coe_embedding_apply (isReal_iff.mp hw) x

theorem norm_embedding_of_isReal {w : InfinitePlace K} (hw : IsReal w) (x : K) :
    ‖embedding_of_isReal hw x‖ = w x := by
  rw [← norm_embedding_eq, ← embedding_of_isReal_apply hw, Complex.norm_real]

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

open scoped Classical in
/-- The multiplicity of an infinite place, that is the number of distinct complex embeddings that
define it, see `card_filter_mk_eq`. -/
noncomputable def mult (w : InfinitePlace K) : ℕ := if (IsReal w) then 1 else 2

theorem mult_pos {w : InfinitePlace K} : 0 < mult w := by
  rw [mult]
  split_ifs <;> norm_num

@[simp]
theorem mult_ne_zero {w : InfinitePlace K} : mult w ≠ 0 := ne_of_gt mult_pos

theorem one_le_mult {w : InfinitePlace K} : (1 : ℝ) ≤ mult w := by
  rw [← Nat.cast_one, Nat.cast_le]
  exact mult_pos

open scoped Classical in
theorem card_filter_mk_eq [NumberField K] (w : InfinitePlace K) : #{φ | mk φ = w} = mult w := by
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
    rwa [Ne, eq_comm, ← ComplexEmbedding.isReal_iff, ← isReal_iff]

open scoped Classical in
noncomputable instance NumberField.InfinitePlace.fintype [NumberField K] :
    Fintype (InfinitePlace K) := Set.fintypeRange _

theorem sum_mult_eq [NumberField K] :
    ∑ w : InfinitePlace K, mult w = Module.finrank ℚ K := by
  classical
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

@[simp]
theorem mkReal_coe (φ : { φ : K →+* ℂ // ComplexEmbedding.IsReal φ }) :
    (mkReal φ : InfinitePlace K) = mk (φ : K →+* ℂ) := rfl

@[simp]
theorem mkComplex_coe (φ : { φ : K →+* ℂ // ¬ComplexEmbedding.IsReal φ }) :
    (mkComplex φ : InfinitePlace K) = mk (φ : K →+* ℂ) := rfl

section NumberField

variable [NumberField K]

/-- The infinite part of the product formula : for `x ∈ K`, we have `Π_w ‖x‖_w = |norm(x)|` where
`‖·‖_w` is the normalized absolute value for `w`. -/
theorem prod_eq_abs_norm (x : K) :
    ∏ w : InfinitePlace K, w x ^ mult w = abs (Algebra.norm ℚ x) := by
  classical
  convert (congr_arg (‖·‖) (@Algebra.norm_eq_prod_embeddings ℚ _ _ _ _ ℂ _ _ _ _ _ x)).symm
  · rw [norm_prod, ← Fintype.prod_equiv RingHom.equivRatAlgHom (fun f => ‖f x‖)
      (fun φ => ‖φ x‖) fun _ => by simp [RingHom.equivRatAlgHom_apply]; rfl]
    rw [← Finset.prod_fiberwise Finset.univ mk (fun φ => ‖φ x‖)]
    have (w : InfinitePlace K) (φ) (hφ : φ ∈ ({φ | mk φ = w} : Finset _)) :
        ‖φ x‖ = w x := by rw [← (Finset.mem_filter.mp hφ).2, apply]
    simp_rw [Finset.prod_congr rfl (this _), Finset.prod_const, card_filter_mk_eq]
  · rw [eq_ratCast, Rat.cast_abs, ← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_ratCast]

theorem one_le_of_lt_one {w : InfinitePlace K} {a : (𝓞 K)} (ha : a ≠ 0)
    (h : ∀ ⦃z⦄, z ≠ w → z a < 1) : 1 ≤ w a := by
  suffices (1 : ℝ) ≤ |Algebra.norm ℚ (a : K)| by
    contrapose! this
    rw [← InfinitePlace.prod_eq_abs_norm, ← Finset.prod_const_one]
    refine Finset.prod_lt_prod_of_nonempty (fun _ _ ↦ ?_) (fun z _ ↦ ?_) Finset.univ_nonempty
    · exact pow_pos (pos_iff.mpr ((Subalgebra.coe_eq_zero _).not.mpr ha)) _
    · refine pow_lt_one₀ (apply_nonneg _ _) ?_ (by rw [mult]; split_ifs <;> norm_num)
      by_cases hz : z = w
      · rwa [hz]
      · exact h hz
  rw [← Algebra.coe_norm_int, ← Int.cast_one, ← Int.cast_abs, Rat.cast_intCast, Int.cast_le]
  exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr ha)

open scoped IntermediateField in
theorem _root_.NumberField.is_primitive_element_of_infinitePlace_lt {x : 𝓞 K}
    {w : InfinitePlace K} (h₁ : x ≠ 0) (h₂ : ∀ ⦃w'⦄, w' ≠ w → w' x < 1)
    (h₃ : IsReal w ∨ |(w.embedding x).re| < 1) : ℚ⟮(x : K)⟯ = ⊤ := by
  rw [Field.primitive_element_iff_algHom_eq_of_eval ℚ ℂ ?_ _ w.embedding.toRatAlgHom]
  · intro ψ hψ
    have h : 1 ≤ w x := one_le_of_lt_one h₁ h₂
    have main : w = InfinitePlace.mk ψ.toRingHom := by
      erw [← norm_embedding_eq, hψ] at h
      contrapose! h
      exact h₂ h.symm
    rw [(mk_embedding w).symm, mk_eq_iff] at main
    cases h₃ with
    | inl hw =>
      rw [conjugate_embedding_eq_of_isReal hw, or_self] at main
      exact congr_arg RingHom.toRatAlgHom main
    | inr hw =>
      refine congr_arg RingHom.toRatAlgHom (main.resolve_right fun h' ↦ hw.not_le ?_)
      have : (embedding w x).im = 0 := by
        erw [← Complex.conj_eq_iff_im, RingHom.congr_fun h' x]
        exact hψ.symm
      rwa [← norm_embedding_eq, ← Complex.re_add_im (embedding w x), this, Complex.ofReal_zero,
        zero_mul, add_zero, Complex.norm_real] at h
  · exact fun x ↦ IsAlgClosed.splits_codomain (minpoly ℚ x)

theorem _root_.NumberField.adjoin_eq_top_of_infinitePlace_lt {x : 𝓞 K} {w : InfinitePlace K}
    (h₁ : x ≠ 0) (h₂ : ∀ ⦃w'⦄, w' ≠ w → w' x < 1) (h₃ : IsReal w ∨ |(w.embedding x).re| < 1) :
    Algebra.adjoin ℚ {(x : K)} = ⊤ := by
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_integral (IsIntegral.of_finite ℚ _)]
  exact congr_arg IntermediateField.toSubalgebra <|
    NumberField.is_primitive_element_of_infinitePlace_lt h₁ h₂ h₃

end NumberField

open Fintype Module

variable (K)

section NumberField

variable [NumberField K]

open scoped Classical in
/-- The number of infinite real places of the number field `K`. -/
noncomputable abbrev nrRealPlaces := card { w : InfinitePlace K // IsReal w }

@[deprecated (since := "2024-10-24")] alias NrRealPlaces := nrRealPlaces

open scoped Classical in
/-- The number of infinite complex places of the number field `K`. -/
noncomputable abbrev nrComplexPlaces := card { w : InfinitePlace K // IsComplex w }

@[deprecated (since := "2024-10-24")] alias NrComplexPlaces := nrComplexPlaces

open scoped Classical in
theorem card_real_embeddings :
    card { φ : K →+* ℂ // ComplexEmbedding.IsReal φ } = nrRealPlaces K := Fintype.card_congr mkReal

theorem card_eq_nrRealPlaces_add_nrComplexPlaces :
    Fintype.card (InfinitePlace K) = nrRealPlaces K + nrComplexPlaces K := by
  classical
  convert Fintype.card_subtype_or_disjoint (IsReal (K := K)) (IsComplex (K := K))
    (disjoint_isReal_isComplex K) using 1
  exact (Fintype.card_of_subtype _ (fun w ↦ ⟨fun _ ↦ isReal_or_isComplex w, fun _ ↦ by simp⟩)).symm

open scoped Classical in
theorem card_complex_embeddings :
    card { φ : K →+* ℂ // ¬ComplexEmbedding.IsReal φ } = 2 * nrComplexPlaces K := by
  suffices ∀ w : { w : InfinitePlace K // IsComplex w },
     #{φ : {φ //¬ ComplexEmbedding.IsReal φ} | mkComplex φ = w} = 2 by
    rw [Fintype.card, Finset.card_eq_sum_ones, ← Finset.sum_fiberwise _ (fun φ => mkComplex φ)]
    simp_rw [Finset.sum_const, this, smul_eq_mul, mul_one, Fintype.card, Finset.card_eq_sum_ones,
      Finset.mul_sum, Finset.sum_const, smul_eq_mul, mul_one]
  rintro ⟨w, hw⟩
  convert card_filter_mk_eq w
  · rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    refine Fintype.card_congr (Equiv.ofBijective ?_ ⟨fun _ _ h => ?_, fun ⟨φ, hφ⟩ => ?_⟩)
    · exact fun ⟨φ, hφ⟩ => ⟨φ.val, by rwa [Subtype.ext_iff] at hφ⟩
    · rwa [Subtype.mk_eq_mk, ← Subtype.ext_iff, ← Subtype.ext_iff] at h
    · refine ⟨⟨⟨φ, not_isReal_of_mk_isComplex (hφ.symm ▸ hw)⟩, ?_⟩, rfl⟩
      rwa [Subtype.ext_iff, mkComplex_coe]
  · simp_rw [mult, not_isReal_iff_isComplex.mpr hw, ite_false]

theorem card_add_two_mul_card_eq_rank :
    nrRealPlaces K + 2 * nrComplexPlaces K = finrank ℚ K := by
  classical
  rw [← card_real_embeddings, ← card_complex_embeddings, Fintype.card_subtype_compl,
    ← Embeddings.card K ℂ, Nat.add_sub_of_le]
  exact Fintype.card_subtype_le _

variable {K}

theorem nrComplexPlaces_eq_zero_of_finrank_eq_one (h : finrank ℚ K = 1) :
    nrComplexPlaces K = 0 := by linarith [card_add_two_mul_card_eq_rank K]

theorem nrRealPlaces_eq_one_of_finrank_eq_one (h : finrank ℚ K = 1) :
    nrRealPlaces K = 1 := by
  have := card_add_two_mul_card_eq_rank K
  rwa [nrComplexPlaces_eq_zero_of_finrank_eq_one h, h, mul_zero, add_zero] at this

/-- The restriction of an infinite place along an embedding. -/
def comap (w : InfinitePlace K) (f : k →+* K) : InfinitePlace k :=
  ⟨w.1.comp f.injective, w.embedding.comp f,
    by { ext x; show _ = w.1 (f x); rw [← w.2.choose_spec]; rfl }⟩

end NumberField

variable {K}

@[simp]
lemma comap_mk (φ : K →+* ℂ) (f : k →+* K) : (mk φ).comap f = mk (φ.comp f) := rfl

lemma comap_id (w : InfinitePlace K) : w.comap (RingHom.id K) = w := rfl

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

lemma comap_surjective [Algebra k K] [Algebra.IsAlgebraic k K] :
    Function.Surjective (comap · (algebraMap k K)) := fun w ↦
  letI := w.embedding.toAlgebra
  ⟨mk (IsAlgClosed.lift (M := ℂ) (R := k)).toRingHom,
    by simp [this, comap_mk, RingHom.algebraMap_toAlgebra]⟩

lemma mult_comap_le (f : k →+* K) (w : InfinitePlace K) : mult (w.comap f) ≤ mult w := by
  rw [mult, mult]
  split_ifs with h₁ h₂ h₂
  pick_goal 3
  · exact (h₁ (h₂.comap _)).elim
  all_goals decide

variable [Algebra k K] (σ : K ≃ₐ[k] K) (w : InfinitePlace K)
variable (k K)

lemma card_mono [NumberField k] [NumberField K] :
    card (InfinitePlace k) ≤ card (InfinitePlace K) :=
  have := Module.Finite.of_restrictScalars_finite ℚ k K
  Fintype.card_le_of_surjective _ comap_surjective

variable {k K}

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

lemma ComplexEmbedding.exists_comp_symm_eq_of_comp_eq [IsGalois k K] (φ ψ : K →+* ℂ)
    (h : φ.comp (algebraMap k K) = ψ.comp (algebraMap k K)) :
    ∃ σ : K ≃ₐ[k] K, φ.comp σ.symm = ψ := by
  letI := (φ.comp (algebraMap k K)).toAlgebra
  letI := φ.toAlgebra
  have : IsScalarTower k K ℂ := IsScalarTower.of_algebraMap_eq' rfl
  let ψ' : K →ₐ[k] ℂ := { ψ with commutes' := fun r ↦ (RingHom.congr_fun h r).symm }
  use (AlgHom.restrictNormal' ψ' K).symm
  ext1 x
  exact AlgHom.restrictNormal_commutes ψ' K x

lemma exists_smul_eq_of_comap_eq [IsGalois k K] {w w' : InfinitePlace K}
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
    obtain ⟨w', hw⟩ := comap_surjective (K := K) w
    exact ⟨⟦w'⟧, hw⟩

lemma orbitRelEquiv_apply_mk'' [IsGalois k K] (w : InfinitePlace K) :
    orbitRelEquiv (Quotient.mk'' w) = comap w (algebraMap k K) := rfl

variable (k w)

/--
An infinite place is unramified in a field extension if the restriction has the same multiplicity.
-/
def IsUnramified : Prop := mult (w.comap (algebraMap k K)) = mult w

variable {k}

lemma isUnramified_self : IsUnramified K w := rfl

variable {w}

lemma IsUnramified.eq (h : IsUnramified k w) : mult (w.comap (algebraMap k K)) = mult w := h

lemma isUnramified_iff_mult_le :
    IsUnramified k w ↔ mult w ≤ mult (w.comap (algebraMap k K)) := by
  rw [IsUnramified, le_antisymm_iff, and_iff_right]
  exact mult_comap_le _ _

variable [Algebra k F]

lemma IsUnramified.comap_algHom {w : InfinitePlace F} (h : IsUnramified k w) (f : K →ₐ[k] F) :
    IsUnramified k (w.comap (f : K →+* F)) := by
  rw [InfinitePlace.isUnramified_iff_mult_le, ← InfinitePlace.comap_comp, f.comp_algebraMap, h.eq]
  exact InfinitePlace.mult_comap_le _ _

variable (K)
variable [Algebra K F] [IsScalarTower k K F]

lemma IsUnramified.of_restrictScalars {w : InfinitePlace F} (h : IsUnramified k w) :
    IsUnramified K w := by
  rw [InfinitePlace.isUnramified_iff_mult_le, ← h.eq, IsScalarTower.algebraMap_eq k K F,
    InfinitePlace.comap_comp]
  exact InfinitePlace.mult_comap_le _ _

lemma IsUnramified.comap {w : InfinitePlace F} (h : IsUnramified k w) :
    IsUnramified k (w.comap (algebraMap K F)) :=
  h.comap_algHom (IsScalarTower.toAlgHom k K F)

variable {K}

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
  classical
  rw [← SetLike.coe_sort_coe, ← mk_embedding w]
  by_cases h : ∃ σ, ComplexEmbedding.IsConj (k := k) (embedding w) σ
  · obtain ⟨σ, hσ⟩ := h
    simp only [hσ.coe_stabilzer_mk, Nat.card_eq_fintype_card, card_ofFinset, Set.toFinset_singleton]
    by_cases 1 = σ
    · left; simp [*]
    · right; simp [*]
  · push_neg at h
    left
    trans Nat.card ({1} : Set (K ≃ₐ[k] K))
    · congr with x
      simp only [SetLike.mem_coe, mem_stabilizer_mk_iff, Set.mem_singleton_iff, or_iff_left_iff_imp,
        h x, IsEmpty.forall_iff]
    · simp

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

open scoped Classical in
lemma card_stabilizer [IsGalois k K] :
    Nat.card (Stab w) = if IsUnramified k w then 1 else 2 := by
  split
  · rwa [← isUnramified_iff_card_stabilizer_eq_one]
  · rwa [← not_isUnramified_iff_card_stabilizer_eq_two]

lemma even_nat_card_aut_of_not_isUnramified [IsGalois k K] (hw : ¬ IsUnramified k w) :
    Even (Nat.card <| K ≃ₐ[k] K) := by
  by_cases H : Finite (K ≃ₐ[k] K)
  · cases nonempty_fintype (K ≃ₐ[k] K)
    rw [even_iff_two_dvd, ← not_isUnramified_iff_card_stabilizer_eq_two.mp hw]
    exact Subgroup.card_subgroup_dvd_card (Stab w)
  · convert Even.zero
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
  · exact finrank_of_not_finite ‹_› ▸ Even.zero

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
  obtain ⟨v, rfl⟩ := comap_surjective (K := K) w
  rw [isUnramifiedIn_comap] at hw
  exact even_card_aut_of_not_isUnramified hw

lemma even_finrank_of_not_isUnramifiedIn
    [IsGalois k K] {w : InfinitePlace k} (hw : ¬ w.IsUnramifiedIn K) :
    Even (finrank k K) := by
  obtain ⟨v, rfl⟩ := comap_surjective (K := K) w
  rw [isUnramifiedIn_comap] at hw
  exact even_finrank_of_not_isUnramified hw

variable (k K)
variable [NumberField K]

open Finset in
open scoped Classical in
lemma card_isUnramified [NumberField k] [IsGalois k K] :
    #{w : InfinitePlace K | w.IsUnramified k} =
      #{w : InfinitePlace k | w.IsUnramifiedIn K} * finrank k K := by
  letI := Module.Finite.of_restrictScalars_finite ℚ k K
  rw [← IsGalois.card_aut_eq_finrank,
    Finset.card_eq_sum_card_fiberwise (f := (comap · (algebraMap k K)))
    (t := {w : InfinitePlace k | w.IsUnramifiedIn K}), ← smul_eq_mul, ← sum_const]
  · refine sum_congr rfl (fun w hw ↦ ?_)
    obtain ⟨w, rfl⟩ := comap_surjective (K := K) w
    simp only [mem_univ, forall_true_left, mem_filter, true_and] at hw
    trans #(MulAction.orbit (K ≃ₐ[k] K) w).toFinset
    · congr; ext w'
      simp only [mem_univ, forall_true_left, filter_congr_decidable, mem_filter, true_and,
        Set.mem_toFinset, mem_orbit_iff, @eq_comm _ (comap w' _), and_iff_right_iff_imp]
      intro e; rwa [← isUnramifiedIn_comap, ← e]
    · rw [← MulAction.card_orbit_mul_card_stabilizer_eq_card_group _ w,
        ← Nat.card_eq_fintype_card (α := Stab w), card_stabilizer, if_pos,
        mul_one, Set.toFinset_card]
      rwa [← isUnramifiedIn_comap]
  · simp [isUnramifiedIn_comap]

open Finset in
open scoped Classical in
lemma card_isUnramified_compl [NumberField k] [IsGalois k K] :
    #({w : InfinitePlace K | w.IsUnramified k} : Finset _)ᶜ =
      #({w : InfinitePlace k | w.IsUnramifiedIn K} : Finset _)ᶜ * (finrank k K / 2) := by
  letI := Module.Finite.of_restrictScalars_finite ℚ k K
  rw [← IsGalois.card_aut_eq_finrank,
    Finset.card_eq_sum_card_fiberwise (f := (comap · (algebraMap k K)))
    (t := ({w : InfinitePlace k | w.IsUnramifiedIn K}: Finset _)ᶜ), ← smul_eq_mul, ← sum_const]
  · refine sum_congr rfl (fun w hw ↦ ?_)
    obtain ⟨w, rfl⟩ := comap_surjective (K := K) w
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

open scoped Classical in
lemma card_eq_card_isUnramifiedIn [NumberField k] [IsGalois k K] :
    Fintype.card (InfinitePlace K) =
      #{w : InfinitePlace k | w.IsUnramifiedIn K} * finrank k K +
      #({w : InfinitePlace k | w.IsUnramifiedIn K} : Finset _)ᶜ * (finrank k K / 2) := by
  rw [← card_isUnramified, ← card_isUnramified_compl, Finset.card_add_card_compl]

end NumberField.InfinitePlace

variable (k K F)
variable [Algebra k K] [Algebra k F] [Algebra K F] [IsScalarTower k K F]

/-- A field extension is unramified at infinite places if every infinite place is unramified. -/
class IsUnramifiedAtInfinitePlaces : Prop where
  isUnramified : ∀ w : InfinitePlace K, w.IsUnramified k

instance IsUnramifiedAtInfinitePlaces.id : IsUnramifiedAtInfinitePlaces K K where
  isUnramified w := w.isUnramified_self

lemma IsUnramifiedAtInfinitePlaces.trans
    [h₁ : IsUnramifiedAtInfinitePlaces k K] [h₂ : IsUnramifiedAtInfinitePlaces K F] :
    IsUnramifiedAtInfinitePlaces k F where
  isUnramified w :=
    Eq.trans (IsScalarTower.algebraMap_eq k K F ▸ h₁.1 (w.comap (algebraMap _ _))) (h₂.1 w)

lemma IsUnramifiedAtInfinitePlaces.top [h : IsUnramifiedAtInfinitePlaces k F] :
    IsUnramifiedAtInfinitePlaces K F where
  isUnramified w := (h.1 w).of_restrictScalars K

lemma IsUnramifiedAtInfinitePlaces.bot [h₁ : IsUnramifiedAtInfinitePlaces k F]
    [Algebra.IsAlgebraic K F] :
    IsUnramifiedAtInfinitePlaces k K where
  isUnramified w := by
    obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (K := F) w
    exact (h₁.1 w).comap K

variable {K}

lemma NumberField.InfinitePlace.isUnramified [IsUnramifiedAtInfinitePlaces k K]
    (w : InfinitePlace K) : IsUnramified k w := IsUnramifiedAtInfinitePlaces.isUnramified w

variable {k} (K)

lemma NumberField.InfinitePlace.isUnramifiedIn [IsUnramifiedAtInfinitePlaces k K]
    (w : InfinitePlace k) : IsUnramifiedIn K w := fun v _ ↦ v.isUnramified k

variable {K}

lemma IsUnramifiedAtInfinitePlaces_of_odd_card_aut [IsGalois k K] [FiniteDimensional k K]
    (h : Odd (Fintype.card <| K ≃ₐ[k] K)) : IsUnramifiedAtInfinitePlaces k K :=
  ⟨fun _ ↦ not_not.mp (Nat.not_even_iff_odd.2 h ∘ InfinitePlace.even_card_aut_of_not_isUnramified)⟩

lemma IsUnramifiedAtInfinitePlaces_of_odd_finrank [IsGalois k K]
    (h : Odd (Module.finrank k K)) : IsUnramifiedAtInfinitePlaces k K :=
  ⟨fun _ ↦ not_not.mp (Nat.not_even_iff_odd.2 h ∘ InfinitePlace.even_finrank_of_not_isUnramified)⟩

variable (k K)

open Module in
lemma IsUnramifiedAtInfinitePlaces.card_infinitePlace [NumberField k] [NumberField K]
    [IsGalois k K] [IsUnramifiedAtInfinitePlaces k K] :
    Fintype.card (InfinitePlace K) = Fintype.card (InfinitePlace k) * finrank k K := by
  classical
  rw [InfinitePlace.card_eq_card_isUnramifiedIn (k := k) (K := K), Finset.filter_true_of_mem,
    Finset.card_univ, Finset.card_eq_zero.mpr, zero_mul, add_zero]
  · exact Finset.compl_univ
  simp only [Finset.mem_univ, forall_true_left, Finset.filter_eq_empty_iff]
  exact InfinitePlace.isUnramifiedIn K

namespace NumberField.InfinitePlace

variable {K : Type*} [Field K] {v : InfinitePlace K} (w : InfinitePlace K)

theorem pos_of_pos {x : K} (hv : 0 < v x) : 0 < w x := by
  rw [coe_apply] at hv ⊢
  exact v.1.pos_of_pos _ hv

variable {w}

/--
If $v$ and `w` are infinite places of `K` and `v = w ^ t` for some `t` then `t = 1`.
-/
theorem rpow_one_of_rpow_eq {t : ℝ} (h : (fun x => w x ^ t) = v) : t = 1 := by
  let ⟨ψv, hψv⟩ := v.2
  let ⟨ψw, hψw⟩ := w.2
  simp only [coe_apply, ← hψv, ← hψw, funext_iff] at h
  simpa [place_apply, map_ofNat] using congrArg (Real.logb 2) (h 2)

/--
If `v` and `w` are infinite places of `K` with equivalent underlying absolute values, then `v = w`.
-/
theorem eq_of_isEquiv (h : w.1.IsEquiv v.1) : w = v := by
  let ⟨t, _, h⟩ := h
  simp [funext_iff, rpow_one_of_rpow_eq h] at h
  exact Subtype.ext <| AbsoluteValue.ext h

variable (v)

/--
Infinite places are represented by non-trivial absolute values.
-/
theorem isNontrivial : v.1.IsNontrivial := by
  refine AbsoluteValue.isNontrivial_iff_exists_abv_one_lt.2 ⟨2, let ⟨φ, hφ⟩ := v.2; ?_⟩
  simp [← hφ, place_apply, map_ofNat]

variable {v}

open Filter in
/--
- $K$: field;
- $v$: infinite place of $K$;
- $c \in K$;
- $1 < v(c)$;
- $w(c) > 1$ for any infinite place $w\neq v$.

There is a sequence in $K$ that tends to $1$ with respect
to $v$ and tends to $0$ with respect to all other $w\neq v$.

Such a sequence is given by $\frac{1}{1 + c ^ {-n}}$.
-/
theorem exists_tendsto_one_tendsto_zero {v : InfinitePlace K} {c : K} (hv : 1 < v c)
    (h : ∀ w : InfinitePlace K, w ≠ v → w c < 1) :
    ∃ a : ℕ → K, atTop.Tendsto (β := WithAbs v.1) a (𝓝 1) ∧
      (∀ w ≠ v, atTop.Tendsto (β := WithAbs w.1) a (𝓝 0)) := by
  refine ⟨fun n => 1 / (1 + c⁻¹ ^ n), ?_, fun w hwv => ?_⟩
  · nth_rw 3 [show (1 : WithAbs v.1) = 1 / 1 by norm_num]
    apply Tendsto.div tendsto_const_nhds _ one_ne_zero
    nth_rw 2 [← add_zero (1 : WithAbs v.1)]
    apply Tendsto.const_add
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hx₁ := map_inv₀ v _ ▸ inv_lt_one_of_one_lt₀ hv
    simpa using tendsto_pow_atTop_nhds_zero_of_lt_one (AbsoluteValue.nonneg _ _) hx₁
  · simp_rw [div_eq_mul_inv, one_mul]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [norm_inv]
    apply Tendsto.inv_tendsto_atTop
    have (a : WithAbs w.1) (n : ℕ) : ‖a ^ n‖ - 1 ≤  ‖1 + a ^ n‖  := by
      simp_rw [add_comm, ← norm_one (α := WithAbs w.1), tsub_le_iff_right]
      exact norm_le_add_norm_add _ _
    apply tendsto_atTop_mono (this _) (tendsto_atTop_add_right_of_le _ (-1) _ (fun _ => le_rfl))
    refine tendsto_atTop_of_geom_le (c := w c⁻¹) (by simp) ?_ (fun n => ?_)
    · exact map_inv₀ w _ ▸ (one_lt_inv₀ (pos_of_pos w (by linarith))).2 (h w hwv)
    · simp only [map_inv₀, norm_inv, norm_pow]
      rw [pow_add, pow_one, mul_comm]
      exact le_rfl

/--
- $K$: field;
- $v$: infinite place of $K$;
- $\exists w \neq v$;

There is an $x\in K$ such that $v(x) > 1$ and $w(x) < 1$ for all $w\neq v$.
-/
theorem exists_one_lt_lt_one [NumberField K] (h : 1 < Fintype.card (InfinitePlace K)) :
    ∃ (x : K), 1 < v x ∧ ∀ w ≠ v, w x < 1 := by
  let ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (InfinitePlace K)
  have : 1 < n := by linarith [Fintype.card_fin n ▸ Fintype.card_eq.2 ⟨e⟩]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' this
  let ⟨m, hm⟩ := e.symm.surjective v
  let e₀ := e.trans (Equiv.swap 0 m)
  let ⟨x, hx⟩ := AbsoluteValue.exists_one_lt_lt_one (fun i => (e₀.symm i).isNontrivial)
      (fun i j hj => mt eq_of_isEquiv <| e₀.symm.injective.ne hj)
  refine ⟨x, hm ▸ hx.1, fun w hw => ?_⟩
  have he₀ : e₀ v = 0 := by simp [e₀, e.symm_apply_eq.1 hm]
  exact e₀.symm_apply_apply _ ▸ hx.2 (e₀ w) <| he₀ ▸ e₀.injective.ne hw

open scoped Classical in
open Filter in
variable (K) in
/--
*Weak approximation for infinite places*

The number field $K$ is dense in $\prod_v (K, v)$, where $v$ ranges over the infinite places
of $K$ and $(K, v)$ denotes $K$ equipped with the topology induced by $v$. In other words,
for any $(x_v)_v$, with $x_v\in K$, there exists a $y\in K$ such that each $|y - x_v|_v$ is
arbitrarily small.
-/
theorem denseRange_algebraMap_pi [NumberField K] :
    DenseRange <| algebraMap K ((v : InfinitePlace K) → WithAbs v.1) := by
  by_cases hcard : Fintype.card (InfinitePlace K) = 1
  · -- If there is only one infinite place this is the identity map
    letI := Fintype.equivFinOfCardEq hcard |>.unique
    let f := Homeomorph.funUnique (InfinitePlace K) (WithAbs this.default.1)
    convert DenseRange.comp f.symm.surjective.denseRange denseRange_id f.continuous_invFun <;>
    exact this.uniq _
  -- We have to show that for some `(zᵥ)ᵥ` there is a `y` in `K` that is arbitrarily close to `z`
  -- under the embedding `y ↦ (y)ᵥ`
  refine Metric.denseRange_iff.2 fun z r hr => ?_
  -- For some `v`, by previous results we can select a sequence `xᵥₙ → 1` in `v`'s topology
  -- and `→ 0` in any other infinite place topology
  have (v : InfinitePlace K) : ∃ (x : ℕ → WithAbs v.1),
    atTop.Tendsto (fun n => x n) (𝓝 1) ∧ ∀ w ≠ v,
        atTop.Tendsto (β := WithAbs w.1) (fun n => x n) (𝓝 0) := by
    haveI : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
    let ⟨_, hx⟩ := v.exists_one_lt_lt_one (by omega)
    exact exists_tendsto_one_tendsto_zero hx.1 hx.2
  choose x h using this
  -- Define the sequence `yₙ = ∑ v, xᵥₙ * zᵥ` in `K`
  let y := fun n => ∑ v, x v n * z v
  -- At each place `w` the limit of `y` with respect to `w`'s topology is `z w`.
  have : atTop.Tendsto (fun n w => (∑ v, x v n * z v : WithAbs w.1)) (𝓝 z) := by
    refine tendsto_pi_nhds.2 fun w => ?_
    simp_rw [← Finset.sum_ite_eq_of_mem _ _ _ (Finset.mem_univ w)]
    -- In `w`'s topology we have that `x v n * z v → z v`  if `v = w` else `→ 0`
    refine tendsto_finset_sum _ fun v _ => ?_
    by_cases hw : w = v
    · -- because `x w → 1` in `w`'s topology
      simp only [hw, if_true, ← congrArg (β := ℕ → K) x hw, ← congrArg z hw]
      nth_rw 2 [← one_mul (z w)]
      exact Tendsto.mul_const _ (h w).1
    · -- while `x v → 0` in `w`'s topology (v ≠ w)
      simp only [hw, if_false]
      rw [← zero_mul (z v)]
      exact Tendsto.mul_const _ <| (h v).2 w hw
  let ⟨N, h⟩ := Metric.tendsto_atTop.1 this r hr
  exact ⟨y N, dist_comm z (algebraMap K _ (y N)) ▸ h N le_rfl⟩

end NumberField.InfinitePlace

end InfinitePlace

namespace IsPrimitiveRoot

variable {K : Type*} [Field K] [NumberField K] {ζ : K} {k : ℕ}

theorem nrRealPlaces_eq_zero_of_two_lt (hk : 2 < k) (hζ : IsPrimitiveRoot ζ k) :
    NumberField.InfinitePlace.nrRealPlaces K = 0 := by
  refine (@Fintype.card_eq_zero_iff _ (_)).2 ⟨fun ⟨w, hwreal⟩ ↦ ?_⟩
  rw [NumberField.InfinitePlace.isReal_iff] at hwreal
  let f := w.embedding
  have hζ' : IsPrimitiveRoot (f ζ) k := hζ.map_of_injective f.injective
  have him : (f ζ).im = 0 := by
    rw [← Complex.conj_eq_iff_im, ← NumberField.ComplexEmbedding.conjugate_coe_eq]
    congr
  have hre : (f ζ).re = 1 ∨ (f ζ).re = -1 := by
    rw [← Complex.abs_re_eq_norm] at him
    have := Complex.norm_eq_one_of_pow_eq_one hζ'.pow_eq_one (by omega)
    rwa [← him, ← abs_one, abs_eq_abs] at this
  cases hre with
  | inl hone =>
    exact hζ'.ne_one (by omega) <| Complex.ext (by simp [hone]) (by simp [him])
  | inr hnegone =>
    replace hζ' := hζ'.eq_orderOf
    simp only [show f ζ = -1 from Complex.ext (by simp [hnegone]) (by simp [him]),
      orderOf_neg_one, ringChar.eq_zero, OfNat.zero_ne_ofNat, ↓reduceIte] at hζ'
    omega

end IsPrimitiveRoot

/-!

## The infinite place of the rationals.

-/

namespace Rat

open NumberField

/-- The infinite place of `ℚ`, coming from the canonical map `ℚ → ℂ`. -/
noncomputable def infinitePlace : InfinitePlace ℚ := .mk (Rat.castHom _)

@[simp]
lemma infinitePlace_apply (v : InfinitePlace ℚ) (x : ℚ) : v x = |x| := by
  rw [NumberField.InfinitePlace.coe_apply]
  obtain ⟨_, _, rfl⟩ := v
  simp

instance : Subsingleton (InfinitePlace ℚ) where
  allEq a b := by ext; simp

lemma isReal_infinitePlace : InfinitePlace.IsReal (infinitePlace) :=
  ⟨Rat.castHom ℂ, by ext; simp, rfl⟩

end Rat

/-

## Totally real number fields

-/

namespace NumberField

/-- A number field `K` is totally real if all of its infinite places
are real. In other words, the image of every ring homomorphism `K → ℂ`
is a subset of `ℝ`. -/
class IsTotallyReal (K : Type*) [Field K] [NumberField K] where
  isReal : ∀ v : InfinitePlace K, v.IsReal

instance : IsTotallyReal ℚ where
  isReal v := by
    rw [Subsingleton.elim v Rat.infinitePlace]
    exact Rat.isReal_infinitePlace

end NumberField
