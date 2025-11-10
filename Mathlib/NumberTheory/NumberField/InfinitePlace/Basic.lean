/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Topology.Instances.Complex

/-!
# Infinite places of a number field

This file defines the infinite places of a number field.

## Main Definitions and Results

* `NumberField.InfinitePlace`: the type of infinite places of a number field `K`.
* `NumberField.InfinitePlace.mk_eq_iff`: two complex embeddings define the same infinite place iff
  they are equal or complex conjugates.
* `NumberField.InfinitePlace.IsReal`: The predicate on infinite places saying
  that a place is real, i.e., defined by a real embedding.
* `NumberField.InfinitePlace.IsComplex`: The predicate on infinite places saying
  that a place is complex, i.e., defined by a complex embedding that is not real.
* `NumberField.InfinitePlace.mult`: the multiplicity of an infinite place, that is the number of
  distinct complex embeddings that define it. So it is equal to `1` if the place is real and `2`
  if the place is complex.
* `NumberField.InfinitePlace.prod_eq_abs_norm`: the infinite part of the product formula, that is
  for `x ∈ K`, we have `Π_w ‖x‖_w = |norm(x)|` where the product is over the infinite place `w` and
  `‖·‖_w` is the normalized absolute value for `w`.
* `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank`: the degree of `K` is equal to the
  number of real places plus twice the number of complex places.

## Tags

number field, infinite places
-/

open scoped Finset

open NumberField Fintype Module

variable {k : Type*} [Field k] (K : Type*) [Field K] {F : Type*} [Field F]

/-- An infinite place of a number field `K` is a place associated to a complex embedding. -/
def NumberField.InfinitePlace := { w : AbsoluteValue K ℝ // ∃ φ : K →+* ℂ, place φ = w }

instance [NumberField K] : Nonempty (NumberField.InfinitePlace K) := Set.instNonemptyRange _

variable {K}

/-- Return the infinite place defined by a complex embedding `φ`. -/
noncomputable def NumberField.InfinitePlace.mk (φ : K →+* ℂ) : NumberField.InfinitePlace K :=
  ⟨place φ, ⟨φ, rfl⟩⟩

namespace NumberField.InfinitePlace

instance {K : Type*} [Field K] : FunLike (InfinitePlace K) K ℝ where
  coe w x := w.1 x
  coe_injective' _ _ h := Subtype.eq (AbsoluteValue.ext fun x => congr_fun h x)

lemma coe_apply {K : Type*} [Field K] (v : InfinitePlace K) (x : K) : v x = v.1 x := rfl

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

variable (K) in
theorem embedding_injective : (embedding (K := K)).Injective :=
  fun _ _ h ↦ by simpa using congr_arg mk h

@[simp]
theorem embedding_inj {v₁ v₂ : InfinitePlace K} : v₁.embedding = v₂.embedding ↔ v₁ = v₂ :=
  (embedding_injective _).eq_iff

variable (K) in
theorem conjugate_embedding_injective :
    (fun (v : InfinitePlace K) ↦ ComplexEmbedding.conjugate v.embedding).Injective :=
  star_injective.comp <| embedding_injective K

variable (K) in
theorem eq_of_embedding_eq_conjugate {v₁ v₂ : InfinitePlace K}
    (h : v₁.embedding = ComplexEmbedding.conjugate v₂.embedding) : v₁ = v₂ := by
  rw [← mk_embedding v₁, h, mk_conjugate_eq, mk_embedding]

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

/-- An infinite place is complex if it is defined by a complex (i.e. not real) embedding. -/
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

@[simp]
theorem mult_isReal (w : {w : InfinitePlace K // IsReal w}) :
    mult w.1 = 1 := by
  rw [mult, if_pos w.prop]

@[simp]
theorem mult_isComplex (w : {w : InfinitePlace K // IsComplex w}) :
    mult w.1 = 2 := by
  rw [mult, if_neg (not_isReal_iff_isComplex.mpr w.prop)]

theorem mult_pos {w : InfinitePlace K} : 0 < mult w := by
  rw [mult]
  split_ifs <;> norm_num

@[simp]
theorem mult_ne_zero {w : InfinitePlace K} : mult w ≠ 0 := ne_of_gt mult_pos

theorem mult_coe_ne_zero {w : InfinitePlace K} : (mult w : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr mult_ne_zero

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

open scoped Classical in
@[to_additive]
theorem prod_eq_prod_mul_prod {α : Type*} [CommMonoid α] [NumberField K] (f : InfinitePlace K → α) :
    ∏ w, f w = (∏ w : {w // IsReal w}, f w.1) * (∏ w : {w // IsComplex w}, f w.1) := by
  rw [← Equiv.prod_comp (Equiv.subtypeEquivRight (fun _ ↦ not_isReal_iff_isComplex))]
  simp [Fintype.prod_subtype_mul_prod_subtype]

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

variable [NumberField K]

/-- The infinite part of the product formula : for `x ∈ K`, we have `Π_w ‖x‖_w = |norm(x)|` where
`‖·‖_w` is the normalized absolute value for `w`. -/
theorem prod_eq_abs_norm (x : K) :
    ∏ w : InfinitePlace K, w x ^ mult w = abs (Algebra.norm ℚ x) := by
  classical
  convert (congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ x)).symm
  · rw [norm_prod, ← Fintype.prod_equiv RingHom.equivRatAlgHom (fun f => ‖f x‖)
      (fun φ => ‖φ x‖) fun _ => by simp [RingHom.equivRatAlgHom_apply]]
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
      simp only [RingHom.toRatAlgHom_apply] at hψ
      rw [← norm_embedding_eq, hψ] at h
      contrapose! h
      exact h₂ h.symm
    rw [(mk_embedding w).symm, mk_eq_iff] at main
    cases h₃ with
    | inl hw =>
      rw [conjugate_embedding_eq_of_isReal hw, or_self] at main
      exact congr_arg RingHom.toRatAlgHom main
    | inr hw =>
      refine congr_arg RingHom.toRatAlgHom (main.resolve_right fun h' ↦ hw.not_ge ?_)
      have : (embedding w x).im = 0 := by
        rw [← Complex.conj_eq_iff_im]
        have := RingHom.congr_fun h' x
        simp at this
        rw [this]
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

variable (K)

open scoped Classical in
/-- The number of infinite real places of the number field `K`. -/
noncomputable abbrev nrRealPlaces := card { w : InfinitePlace K // IsReal w }

open scoped Classical in
/-- The number of infinite complex places of the number field `K`. -/
noncomputable abbrev nrComplexPlaces := card { w : InfinitePlace K // IsComplex w }

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

theorem nrRealPlaces_pos_of_odd_finrank (h : Odd (finrank ℚ K)) :
    0 < nrRealPlaces K := by
  refine Nat.pos_of_ne_zero ?_
  by_contra hc
  refine (Nat.not_odd_iff_even.mpr ?_) h
  rw [← card_add_two_mul_card_eq_rank, hc, zero_add]
  exact even_two_mul (nrComplexPlaces K)

namespace IsPrimitiveRoot

variable {ζ : K} {k : ℕ}

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
    have := Complex.norm_eq_one_of_pow_eq_one hζ'.pow_eq_one (by cutsat)
    rwa [← him, ← abs_one, abs_eq_abs] at this
  cases hre with
  | inl hone =>
    exact hζ'.ne_one (by cutsat) <| Complex.ext (by simp [hone]) (by simp [him])
  | inr hnegone =>
    replace hζ' := hζ'.eq_orderOf
    simp only [show f ζ = -1 from Complex.ext (by simp [hnegone]) (by simp [him]),
      orderOf_neg_one, ringChar.eq_zero, OfNat.zero_ne_ofNat, ↓reduceIte] at hζ'
    cutsat

end IsPrimitiveRoot

end NumberField.InfinitePlace

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
