/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.NumberTheory.NumberField.InfinitePlace.Completion
import Mathlib.NumberTheory.RamificationInertia.Basic

/-!
# Dimensions of completions at infinite places

Let `L/K` and `w` be an infinite place of `L` lying above the infinite place `v` of `K`.
In this file, we prove:
- the sum of the ramification indices of all such places `w` is the same as `[L : K]`;
- the `v.Completion` dimension of `w.Completion` is equal to the ramification index.
-/

noncomputable section

namespace NumberField.InfinitePlace

open NumberField.ComplexEmbedding Finset

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

variable {v : InfinitePlace K} (w : InfinitePlace L)

variable (L v)

theorem bijOn_sumElim_conjugate :
    (Set.sumEquiv.symm (ramifiedPlacesOver L v, ramifiedPlacesOver L v)).BijOn
      (Sum.elim embedding (conjugate ∘ embedding)) (mixedEmbeddingsOver L v.embedding) :=
  ⟨.sumElim embedding_mem_mixedEmbeddingsOver conjugate_embedding_mem_mixedEmbeddingsOver,
    (embedding_injective L).injOn.sumElim (star_injective.comp (embedding_injective L)).injOn
      (fun _ _ _ h ↦ h.2.ne_conjugate), fun ψ h ↦ by cases embedding_mk_eq ψ with
        | inl hl => simpa using .inl ⟨mk ψ, mk_mem_ramifiedPlacesOver h, hl⟩
        | inr hr => simpa using .inr ⟨mk ψ, mk_mem_ramifiedPlacesOver h, by aesop⟩⟩

/-- The number of mixed embeddings over an infinite place is twice the number of ramified places
over the place. -/
theorem ramifiedPlacesOver_ncard [NumberField L] :
    2 * (ramifiedPlacesOver L v).ncard = (mixedEmbeddingsOver L v.embedding).ncard := by
  rw [← (bijOn_sumElim_conjugate L v).ncard_eq, two_mul, Set.ncard_eq_toFinset_card,
    Set.ncard_eq_toFinset_card]
  convert (card_disjSum _ _).symm
  ext; aesop

open scoped Classical in
private def embeddingConjugateIte (v : InfinitePlace K) (w : InfinitePlace L) : L →+* ℂ :=
  if ComplexEmbedding.LiesOver w.embedding v.embedding then w.embedding else conjugate w.embedding

private theorem embeddingConjugateIte_pos {v : InfinitePlace K} {w : InfinitePlace L}
    (h : ComplexEmbedding.LiesOver w.embedding v.embedding) :
    embeddingConjugateIte L v w = w.embedding := by simp [embeddingConjugateIte, h]

private theorem embeddingConjugateIte_neg {v : InfinitePlace K} {w : InfinitePlace L}
    (h : ¬ComplexEmbedding.LiesOver w.embedding v.embedding) :
    embeddingConjugateIte L v w = conjugate w.embedding := by simp [embeddingConjugateIte, h]

private theorem mapsTo_embeddingConjugateIte (v : InfinitePlace K) :
    Set.MapsTo (embeddingConjugateIte L v) (unramifiedPlacesOver L v)
      (unmixedEmbeddingsOver L v.embedding) := by
  intro w hw
  obtain ⟨_, hw⟩ := hw
  by_cases h : ComplexEmbedding.LiesOver w.embedding v.embedding
  · simpa [embeddingConjugateIte_pos L h] using ⟨h, hw.isUnmixed⟩
  · simpa [embeddingConjugateIte_neg L h] using
      ⟨⟨(LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w v).resolve_left
        (liesOver_iff.not.1 h)⟩, hw.isUnmixed_conjugate⟩

private theorem surjOn_embeddingConjugateIte (v : InfinitePlace K) :
    Set.SurjOn (embeddingConjugateIte L v) (unramifiedPlacesOver L v)
      (unmixedEmbeddingsOver L v.embedding) := by
  intro ψ h
  refine ⟨mk ψ, mk_mem_unramifiedPlacesOver h, ?_⟩
  rcases embedding_mk_eq ψ with (_ | hψ)
  · aesop (add simp [embeddingConjugateIte, unmixedEmbeddingsOver])
  · simp_all only [unmixedEmbeddingsOver, IsUnmixed, Set.mem_setOf_eq, embeddingConjugateIte,
      star_star, ite_eq_right_iff]
    intro hψ
    have := hψ.over
    have := h.1.over
    aesop

open scoped Classical in
private theorem bijOn_extensionIte :
    Set.BijOn (embeddingConjugateIte L v) (unramifiedPlacesOver L v)
      (unmixedEmbeddingsOver L v.embedding) :=
  ⟨mapsTo_embeddingConjugateIte L v, star_involutive.injective_ite (embedding_injective _)
    (fun _ _ ↦ eq_of_embedding_eq_conjugate L) |>.injOn, surjOn_embeddingConjugateIte L v⟩

/-- The number of unramified places over an infinite place is equal to the number of unmixed
embeddings over the place. -/
theorem unramifiedPlacesOver_ncard [NumberField L] :
    (unramifiedPlacesOver L v).ncard = (unmixedEmbeddingsOver L v.embedding).ncard := by
  rw [(bijOn_extensionIte L v).ncard_eq]

namespace LiesOver

variable [w.1.LiesOver v.1]

set_option backward.isDefEq.respectTransparency false in
scoped instance : Algebra v.Completion w.Completion :=
  (LiesOver.isometry_algebraMap w v).mapRingHom.toAlgebra

set_option backward.isDefEq.respectTransparency false in
scoped instance : IsScalarTower K v.Completion w.Completion :=
  .of_algebraMap_eq fun x ↦ by
    simp_rw [RingHom.algebraMap_toAlgebra, UniformSpace.Completion.algebraMap_def,
      Isometry.mapRingHom_coe]
    simp [WithAbs.algebraMap_left_apply, WithAbs.algebraMap_right_apply]

set_option backward.isDefEq.respectTransparency false in
scoped instance : ContinuousSMul v.Completion w.Completion where
  continuous_smul := (UniformSpace.Completion.continuous_map.comp continuous_fst).mul
    (Continuous.comp continuous_id continuous_snd)

end LiesOver

open scoped LiesOver

namespace Completion

open AbsoluteValue.Completion NumberField.ComplexEmbedding

variable {K : Type*} [Field K] {v : InfinitePlace K}
variable {L : Type*} [Field L] [Algebra K L]
variable [Algebra v.Completion w.Completion]

set_option backward.isDefEq.respectTransparency false in
variable (v) in
/-- If `w` is a ramified place over `v` then `w.Completion` has `v.Completion` dimension two. -/
theorem finrank_eq_two_of_isRamified (w : InfinitePlace L) [w.1.LiesOver v.1]
    (h : w.IsRamified K) : Module.finrank v.Completion w.Completion = 2 := by
  letI := LiesOver.extensionEmbedding_liesOver_of_isReal w <| h.liesOver_isReal_under w v
  rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivRealOfIsReal <| h.liesOver_isReal_under w v)
      (ringEquivComplexOfIsComplex h.isComplex) (by ext; simp [this.over_apply]),
    Complex.finrank_real_complex]

variable {L : Type*} [Field L] [Algebra K L]

set_option backward.isDefEq.respectTransparency false in
variable (v) in
/-- If `w` is an unramified place over `v` then `w.Completion` has `v.Completion` dimension one. -/
theorem finrank_eq_one_of_isUnramified (w : InfinitePlace L) [w.1.LiesOver v.1]
    (h : w.IsUnramified K) : Module.finrank v.Completion w.Completion = 1 := by
  by_cases hv : v.IsReal
  · letI := LiesOver.extensionEmbedding_liesOver_of_isReal w hv
    rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivRealOfIsReal hv) (ringEquivRealOfIsReal
        (h.liesOver_isReal_over _ _ hv)) (RingHom.ext fun _ ↦ Complex.ofReal_inj.1 <| by
        simp [this.over_apply]), Module.finrank_self]
  · have hv : v.IsComplex := not_isReal_iff_isComplex.1 hv
    cases LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w v with
    | inl hl =>
      letI : ComplexEmbedding.LiesOver w.embedding v.embedding := ⟨hl⟩
      letI := liesOver_extensionEmbedding w v
      rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivComplexOfIsComplex hv)
          (ringEquivComplexOfIsComplex (LiesOver.isComplex_of_isComplex_under _ hv))
          (by ext; simp [this.over_apply]), Module.finrank_self]
    | inr hr =>
      letI : ComplexEmbedding.LiesOver (conjugate w.embedding) v.embedding := ⟨hr⟩
      letI := liesOver_conjugate_extensionEmbedding w v
      rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivComplexOfIsComplex hv)
        ((ringEquivComplexOfIsComplex (LiesOver.isComplex_of_isComplex_under _ hv)).trans
          (starRingAut (R := ℂ))) (by ext; simp [← conjugate_coe_eq, this.over_apply]),
        Module.finrank_self]

end Completion

open Completion

/-- The degree of `L` over `K` is equal to the number of unramified places over `v` plus twice the
number of ramified places over `v`. -/
theorem add_placesOver_ncard_eq_finrank [NumberField K] [NumberField L] :
    (unramifiedPlacesOver L v).ncard + 2 * (ramifiedPlacesOver L v).ncard = Module.finrank K L := by
  classical
  letI : Algebra K ℂ := v.embedding.toAlgebra
  rw [← AlgHom.card K L ℂ, ramifiedPlacesOver_ncard, unramifiedPlacesOver_ncard,
    ← Set.ncard_union_eq (disjoint_unmixedEmbeddingsOver_mixedEmbeddingsOver L v.embedding),
    union_unmixedEmbeddingsOver_mixedEmbeddingsOver, Set.ncard_eq_toFinset_card]
  apply (card_nbij AlgHom.toRingHom (fun σ _ ↦ by simpa using ⟨by aesop⟩)
    AlgHom.coe_ringHom_injective.injOn (fun ψ hψ ↦ ?_)).symm
  simp only [Set.Finite.toFinset_setOf, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hψ
  exact ⟨⟨ψ, fun _ ↦ by simp [RingHom.algebraMap_toAlgebra, ← hψ.over]⟩, by simp⟩

variable {L}

open scoped Classical in
protected def inertiaDeg (w : InfinitePlace L) : ℕ :=
  if _ : w.1.LiesOver v.1 then (⊥ : Ideal v.Completion).inertiaDeg (⊥ : Ideal w.Completion) else 0

theorem inertiaDeg_of_liesOver (w : InfinitePlace L) [w.1.LiesOver v.1] :
    v.inertiaDeg w = (⊥ : Ideal v.Completion).inertiaDeg (⊥ : Ideal w.Completion) := by
  simp [InfinitePlace.inertiaDeg, dif_pos]

theorem inertiaDeg_eq_finrank (v : InfinitePlace K) (w : InfinitePlace L) [w.1.LiesOver v.1] :
    v.inertiaDeg w = Module.finrank v.Completion w.Completion := by
  simp only [inertiaDeg_of_liesOver, Ideal.inertiaDeg, Ideal.comap_bot_of_injective _ <|
    FaithfulSMul.algebraMap_injective v.Completion w.Completion]
  apply Algebra.finrank_eq_of_equiv_equiv (RingEquiv.quotientBot v.Completion)
    (RingEquiv.quotientBot w.Completion)
  ext; simp [RingHom.algebraMap_toAlgebra]

variable {v w} in
open Completion in
theorem inertiaDeg_eq_one (hw : w ∈ unramifiedPlacesOver L v) : v.inertiaDeg w = 1 :=
  have := hw.1; finrank_eq_one_of_isUnramified v w hw.2 ▸ inertiaDeg_eq_finrank v w

variable {v w} in
open Completion in
theorem inertiaDeg_eq_two (hw : w ∈ ramifiedPlacesOver L v) : v.inertiaDeg w = 2 :=
  have := hw.1; finrank_eq_two_of_isRamified v w hw.2 ▸ inertiaDeg_eq_finrank v w

variable (K L) in
open scoped Classical in
open Completion Finset Set in
/-- The degree of `L` over `K` is equal to the sum of the inertia degrees of the places over `v`. -/
theorem sum_inertiaDeg_eq_finrank [NumberField K] [NumberField L] :
    ∑ w ∈ v.placesOver L, v.inertiaDeg w = Module.finrank K L := by
  rw [← union_ramifiedPlacesOver_unramifiedPlacesOver L v, toFinset_union,
    sum_union (Set.disjoint_toFinset.2 <| disjoint_ramifiedPlacesOver_unramifiedPlacesOver L v),
    sum_congr rfl (fun _ h ↦ inertiaDeg_eq_two (by simpa using h)),
    sum_congr rfl (fun _ h ↦ inertiaDeg_eq_one (by simpa using h)), sum_const, add_comm]
  simp [← add_placesOver_ncard_eq_finrank L v, mul_comm, ncard_eq_toFinset_card']

end NumberField.InfinitePlace
