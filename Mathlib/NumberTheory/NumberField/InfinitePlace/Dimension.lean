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
    Set.BijOn (Sum.elim embedding (conjugate ∘ embedding))
      (Set.sumEquiv.symm ((ramifiedPlacesOver L v), (ramifiedPlacesOver L v)))
      (mixedEmbeddingsOver L v.embedding) := by
  refine ⟨?_, ?_, fun ψ h ↦ ?_⟩
  · exact Set.MapsTo.sumElim embedding_mem_mixedEmbeddingsOver
      conjugate_embedding_mem_mixedEmbeddingsOver
  · exact (embedding_injective L).injOn.sumElim (star_injective.comp (embedding_injective L)).injOn
      (fun _ _ _ h ↦ h.2.ne_conjugate)
  · cases embedding_mk_eq ψ with
    | inl hl => simpa [Set.sumEquiv] using .inl ⟨mk ψ, mk_mem_ramifiedPlacesOver h, hl⟩
    | inr hr => simpa [Set.sumEquiv] using .inr ⟨_, mk_mem_ramifiedPlacesOver h, by aesop⟩

-- theorem _root_.Set.BijOn.ncard_eq {α β : Type*} {f : α → β} {s : Set α} {t : Set β}
--     (h : Set.BijOn f s t) :
--     s.ncard = t.ncard :=
--   Set.ncard_congr _ h.mapsTo (fun _ _ ha hb heq ↦ h.injOn ha hb heq)
--     (fun _ ha ↦ bex_def.2 (h.surjOn ha))

theorem _root_.Set.BijOn_toFinset {α β : Type*} {f : α → β} {s : Set α} {t : Set β}
    (hs : s.Finite := by toFinite_tac) (ht : t.Finite := by toFinite_tac) :
    Set.BijOn f s t ↔ Set.BijOn f ↑(hs.toFinset) ↑(ht.toFinset) := by
  simp only [Set.Finite.coe_toFinset]

alias ⟨_root_.Set.BijOn.toFinset, _⟩ := Set.BijOn_toFinset

theorem ramifiedPlacesOver_ncard [NumberField L] :
    2 * (ramifiedPlacesOver L v).ncard = (mixedEmbeddingsOver L v.embedding).ncard := by
  rw [Set.ncard_eq_toFinset_card, Set.ncard_eq_toFinset_card,
    ← (bijOn_sumElim_conjugate L v).toFinset.finsetCard_eq]
  rw [two_mul]
  convert (card_disjSum _ _).symm
  ext; aesop (add simp [Set.sumEquiv])

open scoped Classical in
def embeddingConjugateIte (v : InfinitePlace K) :
    InfinitePlace L → L →+* ℂ :=
  fun w ↦ if ComplexEmbedding.LiesOver w.embedding v.embedding then w.embedding else conjugate w.embedding

theorem embeddingConjugateIte_pos {v : InfinitePlace K} {w : InfinitePlace L}
    (h : ComplexEmbedding.LiesOver w.embedding v.embedding) :
    embeddingConjugateIte L v w = w.embedding := by
  simp [embeddingConjugateIte, h]

theorem embeddingConjugateIte_neg {v : InfinitePlace K} {w : InfinitePlace L}
    (h : ¬ComplexEmbedding.LiesOver w.embedding v.embedding) :
    embeddingConjugateIte L v w = conjugate w.embedding := by
  simp [embeddingConjugateIte, h]

theorem _root_.Function.Involutive.injective_ite {α β : Type*} {p : α → Prop} [DecidablePred p]
    {f : α → β} {g : β → β} (hf : Function.Injective f) (hg : Function.Involutive g)
    (hfg : ∀ x y, f x = g (f y) → x = y) :
    Function.Injective (fun x ↦ if p x then f x else g (f x)) := by
  intro x y h
  dsimp at h
  split_ifs at h
  · exact hf h
  · exact hfg _ _ h
  · exact hfg _ _ <| hg.eq_iff.1 h
  · exact hf <| hg.injective h

theorem not_liesOver {φ : L →+* ℂ} {ψ : K →+* ℂ} :
    ¬ComplexEmbedding.LiesOver φ ψ ↔ ¬φ.comp (algebraMap K L) = ψ := by
  apply Iff.not
  exact ⟨fun h ↦ h.over, fun h ↦ ⟨h⟩⟩

theorem mapsTo_embeddingConjugateIte (v : InfinitePlace K) :
    Set.MapsTo (embeddingConjugateIte L v) (unramifiedPlacesOver L v)
      (unmixedEmbeddingsOver L v.embedding) := by
  intro w hw
  obtain ⟨_, hw⟩ := hw
  by_cases h : ComplexEmbedding.LiesOver w.embedding v.embedding
  · simpa [embeddingConjugateIte_pos L h] using ⟨h, hw.isUnmixed⟩
  · simpa [embeddingConjugateIte_neg L h] using
      ⟨⟨(LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w v).resolve_left (by
        simp [not_liesOver] at h
        exact h)⟩ ,
        hw.isUnmixed_conjugate⟩

theorem surjOn_embeddingConjugateIte (v : InfinitePlace K) :
    Set.SurjOn (embeddingConjugateIte L v) (unramifiedPlacesOver L v)
      (unmixedEmbeddingsOver L v.embedding) := by
  intro ψ h
  refine ⟨mk ψ, mk_mem_unramifiedPlacesOver h, ?_⟩
  rcases embedding_mk_eq ψ with (_ | _)
  · aesop (add simp [embeddingConjugateIte, unmixedEmbeddingsOver])
  · aesop (add simp [embeddingConjugateIte, unmixedEmbeddingsOver, conjugate_comp,
      ComplexEmbedding.LiesOver, IsUnmixed, IsMixed])
    rw [← h_1]
    have := a.over
    have := left.over
    aesop

open scoped Classical in
theorem bijOn_extensionIte :
    Set.BijOn (embeddingConjugateIte L v) (unramifiedPlacesOver L v)
      (unmixedEmbeddingsOver L v.embedding) :=
  ⟨mapsTo_embeddingConjugateIte L v, star_involutive.injective_ite (embedding_injective _)
    (fun _ _ ↦ eq_of_embedding_eq_conjugate L) |>.injOn,
      surjOn_embeddingConjugateIte L v⟩

theorem unramifiedPlacesOver_ncard [NumberField L] :
    (unramifiedPlacesOver L v).ncard = (unmixedEmbeddingsOver L v.embedding).ncard := by
  rw [Set.ncard_eq_toFinset_card, Set.ncard_eq_toFinset_card,
    (bijOn_extensionIte L v).toFinset.finsetCard_eq]

namespace Completion

open AbsoluteValue.Completion NumberField.ComplexEmbedding

variable {K : Type*} [Field K] {v : InfinitePlace K}
variable {L : Type*} [Field L] [Algebra K L]
variable [Algebra v.Completion w.Completion]

variable (v) in
theorem finrank_eq_two_of_isRamified (w : InfinitePlace L)
    [Algebra v.Completion w.Completion] [w.1.LiesOver v.1]
    [IsScalarTower K v.Completion w.Completion] [ContinuousSMul v.Completion w.Completion]
    (h : w.IsRamified K) :
    Module.finrank v.Completion w.Completion = 2 := by
  erw [Algebra.finrank_eq_of_equiv_equiv (ringEquivRealOfIsReal <| h.liesOver_isReal_under w v)
      (ringEquivComplexOfIsComplex h.isComplex) (by
        erw [(LiesOver.extensionEmbedding_liesOver_of_isReal w <| h.liesOver_isReal_under w v).over]
        simp [RingHom.ext_iff]
        intro
        erw [RingEquiv.ofBijective_apply]
        rw [extensionEmbeddingOfIsReal_apply]),
    Complex.finrank_real_complex]

variable {L : Type*} [Field L] [Algebra K L]

variable (v) in
/-- If `w` is an unramified extension of `v` and both infinite places are complex then
the `v.Completion`-dimension of `w.Completion` is `1`. -/
theorem finrank_eq_one_of_isUnramified (w : InfinitePlace L)
    [Algebra v.Completion w.Completion] [w.1.LiesOver v.1]
    [IsScalarTower K v.Completion w.Completion] [ContinuousSMul v.Completion w.Completion]
    (h : w.IsUnramified K) :
    Module.finrank v.Completion w.Completion = 1 := by
  by_cases hv : v.IsReal
  · rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivRealOfIsReal hv) (ringEquivRealOfIsReal
      (h.liesOver_isReal_over _ _ hv)) (RingHom.ext fun _ ↦ Complex.ofReal_inj.1 <| by
        have := (LiesOver.extensionEmbedding_liesOver_of_isReal w hv).over
        change ((algebraMap ℝ ℝ).comp (extensionEmbeddingOfIsReal hv) _ : ℂ) = _
        simp [← this]
        change _ = ((extensionEmbeddingOfIsReal _) _ : ℂ)
        simp), Module.finrank_self]
  · have hv : v.IsComplex := not_isReal_iff_isComplex.1 hv
    cases LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w v with
    | inl hl => rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivComplexOfIsComplex hv)
        (ringEquivComplexOfIsComplex (LiesOver.isComplex_of_isComplex_under _ hv))
        (RingHom.ext fun _ ↦ by
          simp
          letI : ComplexEmbedding.LiesOver w.embedding v.embedding := ⟨hl⟩
          have := (liesOver_extensionEmbedding (v := v) w).over
          simp [RingHom.ext_iff] at this
          erw [this]
          rfl),
        Module.finrank_self]
    | inr hr => rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivComplexOfIsComplex hv)
        ((ringEquivComplexOfIsComplex (LiesOver.isComplex_of_isComplex_under _ hv)).trans
          (starRingAut (R := ℂ)))
        (RingHom.ext fun _ ↦ by
          simp
          letI : ComplexEmbedding.LiesOver (conjugate w.embedding) (v.embedding) := ⟨hr⟩
          have := (liesOver_conjugate_extensionEmbedding (v := v) (w)).over
          simp [RingHom.ext_iff] at this
          erw [this]
          rfl),
        Module.finrank_self]

end Completion

open Completion

open scoped Classical in
theorem ncard_isUnramified_add_two_mul_ncard_isRamified [NumberField K] [NumberField L] :
    (unramifiedPlacesOver L v).ncard + 2 * (ramifiedPlacesOver L v).ncard = Module.finrank K L := by
  letI : Algebra K ℂ := v.embedding.toAlgebra
  rw [← AlgHom.card K L ℂ, ramifiedPlacesOver_ncard, unramifiedPlacesOver_ncard,
    ← Set.ncard_union_eq (disjoint_unmixedEmbeddingsOver_mixedEmbeddingsOver L v.embedding),
    union_unmixedEmbeddingsOver_mixedEmbeddingsOver, Set.ncard_eq_toFinset_card]
  apply (card_nbij AlgHom.toRingHom (fun σ _ ↦ by simp; apply LiesOver.mk; simp [σ.commutes, RingHom.algebraMap_toAlgebra]) -- [LiesOver, RingHom.algebraMap_toAlgebra])
    AlgHom.coe_ringHom_injective.injOn (fun ψ hψ ↦ ?_)).symm
  simp only [Set.Finite.toFinset_setOf, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hψ
  exact ⟨⟨ψ, fun _ ↦ by simp [RingHom.algebraMap_toAlgebra, ← hψ.over]⟩, by simp⟩

namespace LiesOver

variable [w.1.LiesOver v.1]

set_option backward.isDefEq.respectTransparency false in
scoped instance : Algebra v.Completion w.Completion :=
  (LiesOver.isometry_algebraMap (v := v) w).mapRingHom.toAlgebra

set_option backward.isDefEq.respectTransparency false in
scoped instance : IsScalarTower K v.Completion w.Completion :=
  .of_algebraMap_eq fun x ↦ by
    simp [RingHom.algebraMap_toAlgebra]
    erw [Isometry.mapRingHom_coe]
    rfl

set_option backward.isDefEq.respectTransparency false in
scoped instance : ContinuousSMul v.Completion w.Completion where
  continuous_smul := by
    simp_rw [RingHom.smul_toAlgebra]
    apply (UniformSpace.Completion.continuous_map.comp continuous_fst).mul
      (Continuous.comp continuous_id continuous_snd)

end LiesOver

open scoped LiesOver

variable {L} in
open scoped Classical in
protected def inertiaDeg (w : InfinitePlace L) : ℕ :=
  if _ : w.1.LiesOver v.1 then (⊥ : Ideal v.Completion).inertiaDeg (⊥ : Ideal w.Completion) else 0

theorem inertiaDeg_of_liesOver (w : InfinitePlace L) [w.1.LiesOver v.1] :
    v.inertiaDeg w = (⊥ : Ideal v.Completion).inertiaDeg (⊥ : Ideal w.Completion) := by
  simp [InfinitePlace.inertiaDeg, dif_pos]

variable {L} in
theorem inertiaDeg_eq_finrank (v : InfinitePlace K) (w : InfinitePlace L) [w.1.LiesOver v.1] :
    v.inertiaDeg w = Module.finrank v.Completion w.Completion := by
  simp only [inertiaDeg_of_liesOver, Ideal.inertiaDeg, Ideal.comap_bot_of_injective _ <|
    FaithfulSMul.algebraMap_injective v.Completion w.Completion]
  apply Algebra.finrank_eq_of_equiv_equiv (RingEquiv.quotientBot v.Completion)
    (RingEquiv.quotientBot w.Completion)
  ext; simp [RingHom.algebraMap_toAlgebra]

variable {L} in
open Completion in
theorem inertiaDeg_eq_one (w : InfinitePlace L)
    (hw : w ∈ unramifiedPlacesOver L v) : v.inertiaDeg w = 1 := by
  have := hw.1
  exact finrank_eq_one_of_isUnramified v w hw.2 ▸ inertiaDeg_eq_finrank v w

variable {L} in
open Completion in
theorem inertiaDeg_eq_two (w : InfinitePlace L)
    (hw : w ∈ ramifiedPlacesOver L v) : v.inertiaDeg w = 2 := by
  have := hw.1
  exact finrank_eq_two_of_isRamified v w hw.2 ▸ inertiaDeg_eq_finrank v w

open scoped Classical in
open Completion Finset in
theorem sum_inertiaDeg_eq_finrank [NumberField K] [NumberField L] :
    ∑ w ∈ v.placesOver L, v.inertiaDeg w = Module.finrank K L := by
  simp [← union_ramifiedPlacesOver_unramifiedPlacesOver L v,
    sum_union (Set.disjoint_toFinset.2 <| disjoint_ramifiedPlacesOver_unramifiedPlacesOver L v)]
  rw [sum_congr rfl (fun _ h ↦ inertiaDeg_eq_two v _ (by simpa using h))]
  rw [sum_congr rfl (fun _ h ↦ inertiaDeg_eq_one v _ (by simpa using h))]
  simp only [sum_const]
  simp [← ncard_isUnramified_add_two_mul_ncard_isRamified L v, add_comm, mul_comm,
    Set.ncard_eq_toFinset_card']

end NumberField.InfinitePlace
