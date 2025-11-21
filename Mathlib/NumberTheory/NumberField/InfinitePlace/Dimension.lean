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

open NumberField.ComplexEmbedding ramifiedPlacesOver unmixedEmbeddingsOver
  unramifiedPlacesOver mixedEmbeddingsOver Finset

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

variable {v : InfinitePlace K} (w : InfinitePlace L)

variable (L v)

def _root_.Set.disjSum {α β : Type*} (s : Set α) (t : Set β) : Set (α ⊕ β) :=
  Sum.inl '' s ∪ Sum.inr '' t

theorem _root_.Set.disjSum_toFinset {α β : Type*} (s : Set α) (t : Set β)
    (hs : s.Finite := by toFinite_tac) (ht : t.Finite := by toFinite_tac)
    (hst : (s.disjSum t).Finite := by toFinite_tac) :
    hst.toFinset = hs.toFinset.disjSum ht.toFinset := by
  ext ; aesop (add simp [disjSum, Finset.disjSum, Set.disjSum])

@[simp]
theorem _root_.Finset.coe_disjSum {α β : Type*} (s : Finset α) (t : Finset β) :
    (s.disjSum t : Set (α ⊕ β)) = s.disjSum t := by
  ext ; aesop (add simp [disjSum, Set.disjSum, Finset.disjSum])

theorem _root_.Set.MapsTo.sumElim {α β γ : Type*} {f : α → γ} {g : β → γ} {r : Set α}
    {s : Set β} {t : Set γ} (hf : Set.MapsTo f r t) (hg : Set.MapsTo g s t) :
    Set.MapsTo (Sum.elim f g) (r.disjSum s) t := by
  rintro (a | b)
  · simpa [Set.disjSum] using fun ha ↦ hf ha
  · simpa [Set.disjSum] using fun hb ↦ hg hb

theorem _root_.Set.InjOn.sumElim {α β γ : Type*} {f : α → γ} {g : β → γ} {r : Set α}
    {s : Set β} (hf : Set.InjOn f r) (hg : Set.InjOn g s)
    (hfg : ∀ᵉ (a ∈ r) (b ∈ s), f a ≠ g b) :
    Set.InjOn (Sum.elim f g) (r.disjSum s) := by
  rintro (a₁ | b₁) h₁ (a₂ | b₂) h₂ heq <;> simp [Set.disjSum] at h₁ h₂
  · aesop
  · exact (hfg _ (by simpa using h₁) _ (by simpa using h₂) heq).elim
  · exact (hfg _ (by simpa using h₂) _ (by simpa using h₁) heq.symm).elim
  · aesop

theorem bijOn_sumElim_conjugate :
    Set.BijOn (Sum.elim embedding (conjugate ∘ embedding))
      ((ramifiedPlacesOver L v).disjSum (ramifiedPlacesOver L v))
      (mixedEmbeddingsOver L v.embedding) := by
  refine ⟨?_, ?_, fun ψ h ↦ ?_⟩
  · exact Set.MapsTo.sumElim embedding_mem_mixedEmbeddingsOver
      conjugate_embedding_mem_mixedEmbeddingsOver
  · exact (embedding_injective L).injOn.sumElim (star_injective.comp (embedding_injective L)).injOn
      (fun _ _ _ h ↦ (isRamified h).ne_conjugate)
  · cases embedding_mk_eq ψ with
    | inl hl => simpa [Set.disjSum] using .inl ⟨mk ψ, mk_mem_ramifiedPlacesOver h, hl⟩
    | inr hr => simpa [Set.disjSum] using .inr ⟨_, mk_mem_ramifiedPlacesOver h, by aesop⟩

theorem _root_.Set.BijOn.ncard_eq {α β : Type*} {f : α → β} {s : Set α} {t : Set β}
    (h : Set.BijOn f s t) :
    s.ncard = t.ncard :=
  Set.ncard_congr _ h.mapsTo (fun _ _ ha hb heq ↦ h.injOn ha hb heq)
    (fun _ ha ↦ bex_def.2 (h.surjOn ha))

theorem _root_.Set.BijOn_toFinset {α β : Type*} {f : α → β} {s : Set α} {t : Set β}
    (hs : s.Finite := by toFinite_tac) (ht : t.Finite := by toFinite_tac) :
    Set.BijOn f s t ↔ Set.BijOn f ↑(hs.toFinset) ↑(ht.toFinset) := by
  simp only [Set.Finite.coe_toFinset]

alias ⟨_root_.Set.BijOn.toFinset, _⟩ := Set.BijOn_toFinset

theorem ramifiedPlacesOver_ncard [NumberField L] :
    2 * (ramifiedPlacesOver L v).ncard = (mixedEmbeddingsOver L v.embedding).ncard := by
  rw [Set.ncard_eq_toFinset_card, Set.ncard_eq_toFinset_card,
    ← (bijOn_sumElim_conjugate L v).toFinset.finsetCard_eq, Set.disjSum_toFinset,
    card_disjSum, two_mul]

open scoped Classical in
def embeddingConjugateIte (v : InfinitePlace K) :
    InfinitePlace L → L →+* ℂ :=
  fun w ↦ if IsExtension v.embedding w.embedding then w.embedding else conjugate w.embedding

theorem embeddingConjugateIte_pos {v : InfinitePlace K} {w : InfinitePlace L}
    (h : IsExtension v.embedding w.embedding) :
    embeddingConjugateIte L v w = w.embedding := by
  simp [embeddingConjugateIte, h]

theorem embeddingConjugateIte_neg {v : InfinitePlace K} {w : InfinitePlace L}
    (h : ¬IsExtension v.embedding w.embedding) :
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

theorem mapsTo_embeddingConjugateIte (v : InfinitePlace K) :
    Set.MapsTo (embeddingConjugateIte L v) (unramifiedPlacesOver L v)
      (unmixedEmbeddingsOver L v.embedding) := by
  intro w hw
  obtain ⟨_, hw⟩ := mem_unramifiedPlacesOver.1 hw
  by_cases h : IsExtension v.embedding w.embedding
  · simpa [embeddingConjugateIte_pos L h] using mem_unmixedEmbeddingsOver.2 ⟨h, hw.isUnmixed⟩
  · simpa [embeddingConjugateIte_neg L h] using mem_unmixedEmbeddingsOver.2
      ⟨(LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w v).resolve_left h,
        hw.isUnmixed_conjugate⟩

theorem surjOn_embeddingConjugateIte (v : InfinitePlace K) :
    Set.SurjOn (embeddingConjugateIte L v) (unramifiedPlacesOver L v)
      (unmixedEmbeddingsOver L v.embedding) := by
  intro ψ h
  refine ⟨mk ψ, mk_mem_unramifiedPlacesOver h, ?_⟩
  rcases embedding_mk_eq ψ with (_ | _)
  · aesop (add simp [embeddingConjugateIte, unmixedEmbeddingsOver])
  · aesop (add simp [embeddingConjugateIte, unmixedEmbeddingsOver, conjugate_comp, IsExtension,
      IsUnmixed, IsMixed])

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

variable (v) in
theorem finrank_eq_two_of_isRamified (w : InfinitePlace L) [w.1.LiesOver v.1] (h : w.IsRamified K) :
    Module.finrank v.Completion w.Completion = 2 := by
  rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivRealOfIsReal <| h.liesOver_isReal_under w v)
      (ringEquivComplexOfIsComplex h.isComplex) (by simp [RingHom.ext_iff,
        ← LiesOver.extensionEmbedding_algebraMap_of_isReal w <| h.liesOver_isReal_under w v]),
    Complex.finrank_real_complex]

variable {L : Type*} [Field L] [Algebra K L]

variable (v) in
/-- If `w` is an unramified extension of `v` and both infinite places are complex then
the `v.Completion`-dimension of `w.Completion` is `1`. -/
theorem finrank_eq_one_of_isUnramified (w : InfinitePlace L) [w.1.LiesOver v.1]
    (h : w.IsUnramified K) :
    Module.finrank v.Completion w.Completion = 1 := by
  by_cases hv : v.IsReal
  · rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivRealOfIsReal hv) (ringEquivRealOfIsReal
      (h.liesOver_isReal_over _ _ hv)) (RingHom.ext fun _ ↦ Complex.ofReal_inj.1 <| by
        simp [← LiesOver.extensionEmbedding_algebraMap_of_isReal w hv]), Module.finrank_self]
  · have hv : v.IsComplex := not_isReal_iff_isComplex.1 hv
    cases LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w v with
    | inl hl => rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivComplexOfIsComplex hv)
        (ringEquivComplexOfIsComplex (LiesOver.isComplex_of_isComplex_under _ hv))
        (RingHom.ext fun _ ↦ by simp [← LiesOver.extensionEmbedding_algebraMap _ hl]),
        Module.finrank_self]
    | inr hr => rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivComplexOfIsComplex hv)
        ((ringEquivComplexOfIsComplex (LiesOver.isComplex_of_isComplex_under _ hv)).trans
          (starRingAut (R := ℂ)))
        (RingHom.ext fun _ ↦ by simp [← LiesOver.conjugate_extensionEmbedding_algebraMap _ hr]),
        Module.finrank_self]

end Completion

open Completion

open scoped Classical in
theorem ncard_isUnramified_add_two_mul_ncard_isRamified [NumberField K] [NumberField L] :
    (unramifiedPlacesOver L v).ncard + 2 * (ramifiedPlacesOver L v).ncard = Module.finrank K L := by
  letI : Algebra K ℂ := v.embedding.toAlgebra
  rw [← AlgHom.card K L ℂ, ramifiedPlacesOver_ncard, unramifiedPlacesOver_ncard,
    ← Set.ncard_union_eq (disjoint_mixedEmbeddingsOver L v.embedding),
    union_mixedEmbeddingsOver, Set.ncard_eq_toFinset_card]
  apply (card_nbij AlgHom.toRingHom (fun σ _ ↦ by simp [IsExtension, RingHom.algebraMap_toAlgebra])
    AlgHom.coe_ringHom_injective.injOn (fun ψ hψ ↦ ?_)).symm
  simp only [Set.Finite.toFinset_setOf, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hψ
  exact ⟨⟨ψ, fun _ ↦ by simp [RingHom.algebraMap_toAlgebra, ← hψ]⟩, by simp⟩

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
theorem unramifiedPlacesOver.inertiaDeg_eq_one (w : InfinitePlace L)
    (hw : w ∈ unramifiedPlacesOver L v) : v.inertiaDeg w = 1 := by
  have := liesOver hw
  exact finrank_eq_one_of_isUnramified v w (isUnramified hw) ▸ inertiaDeg_eq_finrank v w

variable {L} in
open Completion in
theorem ramifiedPlacesOver.inertiaDeg_eq_two (w : InfinitePlace L)
    (hw : w ∈ ramifiedPlacesOver L v) : v.inertiaDeg w = 2 := by
  have := liesOver hw
  exact finrank_eq_two_of_isRamified v w (isRamified hw) ▸ inertiaDeg_eq_finrank v w

open scoped Classical in
open Completion Finset in
theorem sum_inertiaDeg_eq_finrank [NumberField K] [NumberField L] :
    ∑ w ∈ v.placesOver L, v.inertiaDeg w = Module.finrank K L := by
  simp [← placesOver_eq_union L v,
    sum_union (Set.disjoint_toFinset.2 <| disjoint_unramifiedPlacesOver L v)]
  rw [sum_congr rfl (fun _ h ↦ inertiaDeg_eq_two v _ (by simpa using h))]
  rw [sum_congr rfl (fun _ h ↦ inertiaDeg_eq_one v _ (by simpa using h))]
  simp only [sum_const]
  simp [← ncard_isUnramified_add_two_mul_ncard_isRamified L v, add_comm, mul_comm,
    Set.ncard_eq_toFinset_card']

end NumberField.InfinitePlace
