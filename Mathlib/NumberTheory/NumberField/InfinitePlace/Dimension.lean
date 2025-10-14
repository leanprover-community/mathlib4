/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.NumberTheory.NumberField.Completion
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
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

theorem _root_.Set.MapsTo.sumElim {α β γ : Type*} {f : α → γ} {g : β → γ} {r : Finset α}
    {s : Finset β} {t : Finset γ} (hf : Set.MapsTo f r t) (hg : Set.MapsTo g s t) :
    Set.MapsTo (Sum.elim f g) (r.disjSum s) t := by
  rintro (a | b)
  · simpa using fun ha ↦ hf ha
  · simpa using fun hb ↦ hg hb

theorem _root_.Set.InjOn.sumElim {α β γ : Type*} {f : α → γ} {g : β → γ} {r : Finset α}
    {s : Finset β} (hf : Set.InjOn f r) (hg : Set.InjOn g s)
    (hfg : ∀ᵉ (a ∈ r) (b ∈ s), f a ≠ g b) :
    Set.InjOn (Sum.elim f g) (r.disjSum s) := by
  rintro (a₁ | b₁) h₁ (a₂ | b₂) h₂ heq
  · aesop
  · exact (hfg _ (by simpa using h₁) _ (by simpa using h₂) heq).elim
  · exact (hfg _ (by simpa using h₂) _ (by simpa using h₁) heq.symm).elim
  · aesop

theorem bijOn_sumElim_conjugate [NumberField L] :
    Set.BijOn (Sum.elim embedding (conjugate ∘ embedding))
      ((ramifiedPlacesOver L v).disjSum (ramifiedPlacesOver L v)).toSet
      (mixedEmbeddingsOver L v.embedding) := by
  refine ⟨?_, ?_, fun ψ h ↦ ?_⟩
  · exact Set.MapsTo.sumElim embedding_mem_mixedEmbeddingsOver
      conjugate_embedding_mem_mixedEmbeddingsOver
  · exact (embedding_injective L).injOn.sumElim (star_injective.comp (embedding_injective L)).injOn
      (fun _ _ _ h ↦ (isRamified h).ne_conjugate)
  · cases embedding_mk_eq ψ with
    | inl hl => simpa using .inl ⟨mk ψ, mk_mem_ramifiedPlacesOver h, hl⟩
    | inr hr => simpa using .inr ⟨_, mk_mem_ramifiedPlacesOver h, by aesop⟩

theorem ramifiedPlacesOver_card [NumberField L] :
    2 * #(ramifiedPlacesOver L v) = #(mixedEmbeddingsOver L v.embedding) := by
  rw [← bijOn_sumElim_conjugate L v |>.finsetCard_eq]; simp; ring

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

theorem mapsTo_embeddingConjugateIte (v : InfinitePlace K) [NumberField L] :
    Set.MapsTo (embeddingConjugateIte L v) (unramifiedPlacesOver L v)
      (unmixedEmbeddingsOver L v.embedding) := by
  intro w hw
  obtain ⟨_, hw⟩ := mem_unramifiedPlacesOver.1 hw
  by_cases h : IsExtension v.embedding w.embedding
  · simpa [embeddingConjugateIte_pos L h] using mem_unmixedEmbeddingsOver.2 ⟨h, hw.isUnmixed⟩
  · simpa [embeddingConjugateIte_neg L h] using mem_unmixedEmbeddingsOver.2
      ⟨LiesOver.embedding_conjugate_comp_eq w v h, hw.isUnmixed_conjugate⟩

theorem surjOn_embeddingConjugateIte (v : InfinitePlace K) [NumberField L] :
    Set.SurjOn (embeddingConjugateIte L v) (unramifiedPlacesOver L v)
      (unmixedEmbeddingsOver L v.embedding) := by
  intro ψ h
  refine ⟨mk ψ, mk_mem_unramifiedPlacesOver h, ?_⟩
  rcases embedding_mk_eq ψ with (hψ | hψ)
  · aesop (add simp [embeddingConjugateIte, unmixedEmbeddingsOver])
  · aesop (add simp [embeddingConjugateIte, unmixedEmbeddingsOver, conjugate_comp, IsExtension,
      IsUnmixed, IsMixed])

open scoped Classical in
theorem bijOn_extensionIte [NumberField L] :
    Set.BijOn (embeddingConjugateIte L v) (unramifiedPlacesOver L v)
      (unmixedEmbeddingsOver L v.embedding) :=
  ⟨mapsTo_embeddingConjugateIte L v, star_involutive.injective_ite (embedding_injective _)
    (eq_of_embedding_eq_conjugate L) |>.injOn,
      surjOn_embeddingConjugateIte L v⟩

theorem unramifiedPlacesOver_card [NumberField L] :
    #(unramifiedPlacesOver L v) = #(unmixedEmbeddingsOver L v.embedding) :=
  bijOn_extensionIte L v |>.finsetCard_eq

namespace Completion

open AbsoluteValue.Completion NumberField.ComplexEmbedding

variable {K : Type*} [Field K] {v : InfinitePlace K}
variable {L : Type*} [Field L] [Algebra K L]

variable (v) in
theorem finrank_eq_two_of_isRamified (w : InfinitePlace L) [w.LiesOver v] (h : w.IsRamified K) :
    Module.finrank v.Completion w.Completion = 2 := by
  rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivRealOfIsReal <| h.liesOver_isReal_under w v)
      (ringEquivComplexOfIsComplex h.isComplex) (by simp [RingHom.ext_iff,
        ← LiesOver.extensionEmbedding_algebraMap_of_isReal w <| h.liesOver_isReal_under w v]),
    Complex.finrank_real_complex]

variable {L : Type*} [Field L] [Algebra K L]

variable (v) in
/-- If `w` is an unramified extension of `v` and both infinite places are complex then
the `v.Completion`-dimension of `w.Completion` is `1`. -/
theorem finrank_eq_one_of_isUnramified (w : InfinitePlace L) [w.LiesOver v] (h : w.IsUnramified K) :
    Module.finrank v.Completion w.Completion = 1 := by
  by_cases hv : v.IsReal
  · rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivRealOfIsReal hv) (ringEquivRealOfIsReal
      (h.liesOver_isReal_over _ _ hv)) (RingHom.ext fun _ ↦ Complex.ofReal_inj.1 <| by
        simp [← LiesOver.extensionEmbedding_algebraMap_of_isReal w hv]), Module.finrank_self]
  · have hv : v.IsComplex := not_isReal_iff_isComplex.1 hv
    cases LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w v with
    | inl hl => rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivComplexOfIsComplex hv)
        (ringEquivComplexOfIsComplex (LiesOver.isComplex_of_isComplex_under hv))
        (RingHom.ext fun _ ↦ by simp [← LiesOver.extensionEmbedding_algebraMap _ hl]),
        Module.finrank_self]
    | inr hr => rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivComplexOfIsComplex hv)
        ((ringEquivComplexOfIsComplex (LiesOver.isComplex_of_isComplex_under hv)).trans
          (starRingAut (R := ℂ)))
        (RingHom.ext fun _ ↦ by simp [← LiesOver.conjugate_extensionEmbedding_algebraMap _ hr]),
        Module.finrank_self]

end Completion

open scoped Classical in
theorem card_isUnramified_add_two_mul_card_isRamified [NumberField K] [NumberField L] :
    #(unramifiedPlacesOver L v) + 2 * #(ramifiedPlacesOver L v) = Module.finrank K L := by
  letI : Algebra K ℂ := v.embedding.toAlgebra
  rw [← AlgHom.card K L ℂ, ramifiedPlacesOver_card, unramifiedPlacesOver_card,
    ← card_disjUnion _ _ (disjoint_mixedEmbeddingsOver L v.embedding), disjUnion_eq_union,
    union_mixedEmbeddingsOver]
  apply (card_nbij AlgHom.toRingHom (fun σ _ ↦ by simp [IsExtension, RingHom.algebraMap_toAlgebra])
    AlgHom.coe_ringHom_injective.injOn (fun ψ hψ ↦ ?_)).symm
  simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hψ
  exact ⟨⟨ψ, fun _ ↦ by simp [RingHom.algebraMap_toAlgebra, ← hψ]⟩, by simp⟩

variable {L} in
open scoped Classical in
protected def inertiaDeg (w : InfinitePlace L) : ℕ :=
  if _ : w.LiesOver v then (⊥ : Ideal v.Completion).inertiaDeg (⊥ : Ideal w.Completion) else 0

variable {L} in
theorem inertiaDeg_eq_finrank (v : InfinitePlace K)
    (w : InfinitePlace L) [i : w.LiesOver v] :
    v.inertiaDeg w = Module.finrank v.Completion w.1.Completion := by
  simp only [InfinitePlace.inertiaDeg, Ideal.inertiaDeg, i, dif_pos]
  simp [Ideal.comap_bot_of_injective _ <| FaithfulSMul.algebraMap_injective _ _]
  apply Algebra.finrank_eq_of_equiv_equiv (RingEquiv.quotientBot v.Completion)
    (RingEquiv.quotientBot w.Completion)
  ext
  simp [RingHom.algebraMap_toAlgebra]

variable {L} in
open Completion in
theorem unramifiedPlacesOver.inertiaDeg_eq_one [NumberField L] (w : InfinitePlace L)
    (hw : w ∈ unramifiedPlacesOver L v) : v.inertiaDeg w = 1 := by
  have := liesOver hw
  exact finrank_eq_one_of_isUnramified v w (isUnramified hw) ▸ inertiaDeg_eq_finrank v w

variable {L} in
open Completion in
theorem ramifiedPlacesOver.inertiaDeg_eq_two [NumberField L] (w : InfinitePlace L)
    (hw : w ∈ ramifiedPlacesOver L v) : v.inertiaDeg w = 2 := by
  have := liesOver hw
  exact finrank_eq_two_of_isRamified v w (isRamified hw) ▸ inertiaDeg_eq_finrank v w

open scoped Classical in
open Completion Finset in
theorem sum_inertiaDeg_eq_finrank [NumberField K] [NumberField L] :
    ∑ w ∈ v.placesOver L, v.inertiaDeg w = Module.finrank K L := by
  simp [placesOver_eq_union L v, -disjUnion_eq_union, sum_congr rfl (inertiaDeg_eq_one v),
    sum_congr rfl (inertiaDeg_eq_two v), sum_disjUnion (disjoint_unramifiedPlacesOver L v),
    add_comm, mul_comm, ← card_isUnramified_add_two_mul_card_isRamified L v]

end NumberField.InfinitePlace
