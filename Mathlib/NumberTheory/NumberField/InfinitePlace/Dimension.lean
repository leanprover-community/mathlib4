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

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]

namespace NumberField.InfinitePlace

open NumberField.ComplexEmbedding

variable {v : InfinitePlace K}

namespace Extension

variable (L v) in
open scoped Classical in
abbrev toComplexExtension : v.Extension L ↪ ComplexEmbedding.Extension L v.embedding where
  toFun := fun w ↦
    if hw : w.1.embedding.comp (algebraMap K L) = v.embedding then
      ⟨w.1.embedding, hw⟩ else
        ⟨conjugate w.1.embedding, embedding_conjugate_comp_eq_of_not_embedding_comp_eq _ hw⟩
  inj' := by
    have := @Function.Injective.dite (α := v.Extension L) (β := Extension L v.embedding)
      (fun w ↦ w.1.embedding.comp (algebraMap K L) = v.embedding) _
      (fun w ↦ ⟨w.1.1.embedding, w.2⟩) (fun w ↦ ⟨conjugate w.1.1.embedding,
        embedding_conjugate_comp_eq_of_not_embedding_comp_eq _ w.2⟩)
    apply this <;> clear this
    · aesop (add simp [Function.Injective])
    · aesop (add simp [Function.Injective])
    · intro ⟨w₁, _⟩ ⟨w₂, h₂⟩ hw₁ hw₂
      by_cases hw₂r : IsReal v
      · subst h₂;
        simp_all only [ne_eq, Subtype.mk.injEq]
        simp_all [comap_embedding_eq_comp_of_isReal, not_true_eq_false]
      · by_cases h₁₂ : w₁ = w₂
        · aesop
        · simpa using mt (eq_of_embedding_eq_conjugate L) h₁₂

abbrev inertiaDeg {v : InfinitePlace K} (w : v.Extension L) :=
  (⊥ : Ideal v.Completion).inertiaDeg (⊥ : Ideal w.1.Completion)

theorem inertiaDeg_eq_finrank {v : InfinitePlace K} (w : v.Extension L) :
    w.inertiaDeg = Module.finrank v.Completion w.1.Completion := by
  simp only [Ideal.inertiaDeg]
  have : Ideal.comap (algebraMap v.Completion w.1.Completion) ⊥ = ⊥ := by
    rw [Ideal.comap_bot_of_injective]
    exact FaithfulSMul.algebraMap_injective _ _
  simp [this]
  have := Algebra.finrank_eq_of_equiv_equiv (RingEquiv.quotientBot v.Completion)
    (RingEquiv.quotientBot w.1.Completion)
  apply this
  rw [RingHom.algebraMap_toAlgebra]
  ext
  simp
  rfl

end Extension

open NumberField.ComplexEmbedding

variable {v : InfinitePlace K} {w : InfinitePlace L}

theorem comap_mk_of_comp_eq (ψ : L →+* ℂ) (h : ψ.comp (algebraMap K L) = v.embedding) :
    (mk ψ).comap (algebraMap K L) = v := by
  aesop

theorem comap_mk_of_extension (ψ : ComplexEmbedding.Extension L v.embedding) :
    (mk ψ).comap (algebraMap K L) = v := by
  aesop

variable (w)

namespace RamifiedExtension

variable {w : v.Extension L}

theorem embedding_comp_eq (h : w.1.IsRamified K) :
    w.1.embedding.comp (algebraMap K L) = v.embedding := by
  rw [← congrArg embedding w.2,
    ← comap_embedding_eq_comp_of_isReal _ (isRamified_iff.1 h).2]

theorem conjugate_embedding_comp_eq (h : w.1.IsRamified K) :
    (conjugate w.1.embedding).comp (algebraMap K L) = v.embedding := by
  have := (w.2 ▸ (isRamified_iff.1 h).2)
  rw [← ComplexEmbedding.isReal_iff.1 <| isReal_iff.1 this,
    ← congrArg InfinitePlace.embedding w.2]
  simp [comap_embedding_eq_comp_of_isReal _ ((isRamified_iff.1 h).2)]

theorem isMixed_embedding (h : w.1.IsRamified K) :
    IsMixed w.1.embedding v.embedding :=
  ⟨isReal_iff.1 (w.2 ▸ isRamified_iff.1 h).2, isComplex_iff.1 (isRamified_iff.1 h).1⟩

theorem isMixed_conjugate_embedding (h : w.1.IsRamified K) :
    IsMixed (conjugate w.1.embedding) v.embedding :=
  ⟨isReal_iff.1 (w.2 ▸ isRamified_iff.1 h).2,
    mt ComplexEmbedding.isReal_conjugate_iff.1 <| isComplex_iff.1 (isRamified_iff.1 h).1⟩

-- TODO: move this
theorem isRamified_mk_of_isMixed {ψ : Extension L v.embedding} (h : IsMixed ψ.1 v.embedding) :
    (mk ψ.1).IsRamified K := by
  rw [isRamified_iff, isComplex_iff, comap_mk, isReal_iff, ψ.2, embedding_mk_eq_of_isReal h.1]
  exact ⟨by rcases embedding_mk_eq ψ.1 with (_ | _) <;> aesop, h.1⟩

variable (L v)


/-- The equivalence between two copies of ramified places `w` over `v` and the type of all
mixed extensions of `v.embedding`. This two-fold equivalence exists because when `w` ramifies
over `v` both `w.embedding` and `conjugate w.embedding` give distinct mixed extensions of
`v.embedding`. -/
def sumEquivIsMixedExtension :
    { w : v.Extension L // w.1.IsRamified K } ⊕ { w : v.Extension L // w.1.IsRamified K } ≃
      { ψ : Extension L v.embedding // IsMixed ψ.1 v.embedding } := by
  apply Equiv.ofBijective <| Sum.elim
    (Subtype.coind (fun ⟨w, h⟩ ↦ ⟨_, embedding_comp_eq h⟩) fun ⟨_, hr⟩ ↦ isMixed_embedding hr)
    (Subtype.coind (fun ⟨w, h⟩ ↦ ⟨_, conjugate_embedding_comp_eq h⟩)
      fun ⟨_, hr⟩ ↦ isMixed_conjugate_embedding hr)
  refine ⟨?_, fun ⟨ψ, h⟩ ↦ ?_⟩
  · exact (Subtype.coind_injective _ (by simp_all [Function.Injective])).sumElim
      (Subtype.coind_injective _ (by aesop (add simp [Function.Injective]))) <|
      fun a b ↦ by simpa [Subtype.coind] using b.2.ne_conjugate
  · cases embedding_mk_eq ψ.1 with
    | inl hl => exact ⟨.inl ⟨⟨mk ψ, comap_mk_of_extension ψ⟩, isRamified_mk_of_isMixed h⟩,
        by simp [Subtype.coind, hl]⟩
    | inr hr => exact ⟨.inr ⟨⟨mk ψ, comap_mk_of_extension ψ⟩, isRamified_mk_of_isMixed h⟩,
        by simp [Subtype.coind, hr]⟩

open scoped Classical in
theorem two_mul_card_eq [NumberField L] :
    2 * Fintype.card ({ w : v.Extension L // w.1.IsRamified K }) =
      Fintype.card { ψ : Extension L v.embedding // IsMixed ψ.1 v.embedding } := by
  simp [← Fintype.card_eq.2 ⟨sumEquivIsMixedExtension L v⟩]; ring

end RamifiedExtension

namespace UnramifiedExtension

open Extension

variable {w : InfinitePlace L}

theorem isUnmixed (hw : w.IsUnramified K)
    (he : w.embedding.comp (algebraMap K L) = v.embedding) :
    IsUnmixed w.embedding v.embedding := by
  simp_all only [isUnramified_iff, not_and, not_not]
  intro a
  cases hw with
  | inl h => simp_all only [mk_embedding, isReal_of_mk_isReal]
  | inr h_1 =>
    rw [← mk_embedding (w.comap (algebraMap K L))] at h_1
    have := not_isReal_of_mk_isComplex h_1
    have := comap_mk_of_comp_eq _ he
    simp at this
    rw [comap_embedding_eq_comp_of_isReal _ (isReal_iff.2 <| this ▸ a)] at h_1
    rw [he] at h_1
    simp_all

theorem isUnmixed_conjugate (hw : w.IsUnramified K)
    (he : (conjugate w.embedding).comp (algebraMap K L) = v.embedding) :
    IsUnmixed w.embedding v.embedding := by
  simp_all only [isUnramified_iff, not_and, not_not]
  intro a
  cases hw with
  | inl h => simp_all [mk_embedding, isReal_of_mk_isReal]
  | inr h_1 =>
    rw [← mk_embedding (w.comap (algebraMap K L))] at h_1
    have := not_isReal_of_mk_isComplex h_1
    have := comap_mk_of_comp_eq _ he
    simp at this
    rw [comap_embedding_eq_comp_of_isReal _ (isReal_iff.2 <| this ▸ a)] at h_1
    simp_all

theorem isUnmixed_mk_isUnramified {ψ : Extension L v.embedding} (h : IsUnmixed ψ.1 v.embedding) :
    (mk ψ.1).IsUnramified K := by
  rw [isUnramified_iff, isReal_iff]
  by_cases hv : ComplexEmbedding.IsReal v.embedding
  · simpa [embedding_mk_eq_of_isReal <| h.isReal_of_isReal hv] using Or.inl (h.isReal_of_isReal hv)
  · simpa [comap_mk, ψ.2, mk_embedding, isComplex_iff] using Or.inr hv

variable (L v)

def toIsUnmixedExtension :
    {w : v.Extension L // w.1.IsUnramified K } ↪
      { ψ : Extension L v.embedding // IsUnmixed ψ.1 v.embedding } := by
  apply (toComplexExtension L v).subtypeMap
  simp only [toComplexExtension]
  intro w hw
  dsimp
  split_ifs with h
  · exact isUnmixed hw ‹_›
  · have := isUnmixed_conjugate hw <| embedding_conjugate_comp_eq_of_not_embedding_comp_eq _ h
    aesop

/-- If `w` is an unramified place above `v` then there are the following two cases:
- `v` and `w` are both real;
- `v` and `w` are both complex.
In the first case `w.embedding` and `conjugate w.embedding` coincide. In the second case
only one of `w.embedding` and `conjugate w.embedding` can extend `v.embedding`. In both cases
then, there is a unique unmixed extension of `v.embedding` associated to the unramified
place `w` over `v`. -/
def equivIsUnmixedExtension :
    {w : v.Extension L // w.1.IsUnramified K } ≃
      { ψ : Extension L v.embedding // IsUnmixed ψ.1 v.embedding } := by
  apply (toIsUnmixedExtension L v).equivOfSurjective
  rintro ⟨ψ, h⟩
  use ⟨⟨mk ψ, comap_mk_of_extension ψ⟩, isUnmixed_mk_isUnramified h⟩
  rcases embedding_mk_eq ψ.1 with (_ | _) <;>
    aesop (add simp [toIsUnmixedExtension, toComplexExtension, Function.Embedding.subtypeMap,
      Subtype.map])

open scoped Classical in
theorem card_eq [NumberField L] :
    Fintype.card ({w : v.Extension L // w.1.IsUnramified K }) =
      Fintype.card { ψ : Extension L v.embedding // IsUnmixed ψ.1 v.embedding } := by
  rw [← Fintype.card_eq.2 ⟨equivIsUnmixedExtension L v⟩]

end UnramifiedExtension

namespace Completion

open AbsoluteValue.Completion NumberField.ComplexEmbedding

variable {K : Type*} [Field K] {v : InfinitePlace K}
variable {L : Type*} [Field L] [Algebra K L]

namespace RamifiedExtension

variable {w : v.Extension L}

variable (w) in
/-- If `w` is a ramified extension of `v`, then the `v.Completion`-dimension of `w.Completion`
is `2`. -/
theorem finrank_eq_two (h : w.1.IsRamified K) :
    Module.finrank v.Completion w.1.Completion = 2 := by
  have := Algebra.finrank_eq_of_equiv_equiv (R₀ := v.Completion) (R₁ := ℝ) (S₀ := w.1.Completion)
    (S₁ := ℂ) (ringEquivRealOfIsReal (w.2 ▸ (isRamified_iff.1 h).2))
    (ringEquivComplexOfIsComplex (isRamified_iff.1 h).1)
  rw [this, Complex.finrank_real_complex]
  ext
  simp [← extensionEmbedding_algebraMap_of_isReal w <| w.2 ▸ (isRamified_iff.1 h).2]

end RamifiedExtension

namespace UnramifiedExtension

open NumberField.ComplexEmbedding Extension

variable {L : Type*} [Field L] [Algebra K L] (w : v.Extension L)


/-- If `w` is an unramified extension of `v` and both infinite places are complex then
the `v.Completion`-dimension of `w.Completion` is `1`. -/
theorem finrank_eq_one (h : w.1.IsUnramified K) :
    Module.finrank v.Completion w.1.Completion = 1 := by
  by_cases hv : v.IsReal
  · have := Algebra.finrank_eq_of_equiv_equiv (R₀ := v.Completion) (R₁ := ℝ) (S₀ := w.1.Completion)
      (S₁ := ℝ) (ringEquivRealOfIsReal hv)
      (ringEquivRealOfIsReal (isReal_of_isReal h hv))
    rw [this, Module.finrank_self]
    ext
    rw [← Complex.ofReal_inj]
    simp [← extensionEmbedding_algebraMap_of_isReal w hv]
  · have hv : v.IsComplex := not_isReal_iff_isComplex.1 hv
    cases embedding_comp_eq_or_conjugate_embedding_comp_eq w with
    | inl hl =>
      have := Algebra.finrank_eq_of_equiv_equiv (R₀ := v.Completion) (R₁ := ℂ)
        (S₀ := w.1.Completion) (S₁ := ℂ) (ringEquivComplexOfIsComplex hv)
        (ringEquivComplexOfIsComplex (w.isComplex_of_isComplex hv))
      rw [this, Module.finrank_self]
      ext
      simp [← extensionEmbedding_algebraMap_of_embedding_comp_eq _ hl]
    | inr hr =>
      have := Algebra.finrank_eq_of_equiv_equiv (R₀ := v.Completion) (R₁ := ℂ)
        (S₀ := w.1.Completion) (S₁ := ℂ) (ringEquivComplexOfIsComplex hv)
        ((ringEquivComplexOfIsComplex (w.isComplex_of_isComplex hv)).trans (starRingAut (R := ℂ)))
      rw [this, Module.finrank_self]
      ext
      simp [← extensionEmbedding_algebraMap_of_conjugate_embedding_comp_eq _ hr]

end UnramifiedExtension

end Completion

namespace Extension

open UnramifiedExtension RamifiedExtension

instance : Algebra (WithAbs v.1) ℂ := v.embedding.toAlgebra

theorem isExtension_algHom (φ : L →ₐ[WithAbs v.1] ℂ) :
    φ.toRingHom.comp (algebraMap K L) = v.embedding := by
  have := v.embedding.algebraMap_toAlgebra ▸ funext_iff.2 φ.commutes'
  simp only [AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
    MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe, AlgHom.commutes,
    DFunLike.coe_fn_eq] at this
  change φ.toRingHom.comp (algebraMap (WithAbs v.1) L) = v.embedding
  rwa [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap_of_tower]

variable (L v)

/-- For any infinite place `v` of `K`, the `K`-algebra maps from `L` to `ℂ` are equivalent to
the embeddings `L →+* ℂ` that extend `v.embedding`. -/
def algHomEquivIsExtension :
    (L →ₐ[WithAbs v.1] ℂ) ≃ Extension L v.embedding :=
  Equiv.ofBijective (fun φ => ⟨φ.toRingHom, isExtension_algHom φ⟩)
    ⟨fun _ _ h => AlgHom.coe_ringHom_injective (by simpa using h),
      fun ⟨σ, h⟩ => ⟨⟨σ, fun _ => by simp [RingHom.algebraMap_toAlgebra, ← h]; rfl⟩, rfl⟩⟩

open scoped Classical in
theorem card_isUnramified_add_two_mul_card_isRamified [NumberField K] [NumberField L] :
    Fintype.card ({w : v.Extension L // w.1.IsUnramified K }) +
      2 * Fintype.card ({w : v.Extension L // w.1.IsRamified K }) =
      Module.finrank K L := by
  change _ = Module.finrank (WithAbs v.1) L
  rw [← AlgHom.card (WithAbs v.1) L ℂ, Fintype.card_eq.2 ⟨algHomEquivIsExtension L v⟩,
    Fintype.card_eq.2 ⟨Extension.equivSum v.embedding⟩, Fintype.card_sum,
    RamifiedExtension.two_mul_card_eq, UnramifiedExtension.card_eq]
  ring

open scoped Classical in
open Completion in
theorem sum_ramificationIdx_eq [NumberField K] [NumberField L] :
    ∑ w : v.Extension L, w.inertiaDeg = Module.finrank K L := by
  rw [Fintype.sum_equiv (Equiv.sumCompl fun w ↦ w.1.IsUnramified K).symm _
    ((fun w ↦ w.inertiaDeg) ∘ (Equiv.sumCompl fun w : v.Extension L ↦ w.1.IsUnramified K))
    (fun _ => by rw [Function.comp_apply, Equiv.apply_symm_apply])]
  simp only [Function.comp_apply, Fintype.sum_sum_type, Equiv.sumCompl_apply_inl,
    Equiv.sumCompl_apply_inr]
  rw [Finset.sum_congr rfl (fun w  _ =>
      inertiaDeg_eq_finrank w.1 ▸ UnramifiedExtension.finrank_eq_one w.1 w.2),
    Finset.sum_const,
    Finset.sum_congr rfl
      (fun w _  => inertiaDeg_eq_finrank w.1 ▸ RamifiedExtension.finrank_eq_two w.1 w.2),
    Finset.sum_const, ← Fintype.card, ← Fintype.card, smul_eq_mul, mul_one,
    smul_eq_mul, mul_comm, ← card_isUnramified_add_two_mul_card_isRamified L v]

end Extension

end NumberField.InfinitePlace
