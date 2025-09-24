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

open NumberField.ComplexEmbedding

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : InfinitePlace K)

namespace Extension

variable (L)

open scoped Classical in
private abbrev toComplexExtension :
    v.Extension L ↪ ComplexEmbedding.Extension L v.embedding where
  toFun := fun w ↦ if hw : w.1.embedding.comp (algebraMap K L) = v.embedding then
    ⟨w.1.embedding, hw⟩ else ⟨conjugate w.1.embedding, embedding_conjugate_comp_eq _ hw⟩
  inj' := Function.Injective.dite (α := v.Extension L) (β := Extension L v.embedding) _
    (f := fun ⟨w, hw⟩ ↦ ⟨w.1.embedding, hw⟩)
    (f' := fun ⟨w, hw⟩ ↦ ⟨_, embedding_conjugate_comp_eq _ hw⟩)
    (by aesop (add simp [Function.Injective]))
    (by aesop (add simp [Function.Injective]))
    fun hc ↦ by simp at hc; simp_all [eq_of_embedding_eq_conjugate L hc]

open scoped Classical in
private abbrev toComplexExtensionConjugate :
    v.Extension L ↪ ComplexEmbedding.Extension L v.embedding where
  toFun := fun w ↦ if hw : (conjugate w.1.embedding).comp (algebraMap K L) = v.embedding then
    ⟨conjugate w.1.embedding, hw⟩ else ⟨w.1.embedding, embedding_comp_eq _ hw⟩
  inj' := Function.Injective.dite (α := v.Extension L) (β := Extension L v.embedding) _
    (f' := fun ⟨w, hw⟩ ↦ ⟨w.1.embedding, embedding_comp_eq _ hw⟩)
    (f := fun ⟨w, hw⟩ ↦ ⟨_, hw⟩)
    (by aesop (add simp [Function.Injective]))
    (by aesop (add simp [Function.Injective]))
    fun hc ↦ by simp at hc; simp_all [eq_of_embedding_eq_conjugate L hc.symm]

variable {L v}

abbrev inertiaDeg {v : InfinitePlace K} (w : v.Extension L) :=
  (⊥ : Ideal v.Completion).inertiaDeg (⊥ : Ideal w.1.Completion)

theorem inertiaDeg_eq_finrank {v : InfinitePlace K} (w : v.Extension L) :
    w.inertiaDeg = Module.finrank v.Completion w.1.Completion := by
  simp only [Ideal.inertiaDeg]
  simp [Ideal.comap_bot_of_injective _ <| FaithfulSMul.algebraMap_injective _ _]
  apply Algebra.finrank_eq_of_equiv_equiv (RingEquiv.quotientBot v.Completion)
    (RingEquiv.quotientBot w.1.Completion)
  ext
  simp [RingHom.algebraMap_toAlgebra]

end Extension

open NumberField.ComplexEmbedding

variable {v : InfinitePlace K} (w : InfinitePlace L)

namespace RamifiedExtension

open Extension

-- TODO : move
@[simps!]
def _root_.Function.Embedding.sumElim {α β γ : Type*} (e₁ : α ↪ γ) (e₂ : β ↪ γ)
    (h : ∀ a b, e₁ a ≠ e₂ b) : α ⊕ β ↪ γ where
  toFun := Sum.elim e₁ e₂
  inj' := e₁.injective.sumElim e₂.injective h

@[simp]
theorem _root_.Function.Embedding.subtypeMap_apply {α β : Sort*} {p : α → Prop} {q : β → Prop}
    (f : α ↪ β) (h : ∀ ⦃x : α⦄, p x → q (f x)) (a : {a : α // p a}) :
    f.subtypeMap h a = ⟨f a, h a.2⟩ := rfl

private theorem isMixed_toComplexExtension (w : v.Extension L) (h : w.1.IsRamified K) :
    IsMixed K (toComplexExtension L v w).1 := by
  simpa [w.2, ← h.comap_embedding] using h.isMixed_embedding

private theorem isMixed_toComplexExtensionConjugate (w : v.Extension L) (h : w.1.IsRamified K) :
    IsMixed K (toComplexExtensionConjugate L v w).1 := by
  simpa [w.2, ← h.comap_embedding_conjugate] using h.isMixed_conjugate_embedding

private theorem toComplexExtension_apply (w : v.Extension L) (h : w.1.IsRamified K) :
    toComplexExtension L v w = w.1.embedding := by
  simp [w.2, ← h.comap_embedding]

private theorem toComplexExtensionConjugate_apply (w : v.Extension L) (h : w.1.IsRamified K) :
    toComplexExtensionConjugate L v w = conjugate w.1.embedding := by
  simp [w.2, ← h.comap_embedding_conjugate]

private theorem toComplexExtension_ne_conjugate (w₁ w₂ : v.Extension L) (h₁ : w₁.1.IsRamified K)
    (h₂ : w₂.1.IsRamified K) :
    toComplexExtension L v w₁ ≠ toComplexExtensionConjugate L v w₂ := by
  rw [ne_eq, Subtype.mk.injEq]
  simp [-Function.Embedding.coeFn_mk, toComplexExtension_apply _ h₁,
    toComplexExtensionConjugate_apply _ h₂, h₂.ne_conjugate]

variable (L v)

/-- The equivalence between two copies of ramified places `w` over `v` and the type of all
mixed extensions of `v.embedding`. This two-fold equivalence exists because when `w` ramifies
over `v` both `w.embedding` and `conjugate w.embedding` give distinct mixed extensions of
`v.embedding`. -/
def sumEquivIsMixedExtension :
    { w : v.Extension L // w.1.IsRamified K } ⊕ { w : v.Extension L // w.1.IsRamified K } ≃
      { ψ : Extension L v.embedding // IsMixed K ψ.1 } := by
  let f : { w : v.Extension L // w.1.IsRamified K } ⊕ { w : v.Extension L // w.1.IsRamified K } ↪
      { ψ : Extension L v.embedding // IsMixed K ψ.1 } :=
    (toComplexExtension L v |>.subtypeMap isMixed_toComplexExtension).sumElim
      (toComplexExtensionConjugate L v |>.subtypeMap isMixed_toComplexExtensionConjugate)
        (fun ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ ↦ by simpa using toComplexExtension_ne_conjugate w₁ w₂ h₁ h₂)
  exact f.equivOfSurjective fun ⟨ψ, h⟩ ↦ by cases embedding_mk_eq ψ.1 with
  | inl hl => exact ⟨.inl ⟨⟨mk ψ, ψ.comap_mk_eq⟩, h.mk_isRamified⟩, by aesop⟩
  | inr hr => exact ⟨.inr ⟨⟨mk ψ, ψ.comap_mk_eq⟩, h.mk_isRamified⟩, by aesop⟩

open scoped Classical in
theorem two_mul_card_eq [NumberField L] :
    2 * Fintype.card ({ w : v.Extension L // w.1.IsRamified K }) =
      Fintype.card { ψ : Extension L v.embedding // IsMixed K ψ.1 } := by
  simp [← Fintype.card_eq.2 ⟨sumEquivIsMixedExtension L v⟩]; ring

end RamifiedExtension

namespace UnramifiedExtension

open Extension

private theorem isUnmixed_toComplexExtension (w : v.Extension L) (hw : w.1.IsUnramified K) :
    IsUnmixed K (toComplexExtension L v w).1 := by
  rcases eq_or_ne (w.1.embedding.comp (algebraMap K L)) v.embedding with (h | h)
  · simpa [h] using hw.isUnmixed
  · simpa [h] using hw.isUnmixed_conjugate

variable (L v)

/-- If `w` is an unramified place above `v` then there are the following two cases:
- `v` and `w` are both real;
- `v` and `w` are both complex.
In the first case `w.embedding` and `conjugate w.embedding` coincide. In the second case
only one of `w.embedding` and `conjugate w.embedding` can extend `v.embedding`. In both cases
then, there is a unique unmixed extension of `v.embedding` associated to the unramified
place `w` over `v`. -/
def equivIsUnmixedExtension : {w : v.Extension L // w.1.IsUnramified K } ≃
      { ψ : Extension L v.embedding // IsUnmixed K ψ.1 } := by
  apply ((toComplexExtension L v).subtypeMap isUnmixed_toComplexExtension).equivOfSurjective
  rintro ⟨ψ, h⟩
  use ⟨⟨mk ψ, ψ.comap_mk_eq⟩, h.mk_isUnramified⟩
  rcases embedding_mk_eq ψ.1 with (_ | _) <;> aesop (add simp [conjugate_comp])

open scoped Classical in
theorem card_eq [NumberField L] :
    Fintype.card ({w : v.Extension L // w.1.IsUnramified K }) =
      Fintype.card { ψ : Extension L v.embedding // IsUnmixed K ψ.1 } := by
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
  rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivRealOfIsReal h.extension_isReal_base)
      (ringEquivComplexOfIsComplex h.isComplex) (by simp [RingHom.ext_iff,
        ← w.extensionEmbedding_algebraMap_of_isReal h.extension_isReal_base]),
    Complex.finrank_real_complex]

end RamifiedExtension

namespace UnramifiedExtension

open NumberField.ComplexEmbedding Extension

variable {L : Type*} [Field L] [Algebra K L] (w : v.Extension L)

/-- If `w` is an unramified extension of `v` and both infinite places are complex then
the `v.Completion`-dimension of `w.Completion` is `1`. -/
theorem finrank_eq_one (h : w.1.IsUnramified K) :
    Module.finrank v.Completion w.1.Completion = 1 := by
  by_cases hv : v.IsReal
  · rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivRealOfIsReal hv) (ringEquivRealOfIsReal
      (h.extension_isReal_of_isReal hv)) (RingHom.ext fun _ ↦ Complex.ofReal_inj.1 <| by
        simp [← extensionEmbedding_algebraMap_of_isReal w hv]), Module.finrank_self]
  · have hv : v.IsComplex := not_isReal_iff_isComplex.1 hv
    cases embedding_comp_eq_or_conjugate_embedding_comp_eq w with
    | inl hl => rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivComplexOfIsComplex hv)
        (ringEquivComplexOfIsComplex (w.isComplex_of_isComplex hv))
        (RingHom.ext fun _ ↦ by simp [← extensionEmbedding_algebraMap _ hl]),
        Module.finrank_self]
    | inr hr => rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivComplexOfIsComplex hv)
        ((ringEquivComplexOfIsComplex (w.isComplex_of_isComplex hv)).trans (starRingAut (R := ℂ)))
        (RingHom.ext fun _ ↦ by simp [← conjugate_extensionEmbedding_algebraMap _ hr]),
        Module.finrank_self]

end UnramifiedExtension

end Completion

namespace Extension

open UnramifiedExtension RamifiedExtension

instance : Algebra (WithAbs v.1) ℂ := v.embedding.toAlgebra

theorem algHom_comp_eq (φ : L →ₐ[WithAbs v.1] ℂ) :
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
def algHomEquivExtension :
    (L →ₐ[WithAbs v.1] ℂ) ≃ Extension L v.embedding :=
  Equiv.ofBijective (fun φ => ⟨φ.toRingHom, algHom_comp_eq φ⟩)
    ⟨fun _ _ h => AlgHom.coe_ringHom_injective (by simpa using h),
      fun ⟨σ, h⟩ => ⟨⟨σ, fun _ => by simp [RingHom.algebraMap_toAlgebra, ← h]; rfl⟩, rfl⟩⟩

open scoped Classical in
theorem card_isUnramified_add_two_mul_card_isRamified [NumberField K] [NumberField L] :
    Fintype.card ({w : v.Extension L // w.1.IsUnramified K }) +
      2 * Fintype.card ({w : v.Extension L // w.1.IsRamified K }) =
      Module.finrank (WithAbs v.1) L := by
  rw [← AlgHom.card (WithAbs v.1) L ℂ, Fintype.card_eq.2 ⟨algHomEquivExtension L v⟩,
    Fintype.card_eq.2 ⟨(Equiv.sumCompl fun φ : Extension L _ ↦ IsMixed K φ.1).symm⟩,
    Fintype.card_sum, RamifiedExtension.two_mul_card_eq, UnramifiedExtension.card_eq]; ring

theorem _root_.WithAbs.finrank_left_eq {R R' S : Type*} [Semiring S] [PartialOrder S]
    [CommSemiring R] [Semiring R'] [Algebra R R'] [Module.Finite R R'] (v : AbsoluteValue R S) :
    Module.finrank (WithAbs v) R' = Module.finrank R R' :=
  Algebra.finrank_eq_of_equiv_equiv (WithAbs.equiv v) (RingEquiv.refl R') <|
    RingHom.ext fun x ↦ by simpa using WithAbs.algebraMap_left_apply v x

open scoped Classical in
open Completion Finset in
theorem sum_inertiaDeg_eq_finrank [NumberField K] [NumberField L] :
    ∑ w : v.Extension L, w.inertiaDeg = Module.finrank K L := by
  rw [Fintype.sum_equiv (Equiv.sumCompl fun w ↦ w.1.IsUnramified K).symm _
    ((fun w ↦ w.inertiaDeg) ∘ (Equiv.sumCompl fun w : v.Extension L ↦ w.1.IsUnramified K))
    (fun _ => by rw [Function.comp_apply, Equiv.apply_symm_apply])]
  simp only [Function.comp_apply, Fintype.sum_sum_type, Equiv.sumCompl_apply_inl,
    Equiv.sumCompl_apply_inr]
  rw [sum_congr rfl (fun w  _ => inertiaDeg_eq_finrank w.1 ▸
      UnramifiedExtension.finrank_eq_one w.1 w.2),
    sum_const, sum_congr rfl (fun w _  => inertiaDeg_eq_finrank w.1 ▸
      RamifiedExtension.finrank_eq_two w.1 w.2),
    sum_const, ← Fintype.card, ← Fintype.card, smul_eq_mul, mul_one, smul_eq_mul, mul_comm,
    card_isUnramified_add_two_mul_card_isRamified, WithAbs.finrank_left_eq]

end Extension

end NumberField.InfinitePlace
