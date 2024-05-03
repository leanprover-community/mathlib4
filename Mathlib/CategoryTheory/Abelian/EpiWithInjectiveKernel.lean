/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Epimorphisms with an injective kernel

In this file, we define the class of morphisms `epiWithInjectiveKernel` in an
abelian category. We show that this property of morphisms is multiplicative.

This shall be used in the file `Algebra.Homology.Factorizations.Basic` in
order to define morphisms of cochain complexes which satisfies this property
degreewise.

-/

namespace CategoryTheory

open Category Limits ZeroObject Preadditive

variable {C : Type*} [Category C] [Abelian C]

namespace Abelian

/-- The class of morphisms in an abelian category that are epimorphisms
and have an injective kernel. -/
def epiWithInjectiveKernel : MorphismProperty C :=
  fun _ _ f => Epi f ∧ Injective (kernel f)

/-- A morphism `g : X ⟶ Y` is epi with an injective kernel iff there exists a morphism
`f : I ⟶ X` with `I` injective such that `f ≫ g = 0` and
the the short complex `I ⟶ X ⟶ Y` has a splitting. -/
lemma epiWithInjectiveKernel_iff {X Y : C} (g : X ⟶ Y) :
    epiWithInjectiveKernel g ↔ ∃ (I : C) (_ : Injective I) (f : I ⟶ X) (w : f ≫ g = 0),
      Nonempty (ShortComplex.mk _ _ w).Splitting := by
  constructor
  · rintro ⟨_, _⟩
    let S := ShortComplex.mk (kernel.ι g) g (by simp)
    exact ⟨_, inferInstance, _, S.zero,
      ⟨ShortComplex.Splitting.ofExactOfRetraction S
        (S.exact_of_f_is_kernel (kernelIsKernel g)) (Injective.factorThru (𝟙 _) (kernel.ι g))
        (by simp) inferInstance⟩⟩
  · rintro ⟨I, _,  f, w, ⟨σ⟩⟩
    have : IsSplitEpi g := ⟨σ.s, σ.s_g⟩
    let e : I ≅ kernel g :=
      IsLimit.conePointUniqueUpToIso σ.shortExact.fIsKernel (limit.isLimit _)
    exact ⟨inferInstance, Injective.of_iso e inferInstance⟩

lemma epiWithInjectiveKernel_of_iso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    epiWithInjectiveKernel f := by
  rw [epiWithInjectiveKernel_iff]
  exact ⟨0, inferInstance, 0, by simp,
    ⟨ShortComplex.Splitting.ofIsZeroOfIsIso _ (isZero_zero C) (by dsimp; infer_instance)⟩⟩

instance : (epiWithInjectiveKernel : MorphismProperty C).IsMultiplicative where
  id_mem _ := by apply epiWithInjectiveKernel_of_iso
  comp_mem {X Y Z} g₁ g₂ hg₁ hg₂ := by
    rw [epiWithInjectiveKernel_iff] at hg₁ hg₂ ⊢
    obtain ⟨I₁, _, f₁, w₁, ⟨σ₁⟩⟩ := hg₁
    obtain ⟨I₂, _, f₂, w₂, ⟨σ₂⟩⟩ := hg₂
    have s_g₁ := σ₁.s_g
    have s_g₂ := σ₂.s_g
    have f_r₁ := σ₁.f_r
    have f_r₂ := σ₂.f_r
    have id₁ := σ₁.id
    have id₂ := σ₂.id
    dsimp at s_g₁ s_g₂ f_r₁ f_r₂ id₁ id₂
    refine' ⟨I₁ ⊞ I₂, inferInstance, biprod.fst ≫ f₁ + biprod.snd ≫ f₂ ≫ σ₁.s, _, ⟨_⟩⟩
    · ext
      · simp [reassoc_of% w₁]
      · simp [reassoc_of% s_g₁, w₂]
    · exact
        { r := σ₁.r ≫ biprod.inl + g₁ ≫ σ₂.r ≫ biprod.inr
          s := σ₂.s ≫ σ₁.s
          f_r := by
            ext
            · simp [f_r₁]
            · simp [reassoc_of% w₁]
            · simp
            · simp [reassoc_of% s_g₁, f_r₂]
          s_g := by simp [reassoc_of% s_g₁, s_g₂]
          id := by
            dsimp
            have h := g₁ ≫= id₂ =≫ σ₁.s
            simp only [add_comp, assoc, comp_add, id_comp] at h
            rw [← h] at id₁
            rw [← id₁]
            simp only [comp_add, add_comp, assoc, BinaryBicone.inl_fst_assoc,
              BinaryBicone.inr_fst_assoc, zero_comp, comp_zero, add_zero,
              BinaryBicone.inl_snd_assoc, BinaryBicone.inr_snd_assoc, zero_add]
            abel }

end Abelian

end CategoryTheory
