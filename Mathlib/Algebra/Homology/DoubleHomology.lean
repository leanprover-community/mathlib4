/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Double
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Refinements
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Homology of double complexes

-/

namespace CategoryTheory

open Limits ZeroObject HomologicalComplex

variable {C : Type*} [Category C] [Abelian C]

namespace ShortComplex

variable (S : ShortComplex C)

@[simps!]
noncomputable def arrowHomToG : Arrow.mk (0 : S.X₁ ⟶ 0) ⟶ Arrow.mk S.g :=
  Arrow.homMk S.f 0

variable {ι : Type*} {c : ComplexShape ι} {i₀ i₁ : ι} (hi₀₁ : c.Rel i₀ i₁) (hi₀₁' : i₀ ≠ i₁)

lemma mono_homologyMap₀_doubleFunctor_map_arrowHomToG_iff :
    Mono (HomologicalComplex.homologyMap ((doubleFunctor C hi₀₁ hi₀₁').map S.arrowHomToG) i₀) ↔
      Mono S.f := by
  let e₁ := doubleXIso₀ (0 : S.X₁ ⟶ 0) hi₀₁
  let e₂ := doubleXIso₀ S.g hi₀₁
  have h₀ : (double (0 : S.X₁ ⟶ 0) hi₀₁).d i₀ i₁ = 0 := by simp [double_d _ hi₀₁ hi₀₁']
  have hf : ((doubleFunctor C hi₀₁ hi₀₁').map S.arrowHomToG).f i₀ = e₁.hom ≫ S.f ≫ e₂.inv := by
    simp [e₁, e₂, doubleFunctor_map]
  rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements _ _ _ _ rfl (c.next_eq' hi₀₁)]
  dsimp
  simp only [hf, h₀, double_d_eq_zero₁ _ _ _ _ hi₀₁', comp_zero, exists_prop,
    forall_const, exists_const]
  constructor
  · intro h
    rw [Preadditive.mono_iff_cancel_zero]
    intro A x₁ hx₁
    have pif := h (x₁ ≫ e₁.inv) (by simp [reassoc_of% hx₁])
    obtain ⟨A', π, _, fac⟩ := h (x₁ ≫ e₁.inv) (by simp [reassoc_of% hx₁])
    rw [← cancel_mono e₁.inv, ← cancel_epi π, fac, zero_comp, comp_zero]
  · intro _ A x₁ hx₁
    refine ⟨A, 𝟙 _, inferInstance, ?_⟩
    rw [Category.id_comp, ← cancel_mono (e₁.hom ≫ S.f ≫ e₂.inv), hx₁, zero_comp]

lemma epi_homologyMap₀_doubleFunctor_map_arrowHomToG_iff :
    Epi (HomologicalComplex.homologyMap ((doubleFunctor C hi₀₁ hi₀₁').map S.arrowHomToG) i₀) ↔
      S.Exact := by
  let e₁ := doubleXIso₀ (0 : S.X₁ ⟶ 0) hi₀₁
  let e₂ := doubleXIso₀ S.g hi₀₁
  let e₃ := doubleXIso₁ S.g hi₀₁ hi₀₁'
  have h₀ : (double (0 : S.X₁ ⟶ 0) hi₀₁).d i₀ i₁ = 0 := by simp [double_d _ hi₀₁ hi₀₁']
  have hf : ((doubleFunctor C hi₀₁ hi₀₁').map S.arrowHomToG).f i₀ = e₁.hom ≫ S.f ≫ e₂.inv := by
    simp [e₁, e₂, doubleFunctor_map]
  have hg : (double S.g hi₀₁).d i₀ i₁ = e₂.hom ≫ S.g ≫ e₃.inv := by
    simp [e₂, e₃, double_d _ hi₀₁ hi₀₁']
  rw [HomologicalComplex.epi_homologyMap_iff_up_to_refinements _ _ _ _ rfl (c.next_eq' hi₀₁),
    exact_iff_exact_up_to_refinements]
  dsimp
  simp only [hf, hg, h₀, double_d_eq_zero₁ S.g hi₀₁ (c.prev i₀) i₀ hi₀₁',
    comp_zero, exists_const, exists_prop, add_zero]
  constructor
  · intro h A x₂ hx₂
    obtain ⟨A', π, _, x₁, fac⟩ := h (x₂ ≫ e₂.inv) (by simp [reassoc_of% hx₂])
    refine ⟨A', π, inferInstance, x₁ ≫ e₁.hom, ?_⟩
    rw [← cancel_mono (e₂.inv), Category.assoc, fac, Category.assoc, Category.assoc]
  · intro h A x₂ hx₂
    obtain ⟨A', π, _, x₁, fac⟩ := h (x₂ ≫ e₂.hom)
      (by simp only [Category.assoc, ← cancel_mono e₃.inv, hx₂, zero_comp])
    exact ⟨A', π, inferInstance, x₁ ≫ e₁.inv, by simp [← cancel_mono e₂.hom, fac]⟩

lemma quasiIsoAt₀_doubleFunctor_map_arrowHomToG_iff :
    _root_.QuasiIsoAt ((doubleFunctor C hi₀₁ hi₀₁').map S.arrowHomToG) i₀ ↔
      S.Exact ∧ Mono S.f := by
  rw [quasiIsoAt_iff_isIso_homologyMap,
    ← mono_homologyMap₀_doubleFunctor_map_arrowHomToG_iff _ hi₀₁ hi₀₁',
    ← epi_homologyMap₀_doubleFunctor_map_arrowHomToG_iff _ hi₀₁ hi₀₁']
  exact ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ isIso_of_mono_of_epi _⟩

lemma quasiIsoAt₁_doubleFunctor_map_arrowHomToG_iff :
    _root_.QuasiIsoAt ((doubleFunctor C hi₀₁ hi₀₁').map S.arrowHomToG) i₁ ↔ Epi S.g := by
  rw [_root_.quasiIsoAt_iff_exactAt]; swap
  · apply ShortComplex.exact_of_isZero_X₂
    exact IsZero.of_iso (Limits.isZero_zero C) (doubleXIso₁ 0 hi₀₁ hi₀₁')
  rw [exactAt_iff' _ _ _ _ (c.prev_eq' hi₀₁) rfl,
    exact_iff_epi _ (double_d_eq_zero₀ S.g hi₀₁ _ _ hi₀₁'.symm)]
  exact (MorphismProperty.epimorphisms _).arrow_mk_iso_iff
    (arrowIsoDoubleD S.g hi₀₁ hi₀₁')

lemma quasiIso_doubleFunctor_map_arrowHomToG_iff_exact :
    _root_.QuasiIso ((doubleFunctor C hi₀₁ hi₀₁').map S.arrowHomToG) ↔ S.ShortExact := by
  let φ := ((doubleFunctor C hi₀₁ hi₀₁').map S.arrowHomToG)
  constructor
  · intro (h : _root_.QuasiIso φ)
    rw [_root_.quasiIso_iff] at h
    have h₀ := h i₀
    have h₁ := h i₁
    rw [quasiIsoAt₀_doubleFunctor_map_arrowHomToG_iff] at h₀
    rw [quasiIsoAt₁_doubleFunctor_map_arrowHomToG_iff] at h₁
    obtain ⟨h, _⟩ := h₀
    exact { exact := h }
  · intro hS
    rw [_root_.quasiIso_iff]
    intro i
    by_cases h₀ : i = i₀
    · subst h₀
      rw [quasiIsoAt₀_doubleFunctor_map_arrowHomToG_iff]
      exact ⟨hS.exact, hS.mono_f⟩
    · by_cases h₁ : i = i₁
      · subst h₁
        rw [quasiIsoAt₁_doubleFunctor_map_arrowHomToG_iff]
        exact hS.epi_g
      · rw [quasiIsoAt_iff_exactAt]
        all_goals
          apply ShortComplex.exact_of_isZero_X₂
          apply isZero_double_X 0 hi₀₁ i h₀ h₁

end ShortComplex

end CategoryTheory
