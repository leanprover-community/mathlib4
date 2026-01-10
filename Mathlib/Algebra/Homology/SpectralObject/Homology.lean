/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Differentials
public import Mathlib.CategoryTheory.ComposableArrows.Four

/-!
# Homology of differentials

-/

@[expose] public section

namespace CategoryTheory

open Category Limits ComposableArrows Preadditive

namespace Abelian

variable {C ι : Type*} [Category C] [Abelian C] [Category ι]

namespace SpectralObject

variable (X : SpectralObject C ι)

section

variable (n₀ n₁ n₂ n₃ : ℤ)
  (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  {i₀' i₀ i₁ i₂ i₃ i₃' : ι} (f₁ : i₀ ⟶ i₁)
  (f₁' : i₀' ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃) (f₃' : i₂ ⟶ i₃')

lemma epi_EMap (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁ f₂ f₃')
    (hα₀ : α.app 0 = 𝟙 _) (hα₁ : α.app 1 = 𝟙 _) (hα₂ : α.app 2 = 𝟙 _) :
    Epi (X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁ f₂ f₃' α) := by
  have := X.πE_EMap  n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _ α (𝟙 _) (by cat_disch)
  rw [cyclesMap_id, id_comp] at this
  exact epi_of_epi_fac this

lemma mono_EMap (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂ f₃)
    (hα₁ : α.app 1 = 𝟙 _) (hα₂ : α.app 2 = 𝟙 _) (hα₃ : α.app 3 = 𝟙 _) :
    Mono (X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂ f₃ α) := by
  have := X.EMap_ιE  n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _ α (𝟙 _) (by cat_disch)
  rw [opcyclesMap_id, comp_id] at this
  exact mono_of_mono_fac this

end

section

variable (n₀ n₁ n₂ n₃ : ℤ)
  (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃)
  {i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (f₃₄ : i₂ ⟶ i₄) (h₃₄ : f₃ ≫ f₄ = f₃₄)

@[reassoc (attr := simp)]
lemma d_EMap_fourδ₄Toδ₃ :
    X.d n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ ≫
      X.EMap n₁ n₂ n₃ hn₂ hn₃ f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) = 0 := by
  rw [← cancel_epi (X.πE n₀ n₁ n₂ hn₁ hn₂ f₃ f₄ f₅),
    ← cancel_epi (X.toCycles n₁ f₃ f₄ f₃₄ h₃₄), comp_zero, comp_zero,
    X.toCycles_πE_d_assoc n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ _ rfl f₃₄ h₃₄,
    X.πE_EMap n₁ n₂ n₃ hn₂ hn₃ f₁ f₂ f₃ f₁ f₂ f₃₄
    (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) (𝟙 _) (by ext <;> simp; rfl),
    cyclesMap_id, Category.id_comp, δ_toCycles_assoc, δToCycles_πE]

instance :
    Epi (X.EMap n₁ n₂ n₃ hn₂ hn₃ f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄)) := by
  apply X.epi_EMap
  all_goals rfl

lemma isIso_EMap_fourδ₄Toδ₃ (h : ((X.H n₁).map (twoδ₁Toδ₀ f₃ f₄ f₃₄ h₃₄) = 0)) :
    IsIso (X.EMap n₁ n₂ n₃ hn₂ hn₃ f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄)) := by
  apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
  · exact (X.exact₂ _ f₃ f₄ f₃₄ h₃₄).epi_f h
  · dsimp
    have : 𝟙 (mk₁ f₂) = homMk₁ (𝟙 _) (𝟙 _) (by simp) := by ext <;> simp
    erw [← this]
    infer_instance
  · dsimp
    have : 𝟙 (mk₁ f₁) = homMk₁ (𝟙 _) (𝟙 _) (by simp) := by ext <;> simp
    erw [← this]
    infer_instance

lemma isIso_EMap_fourδ₄Toδ₃_of_isZero (h : IsZero ((X.H n₁).obj (mk₁ f₄))) :
    IsIso (X.EMap n₁ n₂ n₃ hn₂ hn₃ f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄)) := by
  apply X.isIso_EMap_fourδ₄Toδ₃
  apply h.eq_of_tgt

@[reassoc (attr := simp)]
lemma EMap_fourδ₁Toδ₀_d :
    X.EMap n₀ n₁ n₂ hn₁ hn₂ f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) ≫
      X.d n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ = 0 := by
  rw [← cancel_mono (X.ιE n₁ n₂ n₃ hn₂ hn₃ f₁ f₂ f₃),
    ← cancel_mono (X.fromOpcycles n₂ f₂ f₃ f₂₃ h₂₃), zero_comp, zero_comp, assoc,
    assoc, X.d_ιE_fromOpcycles n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ f₂₃ h₂₃ _ rfl _ rfl]
  rw [X.EMap_ιE_assoc n₀ n₁ n₂ hn₁ hn₂ f₂₃ f₄ f₅ f₃ f₄ f₅
    (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) (𝟙 _) (by ext <;> simp <;> rfl),
    opcyclesMap_id, fromOpcyles_δ, id_comp, ιE_δFromOpcycles]

instance :
    Mono (X.EMap n₀ n₁ n₂ hn₁ hn₂ f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃)) := by
  apply mono_EMap
  all_goals rfl

lemma isIso_EMap_fourδ₁Toδ₀ (h : ((X.H n₂).map (twoδ₂Toδ₁ f₂ f₃ f₂₃ h₂₃) = 0)) :
    IsIso (X.EMap n₀ n₁ n₂ hn₁ hn₂ f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃)) := by
  apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
  · dsimp
    have : 𝟙 (mk₁ f₅) = homMk₁ (𝟙 _) (𝟙 _) (by simp) := by ext <;> simp
    erw [← this]
    infer_instance
  · dsimp
    have : 𝟙 (mk₁ f₄) = homMk₁ (𝟙 _) (𝟙 _) (by simp) := by ext <;> simp
    erw [← this]
    infer_instance
  · exact (X.exact₂ n₂ f₂ f₃ f₂₃ h₂₃).mono_g h

lemma isIso_EMap_fourδ₁Toδ₀_of_isZero (h : IsZero ((X.H n₂).obj (mk₁ f₂))) :
    IsIso (X.EMap n₀ n₁ n₂ hn₁ hn₂ f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃)) := by
  apply X.isIso_EMap_fourδ₁Toδ₀
  apply h.eq_of_src

@[simps!]
noncomputable def dCokernelSequence : ShortComplex C :=
  ShortComplex.mk _ _ (X.d_EMap_fourδ₄Toδ₃ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ f₃₄ h₃₄)

instance : Epi (X.dCokernelSequence n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ f₃₄ h₃₄).g := by
  dsimp
  infer_instance

lemma dCokernelSequence_exact :
    (X.dCokernelSequence n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ f₃₄ h₃₄).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂ ⊢
  have hx₂' := hx₂ =≫ X.ιE _ _ _ _ _ _ _ _
  simp only [assoc, zero_comp] at hx₂'
  rw [X.EMap_ιE n₁ n₂ n₃ hn₂ hn₃ f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄)
    (threeδ₃Toδ₂ f₂ f₃ f₄ f₃₄ h₃₄) (by cat_disch)] at hx₂'
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ :=
    ((X.sequenceΨ_exact n₁ n₂ hn₂ f₂ f₃ f₄ _ rfl
      f₃₄ h₃₄).exact 1).exact_up_to_refinements (x₂ ≫ X.ιE _ _ _ _ _ _ _ _) (by
        dsimp [sequenceΨ, Precomp.map]
        rw [assoc, hx₂'])
  dsimp [sequenceΨ, Precomp.map] at x₁ hx₁
  refine ⟨A₁, π₁, inferInstance, x₁ ≫ X.πE n₀ n₁ n₂ hn₁ hn₂ f₃ f₄ f₅, ?_⟩
  rw [← cancel_mono (X.ιE _ _ _ _ _ _ _ _), assoc, assoc, assoc, hx₁, πE_d_ιE]

@[simps!]
noncomputable def dKernelSequence : ShortComplex C :=
  ShortComplex.mk _ _ (X.EMap_fourδ₁Toδ₀_d n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ f₂₃ h₂₃)

instance : Mono (X.dKernelSequence n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ f₂₃ h₂₃).f := by
  dsimp
  infer_instance

lemma dKernelSequence_exact :
    (X.dKernelSequence n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ f₂₃ h₂₃).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂ ⊢
  obtain ⟨A₁, π₁, _, y₂, hy₂⟩ :=
    surjective_up_to_refinements_of_epi (X.πE n₀ n₁ n₂ hn₁ hn₂ f₃ f₄ f₅) x₂
  have hy₂' := hy₂ =≫ (X.d n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ ≫ X.ιE _ _ _ _ _ _ _ _)
  simp only [assoc, reassoc_of% hx₂, zero_comp, comp_zero, πE_d_ιE] at hy₂'
  obtain ⟨A₂, π₂, _, y₁, hy₁⟩ :=
    ((X.sequenceΨ_exact n₁ n₂ hn₂ f₂ f₃ f₄
      f₂₃ h₂₃ _ rfl).exact 0).exact_up_to_refinements y₂ hy₂'.symm
  dsimp [sequenceΨ] at y₁ hy₁
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, y₁ ≫ X.πE n₀ n₁ n₂ hn₁ hn₂ f₂₃ f₄ f₅, ?_⟩
  rw [assoc, assoc, hy₂, reassoc_of% hy₁,
    X.πE_EMap n₀ n₁ n₂ hn₁ hn₂ f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃)
    (threeδ₁Toδ₀ f₂ f₃ f₄ f₂₃ h₂₃) (by ext <;> simp; rfl)]

end

variable (n₀ n₁ n₂ n₃ n₄ : ℤ)
  (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃) (hn₄ : n₃ + 1 = n₄)
  {i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (f₆ : i₅ ⟶ i₆) (f₇ : i₆ ⟶ i₇)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (f₅₆ : i₄ ⟶ i₆) (h₅₆ : f₅ ≫ f₆ = f₅₆)

@[simps!]
noncomputable def dShortComplex : ShortComplex C :=
  ShortComplex.mk _ _ (X.d_d n₀ n₁ n₂ n₃ n₄ hn₁ hn₂ hn₃ hn₄ f₁ f₂ f₃ f₄ f₅ f₆ f₇)

lemma EMap_fac :
    X.EMap n₁ n₂ n₃ hn₂ hn₃ f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) ≫
      X.EMap n₁ n₂ n₃ hn₂ hn₃ f₃ f₄ f₅ f₃ f₄ f₅₆ (fourδ₄Toδ₃ f₃ f₄ f₅ f₆ f₅₆ h₅₆) =
    X.EMap n₁ n₂ n₃ hn₂ hn₃ f₂₃ f₄ f₅ f₂₃ f₄ f₅₆ (fourδ₄Toδ₃ f₂₃ f₄ f₅ f₆ f₅₆ h₅₆) ≫
      X.EMap n₁ n₂ n₃ hn₂ hn₃ f₂₃ f₄ f₅₆ f₃ f₄ f₅₆ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅₆ f₂₃ h₂₃) := by
  simp only [← EMap_comp]
  congr 1
  ext <;> simp

noncomputable def dHomologyData :
    (X.dShortComplex n₀ n₁ n₂ n₃ n₄ hn₁ hn₂ hn₃ hn₄ f₁ f₂ f₃ f₄ f₅ f₆ f₇).HomologyData :=
  ShortComplex.HomologyData.ofEpiMonoFactorisation
    (X.dShortComplex n₀ n₁ n₂ n₃ n₄ hn₁ hn₂ hn₃ hn₄ f₁ f₂ f₃ f₄ f₅ f₆ f₇)
    (X.dKernelSequence_exact n₁ n₂ n₃ n₄ hn₂ hn₃ hn₄ f₁ f₂ f₃ f₄ f₅ f₂₃ h₂₃).fIsKernel
    (X.dCokernelSequence_exact n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₃ f₄ f₅ f₆ f₇ f₅₆ h₅₆).gIsCokernel
    (X.EMap_fac n₁ n₂ n₃ hn₂ hn₃ f₂ f₃ f₄ f₅ f₆ f₂₃ h₂₃ f₅₆ h₅₆)

noncomputable def dHomologyIso :
    (X.dShortComplex n₀ n₁ n₂ n₃ n₄ hn₁ hn₂ hn₃ hn₄ f₁ f₂ f₃ f₄ f₅ f₆ f₇).homology ≅
      X.E n₁ n₂ n₃ hn₂ hn₃ f₂₃ f₄ f₅₆ :=
  (X.dHomologyData n₀ n₁ n₂ n₃ n₄ hn₁ hn₂ hn₃ hn₄
    f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₂₃ h₂₃ f₅₆ h₅₆).left.homologyIso

end SpectralObject

end Abelian

end CategoryTheory
