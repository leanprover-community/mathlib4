/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Differentials
public import Mathlib.CategoryTheory.ComposableArrows.Four

/-!
# Spectral objects in abelian categories


## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

open Category Limits ComposableArrows

namespace Abelian

namespace SpectralObject

variable {C ι ι' κ : Type*} [Category C] [Abelian C] [Category ι] [Preorder ι']
  (X : SpectralObject C ι) (X' : SpectralObject C ι')

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
    Epi (X.EMap n₁ n₂ n₃ hn₂ hn₃ f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄)) :=
  X.epi_EMap _ _ _ _ _ _ _ _ _ _ rfl rfl rfl

lemma isIso_EMap_fourδ₄Toδ₃ (h : ((X.H n₁).map (twoδ₁Toδ₀ f₃ f₄ f₃₄ h₃₄) = 0)) :
    IsIso (X.EMap n₁ n₂ n₃ hn₂ hn₃ f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄)) := by
  apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
  · exact (X.exact₂ _ f₃ f₄ f₃₄ h₃₄).epi_f h
  · dsimp
    convert inferInstanceAs (IsIso ((X.H n₂).map (𝟙 _)))
    cat_disch
  · dsimp
    convert inferInstanceAs (Mono ((X.H n₃).map (𝟙 (mk₁ f₁))))
    cat_disch

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
    Mono (X.EMap n₀ n₁ n₂ hn₁ hn₂ f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃)) :=
  X.mono_EMap _ _ _ _ _ _ _ _ _ _ rfl rfl rfl

lemma isIso_EMap_fourδ₁Toδ₀ (h : ((X.H n₂).map (twoδ₂Toδ₁ f₂ f₃ f₂₃ h₂₃) = 0)) :
    IsIso (X.EMap n₀ n₁ n₂ hn₁ hn₂ f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃)) := by
  apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
  · dsimp
    convert inferInstanceAs (Epi ((X.H n₀).map (𝟙 _)))
    cat_disch
  · dsimp
    convert inferInstanceAs (IsIso ((X.H n₁).map (𝟙 _)))
    cat_disch
  · exact (X.exact₂ n₂ f₂ f₃ f₂₃ h₂₃).mono_g h

lemma isIso_EMap_fourδ₁Toδ₀_of_isZero (h : IsZero ((X.H n₂).obj (mk₁ f₂))) :
    IsIso (X.EMap n₀ n₁ n₂ hn₁ hn₂ f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃)) := by
  apply X.isIso_EMap_fourδ₁Toδ₀
  apply h.eq_of_src

end

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
    (i₀ i₁ i₂ i₃ i₄ i₅ : ι') (hi₀₁ : i₀ ≤ i₁)
    (hi₁₂ : i₁ ≤ i₂) (hi₂₃ : i₂ ≤ i₃) (hi₃₄ : i₃ ≤ i₄) (hi₄₅ : i₄ ≤ i₅)

/-- EMapFourδ₁Toδ₀' -/
noncomputable abbrev EMapFourδ₁Toδ₀' :=
  X'.EMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _ (fourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄)


/-- EMapFourδ₄Toδ₃' -/
noncomputable abbrev EMapFourδ₄Toδ₃' :=
  X'.EMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _ (fourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄)

@[reassoc]
lemma EMapFourδ₁Toδ₀'_comp :
  X'.EMapFourδ₁Toδ₀' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₃ i₄ i₅ hi₀₁ (hi₁₂.trans hi₂₃) hi₃₄ hi₄₅ ≫
    X'.EMapFourδ₁Toδ₀' n₀ n₁ n₂ hn₁ hn₂ i₁ i₂ i₃ i₄ i₅ hi₁₂ hi₂₃ hi₃₄ hi₄₅ =
    X'.EMapFourδ₁Toδ₀' n₀ n₁ n₂ hn₁ hn₂ i₀ i₂ i₃ i₄ i₅ (hi₀₁.trans hi₁₂) hi₂₃ hi₃₄ hi₄₅ := by
  rw [← EMap_comp]
  rfl

@[reassoc]
lemma EMapFourδ₄Toδ₃'_comp :
  X'.EMapFourδ₄Toδ₃' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ ≫
    X'.EMapFourδ₄Toδ₃' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₄ i₅ hi₀₁ hi₁₂ (hi₂₃.trans hi₃₄) hi₄₅ =
    X'.EMapFourδ₄Toδ₃' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₅ hi₀₁ hi₁₂ hi₂₃ (hi₃₄.trans hi₄₅) := by
  dsimp [EMapFourδ₄Toδ₃']
  rw [← EMap_comp]
  rfl

@[reassoc]
lemma EMapFourδ₁Toδ₀'_EMapFourδ₃Toδ₃' :
    X'.EMapFourδ₁Toδ₀' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ ≫
      X'.EMapFourδ₄Toδ₃' n₀ n₁ n₂ hn₁ hn₂ i₁ i₂ i₃ i₄ i₅ hi₁₂ hi₂₃ hi₃₄ hi₄₅ =
      X'.EMapFourδ₄Toδ₃' n₀ n₁ n₂ hn₁ hn₂ i₀ i₂ i₃ i₄ i₅ _ _ _ hi₄₅ ≫
        X'.EMapFourδ₁Toδ₀' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₅ hi₀₁ _ _ _ := by
  dsimp [EMapFourδ₁Toδ₀', EMapFourδ₄Toδ₃']
  rw [← EMap_comp, ← EMap_comp]
  rfl

section

variable (h : IsZero ((X'.H n₂).obj (mk₁ (homOfLE hi₀₁))))

include h in
lemma isIso_EMapFourδ₁Toδ₀' :
    IsIso (X'.EMapFourδ₁Toδ₀' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄) := by
  apply X'.isIso_EMap_fourδ₁Toδ₀_of_isZero
  exact h

/-- isoEMapFourδ₁Toδ₀' -/
@[simps! hom]
noncomputable def isoEMapFourδ₁Toδ₀' :
    X'.E n₀ n₁ n₂ hn₁ hn₂ (homOfLE (hi₀₁.trans hi₁₂)) (homOfLE hi₂₃) (homOfLE hi₃₄) ≅
      X'.E n₀ n₁ n₂ hn₁ hn₂ (homOfLE hi₁₂) (homOfLE hi₂₃) (homOfLE hi₃₄) :=
  have := X'.isIso_EMapFourδ₁Toδ₀' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ h
  asIso (X'.EMapFourδ₁Toδ₀' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄)

@[reassoc (attr := simp)]
lemma isoEMapFourδ₁Toδ₀'_hom_inv_id :
    X'.EMapFourδ₁Toδ₀' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ ≫
    (X'.isoEMapFourδ₁Toδ₀' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ h).inv = 𝟙 _ :=
  (X'.isoEMapFourδ₁Toδ₀' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ h).hom_inv_id

@[reassoc (attr := simp)]
lemma isoEMapFourδ₁Toδ₀'_inv_hom_id :
    (X'.isoEMapFourδ₁Toδ₀' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ h).inv ≫
    X'.EMapFourδ₁Toδ₀' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ = 𝟙 _ :=
  (X'.isoEMapFourδ₁Toδ₀' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ h).inv_hom_id

end

section

variable (h : IsZero ((X'.H n₀).obj (mk₁ (homOfLE hi₃₄))))

include h in
lemma isIso_EMapFourδ₄Toδ₃' :
    IsIso (X'.EMapFourδ₄Toδ₃' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄) := by
  apply X'.isIso_EMap_fourδ₄Toδ₃_of_isZero
  exact h

/-- isoEMapFourδ₄Toδ₃' -/
@[simps! hom]
noncomputable def isoEMapFourδ₄Toδ₃' :
    X'.E n₀ n₁ n₂ hn₁ hn₂ (homOfLE hi₀₁) (homOfLE hi₁₂) (homOfLE hi₂₃) ≅
      X'.E n₀ n₁ n₂ hn₁ hn₂ (homOfLE hi₀₁) (homOfLE hi₁₂) (homOfLE (hi₂₃.trans hi₃₄)) :=
  have := X'.isIso_EMapFourδ₄Toδ₃' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ h
  asIso (X'.EMapFourδ₄Toδ₃' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄)

@[reassoc (attr := simp)]
lemma isoEMapFourδ₄Toδ₄'_hom_inv_id :
    X'.EMapFourδ₄Toδ₃' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ ≫
    (X'.isoEMapFourδ₄Toδ₃' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ h).inv = 𝟙 _ :=
  (X'.isoEMapFourδ₄Toδ₃' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ h).hom_inv_id

@[reassoc (attr := simp)]
lemma isoEMapFourδ₄Toδ₄'_inv_hom_id :
    (X'.isoEMapFourδ₄Toδ₃' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ h).inv ≫
    X'.EMapFourδ₄Toδ₃' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ = 𝟙 _ :=
  (X'.isoEMapFourδ₄Toδ₃' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ h).inv_hom_id

end

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
    (i₀ i₁ i₂ i₃ i₄ i₅ : ι') (hi₀₁ : i₀ ≤ i₁)
    (hi₁₂ : i₁ ≤ i₂) (hi₂₃ : i₂ ≤ i₃) (hi₃₄ : i₃ ≤ i₄) (hi₄₅ : i₄ ≤ i₅)

/-- EMapFourδ₂Toδ₁' -/
noncomputable abbrev EMapFourδ₂Toδ₁' :=
  X'.EMap n₀ n₁ n₂ hn₁ hn₂ _ _ _ _ _ _ (fourδ₂Toδ₁' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄)

/-- isIso_EMapFourδ₂Toδ₁' -/
lemma isIso_EMapFourδ₂Toδ₁'
    (h₁ : IsIso ((X'.H n₁).map (twoδ₁Toδ₀' i₁ i₂ i₃ hi₁₂ hi₂₃)))
    (h₂ : IsIso ((X'.H n₂).map (twoδ₂Toδ₁' i₀ i₁ i₂ hi₀₁ hi₁₂))) :
    IsIso (X'.EMapFourδ₂Toδ₁' n₀ n₁ n₂ hn₁ hn₂ i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄) := by
  apply X'.isIso_EMap
  · dsimp
    erw [Functor.map_id]
    infer_instance
  · exact h₁
  · exact h₂

end

end

end SpectralObject

end Abelian

end CategoryTheory
