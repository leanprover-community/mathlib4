/-
Copyright (c) 2026 Joël Riou. All rights reserved.
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

variable
  {i₀' i₀ i₁ i₂ i₃ i₃' : ι} (f₁ : i₀ ⟶ i₁)
  (f₁' : i₀' ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃) (f₃' : i₂ ⟶ i₃')
  (n₀ n₁ n₂ n₃ : ℤ)


lemma epi_EMap (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁ f₂ f₃') (n₀ n₁ n₂ n₃ : ℤ)
    (hα₀ : α.app 0 = 𝟙 _ := by cat_disch) (hα₁ : α.app 1 = 𝟙 _ := by cat_disch)
    (hα₂ : α.app 2 = 𝟙 _ := by cat_disch)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    Epi (X.EMap f₁ f₂ f₃ f₁ f₂ f₃' α n₀ n₁ n₂ hn₁ hn₂) := by
  have := X.πE_EMap  _ _ _ _ _ _ α (𝟙 _) n₀ n₁ n₂
  rw [cyclesMap_id, id_comp] at this
  exact epi_of_epi_fac this

lemma mono_EMap (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂ f₃) (n₀ n₁ n₂ n₃ : ℤ)
    (hα₁ : α.app 1 = 𝟙 _ := by cat_disch) (hα₂ : α.app 2 = 𝟙 _ := by cat_disch)
    (hα₃ : α.app 3 = 𝟙 _ := by cat_disch) (hn₁ : n₀ + 1 = n₁ := by lia)
    (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    Mono (X.EMap f₁ f₂ f₃ f₁' f₂ f₃ α n₀ n₁ n₂ hn₁ hn₂) := by
  have := X.EMap_ιE  _ _ _ _ _ _ α (𝟙 _) n₀ n₁ n₂
  rw [opcyclesMap_id, comp_id] at this
  exact mono_of_mono_fac this

end

section

variable {i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (f₃₄ : i₂ ⟶ i₄) (h₃₄ : f₃ ≫ f₄ = f₃₄)
  (n₀ n₁ n₂ n₃ : ℤ)

@[reassoc (attr := simp)]
lemma d_EMap_fourδ₄Toδ₃ (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫
      X.EMap f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) n₁ n₂ n₃ hn₂ hn₃ = 0 := by
  rw [← cancel_epi (X.πE f₃ f₄ f₅ n₀ n₁ n₂),
    ← cancel_epi (X.toCycles f₃ f₄ f₃₄ h₃₄ n₁), comp_zero, comp_zero,
    X.toCycles_πE_d_assoc f₁ f₂ f₃ f₄ f₅ _ rfl f₃₄ h₃₄ n₀ n₁ n₂ n₃,
    X.πE_EMap f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) (𝟙 _) n₁ n₂ n₃,
    cyclesMap_id, Category.id_comp, δ_toCycles_assoc _ _ _ _ _ _ _ _, δToCycles_πE _ _ _ _ _ _ _]

instance (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃) :
    Epi (X.EMap f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) n₁ n₂ n₃ hn₂ hn₃) :=
  X.epi_EMap _ _ _ _ _ _ _ _ _ rfl rfl rfl hn₂ hn₃ rfl

lemma isIso_EMap_fourδ₄Toδ₃ (h : (X.H n₁).map (twoδ₁Toδ₀ f₃ f₄ f₃₄ h₃₄) = 0 := by cat_disch)
    (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    IsIso (X.EMap f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) n₁ n₂ n₃ hn₂ hn₃ ) := by
  apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
  · exact (X.exact₂ f₃ f₄ f₃₄ h₃₄ _).epi_f h
  · dsimp
    convert inferInstanceAs (IsIso ((X.H n₂).map (𝟙 _)))
    cat_disch
  · dsimp
    convert inferInstanceAs (Mono ((X.H n₃).map (𝟙 (mk₁ f₁))))
    cat_disch

lemma isIso_EMap_fourδ₄Toδ₃_of_isZero (h : IsZero ((X.H n₁).obj (mk₁ f₄)) := by cat_disch)
    (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    IsIso (X.EMap f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) n₁ n₂ n₃ hn₂ hn₃) :=
  X.isIso_EMap_fourδ₄Toδ₃ _ _ _ _ _ _ _ _ _ (h.eq_of_tgt _ _)

@[reassoc (attr := simp)]
lemma EMap_fourδ₁Toδ₀_d (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.EMap f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) n₀ n₁ n₂ hn₁ hn₂ ≫
      X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ = 0 := by
  rw [← cancel_mono (X.ιE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃),
    ← cancel_mono (X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₂ ), zero_comp, zero_comp, assoc,
    assoc, X.d_ιE_fromOpcycles f₁ f₂ f₃ f₄ f₅ f₂₃ h₂₃ _ rfl _ rfl n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃]
  rw [X.EMap_ιE_assoc f₂₃ f₄ f₅ f₃ f₄ f₅
    (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) (𝟙 _) n₀ n₁ n₂ (by ext <;> simp <;> rfl) hn₁ hn₂ ,
    opcyclesMap_id, fromOpcyles_δ _ _ _ _ _ _ _ _, id_comp, ιE_δFromOpcycles _ _ _ _ _ _ _]

instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Mono (X.EMap f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) n₀ n₁ n₂ hn₁ hn₂) :=
  X.mono_EMap _ _ _ _ _ _ _ _ _ rfl rfl rfl _ _ rfl

lemma isIso_EMap_fourδ₁Toδ₀ (h : (X.H n₂).map (twoδ₂Toδ₁ f₂ f₃ f₂₃ h₂₃) = 0 := by cat_disch)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X.EMap f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) n₀ n₁ n₂ hn₁ hn₂) := by
  apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
  · dsimp
    convert inferInstanceAs (Epi ((X.H n₀).map (𝟙 _)))
    cat_disch
  · dsimp
    convert inferInstanceAs (IsIso ((X.H n₁).map (𝟙 _)))
    cat_disch
  · exact (X.exact₂ f₂ f₃ f₂₃ h₂₃ n₂).mono_g h

lemma isIso_EMap_fourδ₁Toδ₀_of_isZero (h : IsZero ((X.H n₂).obj (mk₁ f₂)))
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X.EMap f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) n₀ n₁ n₂ hn₁ hn₂) :=
  X.isIso_EMap_fourδ₁Toδ₀ _ _ _ _ _ _ _ _ _ (h.eq_of_src _ _) _ _

end

section

variable (i₀ i₁ i₂ i₃ i₄ i₅ : ι') (hi₀₁ : i₀ ≤ i₁)
  (hi₁₂ : i₁ ≤ i₂) (hi₂₃ : i₂ ≤ i₃) (hi₃₄ : i₃ ≤ i₄) (hi₄₅ : i₄ ≤ i₅)

/-- EMapFourδ₁Toδ₀' -/
noncomputable abbrev EMapFourδ₁Toδ₀' (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :=
  X'.EMap _ _ _ _ _ _ (fourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄) n₀ n₁ n₂ hn₁ hn₂


/-- EMapFourδ₄Toδ₃' -/
noncomputable abbrev EMapFourδ₄Toδ₃' (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :=
  X'.EMap _ _ _ _ _ _ (fourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄) n₀ n₁ n₂ hn₁ hn₂

@[reassoc]
lemma EMapFourδ₁Toδ₀'_comp (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
  X'.EMapFourδ₁Toδ₀' i₀ i₁ i₃ i₄ i₅ hi₀₁ (hi₁₂.trans hi₂₃) hi₃₄ hi₄₅ n₀ n₁ n₂ hn₁ hn₂ ≫
    X'.EMapFourδ₁Toδ₀' i₁ i₂ i₃ i₄ i₅ hi₁₂ hi₂₃ hi₃₄ hi₄₅ n₀ n₁ n₂ hn₁ hn₂ =
    X'.EMapFourδ₁Toδ₀' i₀ i₂ i₃ i₄ i₅ (hi₀₁.trans hi₁₂) hi₂₃ hi₃₄ hi₄₅ n₀ n₁ n₂ hn₁ hn₂ := by
  symm
  apply EMap_comp

@[reassoc]
lemma EMapFourδ₄Toδ₃'_comp (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
  X'.EMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂ ≫
    X'.EMapFourδ₄Toδ₃' i₀ i₁ i₂ i₄ i₅ hi₀₁ hi₁₂ (hi₂₃.trans hi₃₄) hi₄₅ n₀ n₁ n₂ hn₁ hn₂ =
    X'.EMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₅ hi₀₁ hi₁₂ hi₂₃ (hi₃₄.trans hi₄₅) n₀ n₁ n₂ hn₁ hn₂ := by
  symm
  apply EMap_comp

@[reassoc]
lemma EMapFourδ₁Toδ₀'_EMapFourδ₃Toδ₃' (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.EMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂ ≫
      X'.EMapFourδ₄Toδ₃' i₁ i₂ i₃ i₄ i₅ hi₁₂ hi₂₃ hi₃₄ hi₄₅ n₀ n₁ n₂ hn₁ hn₂ =
      X'.EMapFourδ₄Toδ₃' i₀ i₂ i₃ i₄ i₅ _ _ _ hi₄₅ n₀ n₁ n₂ hn₁ hn₂ ≫
        X'.EMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₅ hi₀₁ _ _ _ n₀ n₁ n₂ hn₁ hn₂ := by
  dsimp [EMapFourδ₁Toδ₀', EMapFourδ₄Toδ₃']
  rw [← EMap_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    ← EMap_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]
  rfl

section

variable (n₀ n₁ n₂ : ℤ) (h : IsZero ((X'.H n₂).obj (mk₁ (homOfLE hi₀₁))))

include h in
lemma isIso_EMapFourδ₁Toδ₀' (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X'.EMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂) :=
  X'.isIso_EMap_fourδ₁Toδ₀_of_isZero _ _ _ _ _ _ _ _ _ h

/-- isoEMapFourδ₁Toδ₀' -/
@[simps! hom]
noncomputable def isoEMapFourδ₁Toδ₀' (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.E (homOfLE (hi₀₁.trans hi₁₂)) (homOfLE hi₂₃) (homOfLE hi₃₄) n₀ n₁ n₂ hn₁ hn₂ ≅
      X'.E (homOfLE hi₁₂) (homOfLE hi₂₃) (homOfLE hi₃₄) n₀ n₁ n₂ hn₁ hn₂ :=
  have := X'.isIso_EMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂
  asIso (X'.EMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂)

@[reassoc (attr := simp)]
lemma isoEMapFourδ₁Toδ₀'_hom_inv_id (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.EMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂ ≫
    (X'.isoEMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv = 𝟙 _ :=
  (X'.isoEMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).hom_inv_id

@[reassoc (attr := simp)]
lemma isoEMapFourδ₁Toδ₀'_inv_hom_id (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X'.isoEMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv ≫
    X'.EMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂ = 𝟙 _ :=
  (X'.isoEMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv_hom_id

end

section

variable (n₀ n₁ n₂ : ℤ) (h : IsZero ((X'.H n₀).obj (mk₁ (homOfLE hi₃₄))))

include h in
lemma isIso_EMapFourδ₄Toδ₃' (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X'.EMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂) :=
  X'.isIso_EMap_fourδ₄Toδ₃_of_isZero _ _ _ _ _ _ _ _ _ h _ _

/-- isoEMapFourδ₄Toδ₃' -/
@[simps! hom]
noncomputable def isoEMapFourδ₄Toδ₃' (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.E (homOfLE hi₀₁) (homOfLE hi₁₂) (homOfLE hi₂₃) n₀ n₁ n₂ hn₁ hn₂ ≅
      X'.E (homOfLE hi₀₁) (homOfLE hi₁₂) (homOfLE (hi₂₃.trans hi₃₄)) n₀ n₁ n₂ hn₁ hn₂ :=
  have := X'.isIso_EMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂
  asIso (X'.EMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂)

@[reassoc (attr := simp)]
lemma isoEMapFourδ₄Toδ₄'_hom_inv_id (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.EMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂ ≫
    (X'.isoEMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv = 𝟙 _ :=
  (X'.isoEMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).hom_inv_id

@[reassoc (attr := simp)]
lemma isoEMapFourδ₄Toδ₄'_inv_hom_id (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X'.isoEMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv ≫
    X'.EMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂ = 𝟙 _ :=
  (X'.isoEMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv_hom_id

end

section

variable (i₀ i₁ i₂ i₃ i₄ i₅ : ι') (hi₀₁ : i₀ ≤ i₁)
  (hi₁₂ : i₁ ≤ i₂) (hi₂₃ : i₂ ≤ i₃) (hi₃₄ : i₃ ≤ i₄) (hi₄₅ : i₄ ≤ i₅)

/-- EMapFourδ₂Toδ₁' -/
noncomputable abbrev EMapFourδ₂Toδ₁' (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :=
  X'.EMap _ _ _ _ _ _ (fourδ₂Toδ₁' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄) n₀ n₁ n₂ hn₁ hn₂

/-- isIso_EMapFourδ₂Toδ₁' -/
lemma isIso_EMapFourδ₂Toδ₁' (n₀ n₁ n₂ : ℤ)
    (h₁ : IsIso ((X'.H n₁).map (twoδ₁Toδ₀' i₁ i₂ i₃ hi₁₂ hi₂₃)))
    (h₂ : IsIso ((X'.H n₂).map (twoδ₂Toδ₁' i₀ i₁ i₂ hi₀₁ hi₁₂)))
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X'.EMapFourδ₂Toδ₁' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂) :=
  X'.isIso_EMap _ _ _ _ _ _ _ _ _ _
    (by exact (inferInstanceAs (IsIso ((X'.H n₀).map (𝟙 _))))) h₁ h₂

end

end

end SpectralObject

end Abelian

end CategoryTheory
