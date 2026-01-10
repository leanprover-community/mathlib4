/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Page
public import Mathlib.CategoryTheory.ComposableArrows.Three

/-!
# Differentials of a spectral object

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

variable {C ι : Type*} [Category C] [Category ι] [Abelian C]

open Category ComposableArrows Limits Preadditive

namespace Abelian

namespace SpectralObject

variable (X : SpectralObject C ι)

section

variable (n₀ n₁ n₂ n₃ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃)
  {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (f₁₂ : i₀ ⟶ i₂) (h₁₂ : f₁ ≫ f₂ = f₁₂)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (f₃₄ : i₂ ⟶ i₄) (h₃₄ : f₃ ≫ f₄ = f₃₄)
  (f₄₅ : i₃ ⟶ i₅) (h₄₅ : f₄ ≫ f₅ = f₄₅)

noncomputable def d : X.E n₀ n₁ n₂ hn₁ hn₂ f₃ f₄ f₅ ⟶ X.E n₁ n₂ n₃ hn₂ hn₃ f₁ f₂ f₃ :=
  X.descE n₀ n₁ n₂ hn₁ hn₂ f₃ f₄ f₅ _ rfl (X.δ n₁ n₂ hn₂ (f₁ ≫ f₂) (f₃ ≫ f₄) ≫
    X.toCycles n₂ n₃ hn₃ f₁ f₂ _ rfl ≫ X.πE n₁ n₂ n₃ hn₂ hn₃ f₁ f₂ f₃) (by
      rw [X.δ_naturality_assoc n₁ n₂ hn₂ (f₁ ≫ f₂) f₃ (f₁ ≫ f₂) (f₃ ≫ f₄)
        (𝟙 _) (twoδ₂Toδ₁ f₃ f₄  _ rfl) rfl, Functor.map_id, id_comp,
        δ_toCycles_assoc, δToCycles_πE]) (by rw [δ_δ_assoc, zero_comp])

@[reassoc]
lemma toCycles_πE_d :
    X.toCycles n₁ n₂ hn₂ f₃ f₄ f₃₄ h₃₄ ≫ X.πE n₀ n₁ n₂ hn₁ hn₂ f₃ f₄ f₅ ≫
      X.d n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ =
        X.δ n₁ n₂ hn₂ f₁₂ f₃₄ ≫ X.toCycles n₂ n₃ hn₃ f₁ f₂ f₁₂ h₁₂ ≫
          X.πE n₁ n₂ n₃ hn₂ hn₃ f₁ f₂ f₃ := by
  subst h₁₂ h₃₄
  simp only [d, δ_toCycles_assoc, toCycles_πE_descE]

include h₃₄ in
@[reassoc]
lemma d_ιE_fromOpcycles :
    X.d n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ ≫ X.ιE n₁ n₂ n₃ hn₂ hn₃ f₁ f₂ f₃ ≫
      X.fromOpcycles n₁ n₂ hn₂ f₂ f₃ f₂₃ h₂₃ =
      X.ιE n₀ n₁ n₂ hn₁ hn₂ f₃ f₄ f₅ ≫ X.fromOpcycles n₀ n₁ hn₁ f₄ f₅ f₄₅ h₄₅ ≫
        X.δ n₁ n₂ hn₂ f₂₃ f₄₅ := by
  rw [← cancel_epi (X.πE n₀ n₁ n₂ hn₁ hn₂ f₃ f₄ f₅),
    ← cancel_epi (X.toCycles n₁ n₂ hn₂ f₃ f₄ f₃₄ h₃₄),
    X.toCycles_πE_d_assoc n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ _ rfl]
  rw [πE_ιE_assoc, p_fromOpcycles, toCycles_i_assoc, fromOpcyles_δ,
    πE_ιE_assoc, pOpcycles_δFromOpcycles, toCycles_i_assoc, ← Functor.map_comp]
  symm
  apply δ_naturality
  simp

end

section

variable (n₀ n₁ n₂ n₃ n₄ : ℤ)
  (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃) (hn₄ : n₃ + 1 = n₄)
  {i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (f₆ : i₅ ⟶ i₆) (f₇ : i₆ ⟶ i₇)

@[reassoc (attr := simp)]
lemma d_d :
    X.d n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₃ f₄ f₅ f₆ f₇ ≫
      X.d n₁ n₂ n₃ n₄ hn₂ hn₃ hn₄ f₁ f₂ f₃ f₄ f₅ = 0 := by
  rw [← cancel_epi (X.πE n₀ n₁ n₂ hn₁ hn₂ f₅ f₆ f₇),
    ← cancel_epi (X.toCycles n₁ n₂ hn₂ f₅ f₆ _ rfl),
    comp_zero, comp_zero,
    X.toCycles_πE_d_assoc n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₃ f₄ f₅ f₆ f₇ _ rfl _ rfl,
    X.toCycles_πE_d n₁ n₂ n₃ n₄ hn₂ hn₃ hn₄ f₁ f₂ f₃ f₄ f₅ _ rfl _ rfl,
    δ_δ_assoc, zero_comp]

end

section

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)
  {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)

/-- When `f₁`, `f₂` and `f₃` are composable morphisms, this is the canonical
morphism `Z^n(f₂, f₃) ⟶ opZ^{n+1}(f₁, f₂)` that is induced both
by `δ : H^n(f₂ ≫ f₃) ⟶ H^{n+1}(f₁)` (see `toCycles_Ψ`) and
by `δ : H^n(f₃) ⟶ H^{n+1}(f₁ ≫ f₂)` (see `Ψ_fromOpcycles`). -/
noncomputable def Ψ : X.cycles n₀ n₁ hn₁ f₂ f₃ ⟶ X.opcycles n₀ n₁ hn₁ f₁ f₂ :=
  X.descCycles n₀ n₁ hn₁ f₂ f₃ _ rfl
    (X.δ n₀ n₁ hn₁ f₁ (f₂ ≫ f₃) ≫ X.pOpcycles n₀ n₁ hn₁ f₁ f₂) (by
      rw [X.δ_naturality_assoc n₀ n₁ hn₁ f₁ f₂ f₁ (f₂ ≫ f₃) (𝟙 _) (twoδ₂Toδ₁ f₂ f₃ _ rfl) rfl,
        Functor.map_id, id_comp, δ_pOpcycles])

@[reassoc (attr := simp)]
lemma toCycles_Ψ :
    X.toCycles n₀ n₁ hn₁ f₂ f₃ f₂₃ h₂₃ ≫ X.Ψ n₀ n₁ hn₁ f₁ f₂ f₃ =
      X.δ n₀ n₁ hn₁ f₁ f₂₃ ≫ X.pOpcycles n₀ n₁ hn₁ f₁ f₂ := by
  subst h₂₃
  simp only [Ψ, toCycles_descCycles]

@[reassoc (attr := simp)]
lemma Ψ_fromOpcycles :
    X.Ψ n₀ n₁ hn₁ f₁ f₂ f₃ ≫ X.fromOpcycles n₀ n₁ hn₁ f₁ f₂ f₁₂ h₁₂ =
      X.iCycles n₀ n₁ hn₁ f₂ f₃ ≫ X.δ n₀ n₁ hn₁ f₁₂ f₃ := by
  rw [← cancel_epi (X.toCycles n₀ n₁ hn₁ f₂ f₃ _ rfl),
    toCycles_Ψ_assoc, p_fromOpcycles, toCycles_i_assoc]
  exact (X.δ_naturality _ _ _ _ _ _ _ _ _ rfl).symm

include h₂₃ in
lemma cyclesMap_Ψ :
    X.cyclesMap n₀ n₁ hn₁ _ _ _ _ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂) ≫
      X.Ψ n₀ n₁ hn₁ f₁ f₂ f₃ = 0 := by
  rw [← cancel_epi (X.toCycles n₀ n₁ hn₁ f₁₂ f₃ (f₁ ≫ f₂ ≫ f₃)
    (by rw [reassoc_of% h₁₂])), comp_zero,
    X.toCycles_cyclesMap_assoc n₀ n₁ hn₁ f₁₂ f₃ f₂ f₃ (f₁ ≫ f₂ ≫ f₃)
    (by rw [reassoc_of% h₁₂]) f₂₃ h₂₃ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂)
    (twoδ₁Toδ₀ f₁ f₂₃ (f₁ ≫ f₂ ≫ f₃) (by rw [h₂₃])) rfl rfl,
    toCycles_Ψ, zero₃_assoc, zero_comp]

include h₁₂ in
lemma Ψ_opcyclesMap :
    X.Ψ n₀ n₁ hn₁ f₁ f₂ f₃ ≫
      X.opcyclesMap n₀ n₁ hn₁ _ _ _ _ (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃) = 0 := by
  rw [← cancel_mono (X.fromOpcycles n₀ n₁ hn₁ f₁ f₂₃ (f₁ ≫ f₂ ≫ f₃) (by rw [h₂₃])),
    zero_comp, assoc, X.opcyclesMap_fromOpcycles n₀ n₁ hn₁ f₁ f₂ f₁ f₂₃ f₁₂ h₁₂
    (f₁ ≫ f₂ ≫ f₃) (by rw [h₂₃]) (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃)
    (twoδ₂Toδ₁ f₁₂ f₃ (f₁ ≫ f₂ ≫ f₃) (by rw [reassoc_of% h₁₂])) rfl rfl,
    Ψ_fromOpcycles_assoc, zero₁, comp_zero]

/-- When `f₁`, `f₂` and `f₃` are composable morphisms, this is the exact sequence
`Z^n(f₁ ≫ f₂, f₃) ⟶ Z^n(f₂, f₃) ⟶ opZ^{n+1}(f₁, f₂) ⟶ opZ^{n+1}(f₁, f₂ ≫ f₃)`. -/
noncomputable def sequenceΨ : ComposableArrows C 3 :=
  mk₃ (X.cyclesMap n₀ n₁ hn₁ _ _ _ _ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂))
    (X.Ψ n₀ n₁ hn₁ f₁ f₂ f₃)
    (X.opcyclesMap n₀ n₁ hn₁ _ _ _ _ (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃))

lemma cyclesMap_Ψ_exact :
    (ShortComplex.mk _ _ (X.cyclesMap_Ψ n₀ n₁ hn₁ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃)).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A z hz
  refine ⟨A, 𝟙 _, inferInstance,
    X.liftCycles n₀ n₁ hn₁ f₁₂ f₃ (z ≫ X.iCycles n₀ n₁ hn₁ f₂ f₃) ?_, ?_⟩
  · dsimp
    rw [assoc, ← X.Ψ_fromOpcycles n₀ n₁ hn₁ f₁ f₂ f₃ f₁₂ h₁₂ , reassoc_of% hz, zero_comp]
  · dsimp
    rw [← cancel_mono (X.iCycles n₀ n₁ hn₁ f₂ f₃), id_comp, assoc,
      X.cyclesMap_i n₀ n₁ hn₁ _ _ _ _ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂) (𝟙 _) (by cat_disch),
     Functor.map_id, comp_id, liftCycles_i]

lemma Ψ_opcyclesMap_exact :
    (ShortComplex.mk _ _ (X.Ψ_opcyclesMap n₀ n₁ hn₁ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃)).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A z₀ hz₀
  dsimp at z₀ hz₀
  obtain ⟨A₁, π₁, _, z₁, hz₁⟩ :=
    surjective_up_to_refinements_of_epi (X.pOpcycles n₀ n₁ hn₁ f₁ f₂) z₀
  obtain ⟨A₂, π₂, _, z₂, hz₂⟩ :=
      (X.cokernelSequenceOpcycles_exact n₀ n₁ hn₁ f₁ f₂₃).exact_up_to_refinements z₁ (by
    dsimp
    have H := X.p_opcyclesMap n₀ n₁ hn₁ f₁ f₂ f₁ f₂₃
      (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃) (𝟙 _) (by cat_disch)
    rw [Functor.map_id, id_comp] at H
    rw [← H, ← reassoc_of% hz₁, hz₀, comp_zero])
  dsimp at z₂ hz₂
  refine ⟨A₂, π₂ ≫ π₁, epi_comp _ _, z₂ ≫ X.toCycles n₀ n₁ hn₁ f₂ f₃ f₂₃ h₂₃, ?_⟩
  dsimp
  rw [← cancel_mono (X.fromOpcycles n₀ n₁ hn₁ f₁ f₂ f₁₂ h₁₂), assoc, assoc,
    assoc, assoc, toCycles_Ψ_assoc, p_fromOpcycles, ← reassoc_of% hz₂,
    reassoc_of% hz₁, p_fromOpcycles]

lemma sequenceΨ_exact :
    (X.sequenceΨ n₀ n₁ hn₁ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃).Exact :=
  exact_of_δ₀
    (X.cyclesMap_Ψ_exact n₀ n₁ hn₁ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃).exact_toComposableArrows
    (X.Ψ_opcyclesMap_exact n₀ n₁ hn₁ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃).exact_toComposableArrows

end


section

variable (n₀ n₁ n₂ n₃ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃)
  {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)

@[reassoc (attr := simp)]
lemma πE_d_ιE :
    X.πE n₀ n₁ n₂ hn₁ hn₂ f₃ f₄ f₅ ≫ X.d n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ ≫
      X.ιE n₁ n₂ n₃ hn₂ hn₃ f₁ f₂ f₃ = X.Ψ n₁ n₂ hn₂ f₂ f₃ f₄ := by
  rw [← cancel_epi (X.toCycles n₁ n₂ hn₂ f₃ f₄ _ rfl), toCycles_Ψ,
    X.toCycles_πE_d_assoc n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ _ rfl,
    πE_ιE, toCycles_i_assoc, ← X.δ_naturality_assoc n₁ n₂ hn₂ (f₁ ≫ f₂) (f₃ ≫ f₄) f₂ (f₃ ≫ f₄)
      (twoδ₁Toδ₀ f₁ f₂ _ rfl) (𝟙 _) rfl, Functor.map_id, id_comp]

end

section

variable (n₀ n₁ n₂ n₃ : ℤ)
  (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃)
  {i₀ i₁ i₂ : ι}
  (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂)

@[reassoc (attr := simp)]
lemma πE_EIsoH_hom :
    X.πE n₀ n₁ n₂ hn₁ hn₂ (𝟙 i₀) f₁ (𝟙 i₁) ≫ (X.EIsoH n₀ n₁ n₂ hn₁ hn₂ f₁).hom =
      (X.cyclesIsoH n₁ n₂ hn₂ f₁).hom := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  simp [πE, cyclesIsoH, EIsoH]

@[reassoc]
lemma d_EIsoH_hom :
    X.d n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ (𝟙 i₀) f₁ (𝟙 i₁) f₂ (𝟙 i₂) ≫
      (X.EIsoH n₁ n₂ n₃ hn₂ hn₃ f₁).hom =
    (X.EIsoH n₀ n₁ n₂ hn₁ hn₂ f₂).hom ≫ X.δ n₁ n₂ hn₂ f₁ f₂ := by
  rw [← cancel_epi (X.πE n₀ n₁ n₂ hn₁ hn₂ (𝟙 i₁) f₂ (𝟙 i₂)),
    ← cancel_epi (X.toCycles n₁ n₂ hn₂ (𝟙 i₁) f₂ f₂ (by simp)),
    X.toCycles_πE_d_assoc n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ (𝟙 i₀) f₁ (𝟙 i₁) f₂ (𝟙 i₂) f₁ (by simp),
    πE_EIsoH_hom, πE_EIsoH_hom_assoc, cyclesIsoH_inv_hom_id, comp_id,
    cyclesIsoH_inv_hom_id_assoc]

end

end SpectralObject

end Abelian

end CategoryTheory
