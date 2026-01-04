/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Page
public import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# Differentials of a spectral object

-/

@[expose] public section

namespace CategoryTheory

variable {C ι : Type*} [Category C] [Category ι] [Abelian C]

open Category ComposableArrows Limits Preadditive

namespace Abelian

namespace SpectralObject

variable (X : SpectralObject C ι)

section

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)
  {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)

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

noncomputable def sequenceΨ : ComposableArrows C 3 :=
  mk₃ (X.cyclesMap n₀ n₁ hn₁ _ _ _ _ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂))
    (X.Ψ n₀ n₁ hn₁ f₁ f₂ f₃)
    (X.opcyclesMap n₀ n₁ hn₁ _ _ _ _ (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃))

lemma cyclesMap_Ψ_exact :
    (ShortComplex.mk _ _ (X.cyclesMap_Ψ n₀ n₁ hn₁ f₁ f₂ f₃ f₁₂ h₁₂ f₂₃ h₂₃)).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A z hz
  dsimp at z hz
  refine ⟨A, 𝟙 _, inferInstance,
    X.liftCycles n₀ n₁ hn₁ f₁₂ f₃ (z ≫ X.iCycles n₀ n₁ hn₁ f₂ f₃) ?_, ?_⟩
  · dsimp
    rw [assoc, ← X.Ψ_fromOpcycles n₀ n₁ hn₁ f₁ f₂ f₃ f₁₂ h₁₂ , reassoc_of% hz, zero_comp]
  · dsimp
    rw [← cancel_mono (X.iCycles n₀ n₁ hn₁ f₂ f₃), id_comp, assoc,
      X.cyclesMap_i n₀ n₁ hn₁ _ _ _ _ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂) (𝟙 _) (by aesop_cat),
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
      (threeδ₃Toδ₂ f₁ f₂ f₃ f₂₃ h₂₃) (𝟙 _) (by aesop_cat)
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

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  {i j k l : ι} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂) (f₂₃ : j ⟶ l) (h₂₃ : f₂ ≫ f₃ = f₂₃)

noncomputable def δToCycles : (X.H n₀).obj (mk₁ f₃) ⟶ X.cycles n₁ n₂ hn₂ f₁ f₂ :=
  X.liftCycles n₁ n₂ hn₂ f₁ f₂ (X.δ n₀ n₁ hn₁ f₂ f₃) (by simp)

@[reassoc (attr := simp)]
lemma δToCycles_iCycles :
    X.δToCycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫ X.iCycles n₁ n₂ hn₂ f₁ f₂ =
      X.δ n₀ n₁ hn₁ f₂ f₃ := by
  simp only [δToCycles, liftCycles_i]

@[reassoc (attr := simp)]
lemma δ_toCycles :
    X.δ n₀ n₁ hn₁ f₁₂ f₃ ≫ X.toCycles n₁ n₂ hn₂ f₁ f₂ f₁₂ h₁₂ =
      X.δToCycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ := by
  rw [← cancel_mono (X.iCycles n₁ n₂ hn₂ f₁ f₂), assoc,
    toCycles_i, δToCycles_iCycles,
    ← X.δ_naturality n₀ n₁ hn₁ f₁₂ f₃ f₂ f₃ (twoδ₁Toδ₀ f₁ f₂ f₁₂ h₁₂) (𝟙 _) rfl,
    Functor.map_id, id_comp]

noncomputable def δFromOpcycles : X.opcycles n₀ n₁ hn₁ f₂ f₃ ⟶ (X.H n₂).obj (mk₁ f₁) :=
  X.descOpcycles n₀ n₁ hn₁ f₂ f₃ (X.δ n₁ n₂ hn₂ f₁ f₂) (by simp)

@[reassoc (attr := simp)]
lemma pOpcycles_δFromOpcycles :
    X.pOpcycles n₀ n₁ hn₁ f₂ f₃ ≫ X.δFromOpcycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ =
      X.δ n₁ n₂ hn₂ f₁ f₂ := by
  simp only [δFromOpcycles, p_descOpcycles]

@[reassoc (attr := simp)]
lemma fromOpcyles_δ :
    X.fromOpcycles n₀ n₁ hn₁ f₂ f₃ f₂₃ h₂₃ ≫ X.δ n₁ n₂ hn₂ f₁ f₂₃ =
      X.δFromOpcycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ := by
  rw [← cancel_epi (X.pOpcycles n₀ n₁ hn₁ f₂ f₃),
    p_fromOpcycles_assoc, pOpcycles_δFromOpcycles,
    X.δ_naturality n₁ n₂ hn₂ f₁ f₂ f₁ f₂₃ (𝟙 _) (twoδ₂Toδ₁ f₂ f₃ f₂₃ h₂₃) rfl,
    Functor.map_id, comp_id]

@[simps]
noncomputable def leftHomologyDataShortComplexE :
    (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).LeftHomologyData where
  K := X.cycles n₁ n₂ hn₂ f₁ f₂
  H := cokernel (X.δToCycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃)
  i := X.iCycles n₁ n₂ hn₂ f₁ f₂
  π := cokernel.π _
  wi := by simp
  hi := kernelIsKernel _
  wπ := cokernel.condition _
  hπ := cokernelIsCokernel _

@[simp]
lemma leftHomologyDataShortComplexE_f' :
    (X.leftHomologyDataShortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).f' =
      X.δToCycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ := rfl

noncomputable def cyclesIso :
    (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).cycles ≅ X.cycles n₁ n₂ hn₂ f₁ f₂ :=
  (X.leftHomologyDataShortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).cyclesIso

@[reassoc (attr := simp)]
lemma cyclesIso_inv_i :
    (X.cyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).inv ≫
      (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).iCycles = X.iCycles n₁ n₂ hn₂ f₁ f₂ :=
  ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles _

@[reassoc (attr := simp)]
lemma cyclesIso_hom_i :
    (X.cyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).hom ≫ X.iCycles n₁ n₂ hn₂ f₁ f₂ =
      (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).iCycles :=
  ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i _

noncomputable def πE : X.cycles n₁ n₂ hn₂ f₁ f₂ ⟶ X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ :=
    (X.cyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).inv ≫
      (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).homologyπ

instance : Epi (X.πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃) := by
  dsimp [πE]
  apply epi_comp

@[reassoc (attr := simp)]
lemma δToCycles_cyclesIso_inv :
    X.δToCycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫ (X.cyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).inv =
      (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).toCycles := by
  -- this could be a general lemma for LeftHomologyData
  rw [← cancel_mono (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).iCycles, assoc,
    cyclesIso_inv_i, δToCycles_iCycles, ShortComplex.toCycles_i, shortComplexE_f]

@[reassoc (attr := simp)]
lemma δToCycles_πE :
    X.δToCycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫ X.πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ = 0 := by
  simp only [πE, δToCycles_cyclesIso_inv_assoc, ShortComplex.toCycles_comp_homologyπ]

/-- cokernelSequenceE' -/
@[simps]
noncomputable def cokernelSequenceE' : ShortComplex C :=
    ShortComplex.mk _ _ (X.δToCycles_πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃)

@[simps!]
noncomputable def cokernelSequenceE'Iso :
    X.cokernelSequenceE' n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≅ ShortComplex.mk _ _
        (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).toCycles_comp_homologyπ :=
  ShortComplex.isoMk (Iso.refl _) (X.cyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).symm
    (Iso.refl _) (by simp) (by simp [πE])

lemma cokernelSequenceE'_exact :
    (X.cokernelSequenceE' n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).Exact :=
  ShortComplex.exact_of_iso (X.cokernelSequenceE'Iso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).symm
    (ShortComplex.exact_of_g_is_cokernel _ (ShortComplex.homologyIsCokernel _))

instance : Epi (X.cokernelSequenceE' n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).g := by
  dsimp
  infer_instance

@[simps]
noncomputable def rightHomologyDataShortComplexE :
    (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).RightHomologyData where
  Q := X.opcycles n₀ n₁ hn₁ f₂ f₃
  H := kernel (X.δFromOpcycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃)
  p := X.pOpcycles n₀ n₁ hn₁ f₂ f₃
  ι := kernel.ι _
  wp := by simp
  hp := cokernelIsCokernel _
  wι := kernel.condition _
  hι := kernelIsKernel _

/-- rightHomologyDataShortComplexE_g' -/
@[simp]
lemma rightHomologyDataShortComplexE_g' :
    (X.rightHomologyDataShortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).g' =
      X.δFromOpcycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ := rfl

noncomputable def opcyclesIso :
    (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).opcycles ≅ X.opcycles n₀ n₁ hn₁ f₂ f₃ :=
  (X.rightHomologyDataShortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).opcyclesIso

@[reassoc (attr := simp)]
lemma p_opcyclesIso_hom :
    (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).pOpcycles ≫
      (X.opcyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).hom =
      X.pOpcycles n₀ n₁ hn₁ f₂ f₃ :=
  ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso_hom _

@[reassoc (attr := simp)]
lemma p_opcyclesIso_inv :
    X.pOpcycles n₀ n₁ hn₁ f₂ f₃ ≫ (X.opcyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).inv =
      (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).pOpcycles :=
  (X.rightHomologyDataShortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).p_comp_opcyclesIso_inv

noncomputable def ιE : X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ⟶ X.opcycles n₀ n₁ hn₁ f₂ f₃ :=
    (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).homologyι ≫
      (X.opcyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).hom

instance : Mono (X.ιE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃) := by
  dsimp [ιE]
  infer_instance

@[reassoc (attr := simp)]
lemma opcyclesIso_hom_δFromOpcycles :
    (X.opcyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).hom ≫ X.δFromOpcycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ =
      (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).fromOpcycles := by
  -- this could be a general lemma for RightHomologyData
  rw [← cancel_epi (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).pOpcycles,
    p_opcyclesIso_hom_assoc, ShortComplex.p_fromOpcycles, shortComplexE_g,
    pOpcycles_δFromOpcycles]

@[reassoc (attr := simp)]
lemma ιE_δFromOpcycles :
    X.ιE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫ X.δFromOpcycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ = 0 := by
  simp only [ιE, assoc, opcyclesIso_hom_δFromOpcycles, ShortComplex.homologyι_comp_fromOpcycles]

@[reassoc (attr := simp)]
lemma πE_ιE :
    X.πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫ X.ιE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ =
      X.iCycles n₁ n₂ hn₂ f₁ f₂ ≫ X.pOpcycles n₀ n₁ hn₁ f₂ f₃ := by
  simp [πE, ιE]

/-- kernelSequenceE' -/
@[simps]
noncomputable def kernelSequenceE' : ShortComplex C :=
    ShortComplex.mk _ _ (X.ιE_δFromOpcycles n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃)

@[simps!]
noncomputable def kernelSequenceE'Iso :
    X.kernelSequenceE' n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≅ ShortComplex.mk _ _
        (X.shortComplexE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).homologyι_comp_fromOpcycles :=
  Iso.symm (ShortComplex.isoMk (Iso.refl _) (X.opcyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃)
    (Iso.refl _) (by simp [ιE]) (by simp))

lemma kernelSequenceE'_exact :
    (X.kernelSequenceE' n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).Exact :=
  ShortComplex.exact_of_iso (X.kernelSequenceE'Iso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).symm
    (ShortComplex.exact_of_f_is_kernel _ (ShortComplex.homologyIsKernel _))

instance : Mono (X.kernelSequenceE' n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).f := by
  dsimp
  infer_instance

@[simps]
noncomputable def cokernelSequenceE : ShortComplex C where
  X₁ := (X.H n₁).obj (mk₁ f₁) ⊞ (X.H n₀).obj (mk₁ f₃)
  X₂ := (X.H n₁).obj (mk₁ f₁₂)
  X₃ := X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃
  f := biprod.desc ((X.H n₁).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂)) (X.δ n₀ n₁ hn₁ f₁₂ f₃)
  g := X.toCycles n₁ n₂ hn₂ f₁ f₂ f₁₂ h₁₂ ≫ X.πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃
  zero := by ext <;> simp

instance : Epi (X.cokernelSequenceE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂).g := by
  dsimp
  apply epi_comp

lemma cokernelSequenceE_exact :
    (X.cokernelSequenceE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, y₁, hy₁⟩ :=
    (X.cokernelSequenceE'_exact n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).exact_up_to_refinements
      (x₂ ≫ X.toCycles n₁ n₂ hn₂ f₁ f₂ f₁₂ h₁₂) (by simpa using hx₂)
  dsimp at y₁ hy₁
  let z := π₁ ≫ x₂ - y₁ ≫ X.δ n₀ n₁ hn₁ f₁₂ f₃
  obtain ⟨A₂, π₂, _, x₁, hx₁⟩ := (X.exact₂ n₁ f₁ f₂ f₁₂ h₁₂).exact_up_to_refinements z (by
      have : z ≫ X.toCycles n₁ n₂ hn₂ f₁ f₂ f₁₂ h₁₂ = 0 := by simp [z, hy₁]
      simpa only [zero_comp, assoc, toCycles_i] using this =≫ X.iCycles n₁ n₂ hn₂ f₁ f₂)
  dsimp at x₁ hx₁
  exact ⟨A₂, π₂ ≫ π₁, epi_comp _ _, biprod.lift x₁ (π₂ ≫ y₁), by simp [z, ← hx₁]⟩

section

variable {A : C} (x : (X.H n₁).obj (mk₁ f₁₂) ⟶ A)
  (h : (X.H n₁).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂) ≫ x = 0)
  (h' : X.δ n₀ n₁ hn₁ f₁₂ f₃ ≫ x = 0)

noncomputable def descE :
    X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ⟶ A :=
  (X.cokernelSequenceE_exact n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂).desc x (by
    dsimp
    ext
    · simp [h]
    · simp [h'])

@[reassoc (attr := simp)]
lemma toCycles_πE_descE :
    X.toCycles n₁ n₂ hn₂ f₁ f₂ f₁₂ h₁₂ ≫ X.πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫
      X.descE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂ x h h' = x := by
  dsimp only [descE]
  rw [← assoc]
  apply (X.cokernelSequenceE_exact n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂).g_desc

end

@[simps]
noncomputable def kernelSequenceE : ShortComplex C where
  X₁ := X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃
  X₂ := (X.H n₁).obj (mk₁ f₂₃)
  X₃ := (X.H n₁).obj (mk₁ f₃) ⊞ (X.H n₂).obj (mk₁ f₁)
  f := X.ιE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫ X.fromOpcycles n₀ n₁ hn₁ f₂ f₃ f₂₃ h₂₃
  g := biprod.lift ((X.H n₁).map (twoδ₁Toδ₀ f₂ f₃ f₂₃ h₂₃)) (X.δ n₁ n₂ hn₂ f₁ f₂₃)
  zero := by ext <;> simp

instance : Mono (X.kernelSequenceE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₂₃ h₂₃).f := by
  dsimp
  infer_instance

lemma kernelSequenceE_exact :
    (X.kernelSequenceE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₂₃ h₂₃).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ :=
    (X.kernelSequenceE'_exact n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).exact_up_to_refinements
      (X.liftOpcycles n₀ n₁ hn₁ f₂ f₃ f₂₃ h₂₃ x₂ (by simpa using hx₂ =≫ biprod.fst)) (by
        dsimp
        rw [← X.fromOpcyles_δ n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₂₃ h₂₃,
          X.liftOpcycles_fromOpcycles_assoc ]
        simpa using hx₂ =≫ biprod.snd)
  dsimp at x₁ hx₁
  refine ⟨A₁, π₁, inferInstance, x₁, ?_⟩
  dsimp
  rw [← reassoc_of% hx₁, liftOpcycles_fromOpcycles]

section

variable {A : C} (x : A ⟶ (X.H n₁).obj (mk₁ f₂₃))
  (h : x ≫ (X.H n₁).map (twoδ₁Toδ₀ f₂ f₃ f₂₃ h₂₃) = 0)
  (h' : x ≫ X.δ n₁ n₂ hn₂ f₁ f₂₃ = 0)

noncomputable def liftE :
    A ⟶ X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ :=
  (X.kernelSequenceE_exact n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₂₃ h₂₃).lift x (by
    dsimp
    ext
    · simp [h]
    · simp [h'])

@[reassoc (attr := simp)]
lemma liftE_ιE_fromOpcycles :
    X.liftE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₂₃ h₂₃ x h h' ≫ X.ιE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫
      X.fromOpcycles n₀ n₁ hn₁ f₂ f₃ f₂₃ h₂₃ = x := by
  apply (X.kernelSequenceE_exact n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₂₃ h₂₃).lift_f

end

end

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

variable (n₀ n₁ n₂ : ℤ)
  (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  {i₀ i₁ : ι} (f : i₀ ⟶ i₁)

noncomputable def cyclesIsoH :
    X.cycles n₁ n₂ hn₂ (𝟙 i₀) f ≅ (X.H n₁).obj (mk₁ f) :=
  (X.cyclesIso n₀ n₁ n₂ hn₁ hn₂ (𝟙 i₀) f (𝟙 i₁)).symm ≪≫ X.cycles'IsoH n₀ n₁ n₂ hn₁ hn₂ f

@[simp]
lemma cyclesIsoH_inv :
    (X.cyclesIsoH n₀ n₁ n₂ hn₁ hn₂ f).inv = X.toCycles n₁ n₂ hn₂ (𝟙 _) f f (by simp) := by
  rw [← cancel_mono (X.iCycles n₁ n₂ hn₂ (𝟙 _) f ), toCycles_i]
  dsimp [cyclesIsoH]
  rw [assoc, cyclesIso_hom_i, cycles'IsoH_inv_iCycles, ← Functor.map_id]
  congr 1
  aesop_cat

@[reassoc (attr := simp)]
lemma cyclesIsoH_hom_inv_id :
    (X.cyclesIsoH n₀ n₁ n₂ hn₁ hn₂ f).hom ≫
      X.toCycles n₁ n₂ hn₂ (𝟙 _) f f (by simp) = 𝟙 _ := by
  simpa using (X.cyclesIsoH n₀ n₁ n₂ hn₁ hn₂ f).hom_inv_id

@[reassoc (attr := simp)]
lemma cyclesIsoH_inv_hom_id :
    X.toCycles n₁ n₂ hn₂ (𝟙 _) f f (by simp) ≫
      (X.cyclesIsoH n₀ n₁ n₂ hn₁ hn₂ f).hom = 𝟙 _ := by
  simpa using (X.cyclesIsoH n₀ n₁ n₂ hn₁ hn₂ f).inv_hom_id

end

section

variable (n₀ n₁ n₂ n₃ : ℤ)
  (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃)
  {i₀ i₁ i₂ : ι}
  (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂)

@[reassoc (attr := simp)]
lemma πE_EIsoH_hom :
    X.πE n₀ n₁ n₂ hn₁ hn₂ (𝟙 i₀) f₁ (𝟙 i₁) ≫ (X.EIsoH n₀ n₁ n₂ hn₁ hn₂ f₁).hom =
      (X.cyclesIsoH n₀ n₁ n₂ hn₁ hn₂ f₁).hom := by
  simp [πE, cyclesIsoH]

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

section

set_option backward.proofsInPublic true

variable (n₀ n₁ n₂ : ℤ)
  (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  {i₀ i₁ i₂ i₃ : ι}
  (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  {i₀' i₁' i₂' i₃' : ι}
  (f₁' : i₀' ⟶ i₁') (f₂' : i₁' ⟶ i₂') (f₃' : i₂' ⟶ i₃')
  (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃')


@[reassoc]
lemma cyclesIso_inv_cyclesMap
    (β : mk₂ f₁ f₂ ⟶ mk₂ f₁' f₂')
    (hβ : β = homMk₂ (α.app 0) (α.app 1) (α.app 2) (naturality' α 0 1 (by lia) (by lia))
    (naturality' α 1 2 (by lia) (by lia))) :
    (X.cyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).inv ≫
      ShortComplex.cyclesMap (X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α) =
      X.cyclesMap n₁ n₂ hn₂ f₁ f₂ f₁' f₂' β ≫
        (X.cyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃').inv := by
  subst hβ
  rw [← cancel_mono (ShortComplex.iCycles _), assoc, assoc, ShortComplex.cyclesMap_i,
    cyclesIso_inv_i_assoc, cyclesIso_inv_i, shortComplexEMap_τ₂]
  symm
  apply cyclesMap_i
  rfl

@[reassoc]
lemma opcyclesMap_opcyclesIso_hom
    (γ : mk₂ f₂ f₃ ⟶ mk₂ f₂' f₃')
    (hγ : γ = homMk₂ (α.app 1) (α.app 2) (α.app 3) (naturality' α 1 2) (naturality' α 2 3)) :
    ShortComplex.opcyclesMap (X.shortComplexEMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α) ≫
      (X.opcyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃').hom =
    (X.opcyclesIso n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃).hom ≫ X.opcyclesMap n₀ n₁ hn₁ f₂ f₃ f₂' f₃' γ := by
  subst hγ
  rw [← cancel_epi (ShortComplex.pOpcycles _), ShortComplex.p_opcyclesMap_assoc,
    p_opcyclesIso_hom, p_opcyclesIso_hom_assoc, shortComplexEMap_τ₂]
  symm
  apply p_opcyclesMap
  rfl

@[reassoc]
lemma πE_EMap (β : mk₂ f₁ f₂ ⟶ mk₂ f₁' f₂')
    (hβ : β = homMk₂ (α.app 0) (α.app 1) (α.app 2) (naturality' α 0 1 (by lia) (by lia))
    (naturality' α 1 2 (by lia) (by lia))) :
    X.πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫ X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α =
      X.cyclesMap n₁ n₂ hn₂ f₁ f₂ f₁' f₂' β ≫ X.πE n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃' := by
  dsimp [πE, EMap]
  simp only [assoc, ShortComplex.homologyπ_naturality,
    X.cyclesIso_inv_cyclesMap_assoc n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α β hβ]

@[reassoc]
lemma EMap_ιE
    (γ : mk₂ f₂ f₃ ⟶ mk₂ f₂' f₃')
    (hγ : γ = homMk₂ (α.app 1) (α.app 2) (α.app 3) (naturality' α 1 2) (naturality' α 2 3)) :
    X.EMap n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α ≫ X.ιE n₀ n₁ n₂ hn₁ hn₂ f₁' f₂' f₃' =
      X.ιE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ ≫ X.opcyclesMap n₀ n₁ hn₁ f₂ f₃ f₂' f₃' γ := by
  dsimp [ιE, EMap]
  simp only [ShortComplex.homologyι_naturality_assoc, assoc,
    X.opcyclesMap_opcyclesIso_hom n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁' f₂' f₃' α γ hγ]

end

section

variable (n₀ n₁ n₂ : ℤ)
  (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
  {i₀ i₁ i₂ i₃ : ι}
  (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₁₂ : i₀ ⟶ i₂) (h₁₂ : f₁ ≫ f₂ = f₁₂)

noncomputable def opcyclesToE : X.opcycles n₀ n₁ hn₁ f₁₂ f₃ ⟶ X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ :=
  X.descOpcycles _ _ _ _ _
    (X.toCycles n₁ n₂ hn₂ f₁ f₂ f₁₂ h₁₂ ≫ X.πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃) (by simp)

@[reassoc (attr := simp)]
lemma p_opcyclesToE :
    X.pOpcycles n₀ n₁ hn₁ f₁₂ f₃ ≫ X.opcyclesToE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂ =
      X.toCycles n₁ n₂ hn₂ f₁ f₂ f₁₂ h₁₂ ≫ X.πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ := by
  simp [opcyclesToE]

@[reassoc (attr := simp)]
lemma opcyclesToE_ιE :
    X.opcyclesToE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂ ≫ X.ιE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ =
      X.opcyclesMap n₀ n₁ hn₁ f₁₂ f₃ f₂ f₃ (threeδ₁Toδ₀ f₁ f₂ f₃ f₁₂ h₁₂) := by
  rw [← cancel_epi (X.pOpcycles n₀ n₁ hn₁ f₁₂ f₃), p_opcyclesToE_assoc,
    πE_ιE, toCycles_i_assoc]
  symm
  apply X.p_opcyclesMap
  rfl

instance : Epi (X.opcyclesToE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂) := by
  have : Epi (X.toCycles n₁ n₂ hn₂ f₁ f₂ f₁₂ h₁₂ ≫ X.πE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃) :=
    epi_comp _ _
  exact epi_of_epi_fac (X.p_opcyclesToE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂)

/-- cokernelSequenceE'' -/
@[simps!]
noncomputable def cokernelSequenceE'' : ShortComplex C where
  X₁ := (X.H n₁).obj (mk₁ f₁)
  X₂ := X.opcycles n₀ n₁ hn₁ f₁₂ f₃
  X₃ := X.E n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃
  f := (X.H n₁).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂) ≫ X.pOpcycles n₀ n₁ hn₁ f₁₂ f₃
  g := X.opcyclesToE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂
  zero := by simp

instance : Epi (X.cokernelSequenceE'' n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂).g := by
  dsimp
  infer_instance

lemma cokernelSequenceE''_exact :
    (X.cokernelSequenceE'' n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂
  obtain ⟨A₁, π₁, _, y₂, hy₂⟩ :=
    surjective_up_to_refinements_of_epi (X.pOpcycles n₀ n₁ hn₁ f₁₂ f₃) x₂
  obtain ⟨A₂, π₂, _, y₁, hy₁⟩ :=
    (X.cokernelSequenceE_exact n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂).exact_up_to_refinements y₂
      (by simpa only [assoc, p_opcyclesToE, hx₂, comp_zero]
        using hy₂.symm =≫ X.opcyclesToE n₀ n₁ n₂ hn₁ hn₂ f₁ f₂ f₃ f₁₂ h₁₂)
  dsimp at y₁ hy₁
  obtain ⟨a, b, rfl⟩ : ∃ a b, y₁ = a ≫ biprod.inl + b ≫ biprod.inr :=
    ⟨y₁ ≫ biprod.fst, y₁ ≫ biprod.snd, by ext <;> simp⟩
  simp only [add_comp, assoc, biprod.inl_desc, biprod.inr_desc] at hy₁
  refine ⟨A₂, π₂ ≫ π₁, epi_comp _ _, a, ?_⟩
  dsimp
  simp only [assoc, hy₂, reassoc_of% hy₁, add_comp, δ_pOpcycles, comp_zero, add_zero]

-- TODO: dual statement?

end


end SpectralObject

end Abelian

end CategoryTheory
