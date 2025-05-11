/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions
import Mathlib.Algebra.Homology.Localization

/-!
# Left derivability structures on homological complexes

-/

open CategoryTheory

variable {A α C₀ : Type*} [Category A] [Abelian A] {c : ComplexShape α}
  [Category C₀] {W₀ : MorphismProperty C₀}
  (Φ : LocalizerMorphism W₀ (HomologicalComplex.quasiIso A c))
  (hW₀ : W₀ = (HomologicalComplex.quasiIso A c).inverseImage Φ.functor)
  {ρ : HomologicalComplex A c ⥤ C₀} (π : ρ ⋙ Φ.functor ⟶ 𝟭 _) [∀ K, QuasiIso (π.app K)]

namespace HomologicalComplex

include hW₀ π

variable [Φ.functor.Full] [Φ.functor.Faithful]

lemma isLocalizedEquivalence_of_functorial_left_resolutions :
    Φ.IsLocalizedEquivalence :=
  Φ.isLocalizedEquivalence_of_functorial_left_resolutions π
    (fun _ ↦ by rw [mem_quasiIso_iff]; infer_instance) hW₀

lemma isConnected_leftResolution_of_functorial_left_resolutions (K : HomologicalComplex A c) :
    letI : W₀.IsMultiplicative := by rw [hW₀]; infer_instance
    IsConnected (Φ.LeftResolution K) :=
  Φ.isConnected_leftResolution_of_functorial_resolutions π
    (fun _ ↦ by rw [mem_quasiIso_iff]; infer_instance) hW₀ _

lemma isLeftDerivabilityStructure_of_functorial_left_resolutions :
    Φ.IsLeftDerivabilityStructure :=
  Φ.isLeftDerivabilityStructure_of_functorial_resolutions π
    (fun _ ↦ by rw [mem_quasiIso_iff]; infer_instance) hW₀

end HomologicalComplex

namespace HomotopyCategory

variable {Φ} {H₀ : Type*} [Category H₀] {W₀ₕ : MorphismProperty H₀}
  {Φₕ : LocalizerMorphism W₀ₕ (quasiIso A c)}
  (hW₀ₕ : W₀ₕ = (quasiIso A c).inverseImage Φₕ.functor)
  {Ψ : LocalizerMorphism W₀ W₀ₕ}
  (iso : Φ.functor ⋙ quotient _ _ ≅ Ψ.functor ⋙ Φₕ.functor)

/-include hW₀ π iso in
lemma isLocalizedEquivalence_of_functorial_left_resolutions
    [Φ.functor.Full] [Φ.functor.Faithful] [Ψ.IsLocalizedEquivalence] :
    Φₕ.IsLocalizedEquivalence := by
  have := iso
  have := HomologicalComplex.isLocalizedEquivalence_of_functorial_left_resolutions Φ hW₀ π
  sorry-/

include π iso in
lemma hasLeftResolutions_of_functorial_left_resolutions :
    Φₕ.HasLeftResolutions := by
  intro K
  obtain ⟨K, rfl⟩ := K.quotient_obj_surjective
  exact ⟨{
    X₁ := Ψ.functor.obj (ρ.obj K)
    w := iso.inv.app _ ≫ (quotient _ _).map (π.app K)
    hw := by
      have : (quasiIso A c) ((quotient A c).map (π.app K)) := by
        rw [quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff]
        infer_instance
      exact (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk (iso.app _) (Iso.refl _))).1 this
  }⟩

include π iso in
lemma hasLeftResolutions_arrow_of_functorial_left_resolutions :
    Φₕ.arrow.HasLeftResolutions := by
  rintro ⟨K, L, f⟩
  obtain ⟨K, rfl⟩ := K.quotient_obj_surjective
  obtain ⟨L, rfl⟩ := L.quotient_obj_surjective
  obtain ⟨f, rfl⟩ := (quotient _ _).map_surjective f
  have h (M : HomologicalComplex A c) :
      (quasiIso A c) (iso.inv.app _ ≫ (quotient _ _).map (π.app M)) := by
    have : (quasiIso A c) ((quotient A c).map (π.app M)) := by
      rw [quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff]
      infer_instance
    exact (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk (iso.app _) (Iso.refl _))).1 this
  exact ⟨{
    X₁ := Arrow.mk (Ψ.functor.map (ρ.map f))
    w := Arrow.homMk (iso.inv.app _ ≫ (quotient _ _).map (π.app K))
      (iso.inv.app _ ≫ (quotient _ _).map (π.app L)) (by
        have h₁ := iso.inv.naturality (ρ.map f)
        have h₂ := π.naturality f
        dsimp at h₁ h₂ ⊢
        rw [Category.assoc, reassoc_of% h₁, ← Functor.map_comp, ← Functor.map_comp, h₂])
    hw := ⟨h _, h _⟩
  }⟩

variable [Ψ.functor.EssSurj] [Φ.functor.Full] [Φ.functor.Faithful]

include hW₀ π iso in
lemma isConnected_leftResolution_of_functorial_left_resolutions
    (K : HomotopyCategory A c) :
    letI : W₀ₕ.IsMultiplicative := by rw [hW₀ₕ]; infer_instance
    IsConnected (Φₕ.LeftResolution K) := by
  have : W₀ₕ.IsMultiplicative := by rw [hW₀ₕ]; infer_instance
  have : W₀.IsMultiplicative := by rw [hW₀]; infer_instance
  have : W₀ₕ.RespectsIso := by rw [hW₀ₕ]; infer_instance
  have := hasLeftResolutions_of_functorial_left_resolutions π iso
  obtain ⟨K, rfl⟩ := K.quotient_obj_surjective
  let P : Φ.LeftResolution K ⥤ Φₕ.LeftResolution ((quotient _ _).obj K) :=
    { obj R :=
        { X₁ := Ψ.functor.obj R.X₁
          w := iso.inv.app _ ≫ (quotient _ _).map R.w
          hw := by
            apply MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isIso _ _) _
            rw [quotient_map_mem_quasiIso_iff]
            exact R.hw }
      map φ :=
        { f := Ψ.functor.map φ.f
          hf := Ψ.map _ (φ.hf)
          comm := by
            have := iso.inv.naturality φ.f
            dsimp at this ⊢
            rw [reassoc_of% this, ← Functor.map_comp, φ.comm] } }
  have : P.EssSurj :=
    { mem_essImage R := by
        obtain ⟨f, hf⟩ := (quotient _ _).map_surjective
          (iso.hom.app _ ≫ Φₕ.functor.map (Ψ.functor.objObjPreimageIso R.X₁).hom ≫ R.w)
        let R' : Φ.LeftResolution K :=
          { X₁ := Ψ.functor.objPreimage R.X₁
            w := f
            hw := by
              rw [← quotient_map_mem_quasiIso_iff, hf, ← Category.assoc]
              exact MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isIso _ _) R.hw }
        exact ⟨R', ⟨LocalizerMorphism.LeftResolution.isoMk (Ψ.functor.objObjPreimageIso R.X₁)
          (by simp [P, R', hf]) ⟩⟩ }
  have := HomologicalComplex.isConnected_leftResolution_of_functorial_left_resolutions Φ hW₀ π K
  exact P.isConnected_of_isConnected_of_essSurj

variable [Ψ.IsLocalizedEquivalence]

/-include hW₀ π hW₀ₕ iso in
lemma isLeftDerivabilityStructure_of_functorial_left_resolutions :
    Φₕ.IsLeftDerivabilityStructure := by
  have : W₀ₕ.IsMultiplicative := by rw [hW₀ₕ]; infer_instance
  have := isLocalizedEquivalence_of_functorial_left_resolutions hW₀ π iso
  have := hasLeftResolutions_arrow_of_functorial_left_resolutions π iso
  have := isConnected_leftResolution_of_functorial_left_resolutions hW₀ π hW₀ₕ iso
  apply LocalizerMorphism.IsLeftDerivabilityStructure.mk'-/

end HomotopyCategory
