/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.NumberTheory.CFT.ClassFormation.GrothendieckTopology
public import Mathlib.NumberTheory.CFT.ClassFormation.GaloisCover

/-!
# Sheaves on the site of connected objects in a Galois category

-/

-- to be moved to `CategoryTheory/Galois`

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits Opposite PreGaloisCategory

variable {C : Type u} [Category.{v} C]

namespace GaloisCategory

variable [GaloisCategory C]

lemma not_isInitial_pullback_of_isConnected
    {X₁ X₂ S : C}
    [PreGaloisCategory.IsConnected X₁] [PreGaloisCategory.IsConnected X₂]
    [PreGaloisCategory.IsConnected S]
    (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S) :
    IsInitial (pullback f₁ f₂) → False := by
  let F := getFiberFunctor C
  rw [not_initial_iff_fiber_nonempty F]
  have := surjective_on_fiber_of_epi F f₁
  let x₂ : F.obj X₂ := Classical.arbitrary _
  obtain ⟨x₁, h⟩ := surjective_of_epi ((forget _).map (F.map f₁)) (F.map f₂ x₂)
  exact ⟨(fiberPullbackEquiv F f₁ f₂).symm ⟨⟨x₁, x₂⟩, h⟩⟩

lemma exists_pullbackCone_isConnected {X₁ X₂ S : C}
    [PreGaloisCategory.IsConnected X₁] [PreGaloisCategory.IsConnected X₂]
    [PreGaloisCategory.IsConnected S]
    (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S) :
    ∃ (Y : C) (_ : PreGaloisCategory.IsConnected Y) (p₁ : Y ⟶ X₁) (p₂ : Y ⟶ X₂),
      p₁ ≫ f₁ = p₂ ≫ f₂ := by
  obtain ⟨Y, f, _, _⟩ := has_connected_component _ (not_isInitial_pullback_of_isConnected f₁ f₂)
  exact ⟨Y, inferInstance, f ≫ pullback.fst _ _, f ≫ pullback.snd _ _,by
    simp [pullback.condition]⟩

lemma exists_aut_of_isGalois {Z Y : C}
    [PreGaloisCategory.IsConnected Z] [PreGaloisCategory.IsGalois Y] (p₁ p₂ : Z ⟶ Y) :
    ∃ (g : Aut Y), p₁ ≫ g.hom = p₂ := by
  let F := getFiberFunctor C
  let z : F.obj Z := Classical.arbitrary _
  obtain ⟨g, hg⟩ := (isPretransitive_of_isGalois F Y).exists_smul_eq
    (F.map p₁ z) (F.map p₂ z)
  exact ⟨g, hom_ext_of_isConnected F z (by simpa [autMulFiber_def] using hg)⟩

lemma exists_aut_of_isGaloisCover
    {Z Y X : C} [PreGaloisCategory.IsConnected Z]
    [PreGaloisCategory.IsConnected Y]
    [PreGaloisCategory.IsConnected X] (f : Y ⟶ X)
    [IsGaloisCover f] (p₁ : Z ⟶ Y) (p₂ : Z ⟶ Y)
    (fac : p₁ ≫ f = p₂ ≫ f) :
    ∃ (g : Aut (Over.mk f)), p₁ ≫ g.hom.left = p₂ := by
  obtain ⟨g, hg⟩ :=
    exists_aut_of_isGalois (Z := Over.mk (p₁ ≫ f)) (Y := Over.mk f)
      (Over.homMk p₁) (Over.homMk p₂)
  exact ⟨Over.isoMk ((Over.forget _).mapIso g) (by simpa using! g.hom.w),
    (Over.forget _).congr_map hg⟩

lemma isSheafFor_singleton (P : (isConnected C).FullSubcategoryᵒᵖ ⥤ Type w)
    (hP : Presieve.IsSheaf (isConnectedTopology C) P)
    {Y X : (isConnected C).FullSubcategory} (f : Y ⟶ X) :
    Presieve.IsSheafFor P (.singleton f) :=
  hP.isSheafFor _ (generate_singleton_mem_isConnectedTopology f)

lemma isSheaf_type_iff (P : (isConnected C).FullSubcategoryᵒᵖ ⥤ Type w) :
    Presieve.IsSheaf (isConnectedTopology C) P ↔
      ∀ ⦃Y X : C⦄ [PreGaloisCategory.IsConnected Y]
        [PreGaloisCategory.IsConnected X] (f : Y ⟶ X) [IsGaloisCover f],
          Presieve.IsSheafFor P (.singleton (isConnectedHomMk f)) :=
  ⟨fun hP _ _ _ _ _ _ ↦ isSheafFor_singleton _ hP _, fun hP ↦ by
    have H {Y X : (isConnected C).FullSubcategory} (f : Y ⟶ X) :
        Presieve.IsSeparatedFor P (.singleton f) := by
      obtain ⟨Z, g, _, _⟩ := exists_isGaloisCover f.hom
      exact Presieve.IsSeparatedFor.of_singleton_comp _ _ (hP (g ≫ f.hom)).isSeparatedFor
    intro X R hR
    obtain ⟨Y, _, f, _, hf⟩ := exists_isGaloisCover_of_mem_isConnectedTopology R hR
    refine Presieve.IsSheafFor.of_singleton (hP f) hf (fun {Z} g hg ↦ ?_)
    obtain ⟨W, _, p₁, p₂, fac⟩ := exists_pullbackCone_isConnected g.hom f
    exact ⟨isConnectedMk W, isConnectedHomMk p₁, isConnectedHomMk p₂,
      by ext; exact fac, H _⟩⟩

instance {Y X : C} [PreGaloisCategory.IsConnected Y] (f : Y ⟶ X) :
    PreGaloisCategory.IsConnected (Over.mk f).left := by assumption

lemma isSheafFor_singleton_iff_of_isGaloisCover
    (P : (isConnected C).FullSubcategoryᵒᵖ ⥤ Type w)
    {Y X : C} [PreGaloisCategory.IsConnected Y]
    [PreGaloisCategory.IsConnected X] (f : Y ⟶ X) [IsGaloisCover f] :
    Presieve.IsSheafFor P (.singleton (isConnectedHomMk f)) ↔
      Function.Injective (P.map (isConnectedHomMk f).op) ∧
        ∀ (y : P.obj (op (isConnectedMk Y)))
          (_ : ∀ (g : Aut (Over.mk f)), P.map ((isConnectedHomMk g.hom.left).op) y = y),
            ∃ (x : P.obj (op (isConnectedMk X))), P.map (isConnectedHomMk f).op x = y := by
  refine ⟨fun hz ↦ ⟨?_, fun y hy ↦ ?_⟩, fun ⟨hz₁, hz₂⟩ ↦ ?_⟩
  · simpa only [Presieve.isSeparatedFor_singleton] using hz.isSeparatedFor
  · rw [Presieve.isSheafFor_singleton] at hz
    refine (hz y (fun {W} p₁ p₂ fac ↦ ?_)).exists
    simp only [ObjectProperty.hom_ext_iff] at fac
    obtain ⟨g, hg⟩ := exists_aut_of_isGaloisCover f p₁.hom p₂.hom
      (by simpa [ObjectProperty.hom_ext_iff] using fac)
    obtain rfl : p₁ ≫ isConnectedHomMk g.hom.left = p₂ := by
      simpa [ObjectProperty.hom_ext_iff]
    simp [hy g]
  · rw [Presieve.isSheafFor_singleton]
    intro y hy
    refine existsUnique_of_exists_of_unique (hz₂ _ (fun g ↦ ?_))
      (fun x₁ x₂ hx₁ hx₂ ↦ hz₁ (by rw [hx₁, hx₂]))
    simpa using! hy (isConnectedHomMk g.hom.left) (𝟙 _) (by ext; simpa using g.hom.w)

end GaloisCategory

end CategoryTheory
