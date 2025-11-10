import Mathlib.Condensed.Light.Epi
import Mathlib.Condensed.Light.Functors
import Mathlib.Condensed.Light.Monoidal
import Mathlib.CategoryTheory.Preadditive.Projective.Internal

universe u

open CategoryTheory MonoidalCategory

variable (R : Type u) [CommRing R]

namespace LightCondensed

noncomputable def ihomPoints (A B : LightCondMod.{u} R) (S : LightProfinite) :
    ((ihom A).obj B).val.obj ⟨S⟩ ≃ ((A ⊗ ((free R).obj S.toCondensed)) ⟶ B) :=
  (((freeForgetAdjunction R).homEquiv _ _).trans
    (coherentTopology _).yonedaEquiv).symm.trans
      ((ihom.adjunction A).homEquiv _ _).symm

lemma ihomPoints_apply (A B : LightCondMod.{u} R) (S : LightProfinite)
    (x : ihom A |>.obj B |>.val.obj ⟨S⟩) :
    ihomPoints R A B S x = (MonoidalClosed.uncurry (((freeForgetAdjunction R).homEquiv _ _).symm
      ((coherentTopology LightProfinite.{u}).yonedaEquiv.symm x))) :=
  rfl

lemma ihomPoints_symm_apply (A B : LightCondMod.{u} R) (S : LightProfinite)
    (x : (A ⊗ ((free R).obj S.toCondensed)) ⟶ B) :
    (ihomPoints R A B S).symm x = (coherentTopology LightProfinite.{u}).yonedaEquiv
      ((freeForgetAdjunction R).homEquiv _ _ (MonoidalClosed.curry x)) := by
  rfl

lemma ihom_map_val_app (A B P : LightCondMod.{u} R) (S : LightProfinite) (e : A ⟶ B)
    (x : ihom P |>.obj A |>.val.obj ⟨S⟩) :
    (((ihom P).map e).val.app ⟨S⟩) x =
        (ihomPoints R P B S).symm (ihomPoints R P A S x ≫ e) := by
  apply (ihomPoints R P B S).injective
  simp only [ihomPoints_apply, Equiv.apply_symm_apply]
  rw [← MonoidalClosed.uncurry_natural_right, ← Adjunction.homEquiv_naturality_right_symm]
  congr
  ext
  simp
  rfl

lemma ihomPoints_symm_comp (B P : LightCondMod.{u} R) (S S' : LightProfinite) (π : S ⟶ S')
    (f : P ⊗ (free R).obj S'.toCondensed ⟶ B) :
    (ihomPoints R P B S).symm (P ◁ (free R).map (lightProfiniteToLightCondSet.map π) ≫ f) =
      ConcreteCategory.hom (((ihom P).obj B).val.map π.op) ((ihomPoints R P B S').symm f) := by
  simp only [ihomPoints_symm_apply, MonoidalClosed.curry_natural_left, Adjunction.homEquiv_apply,
    Functor.comp_obj, Functor.map_comp, Adjunction.unit_naturality_assoc]
  rw [GrothendieckTopology.yonedaEquiv_comp, GrothendieckTopology.yonedaEquiv_comp,
    GrothendieckTopology.yonedaEquiv_apply, GrothendieckTopology.yonedaEquiv_apply]
  have : (lightProfiniteToLightCondSet.map π).val.app (Opposite.op S) (𝟙 S) =
      S'.toCondensed.val.map π.op (𝟙 S') := rfl
  rw [this]
  simp
  rfl

lemma internallyProjective_iff_tensor_condition (P : LightCondMod R) : InternallyProjective P ↔
    ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e],
      (∀ (S : LightProfinite) (g : P ⊗ (free R).obj S.toCondensed ⟶ B), ∃ (S' : LightProfinite)
        (π : S' ⟶ S) (_ : Function.Surjective π) (g' : P ⊗ (free R).obj S'.toCondensed ⟶ A),
          (P ◁ ((lightProfiniteToLightCondSet ⋙ free R).map π)) ≫ g = g' ≫ e) := by
  constructor
  · intro ⟨h⟩ A B e he S g
    have hh := h.1 e
    rw [LightCondMod.epi_iff_locallySurjective_on_lightProfinite] at hh
    specialize hh S ((ihomPoints R P B S).symm g)
    obtain ⟨S', π, hπ, g', hh⟩ := hh
    refine ⟨S', π, hπ, (ihomPoints _ _ _ _) g', ?_⟩
    rw [ihom_map_val_app] at hh
    apply (ihomPoints R P B S').symm.injective
    rw [hh]
    exact ihomPoints_symm_comp R B P S' S π g
  · intro h
    constructor
    constructor
    intro A B e he
    rw [LightCondMod.epi_iff_locallySurjective_on_lightProfinite]
    intro S g
    specialize h e S ((ihomPoints _ _ _ _) g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (ihomPoints _ _ _ _).symm g', ?_⟩
    rw [ihom_map_val_app]
    have := ihomPoints_symm_comp R B P S' S π ((ihomPoints R P B S) g)
    dsimp at hh
    rw [hh] at this
    simp [this]
    rfl

lemma internallyProjective_iff_tensor_condition' (P : LightCondMod R) : InternallyProjective P ↔
    ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e],
      (∀ (S : LightProfinite) (g : (free R).obj S.toCondensed ⊗ P ⟶ B), ∃ (S' : LightProfinite)
        (π : S' ⟶ S) (_ : Function.Surjective π) (g' : (free R).obj S'.toCondensed ⊗ P ⟶ A),
          (((lightProfiniteToLightCondSet ⋙ free R).map π) ▷ P) ≫ g = g' ≫ e) := by
  rw [internallyProjective_iff_tensor_condition]
  refine ⟨fun h A B e he S g ↦ ?_, fun h A B e he S g ↦ ?_⟩
  · specialize h e S ((β_ _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (β_ _ _).inv ≫ g', ?_⟩
    simp [← hh]
  · specialize h e S ((β_ _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (β_ _ _).hom ≫ g', ?_⟩
    simp [← hh]

lemma free_internallyProjective_iff_tensor_condition (P : LightCondSet.{u}) :
    InternallyProjective ((free R).obj P) ↔
      ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e], (∀ (S : LightProfinite)
        (g : (free R).obj (P ⊗ S.toCondensed) ⟶ B), ∃ (S' : LightProfinite)
          (π : S' ⟶ S) (_ : Function.Surjective π) (g' : (free R).obj (P ⊗  S'.toCondensed) ⟶ A),
            ((free R).map (P ◁ ((lightProfiniteToLightCondSet).map π))) ≫ g = g' ≫ e) := by
  rw [internallyProjective_iff_tensor_condition]
  refine ⟨fun h A B e he S g ↦ ?_, fun h A B e he S g ↦ ?_⟩
  · specialize h e S ((Functor.Monoidal.μIso (free R) _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (Functor.Monoidal.μIso (free R) _ _).inv ≫ g', ?_⟩
    rw [Category.assoc, ← hh]
    simp only [← Category.assoc]
    simp only [Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv,
      Functor.comp_map, Functor.OplaxMonoidal.δ_natural_right,
      Category.assoc, Functor.Monoidal.δ_μ, Category.comp_id]
  · specialize h e S ((Functor.Monoidal.μIso (free R) _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (Functor.Monoidal.μIso (free R) _ _).hom ≫ g', ?_⟩
    rw [Category.assoc, ← hh]
    simp only [← Category.assoc]
    simp only [Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv,
      Functor.comp_map, ← Functor.LaxMonoidal.μ_natural_right, Category.assoc,
      Functor.Monoidal.μ_δ, Category.comp_id]

lemma free_internallyProjective_iff_tensor_condition' (P : LightCondSet.{u}) :
    InternallyProjective ((free R).obj P) ↔
      ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e], (∀ (S : LightProfinite)
        (g : (free R).obj (S.toCondensed ⊗ P) ⟶ B), ∃ (S' : LightProfinite)
          (π : S' ⟶ S) (_ : Function.Surjective π) (g' : (free R).obj (S'.toCondensed ⊗ P) ⟶ A),
            ((free R).map (((lightProfiniteToLightCondSet).map π) ▷ P)) ≫ g = g' ≫ e) := by
  rw [internallyProjective_iff_tensor_condition']
  refine ⟨fun h A B e he S g ↦ ?_, fun h A B e he S g ↦ ?_⟩
  · specialize h e S ((Functor.Monoidal.μIso (free R) _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (Functor.Monoidal.μIso (free R) _ _).inv ≫ g', ?_⟩
    rw [Category.assoc, ← hh]
    simp only [← Category.assoc]
    simp only [Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv,
      Functor.comp_map, Functor.OplaxMonoidal.δ_natural_left,
      Category.assoc, Functor.Monoidal.δ_μ, Category.comp_id]
  · specialize h e S ((Functor.Monoidal.μIso (free R) _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (Functor.Monoidal.μIso (free R) _ _).hom ≫ g', ?_⟩
    rw [Category.assoc, ← hh]
    simp only [← Category.assoc]
    simp only [Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv,
      Functor.comp_map, ← Functor.LaxMonoidal.μ_natural_left, Category.assoc,
      Functor.Monoidal.μ_δ, Category.comp_id]

lemma free_lightProfinite_internallyProjective_iff_tensor_condition (P : LightProfinite.{u}) :
    InternallyProjective ((free R).obj P.toCondensed) ↔
      ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e], (∀ (S : LightProfinite)
        (g : (free R).obj ((P ⊗ S).toCondensed) ⟶ B), ∃ (S' : LightProfinite)
          (π : S' ⟶ S) (_ : Function.Surjective π) (g' : (free R).obj (P ⊗ S').toCondensed ⟶ A),
            ((free R).map (lightProfiniteToLightCondSet.map (P ◁ π))) ≫ g = g' ≫ e) := by
  rw [free_internallyProjective_iff_tensor_condition]
  refine ⟨fun h A B e he S g ↦ ?_, fun h A B e he S g ↦ ?_⟩
  · specialize h e S ((free R).map (Functor.Monoidal.μIso lightProfiniteToLightCondSet _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map (Functor.Monoidal.μIso
        lightProfiniteToLightCondSet _ _).inv ≫ g', ?_⟩
    rw [Category.assoc, ← hh]
    simp only [← Category.assoc]
    simp only [← Functor.map_comp, Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv,
      Functor.OplaxMonoidal.δ_natural_right,
      Category.assoc, Functor.Monoidal.δ_μ, Category.comp_id]
  · specialize h e S ((free R).map (Functor.Monoidal.μIso lightProfiniteToLightCondSet _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map
      (Functor.Monoidal.μIso lightProfiniteToLightCondSet _ _).hom ≫ g', ?_⟩
    rw [Category.assoc, ← hh]
    simp only [← Category.assoc]
    simp only [← Functor.map_comp, Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv,
      ← Functor.LaxMonoidal.μ_natural_right, Category.assoc,
      Functor.Monoidal.μ_δ, Category.comp_id]

lemma free_lightProfinite_internallyProjective_iff_tensor_condition' (P : LightProfinite.{u}) :
    InternallyProjective ((free R).obj P.toCondensed) ↔
      ∀ {A B : LightCondMod R} (e : A ⟶ B) [Epi e], (∀ (S : LightProfinite)
        (g : (free R).obj ((S ⊗ P).toCondensed) ⟶ B), ∃ (S' : LightProfinite)
          (π : S' ⟶ S) (_ : Function.Surjective π) (g' : (free R).obj (S' ⊗ P).toCondensed ⟶ A),
            ((free R).map (lightProfiniteToLightCondSet.map (π ▷ P))) ≫ g = g' ≫ e) := by
  rw [free_internallyProjective_iff_tensor_condition']
  refine ⟨fun h A B e he S g ↦ ?_, fun h A B e he S g ↦ ?_⟩
  · specialize h e S ((free R).map (Functor.Monoidal.μIso lightProfiniteToLightCondSet _ _).hom ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map (Functor.Monoidal.μIso
        lightProfiniteToLightCondSet _ _).inv ≫ g', ?_⟩
    rw [Category.assoc, ← hh]
    simp only [← Category.assoc]
    simp only [← Functor.map_comp, Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv,
      Functor.OplaxMonoidal.δ_natural_left,
      Category.assoc, Functor.Monoidal.δ_μ, Category.comp_id]
  · specialize h e S ((free R).map (Functor.Monoidal.μIso lightProfiniteToLightCondSet _ _).inv ≫ g)
    obtain ⟨S', π, hπ, g', hh⟩ := h
    refine ⟨S', π, hπ, (free R).map
      (Functor.Monoidal.μIso lightProfiniteToLightCondSet _ _).hom ≫ g', ?_⟩
    rw [Category.assoc, ← hh]
    simp only [← Category.assoc]
    simp only [← Functor.map_comp, Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv,
      ← Functor.LaxMonoidal.μ_natural_left, Category.assoc,
      Functor.Monoidal.μ_δ, Category.comp_id]

end LightCondensed
