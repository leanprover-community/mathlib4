/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Joël Riou, Ravi Vakil
-/
import Mathlib.CategoryTheory.MorphismProperty.Presheaf
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.GluingHyperCover
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-
# Representability

## References
* https://stacks.math.columbia.edu/tag/01JJ

-/

namespace AlgebraicGeometry

open CategoryTheory Category Limits Opposite

universe u

namespace Scheme

abbrev openImmersion : MorphismProperty (Scheme.{u}) := @IsOpenImmersion

lemma openImmersion_le_monomorphisms :
    openImmersion ≤ MorphismProperty.monomorphisms Scheme.{u} := fun _ _ _ _ ↦
  MorphismProperty.monomorphisms.infer_property _

lemma mono_of_openImmersion_presheaf {F G : Scheme.{u}ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} (hf : openImmersion.presheaf f) : Mono f :=
  MorphismProperty.presheaf_monomorphisms_le_monomorphisms _
    (MorphismProperty.presheaf_monotone (openImmersion_le_monomorphisms) _ hf)

variable (F : Sheaf (Scheme.zariskiTopology.{u}) (Type u)) {ι : Type u}
  {X : ι → Scheme.{u}} (f : (i : ι) → yoneda.obj (X i) ⟶ F.1)
  (hf : ∀ i, openImmersion.presheaf (f i))
  [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)]

namespace Representability

variable {F f}
variable (i j : ι)

noncomputable abbrev V := (hf i).representable.pullback (f j)
noncomputable abbrev p₁ : V hf i j ⟶ X i := (hf i).representable.fst (f j)
noncomputable abbrev p₂ : V hf i j ⟶ X j := (hf i).representable.snd (f j)

noncomputable abbrev symmetryIso : V hf i j ≅ V hf j i :=
  ((hf i).representable.symmetryIso (hf j).representable)

lemma isOpenImmersion_p₂ (i j : ι) :
    IsOpenImmersion (p₂ hf i j) := (hf i).property (f j)

lemma symmetryIso_hom_comp_p₂ (i j : ι) :
    (symmetryIso hf i j).hom ≫ p₂ hf j i = p₁ hf i j := by
  simp

lemma isOpenImmersion_p₁ (i j : ι) :
    IsOpenImmersion (p₁ hf i j) := by
  have := isOpenImmersion_p₂ hf j i
  rw [← symmetryIso_hom_comp_p₂ hf]
  infer_instance

lemma p₁_self_eq_p₂ (i : ι) :
    p₁ hf i i = p₂ hf i i := by
  have := mono_of_openImmersion_presheaf (hf i)
  apply yoneda.map_injective
  rw [← cancel_mono (f i), (hf i).representable.condition (f i)]

lemma isIso_p₁_self (i : ι) :
    IsIso (p₁ hf i i) := by
  refine ⟨(hf i).representable.lift' (𝟙 _) (𝟙 _) (by simp), ?_, by simp⟩
  ext1
  · simp
  · simp [p₁_self_eq_p₂ hf i]

@[simps]
noncomputable def glueData : GlueData where
  J := ι
  U := X
  V := fun (i, j) ↦ V hf i j
  f := p₁ hf
  f_mono i j := by
    have := isOpenImmersion_p₁ hf i j
    infer_instance
  f_id := isIso_p₁_self hf
  t i j := (hf i).representable.symmetry (hf j).representable
  t_id i := by ext1 <;> simp [p₁_self_eq_p₂ hf i]
  t' i j k :=
      pullback.lift
        ((hf j).representable.lift'
          (pullback.fst ≫ (hf i).representable.snd (f j))
          (pullback.snd ≫ (hf i).representable.snd (f k)) sorry)
        ((hf j).representable.lift'
          (pullback.fst ≫ (hf i).representable.snd (f j))
          (pullback.snd ≫ (hf i).representable.fst (f k)) sorry)
        (by simp)
  t_fac := sorry
  cocycle i j k := sorry
  f_open := isOpenImmersion_p₁ hf

noncomputable def toGlued (i : ι) : X i ⟶ (glueData hf).glued :=
  (glueData hf).ι i

noncomputable def yonedaGluedToSheaf :
    subcanonical_zariskiTopology.yoneda.obj (glueData hf).glued ⟶ F :=
  Sheaf.homEquiv.symm (yonedaEquiv.symm
    ((glueData hf).sheafValGluedMk (fun i ↦ yonedaEquiv (f i)) (by
      intro i j
      dsimp
      sorry)))

@[simp]
lemma fac (i : ι) :
    yoneda.map (toGlued hf i) ≫ (yonedaGluedToSheaf hf).val = f i := by
  dsimp [yonedaGluedToSheaf, Sheaf.homEquiv, Functor.FullyFaithful.homEquiv]
  apply yonedaEquiv.injective
  rw [yonedaEquiv_apply, yonedaEquiv_apply]
  dsimp
  simp only [comp_id]
  apply GlueData.sheafValGluedMk_val

instance : Sheaf.IsLocallySurjective (yonedaGluedToSheaf hf) :=
  Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
    (show Sigma.desc (fun i ↦ yoneda.map (toGlued hf i)) ≫
      (yonedaGluedToSheaf hf).val = Sigma.desc f by aesop_cat)

instance : Sheaf.IsLocallyInjective (yonedaGluedToSheaf hf) := sorry

instance : IsIso (yonedaGluedToSheaf hf) := by
  rw [← Sheaf.isLocallyBijective_iff_isIso (yonedaGluedToSheaf hf)]
  constructor <;> infer_instance

noncomputable def yonedaIsoSheaf :
    subcanonical_zariskiTopology.yoneda.obj (glueData hf).glued ≅ F :=
  asIso (yonedaGluedToSheaf hf)

end Representability

open Representability in
theorem representability_is_local : F.1.Representable where
  has_representation := ⟨(glueData hf).glued,
    ⟨(sheafToPresheaf _ _).mapIso (yonedaIsoSheaf hf)⟩⟩

end Scheme

end AlgebraicGeometry
