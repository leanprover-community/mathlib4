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

lemma isOpenImmersion_snd (i j : ι) :
    IsOpenImmersion ((hf i).representable.snd (f j)) := (hf i).property (f j)

lemma symmetryIso_hom_comp_snd (i j : ι) :
    ((hf i).representable.symmetryIso (hf j).representable).hom ≫
      ((hf j).representable.snd (f i)) = (hf i).representable.fst (f j) := by
  simp

lemma isOpenImmersion_fst (i j : ι) :
    IsOpenImmersion ((hf i).representable.fst (f j)) := by
  have := isOpenImmersion_snd F f hf j i
  rw [← symmetryIso_hom_comp_snd F f hf]
  infer_instance

@[simp]
lemma fst_self_eq_snd (i : ι) :
    (hf i).representable.fst (f i) = (hf i).representable.snd (f i) := by
  have := mono_of_openImmersion_presheaf (hf i)
  apply yoneda.map_injective
  rw [← cancel_mono (f i), (hf i).representable.condition (f i)]

lemma isIso_fst_self (i : ι) :
    IsIso ((hf i).representable.fst (f i)) := by
  refine ⟨(hf i).representable.lift' (𝟙 _) (𝟙 _) (by simp), ?_, by simp⟩
  ext1
  · simp
  · simp [fst_self_eq_snd F f hf i]

--@[simps]
noncomputable def glueData : GlueData where
  J := ι
  U := X
  V := fun (i, j) ↦ (hf i).representable.pullback (f j)
  f i j := (hf i).representable.fst (f j)
  f_mono i j := by
    have := isOpenImmersion_fst F f hf i j
    infer_instance
  f_id := isIso_fst_self F f hf
  t i j := (hf i).representable.symmetry (hf j).representable
  t_id i := by ext1 <;> simp [fst_self_eq_snd F f hf i]
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
  f_open := isOpenImmersion_fst F f hf

noncomputable def toGlued (i : ι) : X i ⟶ (glueData F f hf).glued :=
  (glueData F f hf).ι i

noncomputable def yonedaGluedToSheaf :
    subcanonical_zariskiTopology.yoneda.obj (glueData F f hf).glued ⟶ F :=
  Sheaf.homEquiv.symm (yonedaEquiv.symm
    ((glueData F f hf).sheafValGluedMk (fun i ↦ yonedaEquiv (f i)) (by
      intro i j
      dsimp
      sorry)))

@[simp]
lemma fac (i : ι) :
    yoneda.map (toGlued F f hf i) ≫ (yonedaGluedToSheaf F f hf).val = f i := by
  dsimp [yonedaGluedToSheaf, Sheaf.homEquiv, Functor.FullyFaithful.homEquiv]
  apply yonedaEquiv.injective
  rw [yonedaEquiv_apply, yonedaEquiv_apply]
  dsimp
  simp only [comp_id]
  apply GlueData.sheafValGluedMk_val

instance : Sheaf.IsLocallySurjective (yonedaGluedToSheaf F f hf) :=
  Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
    (show Sigma.desc (fun i ↦ yoneda.map (toGlued F f hf i)) ≫
      (yonedaGluedToSheaf F f hf).val = Sigma.desc f by aesop_cat)

instance : Sheaf.IsLocallyInjective (yonedaGluedToSheaf F f hf) := sorry

instance : IsIso (yonedaGluedToSheaf F f hf) := by
  rw [← Sheaf.isLocallyBijective_iff_isIso (yonedaGluedToSheaf F f hf)]
  constructor <;> infer_instance

noncomputable def yonedaIsoSheaf :
    subcanonical_zariskiTopology.yoneda.obj (glueData F f hf).glued ≅ F :=
  asIso (yonedaGluedToSheaf F f hf)

end Representability

open Representability in
theorem representability_is_local : F.1.Representable where
  has_representation := ⟨(glueData F f hf).glued,
    ⟨(sheafToPresheaf _ _).mapIso (yonedaIsoSheaf F f hf)⟩⟩

end Scheme

end AlgebraicGeometry
