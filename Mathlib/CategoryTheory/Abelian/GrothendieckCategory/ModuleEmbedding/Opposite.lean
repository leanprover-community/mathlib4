/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Abelian.Yoneda
import Mathlib.CategoryTheory.Generator.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Embedding opposites of Grothendieck categories

If `C` is Grothendieck abelian and `F : D ⥤ Cᵒᵖ` is a functor from a small category, we construct
an object `G : Cᵒᵖ` such that `preadditiveCoyonedaObj G : Cᵒᵖ ⥤ ModuleCat (End G)ᵐᵒᵖ` is faithful
and exact and its precomposition with `F` is full if `F` is.
-/

universe v u

open CategoryTheory Limits Opposite ZeroObject

namespace CategoryTheory.Abelian.IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] {D : Type v} [SmallCategory D] (F : D ⥤ Cᵒᵖ)

namespace OppositeModuleEmbedding

variable [Abelian C] [IsGrothendieckAbelian.{v} C]

variable (C) in
private noncomputable def projectiveSeparator : Cᵒᵖ :=
  (has_projective_separator (coseparator Cᵒᵖ) (isCoseparator_coseparator Cᵒᵖ)).choose

private instance : Projective (projectiveSeparator C) :=
  (has_projective_separator (coseparator Cᵒᵖ) (isCoseparator_coseparator Cᵒᵖ)).choose_spec.1

private theorem isSeparator_projectiveSeparator : IsSeparator (projectiveSeparator C) :=
  (has_projective_separator (coseparator Cᵒᵖ) (isCoseparator_coseparator Cᵒᵖ)).choose_spec.2

private noncomputable def generator : Cᵒᵖ :=
  ∐ (fun (X : D) => ∐ fun (_ : projectiveSeparator C ⟶ F.obj X) => projectiveSeparator C)

private theorem exists_epi (X : D) : ∃ f : generator F ⟶ F.obj X, Epi f := by
  classical
  refine ⟨Sigma.desc (Pi.single X (𝟙 _)) ≫ Sigma.desc (fun f => f), ?_⟩
  have h := (isSeparator_iff_epi (projectiveSeparator C)).1
    isSeparator_projectiveSeparator (F.obj X)
  suffices Epi (Sigma.desc (Pi.single X (𝟙 _))) from epi_comp' this h
  exact SplitEpi.epi ⟨Sigma.ι (fun (X : D) => ∐ fun _ => projectiveSeparator C) X, by simp⟩

private instance : Projective (generator F) := by
  rw [generator]
  infer_instance

private theorem isSeparator [Nonempty D] : IsSeparator (generator F) := by
  apply isSeparator_sigma_of_isSeparator _ Classical.ofNonempty
  apply isSeparator_sigma_of_isSeparator _ 0
  exact isSeparator_projectiveSeparator

/-- Given a functor `F : D ⥤ Cᵒᵖ`, where `C` is Grothendieck abelian, this is a ring `R` such that
`Cᵒᵖ` has a nice embedding into `ModuleCat (EmbeddingRing F)`; see
`OppositeModuleEmbedding.embedding`. -/
def EmbeddingRing : Type v := (End (generator F))ᵐᵒᵖ

noncomputable instance : Ring (EmbeddingRing F) :=
  inferInstanceAs <| Ring (End (generator F))ᵐᵒᵖ

/-- This is a functor `embedding F : Cᵒᵖ ⥤ ModuleCat (EmbeddingRing F)`. We have that `embedding F`
is faithful and preserves finite limits and colimits. Furthermore, `F ⋙ embedding F` is full. -/
noncomputable def embedding : Cᵒᵖ ⥤ ModuleCat.{v} (EmbeddingRing F) :=
  preadditiveCoyonedaObj (generator F)

instance faithful_embedding [Nonempty D] : (embedding F).Faithful :=
  (isSeparator_iff_faithful_preadditiveCoyonedaObj _).1 (isSeparator F)

instance full_embedding [Nonempty D] [F.Full] : (F ⋙ embedding F).Full :=
  full_comp_preadditiveCoyonedaObj _ (isSeparator F) (exists_epi F)

instance preservesFiniteLimits_embedding : PreservesFiniteLimits (embedding F) := by
  rw [embedding]
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize
  infer_instance

instance preservesFiniteColimits_embedding : PreservesFiniteColimits (embedding F) := by
  apply preservesFiniteColimits_preadditiveCoyonedaObj_of_projective

end OppositeModuleEmbedding

end CategoryTheory.Abelian.IsGrothendieckAbelian
