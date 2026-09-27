/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Generator.Presheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Generators in the category of sheaves

In this file, we show that if `J : GrothendieckTopology C` and `A` is a preadditive
category which has a separator (and suitable coproducts), then `Sheaf J A` has a separator.

-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory

open Limits Opposite

namespace Sheaf

variable {C : Type u} [Category.{v} C]
  (J : GrothendieckTopology C) {A : Type u'} [Category.{v'} A]
  [HasCoproducts.{v} A] [HasWeakSheafify J A]

/-- Given `J : GrothendieckTopology C`, `X : C` and `M : A`, this is the associated
sheaf to the presheaf `Presheaf.freeYoneda X M`. -/
@[implicit_reducible]
noncomputable def freeYoneda (X : C) (M : A) : Sheaf J A :=
  (presheafToSheaf J A).obj (Presheaf.freeYoneda X M)

/-- The morphism between free sheaves induced by a morphism in the site. -/
noncomputable def freeYonedaMap {X Y : C} (f : X ⟶ Y) (M : A) :
    freeYoneda J X M ⟶ freeYoneda J Y M :=
  (presheafToSheaf J A).map (Presheaf.freeYonedaMap f M)

instance {X Y : C} (f : X ⟶ Y) (M : A) [Mono f] [MonoCoprod A]
    [(presheafToSheaf J A).PreservesMonomorphisms] : Mono (freeYonedaMap J f M) :=
  Functor.map_mono _ _

variable {J} in
/-- The bijection `(Sheaf.freeYoneda J X M ⟶ F) ≃ (M ⟶ F.val.obj (op X))`
when `F : Sheaf J A`, `X : C` and `M : A`. -/
noncomputable def freeYonedaHomEquiv {X : C} {M : A} {F : Sheaf J A} :
    (freeYoneda J X M ⟶ F) ≃ (M ⟶ F.obj.obj (op X)) :=
  ((sheafificationAdjunction J A).homEquiv _ _).trans Presheaf.freeYonedaHomEquiv

variable {J} in
@[reassoc]
lemma freeYonedaHomEquiv_naturality {X Y : C} {M : A} {F : Sheaf J A}
    (f : X ⟶ Y) (α : freeYoneda J Y M ⟶ F) :
    freeYonedaHomEquiv (freeYonedaMap J f M ≫ α) =
      freeYonedaHomEquiv α ≫ F.obj.map f.op := by
  simp only [freeYonedaHomEquiv, freeYonedaMap, freeYoneda, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left]
  exact Presheaf.freeYonedaHomEquiv_naturality f _

lemma isSeparating {ι : Type w} {S : ι → A} (hS : ObjectProperty.IsSeparating (.ofObj S)) :
    ObjectProperty.IsSeparating (.ofObj (fun (⟨X, i⟩ : C × ι) ↦ freeYoneda J X (S i))) := by
  intro F G f g hfg
  refine (sheafToPresheaf J A).map_injective (Presheaf.isSeparating C hS _ _ ?_)
  rintro _ ⟨X, i⟩ a
  apply ((sheafificationAdjunction _ _).homEquiv _ _).symm.injective
  simpa only [← Adjunction.homEquiv_naturality_right_symm] using
    hfg _ (ObjectProperty.ofObj_apply _ ⟨X, i⟩)
      (((sheafificationAdjunction _ _).homEquiv _ _).symm a)

lemma isSeparator {ι : Type w} {S : ι → A} (hS : ObjectProperty.IsSeparating (.ofObj S))
    [HasCoproduct (fun (⟨X, i⟩ : C × ι) ↦ freeYoneda J X (S i))] [Preadditive A] :
    IsSeparator (∐ (fun (⟨X, i⟩ : C × ι) ↦ freeYoneda J X (S i))) :=
  (isSeparating J hS).isSeparator_coproduct

variable (A) in
instance hasSeparator [HasSeparator A] [Preadditive A] [HasCoproducts.{u} A] :
    HasSeparator (Sheaf J A) where
  hasSeparator := ⟨_, isSeparator J (S := fun (_ : Unit) ↦ separator A)
      (by simpa using! isSeparator_separator A)⟩

end Sheaf

end CategoryTheory
