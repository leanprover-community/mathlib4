/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Generator

/-!
# Generators in the category of sheaves

In this file, we show that if `J : GrothendieckTopology C` and `A` is a preadditive
category which has a separator (and suitable coproducts), then `Sheaf J A` has a separator.

-/

universe w v' v u' u

namespace CategoryTheory

open Limits Opposite

-- to be moved
open Classical in
lemma IsSeparating.isSeparator_coproduct {C : Type u} [Category.{v} C]
    {ι : Type w} {S : ι → C} (hS : IsSeparating (Set.range S)) [HasCoproduct S]
    [HasZeroMorphisms C] :
    IsSeparator (∐ S) := by
  intro X Y f g h
  refine hS _ _ ?_
  rintro _ ⟨i, rfl⟩ α
  let β : ∐ S ⟶ X := Sigma.desc
    (fun j ↦ if hij : i = j then eqToHom (by rw [hij]) ≫ α else 0)
  have hβ : Sigma.ι S i ≫ β = α := by simp [β]
  simp only [← hβ, Category.assoc, h (∐ S) (by simp) β]

namespace Presheaf

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [∀ (ι : Type v), HasCoproductsOfShape ι A]

/-- Given `X : C` and `M : A`, this is the presheaf `Cᵒᵖ ⥤ A` which sends
`Y : Cᵒᵖ` to the coproduct of copies of `M` indexed by `Y.unop ⟶ X`. -/
@[simps]
noncomputable def freeYoneda (X : C) (M : A) : Cᵒᵖ ⥤ A where
  obj Y := ∐ (fun (i : (yoneda.obj X).obj Y) ↦ M)
  map f := Sigma.map' ((yoneda.obj X).map f) (fun _ ↦ 𝟙 M)

/-- The bijection `(Presheaf.freeYoneda X M ⟶ F) ≃ (M ⟶ F.obj (op X))`. -/
noncomputable def freeYonedaHomEquiv {X : C} {M : A} {F : Cᵒᵖ ⥤ A} :
    (freeYoneda X M ⟶ F) ≃ (M ⟶ F.obj (op X)) where
  toFun f := Sigma.ι (fun (i : (yoneda.obj X).obj _) ↦ M) (𝟙 _) ≫ f.app (op X)
  invFun g :=
    { app Y := Sigma.desc (fun φ ↦ g ≫ F.map φ.op)
      naturality _ _ _ := Sigma.hom_ext _ _ (by simp)}
  left_inv f := by
    ext Y
    refine Sigma.hom_ext _ _ (fun φ ↦ ?_)
    simpa using (Sigma.ι _ (𝟙 _) ≫= f.naturality φ.op).symm
  right_inv g := by simp

@[reassoc]
lemma freeYonedaHomEquiv_comp {X : C} {M : A} {F G : Cᵒᵖ ⥤ A}
    (α : freeYoneda X M ⟶ F) (f : F ⟶ G) :
    freeYonedaHomEquiv (α ≫ f) = freeYonedaHomEquiv α ≫ f.app (op X) := by
  simp [freeYonedaHomEquiv]

@[reassoc]
lemma freeYonedaHomEquiv_symm_comp {X : C} {M : A} {F G : Cᵒᵖ ⥤ A} (α : M ⟶ F.obj (op X))
    (f : F ⟶ G) :
    freeYonedaHomEquiv.symm α ≫ f = freeYonedaHomEquiv.symm (α ≫ f.app (op X)) := by
  obtain ⟨β, rfl⟩ := freeYonedaHomEquiv.surjective α
  apply freeYonedaHomEquiv.injective
  simp only [Equiv.symm_apply_apply, freeYonedaHomEquiv_comp, Equiv.apply_symm_apply]

variable (C)

lemma isSeparating {ι : Type w} {S : ι → A} (hS : IsSeparating (Set.range S)) :
    IsSeparating (Set.range (fun (⟨X, i⟩ : C × ι) ↦ freeYoneda X (S i))) := by
  intro F G f g h
  ext ⟨X⟩
  refine hS _ _ ?_
  rintro _ ⟨i, rfl⟩ α
  apply freeYonedaHomEquiv.symm.injective
  simpa only [freeYonedaHomEquiv_symm_comp] using
    h _ ⟨⟨X, i⟩, rfl⟩ (freeYonedaHomEquiv.symm α)

lemma isSeparator {ι : Type w} {S : ι → A} (hS : IsSeparating (Set.range S))
    [HasCoproduct (fun (⟨X, i⟩ : C × ι) ↦ freeYoneda X (S i))]
    [HasZeroMorphisms A] :
    IsSeparator (∐ (fun (⟨X, i⟩ : C × ι) ↦ freeYoneda X (S i))) :=
  (isSeparating C hS).isSeparator_coproduct

variable (A) in
instance hasSeparator [HasSeparator A] [HasZeroMorphisms A]
    [∀ (ι : Type u), HasCoproductsOfShape ι A] :
    HasSeparator (Cᵒᵖ ⥤ A) where
  hasSeparator := ⟨_, isSeparator C (S := fun (_ : Unit) ↦ separator A)
      (by simpa using isSeparator_separator A)⟩

end Presheaf

namespace Sheaf

variable {C : Type u} [Category.{v} C]
  (J : GrothendieckTopology C) {A : Type u'} [Category.{v'} A]
  [∀ (ι : Type v), HasCoproductsOfShape ι A]
  [HasWeakSheafify J A]

/-- Given `J : GrothendieckTopology C`, `X : C` and `M : A`, this is the associated
sheaf to the presheaf `Presheaf.freeYoneda X M`. -/
noncomputable def freeYoneda (X : C) (M : A) : Sheaf J A :=
  (presheafToSheaf J A).obj (Presheaf.freeYoneda X M)

variable {J} in
/-- The bijection `(Sheaf.freeYoneda J X M ⟶ F) ≃ (M ⟶ F.val.obj (op X))`
when `F : Sheaf J A`, `X : C` and `M : A`. -/
noncomputable def freeYonedaHomEquiv {X : C} {M : A} {F : Sheaf J A} :
    (freeYoneda J X M ⟶ F) ≃ (M ⟶ F.val.obj (op X)) :=
  ((sheafificationAdjunction J A).homEquiv _ _).trans Presheaf.freeYonedaHomEquiv

lemma isSeparating {ι : Type w} {S : ι → A} (hS : IsSeparating (Set.range S)) :
    IsSeparating (Set.range (fun (⟨X, i⟩ : C × ι) ↦ freeYoneda J X (S i))) := by
  intro F G f g hfg
  refine (sheafToPresheaf J A).map_injective ((Presheaf.isSeparating C hS) _ _ ?_)
  rintro _ ⟨⟨X, i⟩, rfl⟩ a
  dsimp at a
  apply ((sheafificationAdjunction _ _).homEquiv _ _).symm.injective
  simpa only [← Adjunction.homEquiv_naturality_right_symm] using
    hfg _ ⟨⟨X, i⟩, rfl⟩ (((sheafificationAdjunction _ _).homEquiv _ _).symm a)

lemma isSeparator {ι : Type w} {S : ι → A} (hS : IsSeparating (Set.range S))
    [HasCoproduct (fun (⟨X, i⟩ : C × ι) ↦ freeYoneda J X (S i))] [Preadditive A] :
    IsSeparator (∐ (fun (⟨X, i⟩ : C × ι) ↦ freeYoneda J X (S i))) :=
  (isSeparating J hS).isSeparator_coproduct

variable (A) in
instance hasSeparator [HasSeparator A] [Preadditive A]
    [∀ (ι : Type u), HasCoproductsOfShape ι A] :
    HasSeparator (Sheaf J A) where
  hasSeparator := ⟨_, isSeparator J (S := fun (_ : Unit) ↦ separator A)
      (by simpa using isSeparator_separator A)⟩

end Sheaf

end CategoryTheory
