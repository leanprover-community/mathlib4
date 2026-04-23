/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Generators in the category of presheaves

In this file, we show that if `A` is a category with zero morphisms that
has a separator (and suitable coproducts), then the category of
presheaves `Cᵒᵖ ⥤ A` also has a separator.

-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory

open Limits Opposite

namespace Presheaf

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasCoproducts.{v} A]

/-- Given `X : C` and `M : A`, this is the presheaf `Cᵒᵖ ⥤ A` which sends
`Y : Cᵒᵖ` to the coproduct of copies of `M` indexed by `Y.unop ⟶ X`. -/
@[simps]
noncomputable def freeYoneda (X : C) (M : A) : Cᵒᵖ ⥤ A where
  obj Y := ∐ (fun (i : (yoneda.obj X).obj Y) ↦ M)
  map f := Sigma.map' ((yoneda.obj X).map f) (fun _ ↦ 𝟙 M)

set_option backward.isDefEq.respectTransparency false in
/-- The bijection `(Presheaf.freeYoneda X M ⟶ F) ≃ (M ⟶ F.obj (op X))`. -/
noncomputable def freeYonedaHomEquiv {X : C} {M : A} {F : Cᵒᵖ ⥤ A} :
    (freeYoneda X M ⟶ F) ≃ (M ⟶ F.obj (op X)) where
  toFun f := Sigma.ι (fun (i : (yoneda.obj X).obj _) ↦ M) (𝟙 _) ≫ f.app (op X)
  invFun g :=
    { app Y := Sigma.desc (fun φ ↦ g ≫ F.map φ.op)
      naturality _ _ _ := Sigma.hom_ext _ _ (by simp) }
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
  apply freeYonedaHomEquiv.injective
  simp only [freeYonedaHomEquiv_comp, Equiv.apply_symm_apply]

variable (C)

lemma isSeparating {ι : Type w} {S : ι → A} (hS : ObjectProperty.IsSeparating (.ofObj S)) :
    ObjectProperty.IsSeparating (.ofObj (fun (⟨X, i⟩ : C × ι) ↦ freeYoneda X (S i))) := by
  intro F G f g h
  ext ⟨X⟩
  refine hS _ _ ?_
  rintro _ ⟨i⟩ α
  apply freeYonedaHomEquiv.symm.injective
  simpa only [freeYonedaHomEquiv_symm_comp] using
    h _ (ObjectProperty.ofObj_apply _ ⟨X, i⟩) (freeYonedaHomEquiv.symm α)

lemma isSeparator {ι : Type w} {S : ι → A} (hS : ObjectProperty.IsSeparating (.ofObj S))
    [HasCoproduct (fun (⟨X, i⟩ : C × ι) ↦ freeYoneda X (S i))]
    [HasZeroMorphisms A] :
    IsSeparator (∐ (fun (⟨X, i⟩ : C × ι) ↦ freeYoneda X (S i))) :=
  (isSeparating C hS).isSeparator_coproduct

variable (A) in
instance hasSeparator [HasSeparator A] [HasZeroMorphisms A] [HasCoproducts.{u} A] :
    HasSeparator (Cᵒᵖ ⥤ A) where
  hasSeparator := ⟨_, isSeparator C (S := fun (_ : Unit) ↦ separator A)
      (by simpa using isSeparator_separator A)⟩

end Presheaf

end CategoryTheory
