/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Adam Topaz
-/
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.TypesFiltered
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.Tactic.ApplyFun

#align_import category_theory.limits.concrete_category from "leanprover-community/mathlib"@"c3019c79074b0619edb4b27553a91b2e82242395"

/-!
# Facts about (co)limits of functors into concrete categories
-/


universe t w v u r

open CategoryTheory

namespace CategoryTheory.Limits

attribute [local instance] ConcreteCategory.instFunLike ConcreteCategory.hasCoeToSort

section Limits

/-- If a functor `G : J ⥤ C` to a concrete category has a limit and that `forget C`
is corepresentable, then `G ⋙ forget C).sections` is small. -/
lemma Concrete.small_sections_of_hasLimit
    {C : Type u} [Category.{v} C] [ConcreteCategory.{v} C]
    [(forget C).Corepresentable] {J : Type w} [Category.{t} J] (G : J ⥤ C) [HasLimit G] :
    Small.{v} (G ⋙ forget C).sections := by
  rw [← Types.hasLimit_iff_small_sections]
  infer_instance

variable {C : Type u} [Category.{v} C] [ConcreteCategory.{max w v} C] {J : Type w} [Category.{t} J]
  (F : J ⥤ C) [PreservesLimit F (forget C)]

theorem Concrete.to_product_injective_of_isLimit {D : Cone F} (hD : IsLimit D) :
    Function.Injective fun (x : D.pt) (j : J) => D.π.app j x := by
  let E := (forget C).mapCone D
  let hE : IsLimit E := isLimitOfPreserves _ hD
  let G := Types.limitCone.{w, v} (F ⋙ forget C)
  let hG := Types.limitConeIsLimit.{w, v} (F ⋙ forget C)
  let T : E.pt ≅ G.pt := hE.conePointUniqueUpToIso hG
  change Function.Injective (T.hom ≫ fun x j => G.π.app j x)
  have h : Function.Injective T.hom := by
    intro a b h
    suffices T.inv (T.hom a) = T.inv (T.hom b) by simpa
    rw [h]
  suffices Function.Injective fun (x : G.pt) j => G.π.app j x by exact this.comp h
  apply Subtype.ext
#align category_theory.limits.concrete.to_product_injective_of_is_limit CategoryTheory.Limits.Concrete.to_product_injective_of_isLimit

theorem Concrete.isLimit_ext {D : Cone F} (hD : IsLimit D) (x y : D.pt) :
    (∀ j, D.π.app j x = D.π.app j y) → x = y := fun h =>
  Concrete.to_product_injective_of_isLimit _ hD (funext h)
#align category_theory.limits.concrete.is_limit_ext CategoryTheory.Limits.Concrete.isLimit_ext

theorem Concrete.limit_ext [HasLimit F] (x y : ↑(limit F)) :
    (∀ j, limit.π F j x = limit.π F j y) → x = y :=
  Concrete.isLimit_ext F (limit.isLimit _) _ _
#align category_theory.limits.concrete.limit_ext CategoryTheory.Limits.Concrete.limit_ext

end Limits

section Colimits

section

variable {C : Type u} [Category.{v} C] [ConcreteCategory.{t} C] {J : Type w} [Category.{r} J]
  (F : J ⥤ C) [PreservesColimit F (forget C)]

theorem Concrete.from_union_surjective_of_isColimit {D : Cocone F} (hD : IsColimit D) :
    let ff : (Σj : J, F.obj j) → D.pt := fun a => D.ι.app a.1 a.2
    Function.Surjective ff := by
  intro ff x
  let E : Cocone (F ⋙ forget C) := (forget C).mapCocone D
  let hE : IsColimit E := isColimitOfPreserves (forget C) hD
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hE x
  exact ⟨⟨j, y⟩, hy⟩
#align category_theory.limits.concrete.from_union_surjective_of_is_colimit CategoryTheory.Limits.Concrete.from_union_surjective_of_isColimit

theorem Concrete.isColimit_exists_rep {D : Cocone F} (hD : IsColimit D) (x : D.pt) :
    ∃ (j : J) (y : F.obj j), D.ι.app j y = x := by
  obtain ⟨a, rfl⟩ := Concrete.from_union_surjective_of_isColimit F hD x
  exact ⟨a.1, a.2, rfl⟩
#align category_theory.limits.concrete.is_colimit_exists_rep CategoryTheory.Limits.Concrete.isColimit_exists_rep

theorem Concrete.colimit_exists_rep [HasColimit F] (x : ↑(colimit F)) :
    ∃ (j : J) (y : F.obj j), colimit.ι F j y = x :=
  Concrete.isColimit_exists_rep F (colimit.isColimit _) x
#align category_theory.limits.concrete.colimit_exists_rep CategoryTheory.Limits.Concrete.colimit_exists_rep

theorem Concrete.isColimit_rep_eq_of_exists {D : Cocone F} {i j : J} (x : F.obj i) (y : F.obj j)
    (h : ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y) :
    D.ι.app i x = D.ι.app j y := by
  let E := (forget C).mapCocone D
  obtain ⟨k, f, g, (hfg : (F ⋙ forget C).map f x = F.map g y)⟩ := h
  let h1 : (F ⋙ forget C).map f ≫ E.ι.app k = E.ι.app i := E.ι.naturality f
  let h2 : (F ⋙ forget C).map g ≫ E.ι.app k = E.ι.app j := E.ι.naturality g
  show E.ι.app i x = E.ι.app j y
  rw [← h1, types_comp_apply, hfg]
  exact congrFun h2 y
#align category_theory.limits.concrete.is_colimit_rep_eq_of_exists CategoryTheory.Limits.Concrete.isColimit_rep_eq_of_exists

theorem Concrete.colimit_rep_eq_of_exists [HasColimit F] {i j : J} (x : F.obj i) (y : F.obj j)
    (h : ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y) :
    colimit.ι F i x = colimit.ι F j y :=
  Concrete.isColimit_rep_eq_of_exists F x y h
#align category_theory.limits.concrete.colimit_rep_eq_of_exists CategoryTheory.Limits.Concrete.colimit_rep_eq_of_exists

end

section FilteredColimits

variable {C : Type u} [Category.{v} C] [ConcreteCategory.{max t w} C] {J : Type w} [Category.{r} J]
  (F : J ⥤ C) [PreservesColimit F (forget C)] [IsFiltered J]

theorem Concrete.isColimit_exists_of_rep_eq {D : Cocone F} {i j : J} (hD : IsColimit D)
    (x : F.obj i) (y : F.obj j) (h : D.ι.app _ x = D.ι.app _ y) :
    ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y := by
  let E := (forget C).mapCocone D
  let hE : IsColimit E := isColimitOfPreserves _ hD
  exact (Types.FilteredColimit.isColimit_eq_iff (F ⋙ forget C) hE).mp h
#align category_theory.limits.concrete.is_colimit_exists_of_rep_eq CategoryTheory.Limits.Concrete.isColimit_exists_of_rep_eq

theorem Concrete.isColimit_rep_eq_iff_exists {D : Cocone F} {i j : J} (hD : IsColimit D)
    (x : F.obj i) (y : F.obj j) :
    D.ι.app i x = D.ι.app j y ↔ ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y :=
  ⟨Concrete.isColimit_exists_of_rep_eq.{t} _ hD _ _,
   Concrete.isColimit_rep_eq_of_exists _ _ _⟩
#align category_theory.limits.concrete.is_colimit_rep_eq_iff_exists CategoryTheory.Limits.Concrete.isColimit_rep_eq_iff_exists

theorem Concrete.colimit_exists_of_rep_eq [HasColimit F] {i j : J} (x : F.obj i) (y : F.obj j)
    (h : colimit.ι F _ x = colimit.ι F _ y) :
    ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y :=
  Concrete.isColimit_exists_of_rep_eq.{t} F (colimit.isColimit _) x y h
#align category_theory.limits.concrete.colimit_exists_of_rep_eq CategoryTheory.Limits.Concrete.colimit_exists_of_rep_eq

theorem Concrete.colimit_rep_eq_iff_exists [HasColimit F] {i j : J} (x : F.obj i) (y : F.obj j) :
    colimit.ι F i x = colimit.ι F j y ↔ ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y :=
  ⟨Concrete.colimit_exists_of_rep_eq.{t} _ _ _, Concrete.colimit_rep_eq_of_exists _ _ _⟩
#align category_theory.limits.concrete.colimit_rep_eq_iff_exists CategoryTheory.Limits.Concrete.colimit_rep_eq_iff_exists

end FilteredColimits

end Colimits

end CategoryTheory.Limits
