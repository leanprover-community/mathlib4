/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Adam Topaz
-/
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.Tactic.ApplyFun

#align_import category_theory.limits.concrete_category from "leanprover-community/mathlib"@"c3019c79074b0619edb4b27553a91b2e82242395"

/-!
# Facts about (co)limits of functors into concrete categories
-/


universe w v u

open CategoryTheory

namespace CategoryTheory.Limits

attribute [local instance] ConcreteCategory.funLike ConcreteCategory.hasCoeToSort

section Limits

variable {C : Type u} [Category.{v} C] [ConcreteCategory.{max w v} C] {J : Type w} [SmallCategory J]
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

variable {C : Type u} [Category.{v} C] [ConcreteCategory.{v} C] {J : Type v} [SmallCategory J]
  (F : J ⥤ C) [PreservesColimit F (forget C)]

theorem Concrete.from_union_surjective_of_isColimit {D : Cocone F} (hD : IsColimit D) :
    let ff : (Σj : J, F.obj j) → D.pt := fun a => D.ι.app a.1 a.2
    Function.Surjective ff := by
  intro ff
  let E := (forget C).mapCocone D
  let hE : IsColimit E := isColimitOfPreserves _ hD
  let G := Types.colimitCocone.{v, v} (F ⋙ forget C)
  let hG := Types.colimitCoconeIsColimit.{v, v} (F ⋙ forget C)
  let T : E ≅ G := hE.uniqueUpToIso hG
  let TX : E.pt ≅ G.pt := (Cocones.forget _).mapIso T
  suffices Function.Surjective (TX.hom ∘ ff) by
    intro a
    obtain ⟨b, hb⟩ := this (TX.hom a)
    refine' ⟨b, _⟩
    apply_fun TX.inv at hb
    change (TX.hom ≫ TX.inv) (ff b) = (TX.hom ≫ TX.inv) _ at hb
    simpa only [TX.hom_inv_id] using hb
  have : TX.hom ∘ ff = fun a => G.ι.app a.1 a.2 := by
    ext a
    change (E.ι.app a.1 ≫ hE.desc G) a.2 = _
    rw [hE.fac]
  rw [this]
  rintro ⟨⟨j, a⟩⟩
  exact ⟨⟨j, a⟩, rfl⟩
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

theorem Concrete.isColimit_rep_eq_of_exists {D : Cocone F} {i j : J} (hD : IsColimit D)
    (x : F.obj i) (y : F.obj j) (h : ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y) :
    D.ι.app i x = D.ι.app j y := by
  let E := (forget C).mapCocone D
  let hE : IsColimit E := isColimitOfPreserves _ hD
  let G := Types.colimitCocone.{v, v} (F ⋙ forget C)
  let hG := Types.colimitCoconeIsColimit.{v, v} (F ⋙ forget C)
  let T : E ≅ G := hE.uniqueUpToIso hG
  let TX : E.pt ≅ G.pt := (Cocones.forget _).mapIso T
  apply_fun TX.hom using injective_of_mono TX.hom
  change (E.ι.app i ≫ TX.hom) x = (E.ι.app j ≫ TX.hom) y
  erw [T.hom.w, T.hom.w]
  obtain ⟨k, f, g, h⟩ := h
  have : G.ι.app i x = (G.ι.app k (F.map f x) : G.pt) := Quot.sound ⟨f, rfl⟩
  rw [this, h]
  symm
  exact Quot.sound ⟨g, rfl⟩
#align category_theory.limits.concrete.is_colimit_rep_eq_of_exists CategoryTheory.Limits.Concrete.isColimit_rep_eq_of_exists

theorem Concrete.colimit_rep_eq_of_exists [HasColimit F] {i j : J} (x : F.obj i) (y : F.obj j)
    (h : ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y) :
    colimit.ι F i x = colimit.ι F j y :=
  Concrete.isColimit_rep_eq_of_exists F (colimit.isColimit _) x y h
#align category_theory.limits.concrete.colimit_rep_eq_of_exists CategoryTheory.Limits.Concrete.colimit_rep_eq_of_exists

section FilteredColimits

variable [IsFiltered J]

theorem Concrete.isColimit_exists_of_rep_eq {D : Cocone F} {i j : J} (hD : IsColimit D)
    (x : F.obj i) (y : F.obj j) (h : D.ι.app _ x = D.ι.app _ y) :
    ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y := by
  let E := (forget C).mapCocone D
  let hE : IsColimit E := isColimitOfPreserves _ hD
  let G := Types.colimitCocone.{v, v} (F ⋙ forget C)
  let hG := Types.colimitCoconeIsColimit.{v, v} (F ⋙ forget C)
  let T : E ≅ G := hE.uniqueUpToIso hG
  let TX : E.pt ≅ G.pt := (Cocones.forget _).mapIso T
  apply_fun TX.hom at h
  change (E.ι.app i ≫ TX.hom) x = (E.ι.app j ≫ TX.hom) y at h
  erw [T.hom.w, T.hom.w] at h
  replace h := Quot.exact _ h
  suffices
    ∀ (a b : Σj, F.obj j) (_ : EqvGen (Limits.Types.Quot.Rel.{v, v} (F ⋙ forget C)) a b),
      ∃ (k : _) (f : a.1 ⟶ k) (g : b.1 ⟶ k), F.map f a.2 = F.map g b.2
    by exact this ⟨i, x⟩ ⟨j, y⟩ h
  intro a b h
  induction h
  case rel x y hh =>
    obtain ⟨e, he⟩ := hh
    use y.1, e, 𝟙 _
    simpa using he.symm
  case refl x =>
    exact ⟨x.1, 𝟙 _, 𝟙 _, rfl⟩
  case symm x y _ hh =>
    obtain ⟨k, f, g, hh⟩ := hh
    exact ⟨k, g, f, hh.symm⟩
  case trans x y z _ _ hh1 hh2 =>
    obtain ⟨k1, f1, g1, h1⟩ := hh1
    obtain ⟨k2, f2, g2, h2⟩ := hh2
    let k0 : J := IsFiltered.max k1 k2
    let e1 : k1 ⟶ k0 := IsFiltered.leftToMax _ _
    let e2 : k2 ⟶ k0 := IsFiltered.rightToMax _ _
    let k : J := IsFiltered.coeq (g1 ≫ e1) (f2 ≫ e2)
    let e : k0 ⟶ k := IsFiltered.coeqHom _ _
    use k, f1 ≫ e1 ≫ e, g2 ≫ e2 ≫ e
    simp only [F.map_comp, comp_apply, h1, ← h2]
    simp only [← comp_apply, ← F.map_comp]
    rw [IsFiltered.coeq_condition]
#align category_theory.limits.concrete.is_colimit_exists_of_rep_eq CategoryTheory.Limits.Concrete.isColimit_exists_of_rep_eq

theorem Concrete.isColimit_rep_eq_iff_exists {D : Cocone F} {i j : J} (hD : IsColimit D)
    (x : F.obj i) (y : F.obj j) :
    D.ι.app i x = D.ι.app j y ↔ ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y :=
  ⟨Concrete.isColimit_exists_of_rep_eq _ hD _ _, Concrete.isColimit_rep_eq_of_exists _ hD _ _⟩
#align category_theory.limits.concrete.is_colimit_rep_eq_iff_exists CategoryTheory.Limits.Concrete.isColimit_rep_eq_iff_exists

theorem Concrete.colimit_exists_of_rep_eq [HasColimit F] {i j : J} (x : F.obj i) (y : F.obj j)
    (h : colimit.ι F _ x = colimit.ι F _ y) :
    ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y :=
  Concrete.isColimit_exists_of_rep_eq F (colimit.isColimit _) x y h
#align category_theory.limits.concrete.colimit_exists_of_rep_eq CategoryTheory.Limits.Concrete.colimit_exists_of_rep_eq

theorem Concrete.colimit_rep_eq_iff_exists [HasColimit F] {i j : J} (x : F.obj i) (y : F.obj j) :
    colimit.ι F i x = colimit.ι F j y ↔ ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y :=
  ⟨Concrete.colimit_exists_of_rep_eq _ _ _, Concrete.colimit_rep_eq_of_exists _ _ _⟩
#align category_theory.limits.concrete.colimit_rep_eq_iff_exists CategoryTheory.Limits.Concrete.colimit_rep_eq_iff_exists

end FilteredColimits

end Colimits

end CategoryTheory.Limits
