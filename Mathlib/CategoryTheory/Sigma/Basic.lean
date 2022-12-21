/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.sigma.basic
! leanprover-community/mathlib commit ba2245edf0c8bb155f1569fd9b9492a9b384cde6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Whiskering
import Mathbin.CategoryTheory.Functor.FullyFaithful
import Mathbin.CategoryTheory.NaturalIsomorphism

/-!
# Disjoint union of categories

We define the category structure on a sigma-type (disjoint union) of categories.
-/


namespace CategoryTheory

namespace Sigma

universe w₁ w₂ w₃ v₁ v₂ u₁ u₂

variable {I : Type w₁} {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]

/-- The type of morphisms of a disjoint union of categories: for `X : C i` and `Y : C j`, a morphism
`(i, X) ⟶ (j, Y)` if `i = j` is just a morphism `X ⟶ Y`, and if `i ≠ j` there are no such morphisms.
-/
inductive SigmaHom : (Σi, C i) → (Σi, C i) → Type max w₁ v₁ u₁
  | mk : ∀ {i : I} {X Y : C i}, (X ⟶ Y) → sigma_hom ⟨i, X⟩ ⟨i, Y⟩
#align category_theory.sigma.sigma_hom CategoryTheory.Sigma.SigmaHom

namespace SigmaHom

/- warning: category_theory.sigma.sigma_hom.id -> CategoryTheory.Sigma.SigmaHom.id is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {C : I -> Type.{u3}} [_inst_1 : forall (i : I), CategoryTheory.Category.{u2, u3} (C i)] (X : Sigma.{u1, u3} I (fun (i : I) => C i)), CategoryTheory.Sigma.SigmaHom.{u1, u2, u3} I (fun (i : I) => C i) (fun (i : I) => _inst_1 i) X X
but is expected to have type
  forall {I : Type.{u3}} {C : I -> Type.{u1}} [_inst_1 : forall (i : I), CategoryTheory.Category.{u2, u1} (C i)] (X : Sigma.{u3, u1} I (fun (i : I) => C i)), CategoryTheory.Sigma.SigmaHom.{u3, u2, u1} I (fun (i : I) => C i) (fun (i : I) => _inst_1 i) X X
Case conversion may be inaccurate. Consider using '#align category_theory.sigma.sigma_hom.id CategoryTheory.Sigma.SigmaHom.idₓ'. -/
/-- The identity morphism on an object. -/
def id : ∀ X : Σi, C i, SigmaHom X X
  | ⟨i, X⟩ => mk (𝟙 _)
#align category_theory.sigma.sigma_hom.id CategoryTheory.Sigma.SigmaHom.id

instance (X : Σi, C i) : Inhabited (SigmaHom X X) :=
  ⟨id X⟩

/- warning: category_theory.sigma.sigma_hom.comp -> CategoryTheory.Sigma.SigmaHom.comp is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {C : I -> Type.{u3}} [_inst_1 : forall (i : I), CategoryTheory.Category.{u2, u3} (C i)] {X : Sigma.{u1, u3} I (fun (i : I) => C i)} {Y : Sigma.{u1, u3} I (fun (i : I) => C i)} {Z : Sigma.{u1, u3} I (fun (i : I) => C i)}, (CategoryTheory.Sigma.SigmaHom.{u1, u2, u3} I (fun (i : I) => C i) (fun (i : I) => _inst_1 i) X Y) -> (CategoryTheory.Sigma.SigmaHom.{u1, u2, u3} I (fun (i : I) => C i) (fun (i : I) => _inst_1 i) Y Z) -> (CategoryTheory.Sigma.SigmaHom.{u1, u2, u3} I (fun (i : I) => C i) (fun (i : I) => _inst_1 i) X Z)
but is expected to have type
  forall {I : Type.{u3}} {C : I -> Type.{u1}} [_inst_1 : forall (i : I), CategoryTheory.Category.{u2, u1} (C i)] {X : Sigma.{u3, u1} I (fun (i : I) => C i)} {Y : Sigma.{u3, u1} I (fun (i : I) => C i)} {Z : Sigma.{u3, u1} I (fun (i : I) => C i)}, (CategoryTheory.Sigma.SigmaHom.{u3, u2, u1} I (fun (i : I) => C i) (fun (i : I) => _inst_1 i) X Y) -> (CategoryTheory.Sigma.SigmaHom.{u3, u2, u1} I (fun (i : I) => C i) (fun (i : I) => _inst_1 i) Y Z) -> (CategoryTheory.Sigma.SigmaHom.{u3, u2, u1} I (fun (i : I) => C i) (fun (i : I) => _inst_1 i) X Z)
Case conversion may be inaccurate. Consider using '#align category_theory.sigma.sigma_hom.comp CategoryTheory.Sigma.SigmaHom.compₓ'. -/
/-- Composition of sigma homomorphisms. -/
def comp : ∀ {X Y Z : Σi, C i}, SigmaHom X Y → SigmaHom Y Z → SigmaHom X Z
  | _, _, _, mk f, mk g => mk (f ≫ g)
#align category_theory.sigma.sigma_hom.comp CategoryTheory.Sigma.SigmaHom.comp

instance : CategoryStruct (Σi, C i) where 
  Hom := SigmaHom
  id := id
  comp X Y Z f g := comp f g

@[simp]
theorem comp_def (i : I) (X Y Z : C i) (f : X ⟶ Y) (g : Y ⟶ Z) : comp (mk f) (mk g) = mk (f ≫ g) :=
  rfl
#align category_theory.sigma.sigma_hom.comp_def CategoryTheory.Sigma.SigmaHom.comp_def

theorem assoc : ∀ (X Y Z W : Σi, C i) (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W), (f ≫ g) ≫ h = f ≫ g ≫ h
  | _, _, _, _, mk f, mk g, mk h => congr_arg mk (Category.assoc _ _ _)
#align category_theory.sigma.sigma_hom.assoc CategoryTheory.Sigma.SigmaHom.assoc

theorem id_comp : ∀ (X Y : Σi, C i) (f : X ⟶ Y), 𝟙 X ≫ f = f
  | _, _, mk f => congr_arg mk (Category.id_comp _)
#align category_theory.sigma.sigma_hom.id_comp CategoryTheory.Sigma.SigmaHom.id_comp

theorem comp_id : ∀ (X Y : Σi, C i) (f : X ⟶ Y), f ≫ 𝟙 Y = f
  | _, _, mk f => congr_arg mk (Category.comp_id _)
#align category_theory.sigma.sigma_hom.comp_id CategoryTheory.Sigma.SigmaHom.comp_id

end SigmaHom

instance sigma : Category (Σi,
        C i) where 
  id_comp' := SigmaHom.id_comp
  comp_id' := SigmaHom.comp_id
  assoc' := SigmaHom.assoc
#align category_theory.sigma.sigma CategoryTheory.Sigma.sigma

/-- The inclusion functor into the disjoint union of categories. -/
@[simps map]
def incl (i : I) : C i ⥤ Σi, C i where 
  obj X := ⟨i, X⟩
  map X Y := SigmaHom.mk
#align category_theory.sigma.incl CategoryTheory.Sigma.incl

@[simp]
theorem incl_obj {i : I} (X : C i) : (incl i).obj X = ⟨i, X⟩ :=
  rfl
#align category_theory.sigma.incl_obj CategoryTheory.Sigma.incl_obj

instance (i : I) :
    Full (incl i : C i ⥤ Σi,
            C i) where 
  preimage := fun X Y ⟨f⟩ => f
  witness' := fun X Y ⟨f⟩ => rfl

instance (i : I) : Faithful (incl i : C i ⥤ Σi, C i) where

section

variable {D : Type u₂} [Category.{v₂} D] (F : ∀ i, C i ⥤ D)

/--
To build a natural transformation over the sigma category, it suffices to specify it restricted to
each subcategory.
-/
def natTrans {F G : (Σi, C i) ⥤ D} (h : ∀ i : I, incl i ⋙ F ⟶ incl i ⋙ G) :
    F ⟶ G where 
  app := fun ⟨j, X⟩ => (h j).app X
  naturality' := by 
    rintro ⟨j, X⟩ ⟨_, _⟩ ⟨f⟩
    apply (h j).naturality
#align category_theory.sigma.nat_trans CategoryTheory.Sigma.natTrans

@[simp]
theorem nat_trans_app {F G : (Σi, C i) ⥤ D} (h : ∀ i : I, incl i ⋙ F ⟶ incl i ⋙ G) (i : I)
    (X : C i) : (natTrans h).app ⟨i, X⟩ = (h i).app X :=
  rfl
#align category_theory.sigma.nat_trans_app CategoryTheory.Sigma.nat_trans_app

/- warning: category_theory.sigma.desc_map -> CategoryTheory.Sigma.descMap is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {C : I -> Type.{u4}} [_inst_1 : forall (i : I), CategoryTheory.Category.{u2, u4} (C i)] {D : Type.{u5}} [_inst_2 : CategoryTheory.Category.{u3, u5} D] (F : forall (i : I), CategoryTheory.Functor.{u2, u3, u4, u5} (C i) (_inst_1 i) D _inst_2) (X : Sigma.{u1, u4} I (fun (i : I) => C i)) (Y : Sigma.{u1, u4} I (fun (i : I) => C i)), (Quiver.Hom.{succ (max u1 u2 u4), max u1 u4} (Sigma.{u1, u4} I (fun (i : I) => C i)) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2 u4, max u1 u4} (Sigma.{u1, u4} I (fun (i : I) => C i)) (CategoryTheory.Sigma.SigmaHom.Sigma.CategoryTheory.categoryStruct.{u1, u2, u4} I (fun (i : I) => C i) (fun (i : I) => _inst_1 i))) X Y) -> (Quiver.Hom.{succ u3, u5} D (CategoryTheory.CategoryStruct.toQuiver.{u3, u5} D (CategoryTheory.Category.toCategoryStruct.{u3, u5} D _inst_2)) (CategoryTheory.Functor.obj.{u2, u3, u4, u5} (C (Sigma.fst.{u1, u4} I (fun (i : I) => C i) X)) (_inst_1 (Sigma.fst.{u1, u4} I (fun (i : I) => C i) X)) D _inst_2 (F (Sigma.fst.{u1, u4} I (fun (i : I) => C i) X)) (Sigma.snd.{u1, u4} I (fun (i : I) => C i) X)) (CategoryTheory.Functor.obj.{u2, u3, u4, u5} (C (Sigma.fst.{u1, u4} I (fun (i : I) => C i) Y)) (_inst_1 (Sigma.fst.{u1, u4} I (fun (i : I) => C i) Y)) D _inst_2 (F (Sigma.fst.{u1, u4} I (fun (i : I) => C i) Y)) (Sigma.snd.{u1, u4} I (fun (i : I) => C i) Y)))
but is expected to have type
  forall {I : Type.{u5}} {C : I -> Type.{u1}} [_inst_1 : forall (i : I), CategoryTheory.Category.{u3, u1} (C i)] {D : Type.{u2}} [_inst_2 : CategoryTheory.Category.{u4, u2} D] (F : forall (i : I), CategoryTheory.Functor.{u3, u4, u1, u2} (C i) (_inst_1 i) D _inst_2) (X : Sigma.{u5, u1} I (fun (i : I) => C i)) (Y : Sigma.{u5, u1} I (fun (i : I) => C i)), (Quiver.Hom.{succ (max u5 u3 u1), max u5 u1} (Sigma.{u5, u1} I (fun (i : I) => C i)) (CategoryTheory.CategoryStruct.toQuiver.{max u5 u3 u1, max u5 u1} (Sigma.{u5, u1} I (fun (i : I) => C i)) (CategoryTheory.Sigma.SigmaHom.Sigma.CategoryTheory.categoryStruct.{u5, u3, u1} I (fun (i : I) => C i) (fun (i : I) => _inst_1 i))) X Y) -> (Quiver.Hom.{succ u4, u2} D (CategoryTheory.CategoryStruct.toQuiver.{u4, u2} D (CategoryTheory.Category.toCategoryStruct.{u4, u2} D _inst_2)) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} (C (Sigma.fst.{u5, u1} I (fun (i : I) => C i) X)) (_inst_1 (Sigma.fst.{u5, u1} I (fun (i : I) => C i) X)) D _inst_2 (F (Sigma.fst.{u5, u1} I (fun (i : I) => C i) X)) (Sigma.snd.{u5, u1} I (fun (i : I) => C i) X)) (CategoryTheory.Functor.obj.{u3, u4, u1, u2} (C (Sigma.fst.{u5, u1} I (fun (i : I) => C i) Y)) (_inst_1 (Sigma.fst.{u5, u1} I (fun (i : I) => C i) Y)) D _inst_2 (F (Sigma.fst.{u5, u1} I (fun (i : I) => C i) Y)) (Sigma.snd.{u5, u1} I (fun (i : I) => C i) Y)))
Case conversion may be inaccurate. Consider using '#align category_theory.sigma.desc_map CategoryTheory.Sigma.descMapₓ'. -/
/-- (Implementation). An auxiliary definition to build the functor `desc`. -/
def descMap : ∀ X Y : Σi, C i, (X ⟶ Y) → ((F X.1).obj X.2 ⟶ (F Y.1).obj Y.2)
  | _, _, sigma_hom.mk g => (F _).map g
#align category_theory.sigma.desc_map CategoryTheory.Sigma.descMap

/-- Given a collection of functors `F i : C i ⥤ D`, we can produce a functor `(Σ i, C i) ⥤ D`.

The produced functor `desc F` satisfies: `incl i ⋙ desc F ≅ F i`, i.e. restricted to just the
subcategory `C i`, `desc F` agrees with `F i`, and it is unique (up to natural isomorphism) with
this property.

This witnesses that the sigma-type is the coproduct in Cat.
-/
@[simps obj]
def desc : (Σi, C i) ⥤ D where 
  obj X := (F X.1).obj X.2
  map X Y g := descMap F X Y g
  map_id' := by 
    rintro ⟨i, X⟩
    apply (F i).map_id
  map_comp' := by 
    rintro ⟨i, X⟩ ⟨_, Y⟩ ⟨_, Z⟩ ⟨f⟩ ⟨g⟩
    apply (F i).map_comp
#align category_theory.sigma.desc CategoryTheory.Sigma.desc

@[simp]
theorem desc_map_mk {i : I} (X Y : C i) (f : X ⟶ Y) : (desc F).map (SigmaHom.mk f) = (F i).map f :=
  rfl
#align category_theory.sigma.desc_map_mk CategoryTheory.Sigma.desc_map_mk

-- We hand-generate the simp lemmas about this since they come out cleaner.
/-- This shows that when `desc F` is restricted to just the subcategory `C i`, `desc F` agrees with
`F i`.
-/
def inclDesc (i : I) : incl i ⋙ desc F ≅ F i :=
  NatIso.ofComponents (fun X => Iso.refl _) (by tidy)
#align category_theory.sigma.incl_desc CategoryTheory.Sigma.inclDesc

@[simp]
theorem incl_desc_hom_app (i : I) (X : C i) : (inclDesc F i).Hom.app X = 𝟙 ((F i).obj X) :=
  rfl
#align category_theory.sigma.incl_desc_hom_app CategoryTheory.Sigma.incl_desc_hom_app

@[simp]
theorem incl_desc_inv_app (i : I) (X : C i) : (inclDesc F i).inv.app X = 𝟙 ((F i).obj X) :=
  rfl
#align category_theory.sigma.incl_desc_inv_app CategoryTheory.Sigma.incl_desc_inv_app

/-- If `q` when restricted to each subcategory `C i` agrees with `F i`, then `q` is isomorphic to
`desc F`.
-/
def descUniq (q : (Σi, C i) ⥤ D) (h : ∀ i, incl i ⋙ q ≅ F i) : q ≅ desc F :=
  (NatIso.ofComponents fun ⟨i, X⟩ => (h i).app X) <| by
    rintro ⟨i, X⟩ ⟨_, _⟩ ⟨f⟩
    apply (h i).Hom.naturality f
#align category_theory.sigma.desc_uniq CategoryTheory.Sigma.descUniq

@[simp]
theorem desc_uniq_hom_app (q : (Σi, C i) ⥤ D) (h : ∀ i, incl i ⋙ q ≅ F i) (i : I) (X : C i) :
    (descUniq F q h).Hom.app ⟨i, X⟩ = (h i).Hom.app X :=
  rfl
#align category_theory.sigma.desc_uniq_hom_app CategoryTheory.Sigma.desc_uniq_hom_app

@[simp]
theorem desc_uniq_inv_app (q : (Σi, C i) ⥤ D) (h : ∀ i, incl i ⋙ q ≅ F i) (i : I) (X : C i) :
    (descUniq F q h).inv.app ⟨i, X⟩ = (h i).inv.app X :=
  rfl
#align category_theory.sigma.desc_uniq_inv_app CategoryTheory.Sigma.desc_uniq_inv_app

/--
If `q₁` and `q₂` when restricted to each subcategory `C i` agree, then `q₁` and `q₂` are isomorphic.
-/
@[simps]
def natIso {q₁ q₂ : (Σi, C i) ⥤ D} (h : ∀ i, incl i ⋙ q₁ ≅ incl i ⋙ q₂) :
    q₁ ≅ q₂ where 
  Hom := natTrans fun i => (h i).Hom
  inv := natTrans fun i => (h i).inv
#align category_theory.sigma.nat_iso CategoryTheory.Sigma.natIso

end

section

variable (C) {J : Type w₂} (g : J → I)

/-- A function `J → I` induces a functor `Σ j, C (g j) ⥤ Σ i, C i`. -/
def map : (Σj : J, C (g j)) ⥤ Σi : I, C i :=
  desc fun j => incl (g j)
#align category_theory.sigma.map CategoryTheory.Sigma.map

@[simp]
theorem map_obj (j : J) (X : C (g j)) : (Sigma.map C g).obj ⟨j, X⟩ = ⟨g j, X⟩ :=
  rfl
#align category_theory.sigma.map_obj CategoryTheory.Sigma.map_obj

@[simp]
theorem map_map {j : J} {X Y : C (g j)} (f : X ⟶ Y) :
    (Sigma.map C g).map (SigmaHom.mk f) = SigmaHom.mk f :=
  rfl
#align category_theory.sigma.map_map CategoryTheory.Sigma.map_map

/-- The functor `sigma.map C g` restricted to the subcategory `C j` acts as the inclusion of `g j`.
-/
@[simps]
def inclCompMap (j : J) : incl j ⋙ map C g ≅ incl (g j) :=
  Iso.refl _
#align category_theory.sigma.incl_comp_map CategoryTheory.Sigma.inclCompMap

variable (I)

/-- The functor `sigma.map` applied to the identity function is just the identity functor. -/
@[simps]
def mapId : map C (id : I → I) ≅ 𝟭 (Σi, C i) :=
  natIso fun i => NatIso.ofComponents (fun X => Iso.refl _) (by tidy)
#align category_theory.sigma.map_id CategoryTheory.Sigma.mapId

variable {I} {K : Type w₃}

/-- The functor `sigma.map` applied to a composition is a composition of functors. -/
@[simps]
def mapComp (f : K → J) (g : J → I) : map (C ∘ g) f ⋙ (map C g : _) ≅ map C (g ∘ f) :=
  (descUniq _ _) fun k =>
    (isoWhiskerRight (inclCompMap (C ∘ g) f k) (map C g : _) : _) ≪≫ inclCompMap _ _ _
#align category_theory.sigma.map_comp CategoryTheory.Sigma.mapComp

end

namespace Functor

variable {C}

variable {D : I → Type u₁} [∀ i, Category.{v₁} (D i)]

/-- Assemble an `I`-indexed family of functors into a functor between the sigma types.
-/
def sigma (F : ∀ i, C i ⥤ D i) : (Σi, C i) ⥤ Σi, D i :=
  desc fun i => F i ⋙ incl i
#align category_theory.sigma.functor.sigma CategoryTheory.Sigma.Functor.sigma

end Functor

namespace NatTrans

variable {C}

variable {D : I → Type u₁} [∀ i, Category.{v₁} (D i)]

variable {F G : ∀ i, C i ⥤ D i}

/-- Assemble an `I`-indexed family of natural transformations into a single natural transformation.
-/
def sigma (α : ∀ i, F i ⟶ G i) :
    Functor.sigma F ⟶
      Functor.sigma G where 
  app f := SigmaHom.mk ((α f.1).app _)
  naturality' := by 
    rintro ⟨i, X⟩ ⟨_, _⟩ ⟨f⟩
    change sigma_hom.mk _ = sigma_hom.mk _
    rw [(α i).naturality]
#align category_theory.sigma.nat_trans.sigma CategoryTheory.Sigma.natTrans.sigma

end NatTrans

end Sigma

end CategoryTheory

