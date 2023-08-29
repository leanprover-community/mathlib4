/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.NatIso

#align_import category_theory.sigma.basic from "leanprover-community/mathlib"@"ba2245edf0c8bb155f1569fd9b9492a9b384cde6"

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
  | mk : ∀ {i : I} {X Y : C i}, (X ⟶ Y) → SigmaHom ⟨i, X⟩ ⟨i, Y⟩
#align category_theory.sigma.sigma_hom CategoryTheory.Sigma.SigmaHom

namespace SigmaHom

/-- The identity morphism on an object. -/
def id : ∀ X : Σi, C i, SigmaHom X X
  | ⟨_, _⟩ => mk (𝟙 _)
-- Porting note: reordered universes
#align category_theory.sigma.sigma_hom.id CategoryTheory.Sigma.SigmaHom.idₓ

instance (X : Σi, C i) : Inhabited (SigmaHom X X) :=
  ⟨id X⟩

/-- Composition of sigma homomorphisms. -/
def comp : ∀ {X Y Z : Σi, C i}, SigmaHom X Y → SigmaHom Y Z → SigmaHom X Z
  | _, _, _, mk f, mk g => mk (f ≫ g)
-- Porting note: reordered universes
#align category_theory.sigma.sigma_hom.comp CategoryTheory.Sigma.SigmaHom.compₓ

instance : CategoryStruct (Σi, C i) where
  Hom := SigmaHom
  id := id
  comp f g := comp f g

@[simp]
lemma comp_def (i : I) (X Y Z : C i) (f : X ⟶ Y) (g : Y ⟶ Z) : comp (mk f) (mk g) = mk (f ≫ g) :=
  rfl
#align category_theory.sigma.sigma_hom.comp_def CategoryTheory.Sigma.SigmaHom.comp_def

lemma assoc
  : ∀ {X Y Z W : Σi, C i} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W), (f ≫ g) ≫ h = f ≫ g ≫ h
  | _, _, _, _, mk _, mk _, mk _ => congr_arg mk (Category.assoc _ _ _)
#align category_theory.sigma.sigma_hom.assoc CategoryTheory.Sigma.SigmaHom.assoc

lemma id_comp : ∀ {X Y : Σi, C i} (f : X ⟶ Y), 𝟙 X ≫ f = f
  | _, _, mk _ => congr_arg mk (Category.id_comp _)
#align category_theory.sigma.sigma_hom.id_comp CategoryTheory.Sigma.SigmaHom.id_comp

lemma comp_id : ∀ {X Y : Σi, C i} (f : X ⟶ Y), f ≫ 𝟙 Y = f
  | _, _, mk _ => congr_arg mk (Category.comp_id _)
#align category_theory.sigma.sigma_hom.comp_id CategoryTheory.Sigma.SigmaHom.comp_id

end SigmaHom

instance sigma : Category (Σi, C i) where
  id_comp := SigmaHom.id_comp
  comp_id := SigmaHom.comp_id
  assoc := SigmaHom.assoc
#align category_theory.sigma.sigma CategoryTheory.Sigma.sigma

/-- The inclusion functor into the disjoint union of categories. -/
@[simps map]
def incl (i : I) : C i ⥤ Σi, C i where
  obj X := ⟨i, X⟩
  map := SigmaHom.mk
#align category_theory.sigma.incl CategoryTheory.Sigma.incl

@[simp]
lemma incl_obj {i : I} (X : C i) : (incl i).obj X = ⟨i, X⟩ :=
  rfl
#align category_theory.sigma.incl_obj CategoryTheory.Sigma.incl_obj

instance (i : I) : Full (incl i : C i ⥤ Σi, C i) where
  preimage := fun ⟨f⟩ => f
  witness := fun ⟨_⟩ => rfl

instance (i : I) : Faithful (incl i : C i ⥤ Σi, C i) where
  -- Porting note: was `tidy`
  map_injective {_ _ _ _} h := by injection h
                                  -- 🎉 no goals

section

variable {D : Type u₂} [Category.{v₂} D] (F : ∀ i, C i ⥤ D)

/--
To build a natural transformation over the sigma category, it suffices to specify it restricted to
each subcategory.
-/
def natTrans {F G : (Σi, C i) ⥤ D} (h : ∀ i : I, incl i ⋙ F ⟶ incl i ⋙ G) : F ⟶ G where
  app := fun ⟨j, X⟩ => (h j).app X
  naturality := by
    rintro ⟨j, X⟩ ⟨_, _⟩ ⟨f⟩
    -- ⊢ F.map (SigmaHom.mk f) ≫
    apply (h j).naturality
    -- 🎉 no goals
#align category_theory.sigma.nat_trans CategoryTheory.Sigma.natTrans

@[simp]
lemma natTrans_app {F G : (Σi, C i) ⥤ D} (h : ∀ i : I, incl i ⋙ F ⟶ incl i ⋙ G) (i : I)
    (X : C i) : (natTrans h).app ⟨i, X⟩ = (h i).app X :=
  rfl
#align category_theory.sigma.nat_trans_app CategoryTheory.Sigma.natTrans_app

/-- (Implementation). An auxiliary definition to build the functor `desc`. -/
def descMap : ∀ X Y : Σi, C i, (X ⟶ Y) → ((F X.1).obj X.2 ⟶ (F Y.1).obj Y.2)
  | _, _, SigmaHom.mk g => (F _).map g
-- Porting note: reordered universes
#align category_theory.sigma.desc_map CategoryTheory.Sigma.descMapₓ

/-- Given a collection of functors `F i : C i ⥤ D`, we can produce a functor `(Σ i, C i) ⥤ D`.

The produced functor `desc F` satisfies: `incl i ⋙ desc F ≅ F i`, i.e. restricted to just the
subcategory `C i`, `desc F` agrees with `F i`, and it is unique (up to natural isomorphism) with
this property.

This witnesses that the sigma-type is the coproduct in Cat.
-/
@[simps obj]
def desc : (Σi, C i) ⥤ D where
  obj X := (F X.1).obj X.2
  map g := descMap F _ _ g
  map_id := by
    rintro ⟨i, X⟩
    -- ⊢ { obj := fun X => (F X.fst).obj X.snd, map := fun {X Y} g => descMap F X Y g …
    apply (F i).map_id
    -- 🎉 no goals
  map_comp := by
    rintro ⟨i, X⟩ ⟨_, Y⟩ ⟨_, Z⟩ ⟨f⟩ ⟨g⟩
    -- ⊢ { obj := fun X => (F X.fst).obj X.snd, map := fun {X Y} g => descMap F X Y g …
    apply (F i).map_comp
    -- 🎉 no goals
#align category_theory.sigma.desc CategoryTheory.Sigma.desc

@[simp]
lemma desc_map_mk {i : I} (X Y : C i) (f : X ⟶ Y) : (desc F).map (SigmaHom.mk f) = (F i).map f :=
  rfl
#align category_theory.sigma.desc_map_mk CategoryTheory.Sigma.desc_map_mk

-- We hand-generate the simp lemmas about this since they come out cleaner.
/-- This shows that when `desc F` is restricted to just the subcategory `C i`, `desc F` agrees with
`F i`.
-/
def inclDesc (i : I) : incl i ⋙ desc F ≅ F i :=
  NatIso.ofComponents fun X => Iso.refl _
#align category_theory.sigma.incl_desc CategoryTheory.Sigma.inclDesc

@[simp]
lemma inclDesc_hom_app (i : I) (X : C i) : (inclDesc F i).hom.app X = 𝟙 ((F i).obj X) :=
  rfl
#align category_theory.sigma.incl_desc_hom_app CategoryTheory.Sigma.inclDesc_hom_app

@[simp]
lemma inclDesc_inv_app (i : I) (X : C i) : (inclDesc F i).inv.app X = 𝟙 ((F i).obj X) :=
  rfl
#align category_theory.sigma.incl_desc_inv_app CategoryTheory.Sigma.inclDesc_inv_app

/-- If `q` when restricted to each subcategory `C i` agrees with `F i`, then `q` is isomorphic to
`desc F`.
-/
def descUniq (q : (Σi, C i) ⥤ D) (h : ∀ i, incl i ⋙ q ≅ F i) : q ≅ desc F :=
  NatIso.ofComponents (fun ⟨i, X⟩ => (h i).app X) <| by
    rintro ⟨i, X⟩ ⟨_, _⟩ ⟨f⟩
    -- ⊢ q.map (SigmaHom.mk f) ≫
    apply (h i).hom.naturality f
    -- 🎉 no goals
#align category_theory.sigma.desc_uniq CategoryTheory.Sigma.descUniq

@[simp]
lemma descUniq_hom_app (q : (Σi, C i) ⥤ D) (h : ∀ i, incl i ⋙ q ≅ F i) (i : I) (X : C i) :
    (descUniq F q h).hom.app ⟨i, X⟩ = (h i).hom.app X :=
  rfl
#align category_theory.sigma.desc_uniq_hom_app CategoryTheory.Sigma.descUniq_hom_app

@[simp]
lemma descUniq_inv_app (q : (Σi, C i) ⥤ D) (h : ∀ i, incl i ⋙ q ≅ F i) (i : I) (X : C i) :
    (descUniq F q h).inv.app ⟨i, X⟩ = (h i).inv.app X :=
  rfl
#align category_theory.sigma.desc_uniq_inv_app CategoryTheory.Sigma.descUniq_inv_app

/--
If `q₁` and `q₂` when restricted to each subcategory `C i` agree, then `q₁` and `q₂` are isomorphic.
-/
@[simps]
def natIso {q₁ q₂ : (Σi, C i) ⥤ D} (h : ∀ i, incl i ⋙ q₁ ≅ incl i ⋙ q₂) : q₁ ≅ q₂ where
  hom := natTrans fun i => (h i).hom
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
lemma map_obj (j : J) (X : C (g j)) : (Sigma.map C g).obj ⟨j, X⟩ = ⟨g j, X⟩ :=
  rfl
#align category_theory.sigma.map_obj CategoryTheory.Sigma.map_obj

@[simp]
lemma map_map {j : J} {X Y : C (g j)} (f : X ⟶ Y) :
    (Sigma.map C g).map (SigmaHom.mk f) = SigmaHom.mk f :=
  rfl
#align category_theory.sigma.map_map CategoryTheory.Sigma.map_map

/-- The functor `Sigma.map C g` restricted to the subcategory `C j` acts as the inclusion of `g j`.
-/
@[simps!]
def inclCompMap (j : J) : incl j ⋙ map C g ≅ incl (g j) :=
  Iso.refl _
#align category_theory.sigma.incl_comp_map CategoryTheory.Sigma.inclCompMap

variable (I)

/-- The functor `Sigma.map` applied to the identity function is just the identity functor. -/
@[simps!]
def mapId : map C (id : I → I) ≅ 𝟭 (Σi, C i) :=
  natIso fun i => NatIso.ofComponents fun X => Iso.refl _
#align category_theory.sigma.map_id CategoryTheory.Sigma.mapId

variable {I} {K : Type w₃}

-- Porting note: Had to expand (G ∘ g) to (fun i => C (g i)) in lemma statement
-- so that the suitable category instances could be found
/-- The functor `Sigma.map` applied to a composition is a composition of functors. -/
@[simps!]
def mapComp (f : K → J) (g : J → I) : map (fun x => C (g x)) f ⋙ (map C g : _) ≅ map C (g ∘ f) :=
  (descUniq _ _) fun k =>
    (isoWhiskerRight (inclCompMap (fun i => C (g i)) f k) (map C g : _) : _) ≪≫ inclCompMap _ _ _
#align category_theory.sigma.map_comp CategoryTheory.Sigma.mapComp

end

namespace Functor

-- variable {C}

variable {D : I → Type u₁} [∀ i, Category.{v₁} (D i)]

/-- Assemble an `I`-indexed family of functors into a functor between the sigma types.
-/
def sigma (F : ∀ i, C i ⥤ D i) : (Σi, C i) ⥤ Σi, D i :=
  desc fun i => F i ⋙ incl i
#align category_theory.sigma.functor.sigma CategoryTheory.Sigma.Functor.sigma

end Functor

namespace natTrans

variable {D : I → Type u₁} [∀ i, Category.{v₁} (D i)]

variable {F G : ∀ i, C i ⥤ D i}

/-- Assemble an `I`-indexed family of natural transformations into a single natural transformation.
-/
def sigma (α : ∀ i, F i ⟶ G i) : Functor.sigma F ⟶ Functor.sigma G where
  app f := SigmaHom.mk ((α f.1).app _)
  naturality := by
    rintro ⟨i, X⟩ ⟨_, _⟩ ⟨f⟩
    -- ⊢ (Functor.sigma F).map (SigmaHom.mk f) ≫ (fun f => SigmaHom.mk (NatTrans.app  …
    change SigmaHom.mk _ = SigmaHom.mk _
    -- ⊢ SigmaHom.mk ((F { fst := i, snd := X }.fst).map f ≫ NatTrans.app (α { fst := …
    rw [(α i).naturality]
    -- 🎉 no goals
#align category_theory.sigma.nat_trans.sigma CategoryTheory.Sigma.natTrans.sigma

end natTrans

end Sigma

end CategoryTheory
