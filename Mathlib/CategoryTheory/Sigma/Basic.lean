/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.NatIso

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
inductive SigmaHom : (Σ i, C i) → (Σ i, C i) → Type max w₁ v₁ u₁
  | mk : ∀ {i : I} {X Y : C i}, (X ⟶ Y) → SigmaHom ⟨i, X⟩ ⟨i, Y⟩

namespace SigmaHom

/-- The identity morphism on an object. -/
def id : ∀ X : Σ i, C i, SigmaHom X X
  | ⟨_, _⟩ => mk (𝟙 _)
-- Porting note: reordered universes

instance (X : Σ i, C i) : Inhabited (SigmaHom X X) :=
  ⟨id X⟩

/-- Composition of sigma homomorphisms. -/
def comp : ∀ {X Y Z : Σ i, C i}, SigmaHom X Y → SigmaHom Y Z → SigmaHom X Z
  | _, _, _, mk f, mk g => mk (f ≫ g)
-- Porting note: reordered universes

instance : CategoryStruct (Σ i, C i) where
  Hom := SigmaHom
  id := id
  comp f g := comp f g

@[simp]
lemma comp_def (i : I) (X Y Z : C i) (f : X ⟶ Y) (g : Y ⟶ Z) : comp (mk f) (mk g) = mk (f ≫ g) :=
  rfl

lemma assoc : ∀ {X Y Z W : Σ i, C i} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W), (f ≫ g) ≫ h = f ≫ g ≫ h
  | _, _, _, _, mk _, mk _, mk _ => congr_arg mk (Category.assoc _ _ _)

lemma id_comp : ∀ {X Y : Σ i, C i} (f : X ⟶ Y), 𝟙 X ≫ f = f
  | _, _, mk _ => congr_arg mk (Category.id_comp _)

lemma comp_id : ∀ {X Y : Σ i, C i} (f : X ⟶ Y), f ≫ 𝟙 Y = f
  | _, _, mk _ => congr_arg mk (Category.comp_id _)

end SigmaHom

instance sigma : Category (Σ i, C i) where
  id_comp := SigmaHom.id_comp
  comp_id := SigmaHom.comp_id
  assoc := SigmaHom.assoc

/-- The inclusion functor into the disjoint union of categories. -/
@[simps map]
def incl (i : I) : C i ⥤ Σ i, C i where
  obj X := ⟨i, X⟩
  map := SigmaHom.mk

@[simp]
lemma incl_obj {i : I} (X : C i) : (incl i).obj X = ⟨i, X⟩ :=
  rfl

instance (i : I) : Functor.Full (incl i : C i ⥤ Σ i, C i) where
  map_surjective := fun ⟨f⟩ => ⟨f, rfl⟩

instance (i : I) : Functor.Faithful (incl i : C i ⥤ Σ i, C i) where
  map_injective {_ _ _ _} h := by injection h

section

variable {D : Type u₂} [Category.{v₂} D] (F : ∀ i, C i ⥤ D)

/--
To build a natural transformation over the sigma category, it suffices to specify it restricted to
each subcategory.
-/
def natTrans {F G : (Σ i, C i) ⥤ D} (h : ∀ i : I, incl i ⋙ F ⟶ incl i ⋙ G) : F ⟶ G where
  app := fun ⟨j, X⟩ => (h j).app X
  naturality := by
    rintro ⟨j, X⟩ ⟨_, _⟩ ⟨f⟩
    apply (h j).naturality

@[simp]
lemma natTrans_app {F G : (Σ i, C i) ⥤ D} (h : ∀ i : I, incl i ⋙ F ⟶ incl i ⋙ G) (i : I)
    (X : C i) : (natTrans h).app ⟨i, X⟩ = (h i).app X :=
  rfl

/-- (Implementation). An auxiliary definition to build the functor `desc`. -/
def descMap : ∀ X Y : Σ i, C i, (X ⟶ Y) → ((F X.1).obj X.2 ⟶ (F Y.1).obj Y.2)
  | _, _, SigmaHom.mk g => (F _).map g
-- Porting note: reordered universes

/-- Given a collection of functors `F i : C i ⥤ D`, we can produce a functor `(Σ i, C i) ⥤ D`.

The produced functor `desc F` satisfies: `incl i ⋙ desc F ≅ F i`, i.e. restricted to just the
subcategory `C i`, `desc F` agrees with `F i`, and it is unique (up to natural isomorphism) with
this property.

This witnesses that the sigma-type is the coproduct in Cat.
-/
@[simps obj]
def desc : (Σ i, C i) ⥤ D where
  obj X := (F X.1).obj X.2
  map g := descMap F _ _ g
  map_id := by
    rintro ⟨i, X⟩
    apply (F i).map_id
  map_comp := by
    rintro ⟨i, X⟩ ⟨_, Y⟩ ⟨_, Z⟩ ⟨f⟩ ⟨g⟩
    apply (F i).map_comp

@[simp]
lemma desc_map_mk {i : I} (X Y : C i) (f : X ⟶ Y) : (desc F).map (SigmaHom.mk f) = (F i).map f :=
  rfl

-- We hand-generate the simp lemmas about this since they come out cleaner.
/-- This shows that when `desc F` is restricted to just the subcategory `C i`, `desc F` agrees with
`F i`.
-/
def inclDesc (i : I) : incl i ⋙ desc F ≅ F i :=
  NatIso.ofComponents fun _ => Iso.refl _

@[simp]
lemma inclDesc_hom_app (i : I) (X : C i) : (inclDesc F i).hom.app X = 𝟙 ((F i).obj X) :=
  rfl

@[simp]
lemma inclDesc_inv_app (i : I) (X : C i) : (inclDesc F i).inv.app X = 𝟙 ((F i).obj X) :=
  rfl

/-- If `q` when restricted to each subcategory `C i` agrees with `F i`, then `q` is isomorphic to
`desc F`.
-/
def descUniq (q : (Σ i, C i) ⥤ D) (h : ∀ i, incl i ⋙ q ≅ F i) : q ≅ desc F :=
  NatIso.ofComponents (fun ⟨i, X⟩ => (h i).app X) <| by
    rintro ⟨i, X⟩ ⟨_, _⟩ ⟨f⟩
    apply (h i).hom.naturality f

@[simp]
lemma descUniq_hom_app (q : (Σ i, C i) ⥤ D) (h : ∀ i, incl i ⋙ q ≅ F i) (i : I) (X : C i) :
    (descUniq F q h).hom.app ⟨i, X⟩ = (h i).hom.app X :=
  rfl

@[simp]
lemma descUniq_inv_app (q : (Σ i, C i) ⥤ D) (h : ∀ i, incl i ⋙ q ≅ F i) (i : I) (X : C i) :
    (descUniq F q h).inv.app ⟨i, X⟩ = (h i).inv.app X :=
  rfl

/--
If `q₁` and `q₂` when restricted to each subcategory `C i` agree, then `q₁` and `q₂` are isomorphic.
-/
@[simps]
def natIso {q₁ q₂ : (Σ i, C i) ⥤ D} (h : ∀ i, incl i ⋙ q₁ ≅ incl i ⋙ q₂) : q₁ ≅ q₂ where
  hom := natTrans fun i => (h i).hom
  inv := natTrans fun i => (h i).inv

end

section

variable (C) {J : Type w₂} (g : J → I)

/-- A function `J → I` induces a functor `Σ j, C (g j) ⥤ Σ i, C i`. -/
def map : (Σj : J, C (g j)) ⥤ Σ i : I, C i :=
  desc fun j => incl (g j)

@[simp]
lemma map_obj (j : J) (X : C (g j)) : (Sigma.map C g).obj ⟨j, X⟩ = ⟨g j, X⟩ :=
  rfl

@[simp]
lemma map_map {j : J} {X Y : C (g j)} (f : X ⟶ Y) :
    (Sigma.map C g).map (SigmaHom.mk f) = SigmaHom.mk f :=
  rfl

/-- The functor `Sigma.map C g` restricted to the subcategory `C j` acts as the inclusion of `g j`.
-/
@[simps!]
def inclCompMap (j : J) : incl j ⋙ map C g ≅ incl (g j) :=
  Iso.refl _

variable (I)

/-- The functor `Sigma.map` applied to the identity function is just the identity functor. -/
@[simps!]
def mapId : map C (id : I → I) ≅ 𝟭 (Σ i, C i) :=
  natIso fun i => NatIso.ofComponents fun _ => Iso.refl _

variable {I} {K : Type w₃}

-- Porting note: Had to expand (C ∘ g) to (fun x => C (g x)) in lemma statement
-- so that the suitable category instances could be found
/-- The functor `Sigma.map` applied to a composition is a composition of functors. -/
@[simps!]
def mapComp (f : K → J) (g : J → I) : map (fun x ↦ C (g x)) f ⋙ (map C g :) ≅ map C (g ∘ f) :=
  (descUniq _ _) fun k =>
    (isoWhiskerRight (inclCompMap (fun i => C (g i)) f k) (map C g :) :) ≪≫ inclCompMap _ _ _

end

namespace Functor

-- variable {C}
variable {D : I → Type u₁} [∀ i, Category.{v₁} (D i)]

/-- Assemble an `I`-indexed family of functors into a functor between the sigma types.
-/
def sigma (F : ∀ i, C i ⥤ D i) : (Σ i, C i) ⥤ Σ i, D i :=
  desc fun i => F i ⋙ incl i

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
    change SigmaHom.mk _ = SigmaHom.mk _
    rw [(α i).naturality]

end natTrans

end Sigma

end CategoryTheory
