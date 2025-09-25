/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Kim Morrison, Floris van Doorn
-/
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Iso

/-!
# The category of functors and natural transformations between two fixed categories.

We provide the category instance on `C ⥤ D`, with morphisms the natural transformations.

At the end of the file, we provide the left and right unitors, and the associator,
for functor composition.
(In fact functor composition is definitionally associative, but very often relying on this causes
extremely slow elaboration, so it is better to insert it explicitly.)

## Universes

If `C` and `D` are both small categories at the same universe level,
this is another small category at that level.
However if `C` and `D` are both large categories at the same universe level,
this is a small category at the next higher level.
-/

set_option mathlib.tactic.category.grind true

namespace CategoryTheory

-- declare the `v`'s first; see note [CategoryTheory universes].
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open NatTrans Category CategoryTheory.Functor

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

attribute [local simp] vcomp_app

variable {C D} {E : Type u₃} [Category.{v₃} E]
variable {E' : Type u₄} [Category.{v₄} E']
variable {F G H I : C ⥤ D}

attribute [local grind =] NatTrans.id_app' in
/-- `Functor.category C D` gives the category structure on functors and natural transformations
between categories `C` and `D`.

Notice that if `C` and `D` are both small categories at the same universe level,
this is another small category at that level.
However if `C` and `D` are both large categories at the same universe level,
this is a small category at the next higher level.
-/
instance Functor.category : Category.{max u₁ v₂} (C ⥤ D) where
  Hom F G := NatTrans F G
  id F := NatTrans.id F
  comp α β := vcomp α β

namespace NatTrans

@[ext, grind ext]
theorem ext' {α β : F ⟶ G} (w : α.app = β.app) : α = β := NatTrans.ext w

@[simp]
theorem vcomp_eq_comp (α : F ⟶ G) (β : G ⟶ H) : vcomp α β = α ≫ β := rfl

theorem vcomp_app' (α : F ⟶ G) (β : G ⟶ H) (X : C) : (α ≫ β).app X = α.app X ≫ β.app X := rfl

theorem congr_app {α β : F ⟶ G} (h : α = β) (X : C) : α.app X = β.app X := by rw [h]

@[simp, grind =]
theorem id_app (F : C ⥤ D) (X : C) : (𝟙 F : F ⟶ F).app X = 𝟙 (F.obj X) := rfl

@[simp, grind _=_]
theorem comp_app {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) (X : C) :
    (α ≫ β).app X = α.app X ≫ β.app X := rfl

attribute [reassoc] comp_app

@[reassoc]
theorem app_naturality {F G : C ⥤ D ⥤ E} (T : F ⟶ G) (X : C) {Y Z : D} (f : Y ⟶ Z) :
    (F.obj X).map f ≫ (T.app X).app Z = (T.app X).app Y ≫ (G.obj X).map f :=
  (T.app X).naturality f

@[reassoc (attr := simp)]
theorem naturality_app {F G : C ⥤ D ⥤ E} (T : F ⟶ G) (Z : D) {X Y : C} (f : X ⟶ Y) :
    (F.map f).app Z ≫ (T.app Y).app Z = (T.app X).app Z ≫ (G.map f).app Z :=
  congr_fun (congr_arg app (T.naturality f)) Z

@[reassoc]
theorem naturality_app_app {F G : C ⥤ D ⥤ E ⥤ E'}
    (α : F ⟶ G) {X₁ Y₁ : C} (f : X₁ ⟶ Y₁) (X₂ : D) (X₃ : E) :
    ((F.map f).app X₂).app X₃ ≫ ((α.app Y₁).app X₂).app X₃ =
      ((α.app X₁).app X₂).app X₃ ≫ ((G.map f).app X₂).app X₃ :=
  congr_app (NatTrans.naturality_app α X₂ f) X₃

/-- A natural transformation is a monomorphism if each component is. -/
theorem mono_of_mono_app (α : F ⟶ G) [∀ X : C, Mono (α.app X)] : Mono α :=
  ⟨fun g h eq => by
    ext X
    rw [← cancel_mono (α.app X), ← comp_app, eq, comp_app]⟩

/-- A natural transformation is an epimorphism if each component is. -/
theorem epi_of_epi_app (α : F ⟶ G) [∀ X : C, Epi (α.app X)] : Epi α :=
  ⟨fun g h eq => by
    ext X
    rw [← cancel_epi (α.app X), ← comp_app, eq, comp_app]⟩

/-- The monoid of natural transformations of the identity is commutative. -/
lemma id_comm (α β : (𝟭 C) ⟶ (𝟭 C)) : α ≫ β = β ≫ α := by
  ext X
  exact (α.naturality (β.app X)).symm

/-- `hcomp α β` is the horizontal composition of natural transformations. -/
@[simps (attr := grind =)]
def hcomp {H I : D ⥤ E} (α : F ⟶ G) (β : H ⟶ I) : F ⋙ H ⟶ G ⋙ I where
  app := fun X : C => β.app (F.obj X) ≫ I.map (α.app X)

/-- Notation for horizontal composition of natural transformations. -/
infixl:80 " ◫ " => hcomp

theorem hcomp_id_app {H : D ⥤ E} (α : F ⟶ G) (X : C) : (α ◫ 𝟙 H).app X = H.map (α.app X) := by
  simp

theorem id_hcomp_app {H : E ⥤ C} (α : F ⟶ G) (X : E) : (𝟙 H ◫ α).app X = α.app _ := by simp

-- Note that we don't yet prove a `hcomp_assoc` lemma here: even stating it is painful, because we
-- need to use associativity of functor composition. (It's true without the explicit associator,
-- because functor composition is definitionally associative,
-- but relying on the definitional equality causes bad problems with elaboration later.)
theorem exchange {I J K : D ⥤ E} (α : F ⟶ G) (β : G ⟶ H) (γ : I ⟶ J) (δ : J ⟶ K) :
    (α ≫ β) ◫ (γ ≫ δ) = (α ◫ γ) ≫ β ◫ δ := by
  cat_disch

end NatTrans

namespace Functor

/-- Flip the arguments of a bifunctor. See also `Currying.lean`. -/
@[simps (attr := grind =) obj_obj obj_map]
protected def flip (F : C ⥤ D ⥤ E) : D ⥤ C ⥤ E where
  obj k :=
    { obj := fun j => (F.obj j).obj k,
      map := fun f => (F.map f).app k, }
  map f := { app := fun j => (F.obj j).map f }

-- `@[simps]` doesn't produce a nicely stated lemma here:
-- the implicit arguments for `app` use the definition of `flip`, rather than `flip` itself.
@[simp, grind =] theorem flip_map_app (F : C ⥤ D ⥤ E) {d d' : D} (f : d ⟶ d') (c : C) :
    (F.flip.map f).app c = (F.obj c).map f := rfl

/-- The left unitor, a natural isomorphism `((𝟭 _) ⋙ F) ≅ F`.
-/
@[simps]
def leftUnitor (F : C ⥤ D) :
    𝟭 C ⋙ F ≅ F where
  hom := { app := fun X => 𝟙 (F.obj X) }
  inv := { app := fun X => 𝟙 (F.obj X) }

/-- The right unitor, a natural isomorphism `(F ⋙ (𝟭 B)) ≅ F`.
-/
@[simps]
def rightUnitor (F : C ⥤ D) :
    F ⋙ 𝟭 D ≅ F where
  hom := { app := fun X => 𝟙 (F.obj X) }
  inv := { app := fun X => 𝟙 (F.obj X) }

/-- The associator for functors, a natural isomorphism `((F ⋙ G) ⋙ H) ≅ (F ⋙ (G ⋙ H))`.

(In fact, `iso.refl _` will work here, but it tends to make Lean slow later,
and it's usually best to insert explicit associators.)
-/
@[simps]
def associator (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') :
    (F ⋙ G) ⋙ H ≅ F ⋙ G ⋙ H where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

protected theorem assoc (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') : (F ⋙ G) ⋙ H = F ⋙ G ⋙ H :=
  rfl

end Functor

variable (C D E) in
/-- The functor `(C ⥤ D ⥤ E) ⥤ D ⥤ C ⥤ E` which flips the variables. -/
@[simps]
def flipFunctor : (C ⥤ D ⥤ E) ⥤ D ⥤ C ⥤ E where
  obj F := F.flip
  map {F₁ F₂} φ :=
    { app := fun Y =>
      { app := fun X => (φ.app X).app Y } }

namespace Iso

@[reassoc (attr := simp)]
theorem map_hom_inv_id_app {X Y : C} (e : X ≅ Y) (F : C ⥤ D ⥤ E) (Z : D) :
    (F.map e.hom).app Z ≫ (F.map e.inv).app Z = 𝟙 _ := by
  cat_disch

@[reassoc (attr := simp)]
theorem map_inv_hom_id_app {X Y : C} (e : X ≅ Y) (F : C ⥤ D ⥤ E) (Z : D) :
    (F.map e.inv).app Z ≫ (F.map e.hom).app Z = 𝟙 _ := by
  cat_disch

end Iso

end CategoryTheory
