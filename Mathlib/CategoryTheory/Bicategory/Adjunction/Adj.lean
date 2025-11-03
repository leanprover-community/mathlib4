/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-!
# The bicategory of adjunctions in a bicategory

Given a bicategory `B`, we construct a bicategory `Adj B` that has essentially
the same objects as `B` but whose `1`-morphisms are adjunctions (in the same
direction as the left adjoints), and `2`-morphisms are tuples of mate maps
between the left and right adjoints (where the map between right
adjoints is in the opposite direction).

Certain pseudofunctors to the bicategory `Adj Cat` are analogous to bifibered categories:
in various contexts, this may be used in order to formalize the properties of
both pullback and pushforward functors.

## References

* https://ncatlab.org/nlab/show/2-category+of+adjunctions
* https://ncatlab.org/nlab/show/transformation+of+adjoints
* https://ncatlab.org/nlab/show/mate

-/

universe w v u

namespace CategoryTheory

namespace Bicategory

/--
The bicategory that has the same objects as a bicategory `B`, in which `1`-morphisms
are adjunctions (in the same direction as the left adjoints),
and `2`-morphisms are tuples of mate maps between the left and right
adjoints (where the map between right adjoints is in the opposite direction).
-/
structure Adj (B : Type u) [Bicategory.{w, v} B] where
  /-- If `a : Adj B`, `a.obj : B` is the underlying object of the bicategory `B`. -/
  obj : B

variable {B : Type u} [Bicategory.{w, v} B]

namespace Adj

@[simp] lemma mk_obj (b : Adj B) : mk b.obj = b := rfl

section

variable (a b : B)

/--
Given two objects `a` and `b` in a bicategory,
this is the type of adjunctions between `a` and `b`.
-/
structure Hom where
  /-- the left adjoint -/
  {l : a ⟶ b}
  /-- the right adjoint -/
  {r : b ⟶ a}
  /-- the adjunction -/
  adj : l ⊣ r

end

@[simps! id_l id_r id_adj comp_l comp_r comp_adj]
instance : CategoryStruct (Adj B) where
  Hom a b := Hom a.obj b.obj
  id a := .mk (Adjunction.id a.obj)
  comp f g := .mk (f.adj.comp g.adj)

variable {a b c d : Adj B}

/-- A morphism between two adjunctions consists of a tuple of mate maps. -/
@[ext]
structure Hom₂ (α β : a ⟶ b) where
  /-- the morphism between left adjoints -/
  τl : α.l ⟶ β.l
  /-- the morphism in the opposite direction between right adjoints -/
  τr : β.r ⟶ α.r
  conjugateEquiv_τl : conjugateEquiv β.adj α.adj τl = τr := by cat_disch

lemma Hom₂.conjugateEquiv_symm_τr {α β : a ⟶ b} (p : Hom₂ α β) :
    (conjugateEquiv β.adj α.adj).symm p.τr = p.τl := by
  rw [← Hom₂.conjugateEquiv_τl, Equiv.symm_apply_apply]

@[simps!]
instance : CategoryStruct (a ⟶ b) where
  Hom α β := Hom₂ α β
  id α :=
    { τl := 𝟙 _
      τr := 𝟙 _ }
  comp {a b c} x y :=
    { τl := x.τl ≫ y.τl
      τr := y.τr ≫ x.τr
      conjugateEquiv_τl := by
        simp [← conjugateEquiv_comp c.adj b.adj a.adj y.τl x.τl,
          Hom₂.conjugateEquiv_τl] }

attribute [reassoc] comp_τl comp_τr

@[ext]
lemma hom₂_ext {α β : a ⟶ b} {x y : α ⟶ β} (hl : x.τl = y.τl) : x = y :=
  Hom₂.ext hl (by simp only [← Hom₂.conjugateEquiv_τl, hl])

instance : Category (a ⟶ b) where

/-- Constructor for isomorphisms between 1-morphisms in the bicategory `Adj B`. -/
@[simps]
def iso₂Mk {α β : a ⟶ b} (el : α.l ≅ β.l) (er : β.r ≅ α.r)
    (h : conjugateEquiv β.adj α.adj el.hom = er.hom) :
    α ≅ β where
  hom :=
    { τl := el.hom
      τr := er.hom
      conjugateEquiv_τl := h }
  inv :=
    { τl := el.inv
      τr := er.inv
      conjugateEquiv_τl := by
        rw [← cancel_mono er.hom, Iso.inv_hom_id, ← h,
          conjugateEquiv_comp, Iso.hom_inv_id, conjugateEquiv_id] }

namespace Bicategory

/-- The associator in the bicategory `Adj B`. -/
@[simps!]
def associator (α : a ⟶ b) (β : b ⟶ c) (γ : c ⟶ d) : (α ≫ β) ≫ γ ≅ α ≫ β ≫ γ :=
  iso₂Mk (α_ _ _ _) (α_ _ _ _) (conjugateEquiv_associator_hom _ _ _)

/-- The left unitor in the bicategory `Adj B`. -/
@[simps!]
def leftUnitor (α : a ⟶ b) : 𝟙 a ≫ α ≅ α :=
  iso₂Mk (λ_ _) (ρ_ _).symm
    (by simpa using conjugateEquiv_id_comp_right_apply α.adj α.adj (𝟙 _))

/-- The right unitor in the bicategory `Adj B`. -/
@[simps!]
def rightUnitor (α : a ⟶ b) : α ≫ 𝟙 b ≅ α :=
  iso₂Mk (ρ_ _) (λ_ _).symm
    (by simpa using conjugateEquiv_comp_id_right_apply α.adj α.adj (𝟙 _))

/-- The left whiskering in the bicategory `Adj B`. -/
@[simps]
def whiskerLeft (α : a ⟶ b) {β β' : b ⟶ c} (y : β ⟶ β') : α ≫ β ⟶ α ≫ β' where
  τl := _ ◁ y.τl
  τr := y.τr ▷ _
  conjugateEquiv_τl := by
    simp [conjugateEquiv_whiskerLeft, Hom₂.conjugateEquiv_τl]

/-- The right whiskering in the bicategory `Adj B`. -/
@[simps]
def whiskerRight {α α' : a ⟶ b} (x : α ⟶ α') (β : b ⟶ c) : α ≫ β ⟶ α' ≫ β where
  τl := x.τl ▷ _
  τr := _ ◁ x.τr
  conjugateEquiv_τl := by
    simp [conjugateEquiv_whiskerRight, Hom₂.conjugateEquiv_τl]

end Bicategory

attribute [local simp] whisker_exchange

@[simps! whiskerRight_τr whiskerRight_τl whiskerLeft_τr whiskerLeft_τl
  associator_hom_τr associator_inv_τr associator_hom_τl associator_inv_τl
  leftUnitor_hom_τr leftUnitor_inv_τr leftUnitor_hom_τl leftUnitor_inv_τl
  rightUnitor_hom_τr rightUnitor_inv_τr rightUnitor_hom_τl rightUnitor_inv_τl]
instance : Bicategory (Adj B) where
  whiskerLeft := Bicategory.whiskerLeft
  whiskerRight := Bicategory.whiskerRight
  associator := Bicategory.associator
  leftUnitor := Bicategory.leftUnitor
  rightUnitor := Bicategory.rightUnitor

/-- The forget pseudofunctor from `Adj B` to `B`. -/
@[simps]
def forget₁ : Pseudofunctor (Adj B) B where
  obj a := a.obj
  map x := x.l
  map₂ α := α.τl
  mapId _ := Iso.refl _
  mapComp _ _ := Iso.refl _

-- TODO: define `forget₂` which sends an adjunction to its right adjoint functor

/-- Given an isomorphism between two 1-morphisms in `Adj B`, this is the
underlying isomorphisms between the left adjoints. -/
@[simps]
def lIso {a b : Adj B} {adj₁ adj₂ : a ⟶ b} (e : adj₁ ≅ adj₂) : adj₁.l ≅ adj₂.l where
  hom := e.hom.τl
  inv := e.inv.τl
  hom_inv_id := by rw [← comp_τl, e.hom_inv_id, id_τl]
  inv_hom_id := by rw [← comp_τl, e.inv_hom_id, id_τl]

/-- Given an isomorphism between two 1-morphisms in `Adj B`, this is the
underlying isomorphisms between the right adjoints. -/
@[simps]
def rIso {a b : Adj B} {adj₁ adj₂ : a ⟶ b} (e : adj₁ ≅ adj₂) : adj₁.r ≅ adj₂.r where
  hom := e.inv.τr
  inv := e.hom.τr
  hom_inv_id := by rw [← comp_τr, e.hom_inv_id, id_τr]
  inv_hom_id := by rw [← comp_τr, e.inv_hom_id, id_τr]

end Adj

end Bicategory

end CategoryTheory
