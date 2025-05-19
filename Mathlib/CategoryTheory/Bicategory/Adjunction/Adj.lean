/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.Opposite
import Mathlib.CategoryTheory.Bicategory.Functor.Strict

/-!
# The bicategory of adjunctions in a bicategory

Given a bicategory `B`, we construct a bicategory `Adj B` that has the same
objects but whose `1`-morphisms are adjunctions (in the same direction
as the left adjoints), and `2`-morphisms are tuples of mate maps between
the left and right adjoints (where the map between right
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

variable {B : Type u} [Bicategory.{w, v} B]

section

variable {a b c d : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a} (adj₁ : l₁ ⊣ r₁)
  {l₂ : c ⟶ d} {r₂ : d ⟶ c} (adj₂ : l₂ ⊣ r₂)

variable {f : a ⟶ c} {g : b ⟶ d}

lemma mateEquiv_id_comp_right (φ : f ≫ 𝟙 _ ≫ l₂ ⟶ l₁ ≫ g) :
    mateEquiv adj₁ ((Adjunction.id _).comp adj₂) φ =
      mateEquiv adj₁ adj₂ (f ◁ (λ_ l₂).inv ≫ φ) ≫ (ρ_ _).inv ≫ (α_ _ _ _).hom := by
  simp only [mateEquiv_apply, Adjunction.homEquiv₁_apply, Adjunction.homEquiv₂_apply,
    Adjunction.id]
  dsimp
  bicategory

lemma mateEquiv_comp_id_right (φ : f ≫ l₂ ≫ 𝟙 d ⟶ l₁ ≫ g) :
    mateEquiv adj₁ (adj₂.comp (Adjunction.id _)) φ =
      mateEquiv adj₁ adj₂ ((ρ_ _).inv ≫ (α_ _ _ _).hom ≫ φ) ≫ g ◁ (λ_ r₂).inv := by
  simp only [mateEquiv_apply, Adjunction.homEquiv₁_apply, Adjunction.homEquiv₂_apply,
    Adjunction.id]
  dsimp
  bicategory

end

section

variable {a b : B} {l : a ⟶ b} {r : b ⟶ a} (adj : l ⊣ r)
    {l' : a ⟶ b} {r' : b ⟶ a} (adj' : l' ⊣ r') (φ : l' ⟶ l)

lemma conjugateEquiv_id_comp_right_apply :
    conjugateEquiv adj ((Adjunction.id _).comp adj') ((λ_ _).hom ≫ φ) =
      conjugateEquiv adj adj' φ ≫ (ρ_ _).inv := by
  simp only [conjugateEquiv_apply, mateEquiv_id_comp_right,
    id_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc]
  bicategory

lemma conjugateEquiv_comp_id_right_apply :
    conjugateEquiv adj (adj'.comp (Adjunction.id _)) ((ρ_ _).hom ≫ φ) =
      conjugateEquiv adj adj' φ ≫ (λ_ _).inv := by
  simp only [conjugateEquiv_apply, Category.assoc, mateEquiv_comp_id_right, id_whiskerLeft,
    Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id, Iso.cancel_iso_inv_left,
    EmbeddingLike.apply_eq_iff_eq]
  bicategory

end

section

variable {a b : B} {l : a ⟶ b} {r : b ⟶ a} (adj : l ⊣ r)

@[simp]
lemma mateEquiv_leftUnitor_hom_rightUnitor_inv :
    mateEquiv adj adj ((λ_ _).hom ≫ (ρ_ _).inv) = (ρ_ _).hom ≫ (λ_ _).inv := by
  simp only [← cancel_mono (λ_ r).hom, ← cancel_epi (ρ_ r).inv,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    ← conjugateEquiv_id adj, conjugateEquiv_apply, Category.id_comp]

end

section

variable {a b c : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a} (adj₁ : l₁ ⊣ r₁)
  {l₂ : b ⟶ c} {r₂ : c ⟶ b} (adj₂ : l₂ ⊣ r₂)
  {l₂' : b ⟶ c} {r₂' : c ⟶ b} (adj₂' : l₂' ⊣ r₂')

lemma conjugateEquiv_whiskerLeft (φ : l₂' ⟶ l₂) :
    conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂') (l₁ ◁ φ) =
      conjugateEquiv adj₂ adj₂' φ ▷ r₁ := by
  have := mateEquiv_hcomp adj₁ adj₁ adj₂ adj₂' ((λ_ _).hom ≫ (ρ_ _).inv)
    ((λ_ _).hom ≫ φ ≫ (ρ_ _).inv)
  dsimp [leftAdjointSquare.hcomp, rightAdjointSquare.hcomp] at this
  simp only [comp_whiskerRight, leftUnitor_whiskerRight, Category.assoc, whiskerLeft_comp,
    whiskerLeft_rightUnitor_inv, Iso.hom_inv_id, Category.comp_id, triangle_assoc,
    inv_hom_whiskerRight_assoc, Iso.inv_hom_id_assoc, mateEquiv_leftUnitor_hom_rightUnitor_inv,
    whiskerLeft_rightUnitor, triangle_assoc_comp_left_inv_assoc, Iso.hom_inv_id_assoc] at this
  simp [conjugateEquiv_apply, this]

end

section

variable {a b c : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a} (adj₁ : l₁ ⊣ r₁)
  {l₁' : a ⟶ b} {r₁' : b ⟶ a} (adj₁' : l₁' ⊣ r₁')
  {l₂ : b ⟶ c} {r₂ : c ⟶ b} (adj₂ : l₂ ⊣ r₂)
  {l₂' : b ⟶ c} {r₂' : c ⟶ b} (adj₂' : l₂' ⊣ r₂')

lemma conjugateEquiv_whiskerRight (φ : l₁' ⟶ l₁) :
    conjugateEquiv (adj₁.comp adj₂) (adj₁'.comp adj₂) (φ ▷ l₂) =
      r₂ ◁ conjugateEquiv adj₁ adj₁' φ := by
  have := mateEquiv_hcomp adj₁ adj₁' adj₂ adj₂
    ((λ_ _).hom ≫ φ ≫ (ρ_ _).inv) ((λ_ _).hom ≫ (ρ_ _).inv)
  dsimp [leftAdjointSquare.hcomp, rightAdjointSquare.hcomp] at this
  simp only [comp_whiskerRight, leftUnitor_whiskerRight, Category.assoc, whiskerLeft_comp,
    whiskerLeft_rightUnitor_inv, Iso.hom_inv_id, Category.comp_id, triangle_assoc,
    inv_hom_whiskerRight_assoc, Iso.inv_hom_id_assoc, mateEquiv_leftUnitor_hom_rightUnitor_inv,
    leftUnitor_inv_whiskerRight, Iso.inv_hom_id, triangle_assoc_comp_right_assoc] at this
  simp [conjugateEquiv_apply, this]

end

section

variable {a b c d : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a} (adj₁ : l₁ ⊣ r₁)
  {l₂ : b ⟶ c} {r₂ : c ⟶ b} (adj₂ : l₂ ⊣ r₂)
  {l₃ : c ⟶ d} {r₃ : d ⟶ c} (adj₃ : l₃ ⊣ r₃)

lemma conjugateEquiv_associator_hom :
    conjugateEquiv (adj₁.comp (adj₂.comp adj₃))
      ((adj₁.comp adj₂).comp adj₃) (α_ _ _ _).hom = (α_ _ _ _).hom := by
  simp [← cancel_epi (ρ_ ((r₃ ≫ r₂) ≫ r₁)).hom, ← cancel_mono (λ_ (r₃ ≫ r₂ ≫ r₁)).inv,
    conjugateEquiv_apply, mateEquiv_eq_iff, Adjunction.homEquiv₁_symm_apply,
    Adjunction.homEquiv₂_apply]
  bicategory

end


variable (B) in
/--
The bicategory that has the same objects as a bicategory `B`, in which `1`-morphisms
are adjunctions (in the same direction as the left adjoints),
and `2`-morphisms are tuples of mate maps between the left and right
adjoints (where the map between right adjoints is in the opposite direction).
-/
def Adj : Type u := B

namespace Adj

/-- If `a : Adj B`, `a.obj : B` is the underlying object of `B`. -/
abbrev obj (a : Adj B) : B := a

variable (a b c d : B)

/--
Given two objects `a` and `b` in a bicategory,
this is the type of adjunctions between `a` and `b`.
-/
structure Hom where
  /-- the left adjoint -/
  l : a ⟶ b
  /-- the right adjoint -/
  r : b ⟶ a
  /-- the adjunction -/
  adj : l ⊣ r

variable {a b} in
/-- Constructor for `1`-morphisms in the bicategory `Adj B`. -/
@[simps]
def Hom.mk' {l : a ⟶ b} {r : b ⟶ a} (adj : l ⊣ r) : Hom a b where
  l := l
  r := r
  adj := adj

instance : CategoryStruct (Adj B) where
  Hom (a : B) b := Hom a b
  id (a : B) := .mk' (Adjunction.id a)
  comp f g := .mk' (f.adj.comp g.adj)

@[simp] lemma id_l (a : Adj B) : Hom.l (𝟙 a) = 𝟙 a.obj := rfl
@[simp] lemma id_r (a : Adj B) : Hom.r (𝟙 a) = 𝟙 a.obj := rfl
@[simp] lemma id_adj (a : Adj B) : Hom.adj (𝟙 a) = Adjunction.id a.obj := rfl

variable {a b c d : Adj B}

@[simp] lemma comp_l (α : a ⟶ b) (β : b ⟶ c) : (α ≫ β).l = α.l ≫ β.l := rfl
@[simp] lemma comp_r (α : a ⟶ b) (β : b ⟶ c) : (α ≫ β).r = β.r ≫ α.r := rfl
@[simp] lemma comp_adj (α : a ⟶ b) (β : b ⟶ c) : (α ≫ β).adj = α.adj.comp β.adj := rfl

/-- A morphism between two adjunctions consists of a tuple of mate maps. -/
@[ext]
structure Hom₂ (α β : a ⟶ b) where
  /-- the morphism between left adjoints -/
  τl : α.l ⟶ β.l
  /-- the morphism in the opposite direction between right adjoints -/
  τr : β.r ⟶ α.r
  conjugateEquiv_τl : conjugateEquiv β.adj α.adj τl = τr := by aesop_cat

namespace Hom₂

variable {α β : a ⟶ b} (p : Hom₂ α β)

lemma conjugateEquiv_symm_τg :
    (conjugateEquiv β.adj α.adj).symm p.τr = p.τl := by
  rw [← Hom₂.conjugateEquiv_τl, Equiv.symm_apply_apply]

lemma homEquiv₂_τl_eq :
    α.adj.homEquiv₂ ((λ_ _).hom ≫ p.τl ≫ (ρ_ _).inv) =
      β.adj.homEquiv₁.symm ((ρ_ _).hom ≫ p.τr ≫ (λ_ _).inv) ≫ (α_ _ _ _).inv := by
  symm
  rw [← cancel_mono (α_ _ _ _).hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, ← mateEquiv_eq_iff, ← p.conjugateEquiv_τl,
    conjugateEquiv_apply, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, Category.comp_id]

lemma homEquiv₁_τl_eq :
    β.adj.homEquiv₁ ((λ_ α.l).hom ≫ p.τl ≫ (ρ_ β.l).inv) =
      (α_ _ _ _).inv ≫ α.adj.homEquiv₂.symm ((ρ_ _).hom ≫ p.τr ≫ (λ_ _).inv) := by
  symm
  rw [← cancel_epi (α_ _ _ _).hom, Iso.hom_inv_id_assoc, ← mateEquiv_eq_iff',
    mateEquiv_eq_iff, homEquiv₂_τl_eq, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Hom₂

instance : CategoryStruct (a ⟶ b) where
  Hom α β := Hom₂ α β
  id α :=
    { τl := 𝟙 _
      τr := 𝟙 _ }
  comp {a b c} x y :=
    { τl := x.τl ≫ y.τl
      τr := y.τr ≫ x.τr
      conjugateEquiv_τl := by simp [← conjugateEquiv_comp c.adj b.adj a.adj y.τl x.τl,
        Hom₂.conjugateEquiv_τl] }

@[ext]
lemma hom₂_ext {α β : a ⟶ b} {x y : α ⟶ β} (hl : x.τl = y.τl) : x = y :=
  Hom₂.ext hl (by simp only [← Hom₂.conjugateEquiv_τl, hl])

@[simp] lemma id_τl (α : a ⟶ b) : Hom₂.τl (𝟙 α) = 𝟙 α.l := rfl
@[simp] lemma id_τr (α : a ⟶ b) : Hom₂.τr (𝟙 α) = 𝟙 α.r := rfl

section

variable {α β γ : a ⟶ b}

@[simp, reassoc] lemma comp_τl (x : α ⟶ β) (y : β ⟶ γ) : (x ≫ y).τl = x.τl ≫ y.τl := rfl
@[simp, reassoc] lemma comp_τr (x : α ⟶ β) (y : β ⟶ γ) : (x ≫ y).τr = y.τr ≫ x.τr := rfl

end

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
    (by simpa using conjugateEquiv_comp_id_right_apply α.adj α.adj (𝟙 _) )

/-- The left whiskering in the bicategory `Adj B`. -/
@[simps]
def whiskerLeft (α : a ⟶ b) {β β' : b ⟶ c} (y : β ⟶ β') : α ≫ β ⟶ α ≫ β' where
  τl := _ ◁ y.τl
  τr := y.τr ▷ _
  conjugateEquiv_τl := by
    dsimp
    simp only [conjugateEquiv_whiskerLeft, Hom₂.conjugateEquiv_τl]

/-- The right whiskering in the bicategory `Adj B`. -/
@[simps]
def whiskerRight {α α' : a ⟶ b} (x : α ⟶ α') (β : b ⟶ c) : α ≫ β ⟶ α' ≫ β where
  τl := x.τl ▷ _
  τr := _ ◁ x.τr
  conjugateEquiv_τl := by
    dsimp
    simp only [conjugateEquiv_whiskerRight, Hom₂.conjugateEquiv_τl]

attribute [local simp] whisker_exchange

instance : Bicategory (Adj B) where
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

@[simp] lemma whiskerRight_τr' {α α' : a ⟶ b} (x : α ⟶ α') (β : b ⟶ c) :
    (x ▷ β).τr = β.r ◁ x.τr := rfl

@[simp] lemma whiskerRight_τl' {α α' : a ⟶ b} (x : α ⟶ α') (β : b ⟶ c) :
    (x ▷ β).τl = x.τl ▷ β.l := rfl

/-- The forget pseudofunctor from `Adj B` to `B`. -/
@[simps obj map map₂ mapId mapComp]
def forget₁ : Pseudofunctor (Adj B) B where
  obj a := a.obj
  map x := x.l
  map₂ α := α.τl
  mapId _ := Iso.refl _
  mapComp _ _ := Iso.refl _

-- this forgets the left adjoints
--@[simps obj map, simps -isSimp map₂ mapId mapComp]
@[simps obj map map₂ mapId mapComp]
def forget₂ : Pseudofunctor (Adj B)ᵒᵖ B where
  obj a := a.unop.obj
  map x := x.unop.r
  map₂ α := α.unop.τr
  mapId _ := Iso.refl _
  mapComp _ _ := Iso.refl _

/-- Given an isomorphism between two 1-morphisms in `Adj B`, this is the
underlying isomorphisms between the left adjoints. -/
@[simps]
def lIso {a b : Adj B} {adj₁ adj₂ : a ⟶ b} (e : adj₁ ≅ adj₂) : adj₁.l ≅ adj₂.l where
  hom := e.hom.τl
  inv := e.inv.τl
  hom_inv_id := by rw [← comp_τl, e.hom_inv_id, id_τl]
  inv_hom_id := by rw [← comp_τl, e.inv_hom_id, id_τl]

@[reassoc (attr := simp)]
lemma hom_inv_τl {a b : Adj B} {adj₁ adj₂ : a ⟶ b} (e : adj₁ ≅ adj₂) :
    e.hom.τl ≫ e.inv.τl = 𝟙 _ :=
  (lIso e).hom_inv_id

@[reassoc (attr := simp)]
lemma inv_hom_τl {a b : Adj B} {adj₁ adj₂ : a ⟶ b} (e : adj₁ ≅ adj₂) :
    e.inv.τl ≫ e.hom.τl = 𝟙 _ :=
  (lIso e).inv_hom_id

/-- Given an isomorphism between two 1-morphisms in `Adj B`, this is the
underlying isomorphisms between the right adjoints. -/
@[simps]
def rIso {a b : Adj B} {adj₁ adj₂ : a ⟶ b} (e : adj₁ ≅ adj₂) : adj₁.r ≅ adj₂.r where
  hom := e.inv.τr
  inv := e.hom.τr
  hom_inv_id := by rw [← comp_τr, e.hom_inv_id, id_τr]
  inv_hom_id := by rw [← comp_τr, e.inv_hom_id, id_τr]

@[reassoc (attr := simp)]
lemma hom_inv_τr {a b : Adj B} {adj₁ adj₂ : a ⟶ b} (e : adj₁ ≅ adj₂) :
    e.hom.τr ≫ e.inv.τr = 𝟙 _ :=
  (rIso e).inv_hom_id

@[reassoc (attr := simp)]
lemma inv_hom_τr {a b : Adj B} {adj₁ adj₂ : a ⟶ b} (e : adj₁ ≅ adj₂) :
    e.inv.τr ≫ e.hom.τr = 𝟙 _ :=
  (rIso e).hom_inv_id

section

variable {C : Type*} [Bicategory C] (F : Pseudofunctor B (Adj C))
  {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (fg : a ⟶ c) (hfg : f ≫ g = fg)

lemma comp_forget₁_mapComp' :
    (F.comp forget₁).mapComp' f g fg hfg = lIso (F.mapComp' f g fg hfg) := by
  subst hfg
  ext
  simp [Pseudofunctor.mapComp'_eq_mapComp, forget₁]

@[reassoc]
lemma unit_comp_mapComp'_hom_τr_comp_counit :
    (F.map g).adj.unit ▷ (F.map f).r ▷ (F.map fg).l ≫
      (α_ _ _ _).hom ▷ _ ≫ (α_ _ _ _).hom ≫
      (F.map g).l ◁ (F.mapComp' f g fg hfg).hom.τr ▷ (F.map fg).l ≫
        (F.map g).l ◁ (F.map fg).adj.counit =
    (α_ _ _ _).hom ≫ (λ_ _).hom ≫ (F.map f).r ◁ (F.mapComp' f g fg hfg).hom.τl ≫
      (α_ _ _ _).inv ≫ (F.map f).adj.counit ▷ _ ≫ (λ_ _).hom ≫ (ρ_ _).inv := by
  -- this proof needs some improvements...
  rw [← cancel_mono (ρ_ _).hom, ← cancel_epi (α_ _ _ _).inv, ← cancel_epi (λ_ _).inv]
  apply (F.map f).adj.homEquiv₁.symm.injective
  simp only [Adjunction.homEquiv₁_symm_apply]
  trans (F.mapComp' f g fg hfg).hom.τl
  · simp only [comp_r, Category.assoc, whiskerLeft_comp, whiskerLeft_rightUnitor,
      ← Hom₂.conjugateEquiv_symm_τg, comp_l, comp_adj, conjugateEquiv_symm_apply',
      Adjunction.comp_unit, Adjunction.compUnit, comp_whiskerRight, whisker_assoc,
      leftUnitor_inv_whiskerRight, Iso.inv_hom_id_assoc, comp_whiskerLeft,
      pentagon_inv_hom_hom_hom_hom_assoc]
  · simp only [comp_l, Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc,
      whiskerLeft_comp]
    trans (λ_ _).inv ≫ ((F.map f).adj.unit ▷ (F.map fg).l ≫
      ((F.map f).l ≫ (F.map f).r) ◁ (F.mapComp' f g fg hfg).hom.τl) ≫
        ((α_ _ _ _ ).hom ≫ _ ◁ (α_ _ _ _).inv) ≫
        ((F.map f).l ◁ (F.map f).adj.counit ▷ (F.map g).l) ≫ _ ◁ (λ_ _).hom
    · rw [← whisker_exchange, id_whiskerLeft, Category.assoc, Category.assoc,
        Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
      trans (F.mapComp' f g fg hfg).hom.τl ≫ (λ_ _).inv ▷ _ ≫
        leftZigzag (F.map f).adj.unit (F.map f).adj.counit ▷ (F.map g).l ≫ (ρ_ _).hom ▷ _
      · simp
      · dsimp only [leftZigzag]
        simp [-Adjunction.left_triangle, bicategoricalComp]
    · simp

end

end Adj

end Bicategory

end CategoryTheory
