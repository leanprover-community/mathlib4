/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-!
# The bicategory of adjunctions in a bicategory

Given a bicategory `B`, we construct a bicategory `Adj B` that has the same
objects but whose `1`-morphisms are adjunctions, and `2`-morphisms are tuples
of mate maps between the left and right adjoints (where the map between right
adjoints is in the opposite direction).

Certain pseudofunctors to the bicategory `Adj Cat` are analogous to bifibered categories:
in various contexts, this may be used in order to formalize the properties of
both pushforward and pullback functors.

## References

* https://ncatlab.org/nlab/show/2-category+of+adjunctions
* https://ncatlab.org/nlab/show/transformation+of+adjoints
* https://ncatlab.org/nlab/show/mate

-/

universe w v u

namespace CategoryTheory

namespace Bicategory

variable (B : Type u) [Bicategory.{w, v} B]

section

variable {B} {c d e f : B} {g : c ⟶ e} {h : d ⟶ f}
  {l₁ : c ⟶ d} {r₁ : d ⟶ c} {l₂ : e ⟶ f} {r₂ : f ⟶ e}
  (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂)

/-
--Would this be helpful?
lemma mateEquiv_eq_iff (α : g ≫ l₂ ⟶ l₁ ≫ h) (β : r₁ ≫ g ⟶ h ≫ r₂) :
  mateEquiv adj₁ adj₂ α = β ↔
    (λ_ _).inv ≫ adj₁.unit ▷ _ ≫ (α_ _ _ _).hom ≫ l₁ ◁ β =
      (ρ_ _).inv ≫ g ◁ adj₂.unit ≫
        (α_ _ _ _).inv ≫ α ▷ r₂ ≫ (α_ _ _ _).hom := by
  sorry-/

end

/--
The bicategory that has the same objects as a bicategory `B`, in which `1`-morphisms
are adjunctions, and `2`-morphisms are tuples of mate maps between the left and right
adjoints (where the map between right adjoints is in the opposite direction).
-/
def Adj : Type u := B

namespace Adj

variable {B}

abbrev obj (a : Adj B) : B := a

variable (a b c d : B)

/--
Given two objects `a` and `b` in a bicategory,
this is the type of adjunctions between `a` and `b`.
-/
structure Hom where
  /-- the left adjoint -/
  f : a ⟶ b
  /-- the right adjoint -/
  g : b ⟶ a
  /-- the adjunction -/
  adj : f ⊣ g

variable {a b} in
def Hom.mk' {f : a ⟶ b} {g : b ⟶ a} (adj : f ⊣ g) : Hom a b where
  f := f
  g := g
  adj := adj

instance : CategoryStruct (Adj B) where
  Hom (a : B) b := Hom a b
  id (a : B) := .mk' (Adjunction.id a)
  comp f g := .mk' (f.adj.comp g.adj)

@[simp] lemma id_f (a : Adj B) : Hom.f (𝟙 a) = 𝟙 a.obj := rfl
@[simp] lemma id_g (a : Adj B) : Hom.g (𝟙 a) = 𝟙 a.obj := rfl
@[simp] lemma id_adj (a : Adj B) : Hom.adj (𝟙 a) = Adjunction.id a.obj := rfl

variable {a b c d : Adj B}

@[simp] lemma comp_f (α : a ⟶ b) (β : b ⟶ c) : (α ≫ β).f = α.f ≫ β.f := rfl
@[simp] lemma comp_g (α : a ⟶ b) (β : b ⟶ c) : (α ≫ β).g = β.g ≫ α.g := rfl
@[simp] lemma comp_adj (α : a ⟶ b) (β : b ⟶ c) : (α ≫ β).adj = α.adj.comp β.adj := rfl

/-- A morphism between two adjunctions consists of a tuple of mate maps. -/
@[ext]
structure Hom₂ (α β : a ⟶ b) where
  /-- the morphism between left adjoints -/
  τf : α.f ⟶ β.f
  /-- the morphism in the opposite direction between right adjoints -/
  τg : β.g ⟶ α.g
  conjugateEquiv_τf : conjugateEquiv β.adj α.adj τf = τg := by aesop_cat

lemma Hom₂.conjugateEquiv_symm_τg {α β : a ⟶ b} (p : Hom₂ α β) :
    (conjugateEquiv β.adj α.adj).symm p.τg = p.τf := by
  rw [← Hom₂.conjugateEquiv_τf, Equiv.symm_apply_apply]

instance : CategoryStruct (a ⟶ b) where
  Hom α β := Hom₂ α β
  id α :=
    { τf := 𝟙 _
      τg := 𝟙 _ }
  comp {a b c} x y :=
    { τf := x.τf ≫ y.τf
      τg := y.τg ≫ x.τg
      conjugateEquiv_τf := by simp [← conjugateEquiv_comp c.adj b.adj a.adj y.τf x.τf,
        Hom₂.conjugateEquiv_τf] }

@[ext]
lemma hom₂_ext {α β : a ⟶ b} {x y : α ⟶ β} (hf : x.τf = y.τf) : x = y := by
  apply Hom₂.ext hf
  simp only [← Hom₂.conjugateEquiv_τf, hf]

@[simp] lemma id_τf (α : a ⟶ b) : Hom₂.τf (𝟙 α) = 𝟙 α.f := rfl
@[simp] lemma id_τg (α : a ⟶ b) : Hom₂.τg (𝟙 α) = 𝟙 α.g := rfl

section

variable {α β γ : a ⟶ b}

@[simp, reassoc] lemma comp_τf (x : α ⟶ β) (y : β ⟶ γ) : (x ≫ y).τf = x.τf ≫ y.τf := rfl
@[simp, reassoc] lemma comp_τg (x : α ⟶ β) (y : β ⟶ γ) : (x ≫ y).τf = x.τf ≫ y.τf := rfl

end

instance : Category (a ⟶ b) where

/-- Constructor for isomorphisms between 1-morphisms in the bicategory `Adj B`. -/
@[simps]
def iso₂Mk {α β : a ⟶ b} (ef : α.f ≅ β.f) (eg : β.g ≅ α.g)
    (h : conjugateEquiv β.adj α.adj ef.hom = eg.hom) :
    α ≅ β where
  hom :=
    { τf := ef.hom
      τg := eg.hom
      conjugateEquiv_τf := h }
  inv :=
    { τf := ef.inv
      τg := eg.inv
      conjugateEquiv_τf := by
        rw [← cancel_mono eg.hom, Iso.inv_hom_id, ← h,
          conjugateEquiv_comp, Iso.hom_inv_id, conjugateEquiv_id] }

/-- The associator in the bicategory `Adj B`. -/
@[simps!]
def associator (α : a ⟶ b) (β : b ⟶ c) (γ : c ⟶ d) : (α ≫ β) ≫ γ ≅ α ≫ β ≫ γ :=
  iso₂Mk (α_ _ _ _) (α_ _ _ _) sorry

/-- The left unitor in the bicategory `Adj B`. -/
@[simps!]
def leftUnitor (α : a ⟶ b) : 𝟙 a ≫ α ≅ α :=
  iso₂Mk (λ_ _) (ρ_ _).symm sorry

/-- The right unitor in the bicategory `Adj B`. -/
@[simps!]
def rightUnitor (α : a ⟶ b) : α ≫ 𝟙 b ≅ α :=
  iso₂Mk (ρ_ _) (λ_ _).symm sorry

/-- The left whiskering in the bicategory `Adj B`. -/
@[simps]
def whiskerLeft (α : a ⟶ b) {β β' : b ⟶ c} (y : β ⟶ β') : α ≫ β ⟶ α ≫ β' where
  τf := _ ◁ y.τf
  τg := y.τg ▷ _
  conjugateEquiv_τf := by
    dsimp
    rw [← iterated_mateEquiv_conjugateEquiv]
    rw [← Hom₂.conjugateEquiv_τf]
    sorry

/-- The right whiskering in the bicategory `Adj B`. -/
@[simps]
def whiskerRight {α α' : a ⟶ b} (x : α ⟶ α') (β : b ⟶ c) : α ≫ β ⟶ α' ≫ β where
  τf := x.τf ▷ _
  τg := _ ◁ x.τg
  conjugateEquiv_τf := sorry

attribute [local simp] whisker_exchange

instance : Bicategory (Adj B) where
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

-- this forgets the right adjoints
def forget₁ : Pseudofunctor (Adj B) B where
  obj a := a.obj
  map x := x.f
  map₂ α := α.τf
  mapId _ := Iso.refl _
  mapComp _ _ := Iso.refl _

end Adj

end Bicategory

end CategoryTheory
