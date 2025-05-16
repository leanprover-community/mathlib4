/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.Opposite

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

variable {B : Type u} [Bicategory.{w, v} B]

namespace Adjunction

/- TODO: refactor `mateEquiv` by using `homEquiv₁/₂`.  -/
variable {a b c d : B} {l : b ⟶ c} {r : c ⟶ b} (adj : l ⊣ r)

@[simps -isSimp]
def homEquiv₁ {g : b ⟶ d} {h : c ⟶ d} : (g ⟶ l ≫ h) ≃ (r ≫ g ⟶ h) where
  toFun γ := r ◁ γ ≫ (α_ _ _ _).inv ≫ adj.counit ▷ h ≫ (λ_ _).hom
  invFun β := (λ_ _).inv ≫ adj.unit ▷ _ ≫ (α_ _ _ _).hom ≫ l ◁ β
  left_inv γ :=
    calc
      _ = 𝟙 _ ⊗≫ (adj.unit ▷ g ≫ (l ≫ r) ◁ γ) ⊗≫ l ◁ adj.counit ▷ h ⊗≫ 𝟙 _:= by
        bicategory
      _ = γ ⊗≫ leftZigzag adj.unit adj.counit ▷ h ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]
        bicategory
      _ = γ := by
        rw [adj.left_triangle]
        bicategory
  right_inv β := by
    calc
      _ = 𝟙 _ ⊗≫ r ◁ adj.unit ▷ g ⊗≫ ((r ≫ l) ◁ β ≫ adj.counit ▷ h) ⊗≫ 𝟙 _ := by
        bicategory
      _ = 𝟙 _ ⊗≫ rightZigzag adj.unit adj.counit ▷ g ⊗≫ β := by
        rw [whisker_exchange]
        bicategory
      _ = β := by
        rw [adj.right_triangle]
        bicategory

@[simps -isSimp]
def homEquiv₂ {g : a ⟶ b} {h : a ⟶ c} : (g ≫ l ⟶ h) ≃ (g ⟶ h ≫ r) where
  toFun α := (ρ_ _).inv ≫ g ◁ adj.unit ≫ (α_ _ _ _).inv ≫ α ▷ r
  invFun γ := γ ▷ l ≫ (α_ _ _ _ ).hom ≫ h ◁ adj.counit ≫ (ρ_ _).hom
  left_inv α :=
    calc
      _ = 𝟙 _ ⊗≫ g ◁ adj.unit ▷ l ⊗≫ (α ▷ (r ≫ l) ≫ h ◁ adj.counit) ⊗≫ 𝟙 _ := by
        bicategory
      _ = 𝟙 _ ⊗≫ g ◁ leftZigzag adj.unit adj.counit ⊗≫ α := by
        rw [← whisker_exchange]
        bicategory
      _ = α := by
        rw [adj.left_triangle]
        bicategory
  right_inv γ :=
    calc
      _ = 𝟙 _ ⊗≫ (g ◁ adj.unit ≫ γ ▷ (l ≫ r)) ⊗≫ h ◁ adj.counit ▷ r ⊗≫ 𝟙 _ := by
        bicategory
      _ = 𝟙 _ ⊗≫ γ ⊗≫ h ◁ rightZigzag adj.unit adj.counit ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]
        bicategory
      _ = γ := by
        rw [adj.right_triangle]
        bicategory

end Adjunction

section

variable {a b c d : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a} (adj₁ : l₁ ⊣ r₁)
  {l₂ : c ⟶ d} {r₂ : d ⟶ c} (adj₂ : l₂ ⊣ r₂)

lemma mateEquiv_eq_trans {g : a ⟶ c} {h : b ⟶ d} :
    mateEquiv adj₁ adj₂ (g := g) (h := h) =
      adj₂.homEquiv₂.trans
        ((Iso.homCongr (Iso.refl _) (α_ _ _ _)).trans adj₁.homEquiv₁) := by
  ext γ
  dsimp [mateEquiv, Adjunction.homEquiv₁, Adjunction.homEquiv₂]
  bicategory

lemma mateEquiv_eq_iff {g : a ⟶ c} {h : b ⟶ d}
    (α : g ≫ l₂ ⟶ l₁ ≫ h) (β : r₁ ≫ g ⟶ h ≫ r₂) :
  mateEquiv adj₁ adj₂ α = β ↔
    adj₁.homEquiv₁.symm β = adj₂.homEquiv₂ α ≫ (α_ _ _ _).hom := by
  conv_lhs => rw [eq_comm, ← adj₁.homEquiv₁.symm.injective.eq_iff']
  simp [mateEquiv_eq_trans]

variable {f : a ⟶ c} {g : b ⟶ d}

lemma mateEquiv_id_comp_right (φ : f ≫ 𝟙 _ ≫ l₂ ⟶ l₁ ≫ g) :
    mateEquiv adj₁ ((Adjunction.id _).comp adj₂) φ =
      mateEquiv adj₁ adj₂ (f ◁ (λ_ l₂).inv ≫ φ) ≫ (ρ_ _).inv ≫ (α_ _ _ _).hom := by
  dsimp [mateEquiv_apply, Adjunction.id]
  bicategory

lemma mateEquiv_comp_id_right (φ : f ≫ l₂ ≫ 𝟙 d ⟶ l₁ ≫ g) :
    mateEquiv adj₁ (adj₂.comp (Adjunction.id _)) φ =
      mateEquiv adj₁ adj₂ ((ρ_ _).inv ≫ (α_ _ _ _).hom ≫ φ) ≫ g ◁ (λ_ r₂).inv := by
  dsimp [mateEquiv_apply, Adjunction.id]
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
are adjunctions, and `2`-morphisms are tuples of mate maps between the left and right
adjoints (where the map between right adjoints is in the opposite direction).
-/
def Adj : Type u := B

namespace Adj

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
@[simp, reassoc] lemma comp_τg (x : α ⟶ β) (y : β ⟶ γ) : (x ≫ y).τg = y.τg ≫ x.τg := rfl

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
  τf := _ ◁ y.τf
  τg := y.τg ▷ _
  conjugateEquiv_τf := by
    dsimp
    simp only [conjugateEquiv_whiskerLeft, Hom₂.conjugateEquiv_τf]

/-- The right whiskering in the bicategory `Adj B`. -/
@[simps]
def whiskerRight {α α' : a ⟶ b} (x : α ⟶ α') (β : b ⟶ c) : α ≫ β ⟶ α' ≫ β where
  τf := x.τf ▷ _
  τg := _ ◁ x.τg
  conjugateEquiv_τf := by
    dsimp
    simp only [conjugateEquiv_whiskerRight, Hom₂.conjugateEquiv_τf]

attribute [local simp] whisker_exchange

instance : Bicategory (Adj B) where
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

@[simp] lemma whiskerRight_τg' {α α' : a ⟶ b} (x : α ⟶ α') (β : b ⟶ c) :
    (x ▷ β).τg = β.g ◁ x.τg := rfl

@[simp] lemma whiskerRight_τf' {α α' : a ⟶ b} (x : α ⟶ α') (β : b ⟶ c) :
    (x ▷ β).τf = x.τf ▷ β.f := rfl

-- this forgets the right adjoints
@[simps obj map, simps -isSimp map₂ mapId mapComp]
def forget₁ : Pseudofunctor (Adj B) B where
  obj a := a.obj
  map x := x.f
  map₂ α := α.τf
  mapId _ := Iso.refl _
  mapComp _ _ := Iso.refl _

-- this forgets the left adjoints
@[simps obj map, simps -isSimp map₂ mapId mapComp]
def forget₂ : Pseudofunctor (Adj B)ᵒᵖ B where
  obj a := a.unop.obj
  map x := x.unop.g
  map₂ α := α.unop.τg
  mapId _ := Iso.refl _
  mapComp _ _ := Iso.refl _

@[simps]
def fIso {a b : Adj B} {adj₁ adj₂ : a ⟶ b} (e : adj₁ ≅ adj₂) : adj₁.f ≅ adj₂.f where
  hom := e.hom.τf
  inv := e.inv.τf
  hom_inv_id := by rw [← comp_τf, e.hom_inv_id, id_τf]
  inv_hom_id := by rw [← comp_τf, e.inv_hom_id, id_τf]

@[simps]
def gIso {a b : Adj B} {adj₁ adj₂ : a ⟶ b} (e : adj₁ ≅ adj₂) : adj₁.g ≅ adj₂.g where
  hom := e.inv.τg
  inv := e.hom.τg
  hom_inv_id := by rw [← comp_τg, e.hom_inv_id, id_τg]
  inv_hom_id := by rw [← comp_τg, e.inv_hom_id, id_τg]

end Adj

end Bicategory

end CategoryTheory
