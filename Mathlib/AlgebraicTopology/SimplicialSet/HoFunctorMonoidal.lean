/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.CategoryTheory.Category.Cat.CartesianClosed
public import Mathlib.CategoryTheory.Functor.CurryingThree
public import Mathlib.CategoryTheory.Products.Associator

/-!
# The homotopy category functor is monoidal

Given `2`-truncated simplicial sets `X` and `Y`, we introduce ad operation
`Truncated.Edge.tensor : Edge x x' → Edge y y' → Edge (x, y) (x', y')`.
We shall use this in order to construct an equivalence of categories
`(X ⊗ Y).HomotopyCategory ≌ X.HomotopyCategory × Y.HomotopyCategory` (TODO @joelriou).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Simplicial SimplicialObject.Truncated
  CartesianMonoidalCategory Limits

namespace SSet

namespace Truncated

namespace Edge

variable {X Y X' Y' Z : Truncated.{u} 2}

/-- The external product of edges of `2`-truncated simplicial sets. -/
@[simps]
def tensor {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
    (e₂ : Edge y y') :
    Edge (X := X ⊗ Y) (x, y) (x', y') where
  edge := (e₁.edge, e₂.edge)
  src_eq := Prod.ext e₁.src_eq e₂.src_eq
  tgt_eq := Prod.ext e₁.tgt_eq e₂.tgt_eq

lemma tensor_surjective {x x' : X _⦋0⦌₂} {y y' : Y _⦋0⦌₂}
    (e : Edge (X := X ⊗ Y) (x, y) (x', y')) :
    ∃ (e₁ : Edge x x') (e₂ : Edge y y'), e₁.tensor e₂ = e :=
  ⟨e.map (fst _ _), e.map (snd _ _), rfl⟩

@[simp]
lemma id_tensor_id (x : X _⦋0⦌₂) (y : Y _⦋0⦌₂) :
    (id x).tensor (id y) = id (X := X ⊗ Y) (x, y):= rfl

@[simp]
lemma map_tensorHom {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
    (e₂ : Edge y y') (f : X ⟶ X') (g : Y ⟶ Y') :
    (e₁.tensor e₂).map (f ⊗ₘ g) =
      (e₁.map f).tensor (e₂.map g) := rfl

@[simp]
lemma map_whiskerRight {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
    (e₂ : Edge y y') (f : X ⟶ X') :
    (e₁.tensor e₂).map (f ▷ _) =
      (e₁.map f).tensor e₂ := rfl

@[simp]
lemma map_whiskerLeft {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
    (e₂ : Edge y y') (g : Y ⟶ Y') :
    (e₁.tensor e₂).map (_ ◁ g) =
      e₁.tensor (e₂.map g) := rfl

@[simp]
lemma map_associator_hom {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂} (e₂ : Edge y y')
    {z z' : Z _⦋0⦌₂} (e₃ : Edge z z') :
    ((e₁.tensor e₂).tensor e₃).map (α_ _ _ _).hom = e₁.tensor (e₂.tensor e₃) :=
  rfl

@[simp]
lemma map_fst {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
    (e₂ : Edge y y') :
    (e₁.tensor e₂).map (fst _ _) = e₁ := rfl

@[simp]
lemma map_snd {x x' : X _⦋0⦌₂} (e₁ : Edge x x') {y y' : Y _⦋0⦌₂}
    (e₂ : Edge y y') :
    (e₁.tensor e₂).map (snd _ _) = e₂ := rfl

/-- The external product of `CompStruct` between edges of `2`-truncated simplicial sets. -/
@[simps simplex_fst simplex_snd]
def CompStruct.tensor
    {x₀ x₁ x₂ : X _⦋0⦌₂} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (hx : CompStruct e₀₁ e₁₂ e₀₂)
    {y₀ y₁ y₂ : Y _⦋0⦌₂} {e'₀₁ : Edge y₀ y₁} {e'₁₂ : Edge y₁ y₂} {e'₀₂ : Edge y₀ y₂}
    (hy : CompStruct e'₀₁ e'₁₂ e'₀₂) :
    CompStruct (e₀₁.tensor e'₀₁) (e₁₂.tensor e'₁₂) (e₀₂.tensor e'₀₂) where
  simplex := (hx.simplex, hy.simplex)
  d₂ := Prod.ext hx.d₂ hy.d₂
  d₀ := Prod.ext hx.d₀ hy.d₀
  d₁ := Prod.ext hx.d₁ hy.d₁

end Edge

namespace HomotopyCategory

instance {n : ℕ} (d : (SimplexCategory.Truncated n)ᵒᵖ) :
    Unique ((𝟙_ (Truncated.{u} n)).obj d) :=
  inferInstanceAs (Unique PUnit)

/-- If `X : Truncated 2` has a unique `0`-simplex and (at most) one `1`-simplex,
this is the isomorphism `Cat.of X.HomotopyCategory ≅ Cat.chosenTerminal` in `Cat`. -/
def isoTerminal (X : Truncated.{u} 2) [Unique (X _⦋0⦌₂)] [Subsingleton (X _⦋1⦌₂)] :
    Cat.of X.HomotopyCategory ≅ Cat.chosenTerminal :=
  IsTerminal.uniqueUpToIso (isTerminal _) Cat.chosenTerminalIsTerminal

lemma square {X Y : Truncated.{u} 2}
    {x₀ x₁ : X _⦋0⦌₂} (ex : Edge x₀ x₁) {y₀ y₁ : Y _⦋0⦌₂} (ey : Edge y₀ y₁) :
    homMk (ex.tensor (.id y₀)) ≫ homMk (Edge.tensor (.id x₁) ey) =
      homMk (Edge.tensor (.id x₀) ey) ≫ homMk (ex.tensor (.id y₁)) := by
  rw [homMk_comp_homMk ((Edge.CompStruct.idComp ex).tensor (Edge.CompStruct.compId ey)),
    homMk_comp_homMk ((Edge.CompStruct.compId ex).tensor (Edge.CompStruct.idComp ey))]

end HomotopyCategory

end Truncated

end SSet
