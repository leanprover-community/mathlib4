/-
Copyright (c) 2025 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic

/-!
# Mates in bicategories

This file establishes the bijection between the 2-cells

```
         l₁                  r₁
      c --→ d             c ←-- d
    g ↓  ↗  ↓ h         g ↓  ↘  ↓ h
      e --→ f             e ←-- f
         l₂                  r₂
```

where `l₁ ⊣ r₁` and `l₂ ⊣ r₂`. The corresponding natural transformations are called mates.

For the bicategory `Cat`, the definitions in this file are provided in
`Mathlib/CategoryTheory/Adjunction/Mates.lean`, where you can find more detailed documentation
about mates.

## Remarks

To be precise, the definitions in `Mathlib/CategoryTheory/Adjunction/Mates.lean` are universe
polymorphic, so they are not simple specializations of the definitions in this file.

-/

universe w v u

namespace CategoryTheory

namespace Bicategory

open Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

section mateEquiv

variable {c d e f : B} {g : c ⟶ e} {h : d ⟶ f} {l₁ : c ⟶ d} {r₁ : d ⟶ c} {l₂ : e ⟶ f} {r₂ : f ⟶ e}
variable (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂)

/-- Suppose we have a square of 1-morphisms (where the top and bottom are adjunctions `l₁ ⊣ r₁`
and `l₂ ⊣ r₂` respectively).

      c ↔ d
    g ↓   ↓ h
      e ↔ f

Then we have a bijection between natural transformations `g ≫ l₂ ⟶ l₁ ≫ h` and
`r₁ ≫ g ⟶ h ≫ r₂`. This can be seen as a bijection of the 2-cells:

         l₁                  r₁
      c --→ d             c ←-- d
    g ↓  ↗  ↓ h         g ↓  ↘  ↓ h
      e --→ f             e ←-- f
         L₂                  R₂

Note that if one of the transformations is an iso, it does not imply the other is an iso.
-/
@[simps]
def mateEquiv : (g ≫ l₂ ⟶ l₁ ≫ h) ≃ (r₁ ≫ g ⟶ h ≫ r₂) where
  toFun α   := 𝟙 _ ⊗≫ r₁ ◁ g ◁ adj₂.unit ⊗≫ r₁ ◁ α ▷ r₂ ⊗≫ adj₁.counit ▷ h ▷ r₂ ⊗≫ 𝟙 _
  invFun β  := 𝟙 _ ⊗≫ adj₁.unit ▷ g ▷ l₂ ⊗≫ l₁ ◁ β ▷ l₂ ⊗≫ l₁ ◁ h ◁ adj₂.counit ⊗≫ 𝟙 _
  left_inv α :=
    calc
      _ = 𝟙 _ ⊗≫ (adj₁.unit ▷ (g ≫ 𝟙 e) ≫ (l₁ ≫ r₁) ◁ g ◁ adj₂.unit) ▷ l₂ ⊗≫
            l₁ ◁ r₁ ◁ α ▷ r₂ ▷ l₂ ⊗≫
              l₁ ◁ (adj₁.counit ▷ h ▷ (r₂ ≫ l₂) ≫ (𝟙 d ≫ h) ◁ adj₂.counit) ⊗≫ 𝟙 _ := by
        bicategory
      _ = 𝟙 _ ⊗≫ g ◁ adj₂.unit ▷ l₂ ⊗≫
            (adj₁.unit ▷ (g ≫ l₂) ≫ (l₁ ≫ r₁) ◁ α) ▷ (r₂ ≫ l₂) ⊗≫
              l₁ ◁ (((r₁ ≫ l₁) ≫ h) ◁ adj₂.counit ≫ adj₁.counit ▷ h ▷ 𝟙 f) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange, ← whisker_exchange]
        bicategory
      _ = 𝟙 _ ⊗≫ g ◁ adj₂.unit ▷ l₂ ⊗≫ α ▷ r₂ ▷ l₂ ⊗≫
            leftZigzag adj₁.unit adj₁.counit ▷ h ▷ r₂ ▷ l₂ ⊗≫ l₁ ◁ h ◁ adj₂.counit ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange, whisker_exchange _ adj₂.counit]
        bicategory
      _ = 𝟙 _ ⊗≫ g ◁ adj₂.unit ▷ l₂ ⊗≫ (α ▷ (r₂ ≫ l₂) ≫ (l₁ ≫ h) ◁ adj₂.counit) ⊗≫ 𝟙 _ := by
        rw [adj₁.left_triangle]
        bicategory
      _ = 𝟙 _ ⊗≫ g ◁ (leftZigzag adj₂.unit adj₂.counit) ⊗≫ α ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]
        bicategory
      _ = α := by
        rw [adj₂.left_triangle]
        bicategory
  right_inv β :=
    calc
      _ = 𝟙 _ ⊗≫ r₁ ◁ ((𝟙 c ≫ g) ◁ adj₂.unit ≫ adj₁.unit ▷ g ▷ (l₂ ≫ r₂)) ⊗≫
            r₁ ◁ l₁ ◁ β ▷ l₂ ▷ r₂ ⊗≫
              ((r₁ ≫ l₁) ◁ h ◁ adj₂.counit ≫ adj₁.counit ▷ (h ≫ 𝟙 f)) ▷ r₂ ⊗≫ 𝟙 _ := by
        bicategory
      _ = 𝟙 _ ⊗≫ r₁ ◁ (adj₁.unit ▷ g ▷ 𝟙 e ≫ ((l₁ ≫ r₁) ≫ g) ◁ adj₂.unit) ⊗≫
            ((r₁ ≫ l₁) ◁ β ≫ adj₁.counit ▷ (h ≫ r₂)) ▷ l₂ ▷ r₂ ⊗≫
              h ◁ adj₂.counit ▷ r₂ ⊗≫ 𝟙 _ := by
        rw [whisker_exchange, whisker_exchange]
        bicategory
      _ = 𝟙 _ ⊗≫ r₁ ◁ g ◁ adj₂.unit ⊗≫ rightZigzag adj₁.unit adj₁.counit ▷ g ▷ l₂ ▷ r₂ ⊗≫
            β ▷ l₂ ▷ r₂ ⊗≫ h ◁ adj₂.counit ▷ r₂ ⊗≫ 𝟙 _ := by
        rw [whisker_exchange, ← whisker_exchange _ adj₂.unit]
        bicategory
      _ = 𝟙 _ ⊗≫ ((r₁ ≫ g) ◁ adj₂.unit ≫ β ▷ (l₂ ≫ r₂)) ⊗≫ h ◁ adj₂.counit ▷ r₂ ⊗≫ 𝟙 _ := by
        rw [adj₁.right_triangle]
        bicategory
      _ = 𝟙 _ ⊗≫ β ⊗≫ h ◁ rightZigzag adj₂.unit adj₂.counit ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]
        bicategory
      _ = β := by
        rw [adj₂.right_triangle]
        bicategory

end mateEquiv

section mateEquivVComp

variable {a b c d e f : B} {g₁ : a ⟶ c} {g₂ : c ⟶ e} {h₁ : b ⟶ d} {h₂ : d ⟶ f}
variable {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : c ⟶ d} {r₂ : d ⟶ c} {l₃ : e ⟶ f} {r₃ : f ⟶ e}
variable (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂) (adj₃ : l₃ ⊣ r₃)

/-- Squares between left adjoints can be composed "vertically" by pasting. -/
def leftAdjointSquare.vcomp (α : g₁ ≫ l₂ ⟶ l₁ ≫ h₁) (β : g₂ ≫ l₃ ⟶ l₂ ≫ h₂) :
    (g₁ ≫ g₂) ≫ l₃ ⟶ l₁ ≫ (h₁ ≫ h₂) :=
  (α_ _ _ _).hom ≫ g₁ ◁ β ≫ (α_ _ _ _).inv ≫ α ▷ h₂ ≫ (α_ _ _ _).hom

/-- Squares between right adjoints can be composed "vertically" by pasting. -/
def rightAdjointSquare.vcomp (α : r₁ ≫ g₁ ⟶ h₁ ≫ r₂) (β : r₂ ≫ g₂ ⟶ h₂ ≫ r₃) :
    r₁ ≫ (g₁ ≫ g₂) ⟶ (h₁ ≫ h₂) ≫ r₃ :=
  (α_ _ _ _).inv ≫ α ▷ g₂ ≫ (α_ _ _ _).hom ≫ h₁ ◁ β ≫ (α_ _ _ _).inv

/-- The mates equivalence commutes with vertical composition. -/
theorem mateEquiv_vcomp (α : g₁ ≫ l₂ ⟶ l₁ ≫ h₁) (β : g₂ ≫ l₃ ⟶ l₂ ≫ h₂) :
    mateEquiv adj₁ adj₃ (leftAdjointSquare.vcomp α β) =
      rightAdjointSquare.vcomp (mateEquiv adj₁ adj₂ α) (mateEquiv adj₂ adj₃ β) := by
  dsimp only [leftAdjointSquare.vcomp, mateEquiv_apply, rightAdjointSquare.vcomp]
  symm
  calc
    _ = 𝟙 _ ⊗≫ r₁ ◁ g₁ ◁ adj₂.unit ▷ g₂ ⊗≫ r₁ ◁ α ▷ r₂ ▷ g₂ ⊗≫
          ((adj₁.counit ▷ (h₁ ≫ r₂ ≫ g₂ ≫ 𝟙 e)) ≫ 𝟙 b ◁ (h₁ ◁ r₂ ◁ g₂ ◁ adj₃.unit)) ⊗≫
            h₁ ◁ r₂ ◁ β ▷ r₃ ⊗≫ h₁ ◁ adj₂.counit ▷ h₂ ▷ r₃ ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ r₁ ◁ g₁ ◁ adj₂.unit ▷ g₂ ⊗≫
          (r₁ ◁ (α ▷ (r₂ ≫ g₂ ≫ 𝟙 e) ≫ (l₁ ≫ h₁) ◁ r₂ ◁ g₂ ◁ adj₃.unit)) ⊗≫
            ((adj₁.counit ▷ (h₁ ≫ r₂) ▷ (g₂ ≫ l₃) ≫ (𝟙 b ≫ h₁ ≫ r₂) ◁ β) ▷ r₃) ⊗≫
              h₁ ◁ adj₂.counit ▷ h₂ ▷ r₃ ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]
      bicategory
    _ = 𝟙 _ ⊗≫ r₁ ◁ g₁ ◁ (adj₂.unit ▷ (g₂ ≫ 𝟙 e) ≫ (l₂ ≫ r₂) ◁ g₂ ◁ adj₃.unit) ⊗≫
          (r₁ ◁ (α ▷ (r₂ ≫ g₂ ≫ l₃) ≫ (l₁ ≫ h₁) ◁ r₂ ◁ β) ▷ r₃) ⊗≫
            (adj₁.counit ▷ h₁ ▷ (r₂ ≫ l₂) ≫ (𝟙 b ≫ h₁) ◁ adj₂.counit) ▷ h₂ ▷ r₃ ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange, ← whisker_exchange]
      bicategory
    _ = 𝟙 _ ⊗≫ r₁ ◁ g₁ ◁ g₂ ◁ adj₃.unit ⊗≫
          r₁ ◁ g₁ ◁ (adj₂.unit ▷ (g₂ ≫ l₃) ≫ (l₂ ≫ r₂) ◁ β) ▷ r₃ ⊗≫
            r₁ ◁ (α ▷ (r₂ ≫ l₂) ≫ (l₁ ≫ h₁) ◁ adj₂.counit) ▷ h₂ ▷ r₃ ⊗≫
              adj₁.counit ▷ h₁ ▷ h₂ ▷ r₃ ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange, ← whisker_exchange, ← whisker_exchange]
      bicategory
    _ = 𝟙 _ ⊗≫ r₁ ◁ g₁ ◁ g₂ ◁ adj₃.unit ⊗≫ r₁ ◁ g₁ ◁ β ▷ r₃ ⊗≫
          ((r₁ ≫ g₁) ◁ leftZigzag adj₂.unit adj₂.counit ▷ (h₂ ≫ r₃)) ⊗≫
            r₁ ◁ α ▷ h₂ ▷ r₃ ⊗≫ adj₁.counit ▷ h₁ ▷ h₂ ▷ r₃ ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange, ← whisker_exchange]
      bicategory
    _ = _ := by
      rw [adj₂.left_triangle]
      bicategory

end mateEquivVComp

section mateEquivHComp

variable {a : B} {b : B} {c : B} {d : B} {e : B} {f : B}
variable {g : a ⟶ d} {h : b ⟶ e} {k : c ⟶ f}
variable {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : d ⟶ e} {r₂ : e ⟶ d}
variable {l₃ : b ⟶ c} {r₃ : c ⟶ b} {l₄ : e ⟶ f} {r₄ : f ⟶ e}
variable (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂) (adj₃ : l₃ ⊣ r₃) (adj₄ : l₄ ⊣ r₄)

/-- Squares between left adjoints can be composed "horizontally" by pasting. -/
def leftAdjointSquare.hcomp (α : g ≫ l₂ ⟶ l₁ ≫ h) (β : h ≫ l₄ ⟶ l₃ ≫ k) :
    g ≫ (l₂ ≫ l₄) ⟶ (l₁ ≫ l₃) ≫ k :=
  (α_ _ _ _).inv ≫ α ▷ l₄ ≫ (α_ _ _ _).hom ≫ l₁ ◁ β ≫ (α_ _ _ _).inv

/-- Squares between right adjoints can be composed "horizontally" by pasting. -/
def rightAdjointSquare.hcomp (α : r₁ ≫ g ⟶ h ≫ r₂) (β : r₃ ≫ h ⟶ k ≫ r₄) :
    (r₃ ≫ r₁) ≫ g ⟶ k ≫ (r₄ ≫ r₂) :=
  (α_ _ _ _).hom ≫ r₃ ◁ α ≫ (α_ _ _ _).inv ≫ β ▷ r₂ ≫ (α_ _ _ _).hom

/-- The mates equivalence commutes with horizontal composition of squares. -/
theorem mateEquiv_hcomp (α : g ≫ l₂ ⟶ l₁ ≫ h) (β : h ≫ l₄ ⟶ l₃ ≫ k) :
    (mateEquiv (adj₁.comp adj₃) (adj₂.comp adj₄)) (leftAdjointSquare.hcomp α β) =
      rightAdjointSquare.hcomp (mateEquiv adj₁ adj₂ α) (mateEquiv adj₃ adj₄ β) := by
  dsimp [mateEquiv, leftAdjointSquare.hcomp, rightAdjointSquare.hcomp]
  calc
    _ = 𝟙 _ ⊗≫ r₃ ◁ r₁ ◁ g ◁ adj₂.unit ⊗≫
          r₃ ◁ r₁ ◁ ((g ≫ l₂) ◁ adj₄.unit ≫ α ▷ (l₄ ≫ r₄)) ▷ r₂ ⊗≫
            r₃ ◁ ((r₁ ≫ l₁) ◁ β ≫ adj₁.counit ▷ (l₃ ≫ k)) ▷ r₄ ▷ r₂ ⊗≫
              adj₃.counit ▷ k ▷ r₄ ▷ r₂ ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ r₃ ◁ r₁ ◁ g ◁ adj₂.unit ⊗≫ r₃ ◁ r₁ ◁ α ▷ r₂ ⊗≫
          r₃ ◁ ((r₁ ≫ l₁) ◁ h ◁ adj₄.unit ≫ adj₁.counit ▷ (h ≫ l₄ ≫ r₄)) ▷ r₂ ⊗≫
            r₃ ◁ β ▷ r₄ ▷ r₂ ⊗≫ adj₃.counit ▷ k ▷ r₄ ▷ r₂ ⊗≫ 𝟙 _ := by
      rw [whisker_exchange, whisker_exchange]
      bicategory
    _ = _ := by
      rw [whisker_exchange]
      bicategory

end mateEquivHComp

end Bicategory

end CategoryTheory
