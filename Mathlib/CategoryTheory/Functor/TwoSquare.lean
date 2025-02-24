/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Jakob von Raumer
-/
import Mathlib.CategoryTheory.Equivalence
/-!
# 2-squares of functors

Given four functors `T`, `L`, `R` and `B`, a 2-square `TwoSquare T L R B` consists of
a natural transformation `w : T ⋙ R ⟶ L ⋙ B`:
```
     T
  C₁ ⥤ C₂
L |     | R
  v     v
  C₃ ⥤ C₄
     B
```

We define operations to paste such squares horizontally and vertically and prove the interchange
law of those two operations.

## TODO

Generalize all of this to double categories.

-/

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉

namespace CategoryTheory

open Category

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)

/-- A `2`-square consists of a natural transformation `T ⋙ R ⟶ L ⋙ B`
involving fours functors `T`, `L`, `R`, `B` that are on the
top/left/right/bottom sides of a square of categories. -/
def TwoSquare := T ⋙ R ⟶ L ⋙ B

namespace TwoSquare

/-- Constructor for `TwoSquare`. -/
abbrev mk (α : T ⋙ R ⟶ L ⋙ B) : TwoSquare T L R B := α

variable {T L R B}

@[ext]
lemma ext (w w' : TwoSquare T L R B) (h : ∀ (X : C₁), w.app X = w'.app X) :
    w = w' :=
  NatTrans.ext (funext h)

/-- The hoizontal identity 2-square. -/
def hId (L : C₁ ⥤ C₃) : TwoSquare (𝟭 _) L L (𝟭 _) :=
  𝟙 _

/-- Notation for the horizontal identity 2-square. -/
scoped notation "𝟙ₕ" => hId  -- type as \b1\_h

/-- The vertical identity 2-square. -/
def vId (T : C₁ ⥤ C₂) : TwoSquare T (𝟭 _) (𝟭 _) T :=
  𝟙 _

/-- Notation for the vertical identity 2-square. -/
scoped notation "𝟙ᵥ" => vId  -- type as \b1\_v

variable {C₅ : Type u₅} {C₆ : Type u₆} {C₇ : Type u₇} {C₈ : Type u₈}
  [Category.{v₅} C₅] [Category.{v₆} C₆] [Category.{v₇} C₇] [Category.{v₈} C₈]
  {T' : C₂ ⥤ C₅} {R' : C₅ ⥤ C₆} {B' : C₄ ⥤ C₆} {L' : C₃ ⥤ C₇} {R'' : C₄ ⥤ C₈} {B'' : C₇ ⥤ C₈}

/-- The horizontal composition of 2-squares. -/
def hComp (w : TwoSquare T L R B) (w' : TwoSquare T' R R' B') :
    TwoSquare (T ⋙ T') L R' (B ⋙ B') :=
  (whiskerLeft T w') ≫ (whiskerRight w B')

/-- Notation for the horizontal composition of 2-squares. -/
scoped infixr:80 " ≫ₕ " => hComp -- type as \gg\_h

/-- The vertical composition of 2-squares. -/
def vComp (w : TwoSquare T L R B) (w' : TwoSquare B L' R'' B'') :
    TwoSquare T (L ⋙ L') (R ⋙ R'') B'' :=
  (whiskerRight w R'') ≫ (whiskerLeft L w')

/-- Notation for the vertical composition of 2-squares. -/
scoped infixr:80 " ≫ᵥ " => vComp -- type as \gg\_v

section Interchange

variable {C₉ : Type u₉} [Category.{v₉} C₉] {R₃ : C₆ ⥤ C₉} {B₃ : C₈ ⥤ C₉}

/-- When composing 2-squares which form a diagram of grid, compositing horionzall first yields the
same result as composing vertically first. -/
lemma hCompVComphComp (w₁ : TwoSquare T L R B) (w₂ : TwoSquare T' R R' B')
    (w₃ : TwoSquare B L' R'' B'') (w₄ : TwoSquare B' R'' R₃ B₃) :
    (w₁ ≫ₕ w₂) ≫ᵥ (w₃ ≫ₕ w₄) = (w₁ ≫ᵥ w₃) ≫ₕ (w₂ ≫ᵥ w₄) := by
  unfold hComp vComp
  unfold whiskerLeft whiskerRight
  ext c
  simp only [Functor.comp_obj, NatTrans.comp_app, Functor.map_comp, assoc]
  slice_rhs 2 3 =>
    rw [← Functor.comp_map _ B₃, ← w₄.naturality]
  simp only [Functor.comp_obj, Functor.comp_map, assoc]

end Interchange

end TwoSquare

end CategoryTheory
