/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.Tactic.CategoryTheory.Slice

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

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉

namespace CategoryTheory

open Category CategoryTheory.Functor

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)

/-- A `2`-square consists of a natural transformation `T ⋙ R ⟶ L ⋙ B`
involving fours functors `T`, `L`, `R`, `B` that are on the
top/left/right/bottom sides of a square of categories. -/
abbrev TwoSquare := T ⋙ R ⟶ L ⋙ B

namespace TwoSquare

/-- Constructor for `TwoSquare`. -/
abbrev mk (α : T ⋙ R ⟶ L ⋙ B) : TwoSquare T L R B := α

variable {T} {L} {R} {B} in
/-- The natural transformation associated to a 2-square. -/
@[deprecated "No replacement" (since := "2026-09-18")]
abbrev natTrans (w : TwoSquare T L R B) : T ⋙ R ⟶ L ⋙ B := w

/-- The type of 2-squares on functors `T`, `L`, `R`, and `B` is trivially equivalent to
the type of natural transformations `T ⋙ R ⟶ L ⋙ B`. -/
@[simps, deprecated "No replacement" (since := "2026-09-18")]
def equivNatTrans : TwoSquare T L R B ≃ (T ⋙ R ⟶ L ⋙ B) where
  toFun := natTrans
  invFun := mk T L R B

variable {T L R B}

/-- The opposite of a `2`-square. -/
abbrev op (α : TwoSquare T L R B) : TwoSquare L.op T.op B.op R.op := NatTrans.op α

@[deprecated "No replacement" (since := "2026-09-18")]
lemma natTrans_op (α : TwoSquare T L R B) :
    α.op.natTrans = NatTrans.op α.natTrans := rfl

@[deprecated "Use NatTrans.ext" (since := "2026-09-18")]
lemma ext (w w' : TwoSquare T L R B) (h : ∀ (X : C₁), w.natTrans.app X = w'.natTrans.app X) :
    w = w' :=
  NatTrans.ext (funext h)

/-- The horizontal identity 2-square. -/
@[simps!]
def hId (L : C₁ ⥤ C₃) : TwoSquare (𝟭 _) L L (𝟭 _) :=
  (Functor.leftUnitor L).hom ≫ (Functor.rightUnitor L).inv

/-- Notation for the horizontal identity 2-square. -/
scoped notation "𝟙ₕ" => hId  -- type as \b1\_h

/-- The vertical identity 2-square. -/
@[simps!]
def vId (T : C₁ ⥤ C₂) : TwoSquare T (𝟭 _) (𝟭 _) T :=
  (Functor.rightUnitor T).hom ≫ (Functor.leftUnitor T).inv

/-- Notation for the vertical identity 2-square. -/
scoped notation "𝟙ᵥ" => vId  -- type as \b1\_v

/-- Whiskering a 2-square with a natural transformation at the top. -/
@[simps!]
protected def whiskerTop {T' : C₁ ⥤ C₂} (w : TwoSquare T' L R B) (α : T ⟶ T') : TwoSquare T L R B :=
  whiskerRight α R ≫ w

/-- Whiskering a 2-square with a natural transformation at the left side. -/
@[simps!]
protected def whiskerLeft {L' : C₁ ⥤ C₃} (w : TwoSquare T L R B) (α : L ⟶ L') :
    TwoSquare T L' R B :=
  w ≫ whiskerRight α B

/-- Whiskering a 2-square with a natural transformation at the right side. -/
@[simps!]
protected def whiskerRight {R' : C₂ ⥤ C₄} (w : TwoSquare T L R' B) (α : R ⟶ R') :
    TwoSquare T L R B :=
  whiskerLeft T α ≫ w

/-- Whiskering a 2-square with a natural transformation at the bottom. -/
@[simps!]
protected def whiskerBottom {B' : C₃ ⥤ C₄} (w : TwoSquare T L R B) (α : B ⟶ B') :
    TwoSquare T L R B' :=
  w ≫ whiskerLeft L α

variable {C₅ : Type u₅} {C₆ : Type u₆} {C₇ : Type u₇} {C₈ : Type u₈}
  [Category.{v₅} C₅] [Category.{v₆} C₆] [Category.{v₇} C₇] [Category.{v₈} C₈]
  {T' : C₂ ⥤ C₅} {R' : C₅ ⥤ C₆} {B' : C₄ ⥤ C₆} {L' : C₃ ⥤ C₇} {R'' : C₄ ⥤ C₈} {B'' : C₇ ⥤ C₈}

/-- The horizontal composition of 2-squares. -/
@[simps!]
def hComp (w : TwoSquare T L R B) (w' : TwoSquare T' R R' B') :
    TwoSquare (T ⋙ T') L R' (B ⋙ B') :=
  (associator _ _ _).hom ≫ (whiskerLeft T w') ≫
    (associator _ _ _).inv ≫ (whiskerRight w B') ≫ (associator _ _ _).hom

/-- Notation for the horizontal composition of 2-squares. -/
scoped infixr:80 " ≫ₕ " => hComp -- type as \gg\_h

/-- The vertical composition of 2-squares. -/
@[simps!]
def vComp (w : TwoSquare T L R B) (w' : TwoSquare B L' R'' B'') :
    TwoSquare T (L ⋙ L') (R ⋙ R'') B'' :=
  (associator _ _ _).inv ≫ whiskerRight w R'' ≫
    (associator _ _ _).hom ≫ whiskerLeft L w' ≫ (associator _ _ _).inv

/-- Notation for the vertical composition of 2-squares. -/
scoped infixr:80 " ≫ᵥ " => vComp -- type as \gg\_v

section Interchange

variable {C₉ : Type u₉} [Category.{v₉} C₉] {R₃ : C₆ ⥤ C₉} {B₃ : C₈ ⥤ C₉}

/-- When composing 2-squares which form a diagram of grid, composing horizontally first yields the
same result as composing vertically first. -/
lemma hCompVCompHComp (w₁ : TwoSquare T L R B) (w₂ : TwoSquare T' R R' B')
    (w₃ : TwoSquare B L' R'' B'') (w₄ : TwoSquare B' R'' R₃ B₃) :
    (w₁ ≫ₕ w₂) ≫ᵥ (w₃ ≫ₕ w₄) = (w₁ ≫ᵥ w₃) ≫ₕ (w₂ ≫ᵥ w₄) := by
  unfold hComp vComp whiskerLeft whiskerRight
  ext c
  simp only [comp_obj, NatTrans.comp_app, associator_hom_app, associator_inv_app, comp_id, id_comp,
    map_comp, assoc]
  slice_rhs 2 3 =>
    rw [← Functor.comp_map _ B₃, ← w₄.naturality]
  simp

end Interchange

section prod

variable {D₁ D₂ D₃ D₄ : Type*}
  [Category* D₁] [Category* D₂] [Category* D₃] [Category* D₄]
  {T' : D₁ ⥤ D₂} {L' : D₁ ⥤ D₃} {R' : D₂ ⥤ D₄} {B' : D₃ ⥤ D₄}

/-- The external product of two `2`-squares of functors. -/
@[simps!]
def prod (w : TwoSquare T L R B) (w' : TwoSquare T' L' R' B') :
    TwoSquare (T.prod T') (L.prod L') (R.prod R') (B.prod B') :=
  NatTrans.prod w w'

end prod

end TwoSquare

end CategoryTheory
