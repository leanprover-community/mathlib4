import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.DeriveFintype

universe w v₁ v₂ u

namespace CategoryTheory

/-- A double quiver on a type `C` of vertices is simply a pair of quiver
structures on `C`. The two sorts of arrows are by convention called
"horizontal" and "vertical"; we picture the vertical arrows as oriented
downwards and the horizontal arrows as oriented left-to-right. -/
class DoubleQuiver (C : Type u) where
  HorizontalHom : C → C → Type v₁
  VerticalHom : C → C → Type v₂

-- TODO: version of `to_additive` for horizontal/vertical

/-- When we have some sort of double-categorical structure `C` and wish to
emphasize its horizontal part we use the type `Horizontal C`. -/
structure Horizontal (C : Type u) where mkH :: X : C
  deriving DecidableEq, Nonempty, Inhabited, Fintype

@[simps]
def Horizontal.equivToHorizontal {C : Type u} : C ≃ Horizontal C :=
  { toFun := mkH, invFun := X, left_inv := fun _ => rfl, right_inv := fun _ => rfl }

instance instSubsingletonHorizontal (C : Type u) [Subsingleton C] :
    Subsingleton (Horizontal C) := Horizontal.equivToHorizontal.symm.subsingleton

instance instUniqueHorizontal (C : Type u) [Unique C] : Unique (Horizontal C) :=
  Horizontal.equivToHorizontal.symm.unique

/-- When we have some sort of double-categorical structure `C` and wish to
emphasize its vertical part we use the type `Vertical C`. -/
structure Vertical (C : Type u) where mkV :: X : C
  deriving DecidableEq, Nonempty, Inhabited, Fintype

@[simps]
def Vertical.equivToVertical {C : Type u} : C ≃ Vertical C :=
  { toFun := mkV, invFun := X, left_inv := fun _ => rfl, right_inv := fun _ => rfl }

instance instSubsingletonVertical (C : Type u) [Subsingleton C] :
    Subsingleton (Vertical C) := Vertical.equivToVertical.symm.subsingleton

instance instUniqueVertical (C : Type u) [Unique C] : Unique (Vertical C) :=
  Vertical.equivToVertical.symm.unique

namespace DoubleQuiver

variable (C : Type u) [DoubleQuiver.{v₁, v₂} C]

--Should this be scoped? if so, in what namespace?
/--
Notation for the type of vertical arrows between a given source and target
in a quiver or category.
-/
infixr:10 " ⟶ₕ " => DoubleQuiver.HorizontalHom

/--
Notation for the type of vertical arrows between a given source and target
in a quiver or category.
-/
infixr:10 " ⟶ᵥ " => DoubleQuiver.VerticalHom

instance : Quiver (Horizontal C) where Hom X Y := X.X ⟶ₕ Y.X
instance : Quiver (Vertical C) where Hom X Y := X.X ⟶ᵥ Y.X

end DoubleQuiver

/-- The boundary of a square in `C`, with descriptive names for the fields. -/
structure SkeletalSquare (C : Type u) [DoubleQuiver.{v₁, v₂} C] where
  topLeft : C
  topRight : C
  bottomLeft : C
  bottomRight : C
  top : topLeft ⟶ₕ topRight
  left : topLeft ⟶ᵥ bottomLeft
  right : topRight ⟶ᵥ bottomRight
  bottom : bottomLeft ⟶ₕ bottomRight

class SquareQuiver (C : Type u) extends DoubleQuiver.{v₁, v₂} C where
  -- order is consistent with CategoryTheory.CommSq
  Square {topLeft topRight bottomLeft bottomRight : C}
    (top : topLeft ⟶ₕ topRight) (left : topLeft ⟶ᵥ bottomLeft)
    (right : topRight ⟶ᵥ bottomRight) (bottom : bottomLeft ⟶ₕ bottomRight) : Type w

namespace SquareQuiver

end SquareQuiver

open scoped SquareQuiver

def SkeletalSquare.Filler {C : Type u} [SquareQuiver.{w, v₁, v₂} C]
    (bd : SkeletalSquare C) : Type w :=
  SquareQuiver.Square bd.top bd.left bd.right bd.bottom

-- Just a proof of concept. Strict double categories will eventually be a form of
-- Verity double bicategory
class DoubleCategoryStruct (C : Type u) extends SquareQuiver.{w, v₁, v₂} C where
  hid₁ (X : C) : X ⟶ₕ X
  vid₁ (X : C) : X ⟶ᵥ X
  hid₂ {X Y : C} (f : X ⟶ᵥ Y) : Square (hid₁ X) f f (hid₁ Y)
  vid₂ {X Y : C} (f : X ⟶ₕ Y) : Square f (vid₁ X) (vid₁ Y) f
  hcomp₁ {X Y Z : C} (f : X ⟶ₕ Y) (g : Y ⟶ₕ Z) : X ⟶ₕ Z
  vcomp₁ {X Y Z : C} (f : X ⟶ᵥ Y) (g : Y ⟶ᵥ Z) : X ⟶ᵥ Z
  hcomp₂ {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} {f₁₁₁₂ : X₁₁ ⟶ₕ X₁₂}
    {f₁₁₂₁ : X₁₁ ⟶ᵥ X₂₁} {f₁₂₁₃ : X₁₂ ⟶ₕ X₁₃} {f₁₂₂₂ : X₁₂ ⟶ᵥ X₂₂}
    {f₁₃₂₃ : X₁₃ ⟶ᵥ X₂₃} {f₂₁₂₂ : X₂₁ ⟶ₕ X₂₂} {f₂₂₂₃ : X₂₂ ⟶ₕ X₂₃} :
    Square f₁₁₁₂ f₁₁₂₁ f₁₂₂₂ f₂₁₂₂ → Square f₁₂₁₃ f₁₂₂₂ f₁₃₂₃ f₂₂₂₃ →
    Square (hcomp₁ f₁₁₁₂ f₁₂₁₃) f₁₁₂₁ f₁₃₂₃ (hcomp₁ f₂₁₂₂ f₂₂₂₃)
  vcomp₂ {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {f₁₁₁₂ : X₁₁ ⟶ₕ X₁₂}
    {f₁₁₂₁ : X₁₁ ⟶ᵥ X₂₁} {f₁₂₂₂ : X₁₂ ⟶ᵥ X₂₂} {f₂₁₂₂ : X₂₁ ⟶ₕ X₂₂}
    {f₂₁₃₁ : X₂₁ ⟶ᵥ X₃₁} {f₂₂₃₂ : X₂₂ ⟶ᵥ X₃₂} {f₃₁₃₂ : X₃₁ ⟶ₕ X₃₂} :
    Square f₁₁₁₂ f₁₁₂₁ f₁₂₂₂ f₂₁₂₂ → Square f₂₁₂₂ f₂₁₃₁ f₂₂₃₂ f₃₁₃₂ →
    Square f₁₁₁₂ (vcomp₁ f₁₁₂₁ f₂₁₃₁) (vcomp₁ f₁₂₂₂ f₂₂₃₂) f₃₁₃₂

/-- Notation for the identity horizontal morphism in a double category. -/
scoped notation "𝟙ₕ" => DoubleCategoryStruct.hid₁

/-- Notation for the identity vertical morphism in a double category. -/
scoped notation "𝟙ᵥ" => DoubleCategoryStruct.vid₁

/-- Notation for the horizontal identity square in a double category. -/
scoped notation "𝟙ₕ_" => DoubleCategoryStruct.hid₂

/-- Notation for the vertical identity square in a double category. -/
scoped notation "𝟙ᵥ_" => DoubleCategoryStruct.vid₂

/-- Notation for composition of horizontal morphisms in a double category. -/
scoped infixr:80 " ≫ₕ " => DoubleCategoryStruct.hcomp₁

/-- Notation for composition of vertical morphisms in a double category. -/
-- I'm not 100% satisfied with `≫ᵥ`. Would be nice to have two stacked vertical arrows
scoped infixr:80 " ≫ᵥ " => DoubleCategoryStruct.vcomp₁

-- possible alternate notation: ⧓ ⧗, ▤ ▥
/-- Notation for horizontal composition of squares in a double category. -/
-- not going to work unless we can move NatTrans.hcomp into a scope
scoped infixr:80 " ◫ " => DoubleCategoryStruct.hcomp₂

/-- Notation for vertical composition of squares in a double category. -/
scoped infixr:80 " ⊟ " => DoubleCategoryStruct.vcomp₂

class DoubleCategory (C : Type u) extends DoubleCategoryStruct.{w, v₁, v₂} C where
  hid₁_hcomp₁ {X Y : C} (f : X ⟶ₕ Y) : 𝟙ₕ X ≫ₕ f = f := by aesop_cat
  hcomp₁_hid₁ {X Y : C} (f : X ⟶ₕ Y) : f ≫ₕ 𝟙ₕ Y = f := by aesop_cat
  vid₁_vcomp₁ {X Y : C} (f : X ⟶ᵥ Y) : 𝟙ᵥ X ≫ᵥ f = f := by aesop_cat
  vcomp₁_vid₁ {X Y : C} (f : X ⟶ᵥ Y) : f ≫ᵥ 𝟙ᵥ Y = f := by aesop_cat

  hid₂_hcomp₂ {topLeft topRight bottomLeft bottomRight : C}
    {top : topLeft ⟶ₕ topRight} {left : topLeft ⟶ᵥ bottomLeft}
    {right : topRight ⟶ᵥ bottomRight} {bottom : bottomLeft ⟶ₕ bottomRight}
    (σ : Square top left right bottom) : 𝟙ₕ_ left ◫ σ =
        cast (congrArg₂ (Square · left right ·)
              (hid₁_hcomp₁ top).symm (hid₁_hcomp₁ bottom).symm) σ := by aesop_cat
  -- hcomp₂_hid₂ {X Y : C} (f : X ⟶ₕ Y) : f ≫ₕ 𝟙ₕ Y = f := by aesop_cat
  -- vid₂_vcomp₂ {X Y : C} (f : X ⟶ᵥ Y) : 𝟙ᵥ X ≫ᵥ f = f := by aesop_cat
  -- vcomp₂_vid₂ {X Y : C} (f : X ⟶ᵥ Y) : f ≫ᵥ 𝟙ᵥ Y = f := by aesop_cat

  hcomp₁_assoc {W X Y Z : C} (f : W ⟶ₕ X) (g : X ⟶ₕ Y) (h : Y ⟶ₕ Z) :
    (f ≫ₕ g) ≫ₕ h = f ≫ₕ g ≫ₕ h := by aesop_cat
  vcomp₁_assoc {W X Y Z : C} (f : W ⟶ᵥ X) (g : X ⟶ᵥ Y) (h : Y ⟶ᵥ Z) :
    (f ≫ᵥ g) ≫ᵥ h = f ≫ᵥ g ≫ᵥ h := by aesop_cat

end CategoryTheory
