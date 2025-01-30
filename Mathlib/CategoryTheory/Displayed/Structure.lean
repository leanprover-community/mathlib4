/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Adjunction.Over


-- (SH) TODO: Make the proof and construction work with `Disp` rather than `Disp'`.


universe u

open CategoryTheory Category Limits

noncomputable section

variable {C : Type u} [Category C] [HasTerminal C] [HasPullbacks C]

variable {𝔼 𝕌 : C} (π : 𝔼 ⟶ 𝕌)

class DisplayStruct {D A : C} (p : D ⟶ A) where
  char : A ⟶ 𝕌
  var : D ⟶ 𝔼
  disp_pullback : IsPullback var p π char

def IsDisplay : MorphismProperty C  :=
  fun D A (p : D ⟶ A) ↦ Nonempty (DisplayStruct π p)

variable (C) in

/-- `Cart C` is a typeclass synonym for `Arrow C` which comes equipped with
a cateogry structure whereby morphisms between arrows `p` and `q` are cartesian
squares between them. -/
structure Cart where
  arr : Arrow C

namespace Cart

abbrev hom (p : Cart C) := p.arr.hom

@[simp]
lemma IsPullback.of_horiz_id {X Y : C} (f : X ⟶ Y) : IsPullback (𝟙 X) f f (𝟙 Y) := by
  apply IsPullback.of_horiz_isIso
  simp only [CommSq.mk, id_comp, comp_id]

instance : Category (Cart C) where
  Hom p q := {v : p.arr ⟶ q.arr // IsPullback v.left p.arr.hom q.arr.hom v.right}
  id p := ⟨ ⟨𝟙 _, 𝟙 _, by simp⟩, IsPullback.of_horiz_id p.arr.hom⟩
  comp {p q r} u v := ⟨⟨u.1.left ≫ v.1.left, u.1.right ≫ v.1.right, by simp⟩, by
    apply IsPullback.paste_horiz u.2 v.2⟩
  id_comp {p q} f:= by
    simp only [Functor.id_obj, Arrow.mk_left, Arrow.mk_right, id_comp]
    rfl -- we can replace by aesop, but they are a bit slow
  comp_id {p q} f := by
    simp only [Functor.id_obj, Arrow.mk_left, Arrow.mk_right, comp_id]
    rfl
  assoc {p q r s} f g h := by
    simp_all only [Functor.id_obj, Arrow.mk_left, Arrow.mk_right, assoc]

abbrev left {p q : Cart C} (f : p ⟶ q) : p.arr.left ⟶ q.arr.left := f.1.left

abbrev right {p q : Cart C} (f : p ⟶ q) : p.arr.right ⟶ q.arr.right := f.1.right

end Cart

def HasIdentities (W : WideSubquiver C) := ∀ {X}, 𝟙 X ∈ W X X

def HasCompositions (W : WideSubquiver C) :=
  ∀ {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}, f ∈ W X Y → g ∈ W Y Z → (f ≫ g ∈ W X Z)

structure WideSubcategory (C) [Category C] where
  hom : WideSubquiver C
  id : HasIdentities hom
  comp : HasCompositions hom

def WideSubcategory.toCategory {C} [Category C] (W : WideSubcategory C) : Category C where
  Hom X Y := { f : X ⟶ Y // f ∈ W.hom X Y }
  id X := ⟨𝟙 X, W.id⟩
  comp {X Y Z} f g := ⟨f.1 ≫ g.1, W.comp f.2 g.2⟩

section

variable {C : Type*} [Category C]

set_option linter.unusedVariables false in
def WideSubcategory' (P : MorphismProperty C)
    (hP₁ : P.ContainsIdentities) (hP₂ : P.IsStableUnderComposition) :=
  C

instance WideSubcategory'.category (P : MorphismProperty C)
    (hP₁ : P.ContainsIdentities) (hP₂ : P.IsStableUnderComposition) :
    Category (WideSubcategory' P hP₁ hP₂) where
  Hom X Y := { f : X ⟶ Y | P f }
  id := by
    intro X
    apply P.id
  comp := by
    intro X Y Z f g hf hg
    apply Nonempty.elim hf
    apply Nonempty.elim hg
    apply Nonempty.intro
    apply P.comp

end

namespace WideSubcategory

open Cart

@[nolint unusedArguments]
abbrev toType {C} [Category C] (_ : WideSubcategory C) : Type u :=
  C

/-- A wide subcategory viewed as a category on its own. -/
instance category {C} [Category C] (W : WideSubcategory C) : Category (toType W) where
  Hom X Y := { f : X ⟶ Y // f ∈ W.1 X Y }
  id X := ⟨𝟙 X, W.id⟩
  comp := fun {X Y Z} f g => ⟨f.1 ≫ g.1, W.comp f.2 g.2⟩

instance cart : WideSubcategory (Arrow C) where
  hom := fun X Y => { f : X ⟶ Y | IsPullback f.left X.hom Y.hom f.right }
  id := by
    intro X
    apply Cart.IsPullback.of_horiz_id
  comp := by
    intro X Y Z f g hf hg
    apply IsPullback.paste_horiz hf hg

end WideSubcategory

def displayStructPresheaf : (Cart C)ᵒᵖ  ⥤ Type u where
  obj p := DisplayStruct π p.unop.hom
  map {p q} f := fun d ↦ ⟨f.unop.1.right ≫ d.char, f.unop.1.left ≫ d.var, by
    apply IsPullback.paste_horiz f.unop.2 d.disp_pullback⟩
  map_id := by sorry
  map_comp := by sorry

/-- A display morphism is an arrow equipped with a display structure. -/
abbrev Disp := ((displayStructPresheaf π).Elements)ᵒᵖ

namespace Disp

variable {π}

def forget : Disp π ⥤ Cart C :=
(CategoryOfElements.π (displayStructPresheaf π)).leftOp

/-- The underlying arrow of a display map. -/
def arr (α : Disp π) : Arrow C := α.unop.1.unop.arr

lemma arr_eq {α : Disp π} : α.arr = (forget.obj α).arr := rfl

/-- The base (i.e. codomain) of a display map. -/
def base (α : Disp π) : C := α.arr.right

def top (α : Disp π) : C := α.arr.left

/-- The charateristic map of a display map. -/
def char (α : Disp π) : α.base ⟶ 𝕌 := α.unop.2.char

/-- The variable map of a display map. -/
def var (α : Disp π) : α.top ⟶ 𝔼 := α.unop.2.var

/-- The pullback square of a displayed map. -/
def pullback (α : Disp π) : IsPullback α.var α.arr.hom π α.char := α.unop.2.disp_pullback

/-- Coercion of `Disp` into `Arrow C`. -/
instance : CoeOut (Disp π) (Arrow C) where
  coe := fun α => α.arr

lemma coe_to_cart {α : Disp π} : (α : Arrow C) = α.arr := rfl

variable {α β : Disp π} (f : α ⟶ β)

def Hom.cart {α β : Disp π} (f : α ⟶ β) := f.unop.1.unop

def Hom.arr {α β : Disp π} (f : α ⟶ β) : α.arr ⟶ β.arr := f.unop.1.unop.1

instance {α β : Disp π} : CoeOut (α ⟶ β) (α.arr ⟶ β.arr) where
  coe := fun f => Hom.arr f

lemma Hom.arr.left : (f : α.arr ⟶ β.arr).left = f.unop.1.unop.1.left := rfl

lemma Hom.arr.right : (f : α.arr ⟶ β.arr).right = f.unop.1.unop.1.right := rfl

/-- The underyling commutative square of a morphism of display maps. A morphism `f : α ⟶ β`
gives rise to a commutative square from `β.arr` to `α.arr`. -/
theorem Hom.commSq {α β : Disp π} (f : α ⟶ β) :
    CommSq (f : α.arr ⟶ β.arr).left α.arr.hom β.arr.hom (f : α.arr ⟶ β.arr).right := by
  apply CommSq.flip
  apply CommSq.of_arrow

/-- The underyling commutative square of a morphism of display maps is cartesian.-/
theorem Hom.is_cartesian {α β : Disp π} (f : α ⟶ β) :
    IsPullback (f : α.arr ⟶ β.arr).left α.arr.hom β.arr.hom (f : α.arr ⟶ β.arr).right :=
  f.unop.1.unop.2

end Disp

def Arrow.Hom.mk {α β : Disp π} (t : β.base ⟶ α.base) (h : t ≫ α.char = β.char) :
    let cone := PullbackCone.mk β.var (β.arr.hom ≫ t) <| by
      rw [Category.assoc, β.pullback.w, h]
    β.arr ⟶ α.arr where
      left := α.pullback.isLimit.lift cone
      right := t
      w := by
        dsimp
        have h₁ := α.pullback
        have h₂ := β.pullback
        have h₃ : _ ≫ α.var = β.var := α.pullback.isLimit.fac _ (some .left)
        rw [← f.2, ← h₃] at h₂
  exact (IsPullback.of_right h₂ (P.disp.disp_pullback.isLimit.fac cone (some .right)) h₁)

def Disp.Hom.mk {α β : Disp π} (t : β.base ⟶ α.base)  (h : t ≫ α.char = β.char) :
    α ⟶ β where
  unop := {
    val := {
      unop := {
        val := α.
        property := _
      }
    }
    property := _
  }

structure Disp' where
  T : C
  B : C
  p : T ⟶ B
  disp : DisplayStruct π p := by infer_instance

namespace DisplayStruct

structure Hom {D A E B : C} (p : D ⟶ A) [i : DisplayStruct π p]
    (q : E ⟶ B) [j : DisplayStruct π q] where
  base : B ⟶ A
  base_eq : base ≫ i.char = j.char

-- Note : This is a different category instance than the one in the `Disp` type.
instance category : Category (Disp' π) where
  Hom P Q :=  {t : P.B ⟶ Q.B // (t ≫ Q.disp.char) = P.disp.char}
  id (P : Disp' π) := ⟨𝟙 P.B, by simp only [id_comp]⟩
  comp {P Q R : Disp' π} f g := ⟨f.1 ≫ g.1, by simp only [assoc, f.2, g.2]⟩

/-- A morphism of display maps is necessarily cartesian: The cartesian square is obtained by the
pullback pasting lemma. -/
theorem is_cartesian' {Q P : Disp' π} (f : Q ⟶ P) :
    let cone := PullbackCone.mk Q.disp.var (Q.p ≫ f.1) <| by
      rw [Category.assoc, f.2]; exact Q.disp.disp_pullback.w
    IsPullback (P.disp.disp_pullback.isLimit.lift cone) Q.p P.p f.1 := by
  let cone := PullbackCone.mk Q.disp.var (Q.p ≫ f.1) <| by
    rw [Category.assoc, f.2]
    exact Q.disp.disp_pullback.w
  let v := P.disp.disp_pullback.isLimit.lift cone
  have h₁ := P.disp.disp_pullback
  have h₂ := Q.disp.disp_pullback
  have h₃ : v ≫ P.disp.var = Q.disp.var := P.disp.disp_pullback.isLimit.fac cone (some .left)
  rw [← f.2, ← h₃] at h₂
  exact (IsPullback.of_right h₂ (P.disp.disp_pullback.isLimit.fac cone (some .right)) h₁)

def pullback {D A E B : C} (π : E ⟶ B) (p : D ⟶ A) (q : E ⟶ B)
    [i : DisplayStruct π p] [j : DisplayStruct π q]
    (t : B ⟶ A) (h : t ≫ i.char = j.char) :
    DisplayStruct p q  where -- should be changed to a morphism from Disp'.mk p to Disp'.mk q
  char := t
  var := i.disp_pullback.isLimit.lift <| PullbackCone.mk j.var (q ≫ t) <| by
    rw [Category.assoc, h]
    exact j.disp_pullback.w
  disp_pullback := by
    let c := PullbackCone.mk j.var (q ≫ t) (by rw [Category.assoc, h]; exact j.disp_pullback.w)
    let v := i.disp_pullback.isLimit.lift c
    show IsPullback v ..
    have h₁ := i.disp_pullback
    have h₂ := j.disp_pullback
    have h₃ : v ≫ i.var = j.var := i.disp_pullback.isLimit.fac c (some .left)
    rw [← h, ← h₃] at h₂
    exact (IsPullback.of_right h₂ (i.disp_pullback.isLimit.fac c (some .right)) h₁)

def displayMapOfPullback {D A B : C} (p : D ⟶ A) [i : DisplayStruct π p] (t : B ⟶ A) :
    DisplayStruct π (pullback.snd : Limits.pullback p t ⟶ B) where
  char := t ≫ i.char
  var := pullback.fst ≫ i.var
  disp_pullback := IsPullback.paste_horiz (IsPullback.of_hasPullback _ _) i.disp_pullback

end DisplayStruct

variable {Ctx : Type u} [SmallCategory Ctx] [HasTerminal Ctx]

open NaturalModel in

instance [NaturalModelBase Ctx] (Γ : Ctx) (A : y(Γ) ⟶ Ty) :
    DisplayStruct tp (yoneda.map (disp Γ A)) where
  char := A
  var := var Γ A
  disp_pullback := disp_pullback A
