/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou
-/
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-!
# The opposite of a bicategory
-/

universe w v u

namespace CategoryTheory

open Opposite

namespace Bicategory.Opposite

variable {B : Type u} [Bicategory.{w, v} B]

instance {X Y : Bᵒᵖ} : Category.{w} (X ⟶ Y) :=
  inferInstanceAs <| Category (Y.unop ⟶ X.unop)ᵒᵖ

@[simp]
lemma Hom.unop_comp {a b : Bᵒᵖ} {f g h : a ⟶ b} (u : f ⟶ g) (v : g ⟶ h)  :
    (u ≫ v).unop = v.unop ≫ u.unop := rfl

@[simp]
lemma Hom.unop_id {a b : Bᵒᵖ} (f : a ⟶ b) :
    (𝟙 f).unop = 𝟙 f.unop := rfl

@[ext]
lemma Hom.ext {a b : Bᵒᵖ} {f g : a ⟶ b} (u v : f ⟶ g) (h : u.unop = v.unop) : u = v :=
  congrArg op h

@[simps!]
def associator {a b c d : Bᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    op (h.unop ≫ Quiver.Hom.unop (Opposite.op (g.unop ≫ f.unop))) ≅
    op (Quiver.Hom.unop (Opposite.op (h.unop ≫ g.unop)) ≫ f.unop) :=
  (α_ h.unop g.unop f.unop).op

@[simps!]
def leftUnitor {a b : Bᵒᵖ} (f : a ⟶ b) :
    op (f.unop ≫ Quiver.Hom.unop (op (𝟙 (unop a)))) ≅ f :=
  (rightUnitor f.unop).symm.op

@[simps!]
def rightUnitor {a b : Bᵒᵖ} (f : a ⟶ b) :
    op (Quiver.Hom.unop (op (𝟙 (unop b))) ≫ f.unop) ≅ f :=
  (Bicategory.leftUnitor f.unop).symm.op

instance : Bicategory Bᵒᵖ where
  id X := ⟨𝟙 X.unop⟩
  comp {X Y Z} f g := ⟨g.unop ≫ f.unop⟩
  whiskerLeft {X Y Z} f g h u := (u.unop ▷ f.unop).op
  whiskerRight {X Y Z} f g h u := (u.unop ◁ h.unop).op
  associator {a b c d} f g h := associator f g h
  leftUnitor {a b} f := leftUnitor f
  rightUnitor {a b} f := rightUnitor f
  whiskerLeft_id {a b c} f g := congrArg op <| id_whiskerRight g.unop f.unop
  id_whiskerRight f g := congrArg op <| whiskerLeft_id g.unop f.unop
  whisker_exchange η θ := congrArg op <| whisker_exchange θ.unop η.unop
  whisker_assoc f g h u v := by
    ext
    dsimp
    rw [whisker_assoc_symm, Category.assoc]
    rfl
  triangle f g := congrArg op <| triangle_assoc_comp_right_inv (unop g) f.unop

@[simp]
lemma unop_comp {a b c : Bᵒᵖ} {f : a ⟶ b} {g : b ⟶ c} : (f ≫ g).unop = g.unop ≫ f.unop := rfl

@[simp] lemma unop_whiskerLeft {a b c : Bᵒᵖ} {f : a ⟶ b} {g h : b ⟶ c} {u : g ⟶ h} :
    (f ◁ u).unop = u.unop ▷ f.unop := rfl

@[simp] lemma unop_whiskerRight {a b c : Bᵒᵖ} {f g : a ⟶ b} (h : b ⟶ c) (u : f ⟶ g) :
    (u ▷ h).unop = h.unop ◁ u.unop := rfl

end Bicategory.Opposite

end CategoryTheory
