/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.Tactic.CategoryTheory.CatNF
public import Mathlib.CategoryTheory.Functor.Const

public section

namespace MathlibTest.CategoryTheory

open _root_.CategoryTheory
universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]
variable (F : C ⥤ D) (G : D ⥤ E)
variable {c1 c2 c3 c4 c5 c6 : C} (f1 : c1 ⟶ c2) (f2 : c2 ⟶ c3) (f3 : c3 ⟶ c4) (f4 : c4 ⟶ c5) (f5 : c5 ⟶ c6)
variable {e7 e8 e9 : E} (h7 : G.obj (F.obj c6) ⟶ e7) (h8 : e7 ⟶ e8) (h9 : e8 ⟶ e9)

-- Making sure associativity is normalized and identities are removed:
/-- info: f1 ≫ f2 ≫ f3 : c1 ⟶ c4 -/
#guard_msgs in
#check cat_nf% ((𝟙 c1 ≫ f1) ≫ 𝟙 c2 ≫ f2) ≫ f3

example : ((F ⋙ G).map (𝟙 _ ≫ f5) ≫ h7) ≫ h8 = G.map (F.map f5) ≫ h7 ≫ h8 := by
  simp only [cat_nf]

example : ((F ⋙ G).map (𝟙 _ ≫ f5) ≫ h7) ≫ h8 = G.map (F.map f5) ≫ h7 ≫ h8 := by
  simp only [cat_nf]

example : ((F ⋙ G).map (𝟙 _ ≫ f5) ≫ h7) ≫ h8 = G.map (F.map f5) ≫ h7 ≫ h8 := by
  simp only [cat_nf]

-- `NatTrans.naturality` must not be tagged with `cat_nf`
variable (F' : C ⥤ D) (φ : F ⟶ F') in
/-- error: `simp` made no progress -/
#guard_msgs in
#check cat_nf% φ.naturality

-- Testing `cat_nf%` on a proof

/-- info: ∀ ⦃X Y : C⦄ (f : X ⟶ Y), f ≫ η.app Y = η.app X ≫ R.map (F.map f) : Prop -/
#guard_msgs in
variable (R : D ⥤ C) (η : 𝟭 C ⟶ F ⋙ R) in
#check type_of% (cat_nf% η.naturality)

-- If `cat_nf%` normalizes to a tautology it will normalize to `True`, let’s say it’s a feature.
/-- info: True : Prop -/
#guard_msgs in
#check type_of% (cat_nf% ((𝟙 (𝟭 C) : _ ⟶ _) |>.naturality f1))

example : ((F ⋙ G).map (𝟙 _ ≫ f5 ≫ 𝟙 _ ≫ 𝟙 _ ≫
    (𝟙 (𝟭 _ |>.obj c6) ≫ 𝟙 (((Functor.const C).obj _).obj c6)) ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) ≫ h7) ≫ h8 =
      G.map (F.map f5) ≫ h7 ≫ (((Functor.const C).map (𝟭 _ |>.map h8)).app c1) := by
  simp only [cat_nf]

end MathlibTest.CategoryTheory
