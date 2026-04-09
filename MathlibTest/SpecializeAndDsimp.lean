/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Condensed.Basic
import Mathlib.Tactic.SpecializeAndDsimp
import Mathlib.Tactic

lemma test {X : Type} [Add X] (x y : X) : x + y = x + y := by
  rfl

spec_dsimp("created", test, Nat)

-- this should create the following lemma:
-- lemma created (x y : Nat) : x + y = x + y := spec_dsimp(test, Nat)

open CategoryTheory Functor

lemma test₂ {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) (X Y : C) (i : X ≅ Y) :
    F.map i.hom ≫ F.map i.inv = 𝟙 (F.obj X) := by
  simp

section created₂_gen
variable {C D E : Type*} [Category* C] [Category* D] [Category* E] (F : C ⥤ D)

spec_dsimp("created₂", test₂, F := (whiskeringLeft C D E).obj F)

/-- info: created₂.{v_1, u_1, v_2, u_2, v_3, u_3} {C : Type u_1} {D : Type u_2} {E : Type u_3} [Category.{v_1, u_1} C]
  [Category.{v_2, u_2} D] [Category.{v_3, u_3} E] (F : C ⥤ D) (X Y : D ⥤ E) (i : X ≅ Y) :
  F.whiskerLeft i.hom ≫ F.whiskerLeft i.inv = 𝟙 (F ⋙ X) -/
#guard_msgs in
#check created₂

end created₂_gen
-- this should create the following lemma:
-- lemma created₂ {C D E : Type*} [Category* C] [Category* D] [Category* E]
--     (F : C ⥤ D) (G H : D ⥤ E) (i : G ≅ H) :
--     whiskerLeft F i.hom ≫ whiskerLeft F i.inv = 𝟙 (F ⋙ G) :=
--   spec_dsimp(test₂, (whiskeringLeft C D E).obj F, G, H, i)

section condensed

lemma test₃ {C A : Type*} [Category* C] [Category* A] (J : GrothendieckTopology C)
    (F : Sheaf J A) {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.obj.map (f ≫ g) = F.obj.map f ≫ F.obj.map g := by
  simp

universe u

spec_dsimp("created₃", test₃, J := coherentTopology CompHaus.{u})

/-- info: created₃.{u, u_1, u_2} (A : Type u_1) (inst✝ : Category.{u_2, u_1} A) (F : Sheaf (coherentTopology CompHaus) A)
  (X Y Z : CompHausᵒᵖ) (f : X ⟶ Y) (g : Y ⟶ Z) : F.obj.map (f ≫ g) = F.obj.map f ≫ F.obj.map g -/
#guard_msgs in
#check created₃

end condensed
