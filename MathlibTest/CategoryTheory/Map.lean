module

public import Mathlib.Tactic.CategoryTheory.Map
public import Mathlib.Tactic.CategoryTheory.Reassoc

open CategoryTheory

namespace Tests.Map

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]

@[reassoc (attr := map)]
lemma comp_map {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (w : f ≫ g = h) :
    f ≫ g = h := w

/-- info: Tests.Map.comp_map_map.{u_2, v✝, u_1, u✝} {C : Type u_1} [Category.{u_2, u_1} C] {x y z : C} (f : x ⟶ y) (g : y ⟶ z)
  (h : x ⟶ z) (w : f ≫ g = h) {D : Type u✝} [instD : Category.{v✝, u✝} D] (F : C ⥤ D) : F.map f ≫ F.map g = F.map h -/
#guard_msgs in
#check comp_map_map

/-- info: Tests.Map.comp_map_assoc_map.{u_2, v✝, u_1, u✝} {C : Type u_1} [Category.{u_2, u_1} C] {x y z : C} (f : x ⟶ y)
  (g : y ⟶ z) (h : x ⟶ z) (w : f ≫ g = h) {Z : C} (h✝ : z ⟶ Z) {D : Type u✝} [instD : Category.{v✝, u✝} D] (F : C ⥤ D) :
  F.map f ≫ F.map g ≫ F.map h✝ = F.map h ≫ F.map h✝ -/
#guard_msgs in
#check comp_map_assoc_map

@[map (attr := reassoc)]
lemma comp_map_reassoc {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (w : f ≫ g = h) :
    f ≫ g = h := w

/-- info: Tests.Map.comp_map_reassoc_map_assoc.{u_2, v✝, u_1, u✝} {C : Type u_1} [Category.{u_2, u_1} C] {x y z : C} (f : x ⟶ y)
  (g : y ⟶ z) (h : x ⟶ z) (w : f ≫ g = h) {D : Type u✝} [instD : Category.{v✝, u✝} D] (F : C ⥤ D) {Z : D}
  (h✝ : F.obj z ⟶ Z) : F.map f ≫ F.map g ≫ h✝ = F.map h ≫ h✝ -/
#guard_msgs in
#check comp_map_reassoc_map_assoc

@[map]
lemma comp_eq_id {x y : C} (f : x ⟶ y) (g : y ⟶ x) (w : f ≫ g = 𝟙 _) :
    f ≫ g = 𝟙 _ := w

/-- info: Tests.Map.comp_eq_id_map.{u_2, v✝, u_1, u✝} {C : Type u_1} [Category.{u_2, u_1} C] {x y : C} (f : x ⟶ y) (g : y ⟶ x)
  (w : f ≫ g = 𝟙 x) {D : Type u✝} [instD : Category.{v✝, u✝} D] (F : C ⥤ D) : F.map f ≫ F.map g = 𝟙 (F.obj x) -/
#guard_msgs in
#check comp_eq_id_map

@[to_dual (attr := map) comp_map_dual]
lemma comp_map_to_dual {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (w : f ≫ g = h) :
    f ≫ g = h := w

/-- info: Tests.Map.comp_map_dual_map.{u_2, v✝, u_1, u✝} {C : Type u_1} [Category.{u_2, u_1} C] {x y z : C} (f : y ⟶ x)
  (g : z ⟶ y) (h : z ⟶ x) (w : g ≫ f = h) {D : Type u✝} [instD : Category.{v✝, u✝} D] (F : C ⥤ D) :
  F.map g ≫ F.map f = F.map h -/
#guard_msgs in
#check comp_map_dual_map

/-- error: `@[map]` expects an equality -/
#guard_msgs in
@[map]
def one : Nat := 1

/-- error: `@[map]` expects an equality of morphisms -/
#guard_msgs in
@[map]
lemma one_plus_one : 1 + 1 = 2 := rfl

/-!
`map_of%` pushes `Functor.map` through an equality and applies `simp only [Functor.map_comp, Functor.map_id]` on each
side.
-/

example {x y z : C} {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z)
    (w : f ≫ g = h) : F.map f ≫ F.map g = F.map h := by
  exact (map_of% w) F

lemma foo {x y z : C} {f : x ⟶ y} {g : y ⟶ z} {h : x ⟶ z} (w : f ≫ g = h) :
    f ≫ g = h := w

example {D : Type*} [Category* D] {x y z : C} (F : C ⥤ D) (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z)
    (w : f ≫ g = h) :
    F.map f ≫ F.map g = F.map h := by
  rw [map_of% foo]
  exact w

example {D : Type*} [Category* D] {x y z : C} (F : C ⥤ D) (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z)
    (w : f ≫ g = h) :
    F.map f ≫ F.map g = F.map h := by
  rw [map_of% (foo)]
  exact w

end Tests.Map
