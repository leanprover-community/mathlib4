module

public import Mathlib.Tactic.CategoryTheory.Map
public import Mathlib.Tactic.CategoryTheory.Reassoc
public import Mathlib.CategoryTheory.Types.Basic

open CategoryTheory

namespace Tests.Map

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]

@[reassoc (attr := map)]
lemma comp_map {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (w : f ≫ g = h) :
    f ≫ g = h := w

/-- info: Tests.Map.comp_map_map.{u✝, v✝, u_1, u_2} {C : Type u_1} [Category.{u_2, u_1} C] {x y z : C} (f : x ⟶ y) (g : y ⟶ z)
  (h : x ⟶ z) (w : f ≫ g = h) {D : Type u✝} [instD : Category.{v✝, u✝} D] (F : C ⥤ D) : F.map f ≫ F.map g = F.map h -/
#guard_msgs in
#check comp_map_map

/-- info: Tests.Map.comp_map_assoc_map.{u✝, v✝, u_1, u_2} {C : Type u_1} [Category.{u_2, u_1} C] {x y z : C} (f : x ⟶ y)
  (g : y ⟶ z) (h : x ⟶ z) (w : f ≫ g = h) {Z : C} (h✝ : z ⟶ Z) {D : Type u✝} [instD : Category.{v✝, u✝} D] (F : C ⥤ D) :
  F.map f ≫ F.map g ≫ F.map h✝ = F.map h ≫ F.map h✝ -/
#guard_msgs in
#check comp_map_assoc_map

@[map (attr := reassoc)]
lemma comp_map_reassoc {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (w : f ≫ g = h) :
    f ≫ g = h := w

/-- info: Tests.Map.comp_map_reassoc_map_assoc.{u✝, v✝, u_1, u_2} {C : Type u_1} [Category.{u_2, u_1} C] {x y z : C} (f : x ⟶ y)
  (g : y ⟶ z) (h : x ⟶ z) (w : f ≫ g = h) {D : Type u✝} [instD : Category.{v✝, u✝} D] (F : C ⥤ D) {Z : D}
  (h✝ : F.obj z ⟶ Z) : F.map f ≫ F.map g ≫ h✝ = F.map h ≫ h✝ -/
#guard_msgs in
#check comp_map_reassoc_map_assoc

@[map]
lemma comp_eq_id {x y : C} (f : x ⟶ y) (g : y ⟶ x) (w : f ≫ g = 𝟙 _) :
    f ≫ g = 𝟙 _ := w

/-- info: Tests.Map.comp_eq_id_map.{u✝, v✝, u_1, u_2} {C : Type u_1} [Category.{u_2, u_1} C] {x y : C} (f : x ⟶ y) (g : y ⟶ x)
  (w : f ≫ g = 𝟙 x) {D : Type u✝} [instD : Category.{v✝, u✝} D] (F : C ⥤ D) : F.map f ≫ F.map g = 𝟙 (F.obj x) -/
#guard_msgs in
#check comp_eq_id_map

@[to_dual (attr := map) comp_map_dual]
lemma comp_map_to_dual {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (w : f ≫ g = h) :
    f ≫ g = h := w

/-- info: Tests.Map.comp_map_dual_map.{u✝, v✝, u_1, u_2} {C : Type u_1} [Category.{u_2, u_1} C] {x y z : C} (f : y ⟶ x)
  (g : z ⟶ y) (h : z ⟶ x) (w : g ≫ f = h) {D : Type u✝} [instD : Category.{v✝, u✝} D] (F : C ⥤ D) :
  F.map g ≫ F.map f = F.map h -/
#guard_msgs in
#check comp_map_dual_map

@[map_functor] abbrev typesId : Type u₁ ⥤ Type u₁ := 𝟭 (Type u₁)

@[map]
lemma type_comp {α β γ : Type u₁} (f : α ⟶ β) (g : β ⟶ γ) (h : α ⟶ γ) (w : f ≫ g = h) :
    f ≫ g = h := w

/-- info: Tests.Map.type_comp_map.{u✝, v✝, u_1} {α β γ : Type u_1} (f : α ⟶ β) (g : β ⟶ γ) (h : α ⟶ γ) (w : f ≫ g = h)
  {D : Type u✝} [instD : Category.{v✝, u✝} D] (F : Type u_1 ⥤ D) : F.map f ≫ F.map g = F.map h -/
#guard_msgs in
#check type_comp_map

/-- info: Tests.Map.type_comp_map_Tests_Map_typesId.{u_1} {α β γ : Type u_1} (f : α ⟶ β) (g : β ⟶ γ) (h : α ⟶ γ) (w : f ≫ g = h) :
  f ≫ g = h -/
#guard_msgs in
#check type_comp_map_Tests_Map_typesId

/-!
`map_of%` pushes `Functor.map` through an equality and applies `simp only [Functor.map_comp, Functor.map_id]` on each
side.
-/
example {x y z : C} {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z)
    (w : f ≫ g = h) : F.map f ≫ F.map g = F.map h := by
  exact (map_of% w) F

end Tests.Map
