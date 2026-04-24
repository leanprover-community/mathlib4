module

public import Mathlib.Tactic.CategoryTheory.Map
public import Mathlib.Tactic.CategoryTheory.Op
public import Mathlib.Tactic.CategoryTheory.Reassoc

open CategoryTheory

namespace Tests.Op

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]

@[op]
lemma comp_op {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (w : f ≫ g = h) :
    f ≫ g = h := w

/-- info: Tests.Op.comp_op_op.{v₁, u₁} {C : Type u₁} [Category.{v₁, u₁} C] {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z)
  (w : f ≫ g = h) : g.op ≫ f.op = h.op -/
#guard_msgs in
#check comp_op_op

@[op (attr := map)]
lemma comp_op_map {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (w : f ≫ g = h) :
    f ≫ g = h := w

/-- info: Tests.Op.comp_op_map_map.{u_2, v✝, u_1, u✝} {C : Type u_1} [Category.{u_2, u_1} C] {x y z : C} (f : x ⟶ y) (g : y ⟶ z)
  (h : x ⟶ z) (w : f ≫ g = h) {D : Type u✝} [instD : Category.{v✝, u✝} D] (F : C ⥤ D) : F.map f ≫ F.map g = F.map h -/
#guard_msgs in
#check comp_op_map_map

/-- info: Tests.Op.comp_op_map_op.{v₁, u₁} {C : Type u₁} [Category.{v₁, u₁} C] {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z)
  (w : f ≫ g = h) : g.op ≫ f.op = h.op -/
#guard_msgs in
#check comp_op_map_op

/-- info: Tests.Op.comp_op_map_op_map.{u_2, v✝, u_1, u✝} {C : Type u_1} [Category.{u_2, u_1} C] {x y z : C} (f : x ⟶ y)
  (g : y ⟶ z) (h : x ⟶ z) (w : f ≫ g = h) {D : Type u✝} [instD : Category.{v✝, u✝} D] (F : Cᵒᵖ ⥤ D) :
  F.map g.op ≫ F.map f.op = F.map h.op -/
#guard_msgs in
#check comp_op_map_op_map

@[op (attr := map (attr := reassoc))]
lemma comp_op_reassoc {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (w : f ≫ g = h) :
    f ≫ g = h := w

/-- info: Tests.Op.comp_op_reassoc_op_assoc.{v₁, u₁} {C : Type u₁} [Category.{v₁, u₁} C] {x y z : C} (f : x ⟶ y) (g : y ⟶ z)
  (h : x ⟶ z) (w : f ≫ g = h) {Z : Cᵒᵖ} (h✝ : Opposite.op x ⟶ Z) : g.op ≫ f.op ≫ h✝ = h.op ≫ h✝ -/
#guard_msgs in
#check comp_op_reassoc_op_assoc

/--
info: Tests.Op.comp_op_reassoc_op_map_assoc.{u_2, v✝, u_1, u✝} {C : Type u_1} [Category.{u_2, u_1} C] {x y z : C} (f : x ⟶ y)
  (g : y ⟶ z) (h : x ⟶ z) (w : f ≫ g = h) {D : Type u✝} [instD : Category.{v✝, u✝} D] (F : Cᵒᵖ ⥤ D) {Z : D}
  (h✝ : F.obj (Opposite.op x) ⟶ Z) : F.map g.op ≫ F.map f.op ≫ h✝ = F.map h.op ≫ h✝
-/
#guard_msgs in
#check comp_op_reassoc_op_map_assoc

/-- error: `@[op]` expects an equality -/
#guard_msgs in
@[op]
def one : Nat := 1

/-- error: `@[op]` expects an equality of morphisms -/
#guard_msgs in
@[op]
lemma one_plus_one : 1 + 1 = 2 := rfl

example {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (w : f ≫ g = h) :
    g.op ≫ f.op = h.op := by
  exact op_of% w

lemma foo {x y z : C} {f : x ⟶ y} {g : y ⟶ z} {h : x ⟶ z} (w : f ≫ g = h) :
    f ≫ g = h := w

example {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (w : f ≫ g = h) :
    g.op ≫ f.op = h.op := by
  rw [op_of% foo]
  exact w

example {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (w : f ≫ g = h) :
    g.op ≫ f.op = h.op := by
  rw [op_of% (foo)]
  exact w

end Tests.Op
