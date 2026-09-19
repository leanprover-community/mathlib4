module

public import Mathlib.Tactic.CategoryTheory.Map
public import Mathlib.Tactic.CategoryTheory.Op
public import Mathlib.Tactic.CategoryTheory.Reassoc
public import Mathlib.CategoryTheory.Functor.Category

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

/-- info: Tests.Op.comp_op_map_map.{v₁, u_2, u₁, u_1} {C : Type u₁} [Category.{v₁, u₁} C] {x y z : C} (f : x ⟶ y) (g : y ⟶ z)
  (h : x ⟶ z) (w : f ≫ g = h) {D : Type u_1} [_instD : Category.{u_2, u_1} D] (F : C ⥤ D) : F.map f ≫ F.map g = F.map h -/
#guard_msgs in
#check comp_op_map_map

/-- info: Tests.Op.comp_op_map_op.{v₁, u₁} {C : Type u₁} [Category.{v₁, u₁} C] {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z)
  (w : f ≫ g = h) : g.op ≫ f.op = h.op -/
#guard_msgs in
#check comp_op_map_op

/-- info: Tests.Op.comp_op_map_op_map.{v₁, u_2, u₁, u_1} {C : Type u₁} [Category.{v₁, u₁} C] {x y z : C} (f : x ⟶ y) (g : y ⟶ z)
  (h : x ⟶ z) (w : f ≫ g = h) {D : Type u_1} [_instD : Category.{u_2, u_1} D] (F : Cᵒᵖ ⥤ D) :
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
info: Tests.Op.comp_op_reassoc_op_map_assoc.{v₁, u_2, u₁, u_1} {C : Type u₁} [Category.{v₁, u₁} C] {x y z : C} (f : x ⟶ y)
  (g : y ⟶ z) (h : x ⟶ z) (w : f ≫ g = h) {D : Type u_1} [_instD : Category.{u_2, u_1} D] (F : Cᵒᵖ ⥤ D) {Z : D}
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

section

variable {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (w : f ≫ g = h)

-- Macro expansion must behave like the underlying theorem, including its implicit arguments.
local macro "op_test_foo" : term => `(foo)

example : g.op ≫ f.op = h.op := by
  rw [op_of% op_test_foo]
  exact w

example : g.op ≫ f.op = h.op := by
  rw [op_of% @foo]
  exact w

example : g.op ≫ f.op = h.op := by
  rw [op_of% foo.{v₁, u₁}]
  exact w

example : g.op ≫ f.op = h.op := by
  exact op_of% (foo w)

-- A local theorem with implicit binders must allow inference from the rewrite target.
example (eqs : ∀ {x y z : C} {f : x ⟶ y} {g : y ⟶ z} {h : x ⟶ z},
    f ≫ g = h → f ≫ g = h) : g.op ≫ f.op = h.op := by
  rw [op_of% eqs]
  exact w

end

@[op]
lemma comp_eq_id {x y : C} (f : x ⟶ y) (g : y ⟶ x) (w : f ≫ g = 𝟙 x) :
    f ≫ g = 𝟙 x := w

example {x y : C} (f : x ⟶ y) (g : y ⟶ x) (w : f ≫ g = 𝟙 x) :
    g.op ≫ f.op = 𝟙 (Opposite.op x) :=
  comp_eq_id_op f g w

example {x y : C} (f : x ⟶ y) (g : y ⟶ x) (w : f ≫ g = 𝟙 x) :
    g.op ≫ f.op = 𝟙 (Opposite.op x) := by
  rw [op_of% comp_eq_id]
  exact w

-- The source instance can be synthesized through the opposite-category instance.
@[op]
lemma op_hom_eq {x y : Cᵒᵖ} (f g : x ⟶ y) (h : f = g) : f = g := h

example {x y : Cᵒᵖ} (f g : x ⟶ y) (h : f = g) : f.op = g.op :=
  op_hom_eq_op f g h

example {x y z : Cᵒᵖ} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (w : f ≫ g = h) :
    g.op ≫ f.op = h.op := by
  rw [op_of% foo]
  exact w

-- Simplification must preserve an equality as the conclusion, even when it is reflexive.
@[op]
lemma refl_hom {x y : C} (f : x ⟶ y) : f = f := rfl

example {x y : C} (f : x ⟶ y) : f.op = f.op :=
  refl_hom_op f

example {x y : C} (f : x ⟶ y) : f.op = f.op :=
  op_of% (rfl : f = f)

-- Applying `op` repeatedly must preserve the original arguments.
attribute [op] comp_eq_id_op

example {x y : C} (f : x ⟶ y) (g : y ⟶ x) (h : f ≫ g = 𝟙 x) :
    f.op.op ≫ g.op.op = 𝟙 (Opposite.op (Opposite.op x)) :=
  comp_eq_id_op_op f g h

example {x y : C} (f g : x ⟶ y) (h : f = g) : f.op.op = g.op.op :=
  op_of% (op_of% h)

-- Natural transformations use a derived category instance with composite universe levels.
@[op]
lemma nat_eq {D : Type u₂} [Category.{v₂} D]
    {F G : C ⥤ D} (α β : F ⟶ G) (h : α = β) : α = β := h

example {D : Type u₂} [Category.{v₂} D] {F G : C ⥤ D} (α β : F ⟶ G) (h : α = β) :
    Quiver.Hom.op α = Quiver.Hom.op β :=
  nat_eq_op α β h

example {D : Type u₂} [Category.{v₂} D] {F G : C ⥤ D} (α β : F ⟶ G) (h : α = β) :
    Quiver.Hom.op α = Quiver.Hom.op β := by
  rw [op_of% nat_eq]
  exact h

end Tests.Op
