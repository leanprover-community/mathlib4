module

public import Mathlib.Tactic.CategoryTheory.Reassoc
public import Mathlib.Tactic.CategoryTheory.SpecializeMap
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Groupoid

open CategoryTheory

namespace Tests.SpecializeMap

universe v₀ v₁ v₂ v₃ u₀ u₁ u₂ u₃

variable {B : Type u₁} [Category.{v₁} B]
variable {C : Type u₂} [Category.{v₂} C]
variable {D : Type u₃} [Category.{v₃} D]

@[simps! obj map]
def whiskeringLeftObj {B C D : Type*} [Category* B] [Category* C] [Category* D]
    (Fp : D ⥤ B) : (B ⥤ C) ⥤ D ⥤ C :=
  (Functor.whiskeringLeft D B C).obj Fp

@[simps! obj map]
def whiskeringRightObj {B C D : Type*} [Category* B] [Category* C] [Category* D]
    (Fp : C ⥤ D) : (B ⥤ C) ⥤ B ⥤ D :=
  (Functor.whiskeringRight B C D).obj Fp

@[specialize_map whiskeringLeftObj (suffix := "_whiskerLeft")]
lemma comp {F G H : B ⥤ C} (α : F ⟶ G) (β : G ⟶ H) (γ : F ⟶ H) (w : α ≫ β = γ) :
    α ≫ β = γ := w

/--
info: Tests.SpecializeMap.comp_whiskerLeft.{u_1, u_2, u_4, u_5, u_6, u_3} {B : Type u_1} [Category.{u_2, u_1} B]
  {C : Type u_3} [Category.{u_4, u_3} C] {F G H : B ⥤ C} (α : F ⟶ G) (β : G ⟶ H) (γ : F ⟶ H) (w : α ≫ β = γ)
  {D : Type u_5} [Category.{u_6, u_5} D] (Fp : D ⥤ B) : Fp.whiskerLeft α ≫ Fp.whiskerLeft β = Fp.whiskerLeft γ
-/
#guard_msgs in
#check comp_whiskerLeft

@[specialize_map whiskeringLeftObj (suffix := "_wl")]
lemma comp_short {F G H : B ⥤ C} (α : F ⟶ G) (β : G ⟶ H) (γ : F ⟶ H) (w : α ≫ β = γ) :
    α ≫ β = γ := w

/--
info: Tests.SpecializeMap.comp_short_wl.{u_1, u_2, u_4, u_5, u_6, u_3} {B : Type u_1} [Category.{u_2, u_1} B] {C : Type u_3}
  [Category.{u_4, u_3} C] {F G H : B ⥤ C} (α : F ⟶ G) (β : G ⟶ H) (γ : F ⟶ H) (w : α ≫ β = γ) {D : Type u_5}
  [Category.{u_6, u_5} D] (Fp : D ⥤ B) : Fp.whiskerLeft α ≫ Fp.whiskerLeft β = Fp.whiskerLeft γ
-/
#guard_msgs in
#check comp_short_wl

@[specialize_map whiskeringLeftObj (suffix := "_wl") (attr := reassoc)]
lemma comp_reassoc {F G H : B ⥤ C} (α : F ⟶ G) (β : G ⟶ H) (γ : F ⟶ H) (w : α ≫ β = γ) :
    α ≫ β = γ := w

/--
info: Tests.SpecializeMap.comp_reassoc_wl_assoc.{u_1, u_2, u_4, u_5, u_6, u_3} {B : Type u_1} [Category.{u_2, u_1} B]
  {C : Type u_3} [Category.{u_4, u_3} C] {F G H : B ⥤ C} (α : F ⟶ G) (β : G ⟶ H) (γ : F ⟶ H) (w : α ≫ β = γ)
  {D : Type u_5} [Category.{u_6, u_5} D] (Fp : D ⥤ B) {Z : D ⥤ C} (h : Fp ⋙ H ⟶ Z) :
  Fp.whiskerLeft α ≫ Fp.whiskerLeft β ≫ h = Fp.whiskerLeft γ ≫ h
-/
#guard_msgs in
#check comp_reassoc_wl_assoc

@[specialize_map whiskeringLeftObj (suffix := "_whiskerLeft")]
lemma comp_eq_id {F G : B ⥤ C} (α : F ⟶ G) (β : G ⟶ F) (w : α ≫ β = 𝟙 _) :
    α ≫ β = 𝟙 _ := w

/--
info: Tests.SpecializeMap.comp_eq_id_whiskerLeft.{u_1, u_2, u_4, u_5, u_6, u_3} {B : Type u_1} [Category.{u_2, u_1} B]
  {C : Type u_3} [Category.{u_4, u_3} C] {F G : B ⥤ C} (α : F ⟶ G) (β : G ⟶ F) (w : α ≫ β = 𝟙 F) {D : Type u_5}
  [Category.{u_6, u_5} D] (Fp : D ⥤ B) : Fp.whiskerLeft α ≫ Fp.whiskerLeft β = 𝟙 (Fp ⋙ F)
-/
#guard_msgs in
#check comp_eq_id_whiskerLeft

@[specialize_map whiskeringLeftObj (suffix := "_whiskerLeft"),
specialize_map whiskeringRightObj (suffix := "_whiskerRight"),
specialize_map MonoidalCategory.tensorLeft (suffix := "_tensorLeft"),
specialize_map MonoidalCategory.tensorRight (suffix := "_tensorRight"),
specialize_map MonoidalCategory.tensor (suffix := "_tensor")]
lemma comp_eq {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) :
    f ≫ g = h := w

/--
info: Tests.SpecializeMap.comp_eq_whiskerLeft.{u_1, u_3, u_4, u_5, u_6, u_2} {B : Type u_1} {C : Type u_2} {D : Type u_3}
  [Category.{u_4, u_1} B] [Category.{u_5, u_2} C] {X Y Z : B ⥤ C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h)
  [Category.{u_6, u_3} D] (Fp : D ⥤ B) : Fp.whiskerLeft f ≫ Fp.whiskerLeft g = Fp.whiskerLeft h
-/
#guard_msgs in
#check comp_eq_whiskerLeft

/--
info: Tests.SpecializeMap.comp_eq_whiskerRight.{u_1, u_4, u_5, u_6, u_2, u_3} {B : Type u_1} {C : Type u_2} {D : Type u_3}
  [Category.{u_4, u_1} B] [Category.{u_5, u_2} C] {X Y Z : B ⥤ C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h)
  [Category.{u_6, u_3} D] (Fp : C ⥤ D) :
  Functor.whiskerRight f Fp ≫ Functor.whiskerRight g Fp = Functor.whiskerRight h Fp
-/
#guard_msgs in
#check comp_eq_whiskerRight

open MonoidalCategory

/--
info: Tests.SpecializeMap.comp_eq_tensorLeft.{u_2, u_1} {B : Type u_1} [Category.{u_2, u_1} B] {X Y Z : B} (f : X ⟶ Y)
  (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) [MonoidalCategory B] (X✝ : B) : X✝ ◁ f ≫ X✝ ◁ g = X✝ ◁ h
-/
#guard_msgs in
#check comp_eq_tensorLeft

/--
info: Tests.SpecializeMap.comp_eq_tensorRight.{u_2, u_1} {B : Type u_1} [Category.{u_2, u_1} B] {X Y Z : B} (f : X ⟶ Y)
  (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h) [MonoidalCategory B] (X✝ : B) : f ▷ X✝ ≫ g ▷ X✝ = h ▷ X✝
-/
#guard_msgs in
#check comp_eq_tensorRight

/--
info: Tests.SpecializeMap.comp_eq_tensor.{u_2, u_1} (C : Type u_1) {X Y Z : C × C} [Category.{u_2, u_1} C]
  (f : (X.1 ⟶ Y.1) × (X.2 ⟶ Y.2)) (g : (Y.1 ⟶ Z.1) × (Y.2 ⟶ Z.2)) (h : (X.1 ⟶ Z.1) × (X.2 ⟶ Z.2)) (w : f ≫ g = h)
  [MonoidalCategory C] : (f.1 ⊗ₘ f.2) ≫ (g.1 ⊗ₘ g.2) = h.1 ⊗ₘ h.2
-/
#guard_msgs in
#check comp_eq_tensor

/-- error: `@[specialize_map]` expects an equality -/
#guard_msgs in
@[specialize_map whiskeringLeftObj]
def one : Nat := 1

-- The generated lemmas retain explicit arguments and infer typeclass instances normally.
example {F G H : B ⥤ C} (α : F ⟶ G) (β : G ⟶ H) (γ : F ⟶ H) (w : α ≫ β = γ)
    (Fp : D ⥤ B) : Fp.whiskerLeft α ≫ Fp.whiskerLeft β = Fp.whiskerLeft γ :=
  comp_whiskerLeft α β γ w Fp

example {F G H : B ⥤ C} (α : F ⟶ G) (β : G ⟶ H) (γ : F ⟶ H) (w : α ≫ β = γ)
    (Fp : C ⥤ D) : Functor.whiskerRight α Fp ≫ Functor.whiskerRight β Fp =
      Functor.whiskerRight γ Fp :=
  comp_eq_whiskerRight α β γ w Fp

example [MonoidalCategory B] {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (w : f ≫ g = h) (T : B) : T ◁ f ≫ T ◁ g = T ◁ h :=
  comp_eq_tensorLeft.{v₁, u₁} f g h w T

example [MonoidalCategory B] {X Y Z : B × B} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (w : f ≫ g = h) : (f.1 ⊗ₘ f.2) ≫ (g.1 ⊗ₘ g.2) = h.1 ⊗ₘ h.2 :=
  comp_eq_tensor B f g h w

-- Abbreviated functor types, equality types, and source instances are reduced.
abbrev Endofunctor (C : Type u₀) [Category.{v₀} C] := C ⥤ C

def identityFunctor (C : Type u₀) [Category.{v₀} C] : Endofunctor C := 𝟭 C

abbrev HomEq {X Y : B} (f g : X ⟶ Y) := f = g

@[specialize_map identityFunctor]
lemma abbreviated {X Y : B} (f g : X ⟶ Y) (h : HomEq f g) : HomEq f g := h

example {X Y : B} (f g : X ⟶ Y) (h : f = g) : f = g :=
  abbreviated_specializeMap.{v₁, u₁} f g h

@[specialize_map identityFunctor]
lemma inherited {E : Type u₀} [Groupoid.{v₀} E] {X Y : E} (f : X ⟶ Y) : f = f := rfl

-- Reflexive equalities must remain equalities rather than simplifying to `True`.
example {E : Type u₀} [Groupoid.{v₀} E] {X Y : E} (f : X ⟶ Y) : f = f :=
  inherited_specializeMap f

-- Universes unrelated to categories come last, as for `@[map]`.
@[specialize_map identityFunctor]
lemma extra {A : Type u₀} (_a : A) {X Y : B} (f g : X ⟶ Y) (h : f = g) : f = g := h

example {A : Type u₀} (a : A) {X Y : B} (f g : X ⟶ Y) (h : f = g) : f = g :=
  extra_specializeMap.{v₁, u₁, u₀} a f g h

-- Ordinary simplification can use a generated lemma, including its instance arguments.
@[specialize_map MonoidalCategory.tensorLeft (attr := simp)]
lemma inverse_comp {X Y : B} (f : X ⟶ Y) (g : Y ⟶ X) (h : f ≫ g = 𝟙 X) :
    f ≫ g = 𝟙 X := h

example [MonoidalCategory B] {X Y : B} (f : X ⟶ Y) (g : Y ⟶ X)
    (h : f ≫ g = 𝟙 X) (T : B) : T ◁ f ≫ T ◁ g = 𝟙 (T ⊗ X) := by
  simp only [inverse_comp_specializeMap f g h]

/-- error: `@[specialize_map]` expects an equality of morphisms -/
#guard_msgs in
@[specialize_map identityFunctor]
lemma not_morphisms (n : Nat) : n = n := rfl

/--
error: `@[specialize_map]` expects a declaration whose type reduces to `∀ .., C ⥤ D`
-/
#guard_msgs in
@[specialize_map Nat.succ]
lemma not_a_functor {X Y : B} (f : X ⟶ Y) : f = f := rfl

/--
error: `@[specialize_map]` could not unify the source of the functor with the source category of the lemma
-/
#guard_msgs in
@[specialize_map whiskeringLeftObj]
lemma incompatible_source {X Y : Discrete Unit} (f : X ⟶ Y) : f = f := rfl

end Tests.SpecializeMap
