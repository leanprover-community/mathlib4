module

public import Mathlib.Tactic.CategoryTheory.Reassoc
public import Mathlib.Tactic.CategoryTheory.SpecializeMap
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Monoidal.Category

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
info: Tests.SpecializeMap.comp_whiskerLeft.{u_1, u_2, u_3, u_4, u_5, u_6} {B : Type u_1} {C : Type u_2} {D : Type u_3}
  {inst✝ : Category.{u_4, u_1} B} {inst✝¹ : Category.{u_5, u_2} C} {inst✝² : Category.{u_6, u_3} D} {F G H : B ⥤ C}
  {Fp : D ⥤ B} {α : F ⟶ G} {β : G ⟶ H} {γ : F ⟶ H} {w : α ≫ β = γ} :
  Fp.whiskerLeft α ≫ Fp.whiskerLeft β = Fp.whiskerLeft γ
-/
#guard_msgs in
#check comp_whiskerLeft

@[specialize_map whiskeringLeftObj (suffix := "_wl")]
lemma comp_short {F G H : B ⥤ C} (α : F ⟶ G) (β : G ⟶ H) (γ : F ⟶ H) (w : α ≫ β = γ) :
    α ≫ β = γ := w

/--
info: Tests.SpecializeMap.comp_short_wl.{u_1, u_2, u_3, u_4, u_5, u_6} {B : Type u_1} {C : Type u_2} {D : Type u_3}
  {inst✝ : Category.{u_4, u_1} B} {inst✝¹ : Category.{u_5, u_2} C} {inst✝² : Category.{u_6, u_3} D} {F G H : B ⥤ C}
  {Fp : D ⥤ B} {α : F ⟶ G} {β : G ⟶ H} {γ : F ⟶ H} {w : α ≫ β = γ} :
  Fp.whiskerLeft α ≫ Fp.whiskerLeft β = Fp.whiskerLeft γ
-/
#guard_msgs in
#check comp_short_wl

@[specialize_map whiskeringLeftObj (suffix := "_wl") (attr := reassoc)]
lemma comp_reassoc {F G H : B ⥤ C} (α : F ⟶ G) (β : G ⟶ H) (γ : F ⟶ H) (w : α ≫ β = γ) :
    α ≫ β = γ := w

/--
info: Tests.SpecializeMap.comp_reassoc_wl_assoc.{u_1, u_2, u_3, u_4, u_5, u_6} {B : Type u_1} {C : Type u_2} {D : Type u_3}
  {inst✝ : Category.{u_4, u_1} B} {inst✝¹ : Category.{u_5, u_2} C} {inst✝² : Category.{u_6, u_3} D} {F G H : B ⥤ C}
  {Fp : D ⥤ B} {α : F ⟶ G} {β : G ⟶ H} {γ : F ⟶ H} {w : α ≫ β = γ} {Z : D ⥤ C} (h : Fp ⋙ H ⟶ Z) :
  Fp.whiskerLeft α ≫ Fp.whiskerLeft β ≫ h = Fp.whiskerLeft γ ≫ h
-/
#guard_msgs in
#check comp_reassoc_wl_assoc

@[specialize_map whiskeringLeftObj (suffix := "_whiskerLeft")]
lemma comp_eq_id {F G : B ⥤ C} (α : F ⟶ G) (β : G ⟶ F) (w : α ≫ β = 𝟙 _) :
    α ≫ β = 𝟙 _ := w

/--
info: Tests.SpecializeMap.comp_eq_id_whiskerLeft.{u_1, u_2, u_3, u_4, u_5, u_6} {B : Type u_1} {C : Type u_2} {D : Type u_3}
  {inst✝ : Category.{u_4, u_1} B} {inst✝¹ : Category.{u_5, u_2} C} {inst✝² : Category.{u_6, u_3} D} {F G : B ⥤ C}
  {Fp : D ⥤ B} {α : F ⟶ G} {β : G ⟶ F} {w : α ≫ β = 𝟙 F} : Fp.whiskerLeft α ≫ Fp.whiskerLeft β = 𝟙 (Fp ⋙ F)
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
info: Tests.SpecializeMap.comp_eq_whiskerLeft.{u_1, u_2, u_3, u_4, u_5, u_6} {B : Type u_1} {C : Type u_2} {D : Type u_3}
  {inst✝ : Category.{u_4, u_1} B} {inst✝¹ : Category.{u_5, u_2} C} {inst✝² : Category.{u_6, u_3} D} {X Y Z : B ⥤ C}
  {Fp : D ⥤ B} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} {w : f ≫ g = h} :
  Fp.whiskerLeft f ≫ Fp.whiskerLeft g = Fp.whiskerLeft h
-/
#guard_msgs in
#check comp_eq_whiskerLeft

/--
info: Tests.SpecializeMap.comp_eq_whiskerRight.{u_1, u_2, u_3, u_4, u_5, u_6} {B : Type u_1} {C : Type u_2} {D : Type u_3}
  {inst✝ : Category.{u_4, u_1} B} {inst✝¹ : Category.{u_5, u_2} C} {inst✝² : Category.{u_6, u_3} D} {X Y Z : B ⥤ C}
  {Fp : C ⥤ D} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} {w : f ≫ g = h} :
  Functor.whiskerRight f Fp ≫ Functor.whiskerRight g Fp = Functor.whiskerRight h Fp
-/
#guard_msgs in
#check comp_eq_whiskerRight

open MonoidalCategory

/--
info: Tests.SpecializeMap.comp_eq_tensorLeft.{u_1, u_2} {B : Type u_1} {inst✝ : Category.{u_2, u_1} B} {X Y Z X✝ : B}
  {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} {inst✝¹ : MonoidalCategory B} {w : f ≫ g = h} : X✝ ◁ f ≫ X✝ ◁ g = X✝ ◁ h
-/
#guard_msgs in
#check comp_eq_tensorLeft

/--
info: Tests.SpecializeMap.comp_eq_tensorRight.{u_1, u_2} {B : Type u_1} {inst✝ : Category.{u_2, u_1} B} {X Y Z X✝ : B}
  {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} {inst✝¹ : MonoidalCategory B} {w : f ≫ g = h} : f ▷ X✝ ≫ g ▷ X✝ = h ▷ X✝
-/
#guard_msgs in
#check comp_eq_tensorRight

/--
info: Tests.SpecializeMap.comp_eq_tensor.{u_1, u_2} {C : Type u_1} {X Y Z : C × C} {inst✝ : Category.{u_2, u_1} C}
  {f : (X.1 ⟶ Y.1) × (X.2 ⟶ Y.2)} {g : (Y.1 ⟶ Z.1) × (Y.2 ⟶ Z.2)} {h : (X.1 ⟶ Z.1) × (X.2 ⟶ Z.2)}
  {inst✝¹ : MonoidalCategory C} {w : f ≫ g = h} : (f.1 ⊗ₘ f.2) ≫ (g.1 ⊗ₘ g.2) = h.1 ⊗ₘ h.2
-/
#guard_msgs in
#check comp_eq_tensor

/-- error: `@[specialize_map]` expects an equality -/
#guard_msgs in
@[specialize_map whiskeringLeftObj]
def one : Nat := 1

end Tests.SpecializeMap
