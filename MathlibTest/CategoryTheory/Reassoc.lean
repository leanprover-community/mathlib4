import Mathlib.Tactic.CategoryTheory.IsoReassoc

open CategoryTheory
namespace Tests.Reassoc

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  {F : C ⥤ D} {G : D ⥤ E}

@[reassoc]
lemma foo {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (w : f ≫ g = h) :
    f ≫ g = h := w

@[reassoc]
lemma foo_iso {x y z : C} (f : x ≅ y) (g : y ≅ z) (h : x ≅ z) (w : f ≪≫ g = h) :
    f ≪≫ g = h := w

/--
info: Tests.Reassoc.foo_assoc.{v₁, u₁} {C : Type u₁} [Category.{v₁, u₁} C] {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z)
  (w : f ≫ g = h) {Z : C} (h✝ : z ⟶ Z) : f ≫ g ≫ h✝ = h ≫ h✝
-/
#guard_msgs in
#check foo_assoc

/--
info: Tests.Reassoc.foo_iso_assoc.{v₁, u₁} {C : Type u₁} [Category.{v₁, u₁} C] {x y z : C} (f : x ≅ y) (g : y ≅ z) (h : x ≅ z)
  (w : f ≪≫ g = h) {Z : C} (h✝ : z ≅ Z) : f ≪≫ g ≪≫ h✝ = h ≪≫ h✝
-/
#guard_msgs in
#check foo_iso_assoc

/-- error: `reassoc` can only be used on terms about equality of (iso)morphisms -/
#guard_msgs in
@[reassoc]
def one : Nat := 1

/-- error: `reassoc` can only be used on terms about equality of (iso)morphisms -/
#guard_msgs in
@[reassoc]
def one_plus_one : 1 + 1 = 2 := rfl

@[reassoc]
lemma foo_functor {x y z : C} (f : x ≅ y) (g : y ≅ z) (h : x ≅ z)
    (w : F.mapIso (f ≪≫ g) = F.mapIso h) :
    F.mapIso (f ≪≫ g) = F.mapIso h := w

/--
info: Tests.Reassoc.foo_functor_assoc.{v₁, v₂, u₁, u₂} {C : Type u₁} {D : Type u₂} [Category.{v₁, u₁} C] [Category.{v₂, u₂} D]
  {F : C ⥤ D} {x y z : C} (f : x ≅ y) (g : y ≅ z) (h : x ≅ z) (w : F.mapIso (f ≪≫ g) = F.mapIso h) {Z : D}
  (h✝ : F.obj z ≅ Z) : F.mapIso f ≪≫ F.mapIso g ≪≫ h✝ = F.mapIso h ≪≫ h✝
-/
#guard_msgs in
#check foo_functor_assoc

@[reassoc]
lemma foo_functor' {x y z : C} (f : x ≅ y) (g : y ≅ z) (h : x ≅ z)
    (w : F.mapIso (f ≪≫ g) = F.mapIso h) {Z : D} (e : F.obj z ≅ Z) :
    F.mapIso f ≪≫ F.mapIso g ≪≫ e = F.mapIso h ≪≫ e := (reassoc_of% w) e

-- checking that _assoc expressions are indeed right_associated:
/--
info: Tests.Reassoc.foo_functor'_assoc.{v₁, v₂, u₁, u₂} {C : Type u₁} {D : Type u₂} [Category.{v₁, u₁} C]
  [Category.{v₂, u₂} D] {F : C ⥤ D} {x y z : C} (f : x ≅ y) (g : y ≅ z) (h : x ≅ z) (w : F.mapIso (f ≪≫ g) = F.mapIso h)
  {Z : D} (e : F.obj z ≅ Z) {Z✝ : D} (h✝ : Z ≅ Z✝) : F.mapIso f ≪≫ F.mapIso g ≪≫ e ≪≫ h✝ = F.mapIso h ≪≫ e ≪≫ h✝
-/
#guard_msgs in
#check foo_functor'_assoc

end Tests.Reassoc
