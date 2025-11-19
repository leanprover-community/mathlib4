import Mathlib.Tactic.CategoryTheory.Associators

namespace CategoryTheory

open CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅
variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable {D : Type u₄} [Category.{v₄} D]
variable {E : Type u₅} [Category.{v₅} E]

variable (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) (I : D ⥤ E)

open Functor

local infixr:81 " ◁ " => Functor.whiskerLeft
local infixl:81 " ▷ " => Functor.whiskerRight
local notation "α_" => Functor.associator
local notation "λ_" => Functor.leftUnitor
local notation "ρ_" => Functor.rightUnitor

/--
info: Try this: (α_ F G H).hom
-/
#guard_msgs in
example : (F ⋙ G) ⋙ H ⟶ F ⋙ (G ⋙ H) :=
  assoc%

/--
info: Try this: (α_ F G H).inv
-/
#guard_msgs in
example : F ⋙ (G ⋙ H) ⟶ (F ⋙ G) ⋙ H :=
  assoc%

/--
info: Try this: (λ_ F).hom
-/
#guard_msgs in
example : 𝟭 _ ⋙ F ⟶ F :=
  assoc%

/--
info: Try this: (λ_ F).inv
-/
#guard_msgs in
example : F ⟶ 𝟭 _ ⋙ F :=
  assoc%

/--
info: Try this: (ρ_ F).hom
-/
#guard_msgs in
example : F ⋙ 𝟭 _ ⟶ F :=
  assoc%

/--
info: Try this: (ρ_ F).inv
-/
#guard_msgs in
example : F ⟶ F ⋙ 𝟭 _ :=
  assoc%

/--
info: Try this: (ρ_ F).hom ▷ G
-/
#guard_msgs in
example : (F ⋙ 𝟭 B) ⋙ G ⟶ F ⋙ G :=
  assoc%

/--
info: Try this: (α_ (F ⋙ G) H I).hom ≫ (α_ F G (H ⋙ I)).hom
-/
#guard_msgs in
example : ((F ⋙ G) ⋙ H) ⋙ I ⟶ F ⋙ G ⋙ H ⋙ I :=
  assoc%

/--
info: Try this: F ◁ (α_ G H I).hom ≫ (α_ F G (H ⋙ I)).inv
-/
#guard_msgs in
example : F ⋙ (G ⋙ H) ⋙ I ⟶ (F ⋙ G) ⋙ H ⋙ I :=
  assoc%

/--
info: Try this: (α_ (F ⋙ G) H I).hom ≫ (α_ F G (H ⋙ I)).hom ≫ F ◁ (λ_ (G ⋙ H ⋙ I)).inv
-/
#guard_msgs in
example : ((F ⋙ G) ⋙ H) ⋙ I ⟶ F ⋙ 𝟭 _ ⋙ G ⋙ H ⋙ I :=
  assoc%

/--
info: Try this: (α_ F G (H ⋙ I)).hom ≫ F ◁ G ◁ (λ_ (H ⋙ I)).inv ≫ F ◁ G ◁ (α_ (𝟭 C) H I).inv ≫ F ◁ (α_ G (𝟭 C ⋙ H) I).inv
-/
#guard_msgs in
example : (F ⋙ G) ⋙ (H ⋙ I) ⟶ F ⋙ (G ⋙ 𝟭 _ ⋙ H) ⋙ I :=
  assoc%

end CategoryTheory
