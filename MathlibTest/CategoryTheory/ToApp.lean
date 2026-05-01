import Mathlib.Tactic.CategoryTheory.ToApp
import Mathlib.CategoryTheory.Bicategory.Functor.Prelax

universe w v u

namespace CategoryTheory.ToAppTest

open Bicategory Category

variable {B : Type u} [Bicategory.{w, v} B] {a b c d e : B}

@[to_app]
theorem whiskerLeft_hom_inv (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) :
    f ◁ η.hom ≫ f ◁ η.inv = 𝟙 (f ≫ g) := by
  rw [← Bicategory.whiskerLeft_comp, Iso.hom_inv_id, Bicategory.whiskerLeft_id]

example {a b c : Cat} (f : a ⟶ b) {g h : b ⟶ c} (η : g ≅ h) (X : a) :
    η.hom.toNatTrans.app (f.toFunctor.obj X) ≫ η.inv.toNatTrans.app (f.toFunctor.obj X) =
      𝟙 ((f ≫ g).toFunctor.obj X) :=
  whiskerLeft_hom_inv_app f η X

@[to_app]
theorem pentagon_hom_hom_inv_inv_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    (α_ f (g ≫ h) i).hom ≫ f ◁ (α_ g h i).hom ≫ (α_ f g (h ≫ i)).inv =
      (α_ f g h).inv ▷ i ≫ (α_ (f ≫ g) h i).hom :=
  eq_of_inv_eq_inv (by simp)

example {a b c d e : Cat} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) (X : a) : True := by
  have hyp := pentagon_hom_hom_inv_inv_hom_app f g h i X
  guard_hyp hyp : 𝟙 (i.toFunctor.obj (h.toFunctor.obj (g.toFunctor.obj (f.toFunctor.obj X)))) =
    i.toFunctor.map (𝟙 (h.toFunctor.obj (g.toFunctor.obj (f.toFunctor.obj X))))
  trivial

@[to_app]
theorem testThm {C : Type*} [Bicategory C] (F : PrelaxFunctor B C) {a b : B} {f g : a ⟶ b}
    (η : f ⟶ g) : F.map₂ η ≫ F.map₂ (𝟙 g) = F.map₂ η := by simp

example {B : Type u_1} [Bicategory B] (F : PrelaxFunctor B Cat)
    {a b : B} {f g : a ⟶ b} (η : f ⟶ g) (X : ↑(F.obj a)) :
    (F.map₂ η).toNatTrans.app X ≫ (F.map₂ (𝟙 g)).toNatTrans.app X = (F.map₂ η).toNatTrans.app X :=
  testThm_app F η X

section UnbundledNatTrans

variable {C : Type u} [Category.{v} C] {D : Type u_1} [Category.{v_1} D]
variable {F G H K : C ⥤ D}

@[to_app]
theorem unbundled_eq_of_eq (η θ : F ⟶ G) (h : η = θ) : η = θ := h

example (η θ : F ⟶ G) (h : η = θ) (X : C) : True := by
  have hyp := unbundled_eq_of_eq_app η θ h X
  guard_hyp hyp : η.app X = θ.app X
  trivial

example (η θ : F ⟶ G) (h : η = θ) (X : C) : True := by
  have hyp := (to_app_of% h) X
  guard_hyp hyp : η.app X = θ.app X
  trivial

@[to_app]
theorem unbundled_comp_assoc (η : F ⟶ G) (θ : G ⟶ H) (κ : H ⟶ K) :
    (η ≫ θ) ≫ κ = η ≫ θ ≫ κ := by
  simp

example (η : F ⟶ G) (θ : G ⟶ H) (κ : H ⟶ K) (X : C) : True := by
  have hyp := unbundled_comp_assoc_app η θ κ X
  guard_hyp hyp : (η.app X ≫ θ.app X) ≫ κ.app X = η.app X ≫ θ.app X ≫ κ.app X
  trivial

section

def foo (η : F ⟶ G) (θ : G ⟶ F) : F ⟶ F := η ≫ θ

@[to_app (attr := local simp)]
theorem unbundled_eq (η : F ⟶ G) (θ : G ⟶ F) : η ≫ θ = foo η θ := rfl

/--
info: CategoryTheory.ToAppTest.unbundled_eq_app.{u_1, u_2, u_3, u_4} {C : Type u_1} [Category.{u_2, u_1} C] {D : Type u_3}
  [Category.{u_4, u_3} D] {F G : C ⥤ D} (η : F ⟶ G) (θ : G ⟶ F) (X : C) : η.app X ≫ θ.app X = (foo η θ).app X
-/
#guard_msgs in
#check unbundled_eq_app

example (η : F ⟶ G) (θ : G ⟶ F) (X : C) : True := by
  have hyp := unbundled_eq_app η θ X
  guard_hyp hyp : η.app X ≫ θ.app X = (foo η θ).app X
  trivial

example (η : F ⟶ G) (θ : G ⟶ F) (X : C) : η.app X ≫ θ.app X = (foo η θ).app X := by
  simp

example (η : F ⟶ G) (θ : G ⟶ F) (X : C) : η.app X ≫ θ.app X = (foo η θ).app X := by
  dsimp

end

attribute [-simp] Iso.inv_hom_id Iso.inv_hom_id_app

@[to_app (attr := simp)]
theorem inv_hom_id (i : F ≅ G) : i.inv ≫ i.hom = 𝟙 _ :=
  i.inv_hom_id

/--
info: CategoryTheory.ToAppTest.inv_hom_id_app.{u_1, u_2, u_3, u_4} {C : Type u_1} [Category.{u_2, u_1} C] {D : Type u_3}
  [Category.{u_4, u_3} D] {F G : C ⥤ D} (i : F ≅ G) (X : C) : i.inv.app X ≫ i.hom.app X = 𝟙 (G.obj X)
-/
#guard_msgs in
#check inv_hom_id_app

example (i : F ≅ G) (X : C) : i.inv.app X ≫ i.hom.app X = 𝟙 _ := by
  simp

end UnbundledNatTrans

end CategoryTheory.ToAppTest
