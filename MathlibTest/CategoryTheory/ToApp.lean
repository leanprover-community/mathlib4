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

set_option backward.defeqAttrib.useBackward true in
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

end CategoryTheory.ToAppTest
