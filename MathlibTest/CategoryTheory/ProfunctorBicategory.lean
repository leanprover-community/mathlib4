import Mathlib.CategoryTheory.Profunctor.Bicategory

open CategoryTheory Bicategory

universe u

variable {C D E F : ProfCat.{u, u}}
  (P : C ⟶ D) (Q : D ⟶ E) (R : E ⟶ F)

example (X : C) (Y : Cᵒᵖ) : ((𝟙 C : C ⟶ C).obj X).obj Y = (Y.unop ⟶ X) := by
  simp

example {S : C ⟶ D} (η θ : P ⟶ S)
    (h : ∀ (X : C) (Y : Dᵒᵖ) (x : (P.obj X).obj Y),
      (η.app X).app Y x = (θ.app X).app Y x) : η = θ := by
  ext X Y x
  exact h X Y x

-- The generated lemmas connect bicategory notation to the existing profunctor simp lemmas.
example {Q' Q'' : D ⟶ E} (η : Q ⟶ Q') (θ : Q' ⟶ Q'') :
    P ◁ (η ≫ θ) = P.whiskerLeft η ≫ P.whiskerLeft θ := by
  simp

example {P' P'' : C ⟶ D} (η : P ⟶ P') (θ : P' ⟶ P'') :
    (η ≫ θ) ▷ Q = Profunctor.whiskerRight Q η ≫ Profunctor.whiskerRight Q θ := by
  simp

example : (α_ P Q R).hom ≫ (P.associator Q R).inv = 𝟙 _ := by
  simp

example : (P.associator Q R).hom ≫ (α_ P Q R).inv = 𝟙 _ := by
  simp

example : (λ_ P).hom ≫ P.leftUnitor.inv = 𝟙 _ := by
  simp

example : P.rightUnitor.hom ≫ (ρ_ P).inv = 𝟙 _ := by
  simp
