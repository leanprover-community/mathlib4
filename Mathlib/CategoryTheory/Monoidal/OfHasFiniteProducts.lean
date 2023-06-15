/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Simon Hudon

! This file was ported from Lean 3 source module category_theory.monoidal.of_has_finite_products
! leanprover-community/mathlib commit f153a85a8dc0a96ce9133fed69e34df72f7f191f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Monoidal.Braided
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# The natural monoidal structure on any category with finite (co)products.

A category with a monoidal structure provided in this way
is sometimes called a (co)cartesian category,
although this is also sometimes used to mean a finitely complete category.
(See <https://ncatlab.org/nlab/show/cartesian+category>.)

As this works with either products or coproducts,
and sometimes we want to think of a different monoidal structure entirely,
we don't set up either construct as an instance.

## Implementation
We had previously chosen to rely on `has_terminal` and `has_binary_products` instead of
`has_finite_products`, because we were later relying on the definitional form of the tensor product.
Now that `has_limit` has been refactored to be a `Prop`,
this issue is irrelevant and we could simplify the construction here.

See `category_theory.monoidal.of_chosen_finite_products` for a variant of this construction
which allows specifying a particular choice of terminal object and binary products.
-/


universe v u

noncomputable section

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] {X Y : C}

open CategoryTheory.Limits

section

/-- A category with a terminal object and binary products has a natural monoidal structure. -/
def monoidalOfHasFiniteProducts [HasTerminal C] [HasBinaryProducts C] : MonoidalCategory C where
  tensorUnit' := ⊤_ C
  tensorObj X Y := X ⨯ Y
  tensorHom f g := Limits.prod.map f g
  associator := prod.associator
  leftUnitor P := prod.leftUnitor P
  rightUnitor P := prod.rightUnitor P
  pentagon := prod.pentagon
  triangle := prod.triangle
  associator_naturality := @prod.associator_naturality _ _ _
#align category_theory.monoidal_of_has_finite_products CategoryTheory.monoidalOfHasFiniteProducts

end

section

attribute [local instance] monoidalOfHasFiniteProducts

open MonoidalCategory

/-- The monoidal structure coming from finite products is symmetric.
-/
@[simps]
def symmetricOfHasFiniteProducts [HasTerminal C] [HasBinaryProducts C] : SymmetricCategory C where
  braiding X Y := Limits.prod.braiding X Y
  braiding_naturality f g := by dsimp [tensorHom]; simp
  hexagon_forward X Y Z := by dsimp [monoidalOfHasFiniteProducts]; simp
  hexagon_reverse X Y Z := by dsimp [monoidalOfHasFiniteProducts]; simp
  symmetry X Y := by dsimp; simp; rfl
#align category_theory.symmetric_of_has_finite_products CategoryTheory.symmetricOfHasFiniteProducts

end

namespace monoidalOfHasFiniteProducts

variable [HasTerminal C] [HasBinaryProducts C]

attribute [local instance] monoidalOfHasFiniteProducts

open scoped MonoidalCategory

@[simp]
theorem tensorObj (X Y : C) : X ⊗ Y = (X ⨯ Y) :=
  rfl
#align category_theory.monoidal_of_has_finite_products.tensor_obj CategoryTheory.monoidalOfHasFiniteProducts.tensorObj

@[simp]
theorem tensorHom {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : f ⊗ g = Limits.prod.map f g :=
  rfl
#align category_theory.monoidal_of_has_finite_products.tensor_hom CategoryTheory.monoidalOfHasFiniteProducts.tensorHom

@[simp]
theorem leftUnitor_hom (X : C) : (λ_ X).hom = Limits.prod.snd :=
  rfl
#align category_theory.monoidal_of_has_finite_products.left_unitor_hom CategoryTheory.monoidalOfHasFiniteProducts.leftUnitor_hom

@[simp]
theorem leftUnitor_inv (X : C) : (λ_ X).inv = prod.lift (terminal.from X) (𝟙 _) :=
  rfl
#align category_theory.monoidal_of_has_finite_products.left_unitor_inv CategoryTheory.monoidalOfHasFiniteProducts.leftUnitor_inv

@[simp]
theorem rightUnitor_hom (X : C) : (ρ_ X).hom = Limits.prod.fst :=
  rfl
#align category_theory.monoidal_of_has_finite_products.right_unitor_hom CategoryTheory.monoidalOfHasFiniteProducts.rightUnitor_hom

@[simp]
theorem rightUnitor_inv (X : C) : (ρ_ X).inv = prod.lift (𝟙 _) (terminal.from X) :=
  rfl
#align category_theory.monoidal_of_has_finite_products.right_unitor_inv CategoryTheory.monoidalOfHasFiniteProducts.rightUnitor_inv

-- We don't mark this as a simp lemma, even though in many particular
-- categories the right hand side will simplify significantly further.
-- For now, we'll plan to create specialised simp lemmas in each particular category.
theorem associator_hom (X Y Z : C) :
    (α_ X Y Z).hom =
      prod.lift (Limits.prod.fst ≫ Limits.prod.fst)
        (prod.lift (Limits.prod.fst ≫ Limits.prod.snd) Limits.prod.snd) :=
  rfl
#align category_theory.monoidal_of_has_finite_products.associator_hom CategoryTheory.monoidalOfHasFiniteProducts.associator_hom

end monoidalOfHasFiniteProducts

section

/-- A category with an initial object and binary coproducts has a natural monoidal structure. -/
def monoidalOfHasFiniteCoproducts [HasInitial C] [HasBinaryCoproducts C] : MonoidalCategory C where
  tensorUnit' := ⊥_ C
  tensorObj X Y := X ⨿ Y
  tensorHom f g := Limits.coprod.map f g
  associator := coprod.associator
  leftUnitor := coprod.leftUnitor
  rightUnitor := coprod.rightUnitor
  pentagon := coprod.pentagon
  triangle := coprod.triangle
  associator_naturality := @coprod.associator_naturality _ _ _
#align category_theory.monoidal_of_has_finite_coproducts CategoryTheory.monoidalOfHasFiniteCoproducts

end

section

attribute [local instance] monoidalOfHasFiniteCoproducts

open MonoidalCategory

/-- The monoidal structure coming from finite coproducts is symmetric.
-/
@[simps]
def symmetricOfHasFiniteCoproducts [HasInitial C] [HasBinaryCoproducts C] : SymmetricCategory C
    where
  braiding := Limits.coprod.braiding
  braiding_naturality f g := by dsimp [tensorHom]; simp
  hexagon_forward X Y Z := by dsimp [monoidalOfHasFiniteCoproducts]; simp
  hexagon_reverse X Y Z := by dsimp [monoidalOfHasFiniteCoproducts]; simp
  symmetry X Y := by dsimp; simp; rfl
#align category_theory.symmetric_of_has_finite_coproducts CategoryTheory.symmetricOfHasFiniteCoproducts

end

namespace monoidalOfHasFiniteCoproducts

variable [HasInitial C] [HasBinaryCoproducts C]

attribute [local instance] monoidalOfHasFiniteCoproducts

open scoped MonoidalCategory

@[simp]
theorem tensorObj (X Y : C) : X ⊗ Y = (X ⨿ Y) :=
  rfl
#align category_theory.monoidal_of_has_finite_coproducts.tensor_obj CategoryTheory.monoidalOfHasFiniteCoproducts.tensorObj

@[simp]
theorem tensorHom {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : f ⊗ g = Limits.coprod.map f g :=
  rfl
#align category_theory.monoidal_of_has_finite_coproducts.tensor_hom CategoryTheory.monoidalOfHasFiniteCoproducts.tensorHom

@[simp]
theorem leftUnitor_hom (X : C) : (λ_ X).hom = coprod.desc (initial.to X) (𝟙 _) :=
  rfl
#align category_theory.monoidal_of_has_finite_coproducts.left_unitor_hom CategoryTheory.monoidalOfHasFiniteCoproducts.leftUnitor_hom

@[simp]
theorem rightUnitor_hom (X : C) : (ρ_ X).hom = coprod.desc (𝟙 _) (initial.to X) :=
  rfl
#align category_theory.monoidal_of_has_finite_coproducts.right_unitor_hom CategoryTheory.monoidalOfHasFiniteCoproducts.rightUnitor_hom

@[simp]
theorem leftUnitor_inv (X : C) : (λ_ X).inv = Limits.coprod.inr :=
  rfl
#align category_theory.monoidal_of_has_finite_coproducts.left_unitor_inv CategoryTheory.monoidalOfHasFiniteCoproducts.leftUnitor_inv

@[simp]
theorem rightUnitor_inv (X : C) : (ρ_ X).inv = Limits.coprod.inl :=
  rfl
#align category_theory.monoidal_of_has_finite_coproducts.right_unitor_inv CategoryTheory.monoidalOfHasFiniteCoproducts.rightUnitor_inv

-- We don't mark this as a simp lemma, even though in many particular
-- categories the right hand side will simplify significantly further.
-- For now, we'll plan to create specialised simp lemmas in each particular category.
theorem associator_hom (X Y Z : C) :
    (α_ X Y Z).hom =
      coprod.desc (coprod.desc coprod.inl (coprod.inl ≫ coprod.inr)) (coprod.inr ≫ coprod.inr) :=
  rfl
#align category_theory.monoidal_of_has_finite_coproducts.associator_hom CategoryTheory.monoidalOfHasFiniteCoproducts.associator_hom

end monoidalOfHasFiniteCoproducts

end CategoryTheory
