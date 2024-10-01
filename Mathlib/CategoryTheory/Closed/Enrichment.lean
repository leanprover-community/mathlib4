/-
Copyright (c) 2024 Daniel Carranza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Carranza
-/
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Closed.Monoidal

/-!
# A closed monoidal category is enriched in itself

From the data of a closed monoidal category V, we define a V-category structure for V
where the hom-object is given by the internal hom (coming from the closed structure).

The instance is given at the end of the file.

All structure field values are defined separately

In particular, the proofs of associativity and unitality use the following outline:
  1. Take adjoint transpose on each side of the equality (uncurry_injective)
  2. Do whatever rewrites/simps are necessary to apply uncurry_curry
  3. Conclude with simp (+ a possible exact)
-/

universe u u₁ v w

namespace CategoryTheory

open MonoidalCategory

namespace MonoidalClosed

variable {V : Type u} [Category.{u₁, u} V] [MonoidalCategory V] [MonoidalClosed V]

/-- The V-identity morphism
  𝟙_ V ⟶ hom(V, v)
used to equip V with the structure of a V-category -/
def id (x : V) : 𝟙_ V ⟶ (ihom x).obj x := curry (ρ_ x).hom

/-- The *uncurried* composition morphism
  x ⊗ (hom(x, y) ⊗ hom(y, z)) ⟶ (x ⊗ hom(x, y)) ⊗ hom(y, z) ⟶ y ⊗ hom(y, z) ⟶ z.
The V-composition morphism is defined as the adjoint transpose of this map. -/
def compTranspose (x y z : V) :=
  (α_ x ((ihom x).obj y) ((ihom y).obj z)).inv ≫
    (ihom.ev x).app y ▷ ((ihom y).obj z) ≫
    (ihom.ev y).app z

/-- The V-composition morphism
  hom(x, y) ⊗ hom(y, z) ⟶ hom(x, z)
used to equip V with the structure of a V-category -/
def comp (x y z : V) := curry (compTranspose x y z)

/-- Unfold the definition of id.
This exists to streamline the proofs of MonoidalClosed.id_comp and MonoidalClosed.comp_id -/
@[simp]
lemma id_eq (x : V) : id x = curry (ρ_ x).hom := rfl

/-- Unfold the definition of compTranspose.
This exists to streamline the proof of MonoidalClosed.assoc -/
@[simp]
lemma compTranpose_eq (x y z : V) : compTranspose x y z = (α_ _ _ _).inv ≫
    (ihom.ev x).app y ▷ _ ≫ (ihom.ev y).app z :=
  rfl

/-- Unfold the definition of comp.
This exists to streamline the proof of MonoidalClosed.assoc -/
@[simp]
lemma comp_eq (x y z : V) : comp x y z = curry (compTranspose x y z) := rfl

/-- Associativity of V-composition. Used to prove that V is enriched in itself. -/
theorem assoc (x y z w : V) : (α_ _ _ _).inv ≫ comp x y z ▷ _ ≫ comp x z w =
    _ ◁ comp y z w ≫ comp x y w := by
  apply uncurry_injective;
  simp only [uncurry_natural_left, comp_eq]
  rw [uncurry_curry, uncurry_curry]; dsimp
  rw [associator_inv_naturality_middle_assoc]
  rw [← comp_whiskerRight_assoc]
  rw [← uncurry_eq, uncurry_curry]
  rw [associator_inv_naturality_right_assoc]
  rw [whisker_exchange_assoc]
  rw [← uncurry_eq, uncurry_curry]
  simp only [comp_whiskerRight, tensorLeft_obj, Category.assoc, pentagon_inv_assoc,
    whiskerRight_tensor, Iso.hom_inv_id_assoc]

/-- Left unitality of V-composition. Used to prove that V is enriched in itself. -/
theorem id_comp (x y : V) : (λ_ _).inv ≫ id x ▷ (ihom x).obj y ≫ comp x x y = 𝟙 _ := by
  apply uncurry_injective; simp only [uncurry_natural_left, comp_eq, id_eq]
  rw [uncurry_curry]
  rw [whisker_assoc_symm];
  simp only [compTranpose_eq, Category.assoc]
  rw [Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc]
  rw [← uncurry_eq, uncurry_curry]
  simp only [Functor.id_obj, triangle_assoc_comp_right_assoc, whiskerLeft_inv_hom_assoc]
  exact Eq.symm (uncurry_id_eq_ev x y)

/-- Right unitality of V-composition. Used to prove that V is enriched in itself. -/
theorem comp_id (x y : V) : (ρ_ _).inv ≫ ((ihom x).obj y) ◁ (id y) ≫ (comp x y y) = 𝟙 _ := by
  apply uncurry_injective; simp only[uncurry_natural_left, comp_eq, id_eq];
  rw [uncurry_curry]; simp only [compTranpose_eq, Category.assoc];
  rw [associator_inv_naturality_right_assoc]
  rw [whisker_exchange_assoc]; dsimp;
  rw [← uncurry_eq, uncurry_curry];
  simp only [whiskerLeft_rightUnitor_inv, MonoidalCategory.whiskerRight_id, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  exact Eq.symm (uncurry_id_eq_ev x y)

/-- For V closed monoidal, build an instance of V as a V-category -/
instance : EnrichedCategory V V where
  Hom := fun x => (ihom x).obj
  id := id
  comp := comp
  id_comp := id_comp
  comp_id := comp_id
  assoc := assoc

end MonoidalClosed
