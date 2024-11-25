/-
Copyright (c) 2024 Daniel Carranza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Carranza
-/
import Mathlib.CategoryTheory.Enriched.Ordinary
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!

# The opposite category of an enriched category

When a monoidal category `V` is braided, we may define the opposite `V`-category of a
`V`-category. The symmetry map is required to define the composition morphism.

This file constructs the opposite `V`-category as an instance on the type `Cᵒᵖ` and constructs an
equivalence between the underlying category `ForgetEnrichment V (Cᵒᵖ)` and the opposite category
`(ForgetEnrichment V C)ᵒᵖ`.

We use `Cᵒᵖ` for the underlying type as this allows us to construct an instance of
`EnrichedOrdinaryCategory V (Cᵒᵖ)` in the case that `C` comes with an instance of
`EnrichedOrdinaryCategory V C`.

-/

universe v₁ u₁ v u

namespace CategoryTheory

open MonoidalCategory BraidedCategory

variable (V : Type u₁) [Category.{v₁} V] [MonoidalCategory V] [BraidedCategory V]

section

variable (C : Type u) [EnrichedCategory V C]

/-- For a `V`-category `C`, construct the opposite `V`-category structure on the type `Cᵒᵖ`
using the braiding in `V`. -/
instance EnrichedCategory.Opposite : EnrichedCategory V Cᵒᵖ where
  Hom y x := EnrichedCategory.Hom x.unop y.unop
  id x := EnrichedCategory.id x.unop
  comp z y x := (β_ _ _).hom ≫ EnrichedCategory.comp (x.unop) (y.unop) (z.unop)
  id_comp _ _ := by
    simp only [braiding_naturality_left_assoc, braiding_tensorUnit_left,
      Category.assoc, Iso.inv_hom_id_assoc]
    exact EnrichedCategory.comp_id _ _
  comp_id _ _ := by
    simp only [braiding_naturality_right_assoc, braiding_tensorUnit_right,
      Category.assoc, Iso.inv_hom_id_assoc]
    exact EnrichedCategory.id_comp _ _
  assoc _ _ _ _ := by
    simp only [braiding_naturality_left_assoc,
      MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [← EnrichedCategory.assoc]
    simp only [braiding_tensor_left, Category.assoc, Iso.inv_hom_id_assoc,
      braiding_naturality_right_assoc, braiding_tensor_right]

end

/-- Unfold the definition of composition in the enriched opposite category. -/
@[reassoc]
lemma eComp_op_eq {C : Type u} [EnrichedCategory V C] (x y z : Cᵒᵖ) :
    eComp V z y x = (β_ _ _).hom ≫ eComp V x.unop y.unop z.unop :=
  rfl

/-- When composing a tensor product of morphisms with the `V`-composition morphism in `Cᵒᵖ`,
this re-writes the `V`-composition to be in `C` and moves the braiding to the left. -/
@[reassoc]
lemma tensorHom_eComp_op_eq {C : Type u} [EnrichedCategory V C] {x y z : Cᵒᵖ} {v w : V}
    (f : v ⟶ EnrichedCategory.Hom z y) (g : w ⟶ EnrichedCategory.Hom y x) :
    (f ⊗ g) ≫ eComp V z y x = (β_ v w).hom ≫ (g ⊗ f) ≫ eComp V x.unop y.unop z.unop := by
  rw [eComp_op_eq]
  exact braiding_naturality_assoc (C := V) f g _

-- In this section, we establish an equivalence between
--  • the underlying category of the `V`-category `Cᵒᵖ`; and
--  • the opposite category of the underlying category of `C`.
-- We also show that if `C` is an enriched ordinary category (i.e. a category enriched in `V`
-- equipped with an identification `(X ⟶ Y) ≃ (𝟙_ V ⟶ (X ⟶[V] Y))`) then `Cᵒᵖ` is again
-- an enriched ordinary category.
section

variable (C : Type u) [EnrichedCategory V C]

/-- The functor going from the underlying category of `Cᵒᵖ` to the opposite of the underlying
category of `C`. -/
def ForgetEnrichment.Opposite.toOp : ForgetEnrichment V Cᵒᵖ ⥤ (ForgetEnrichment V C)ᵒᵖ where
  obj x := x
  map {x y} f := f.op
  map_comp {x y z} f g := by
    have : (f ≫ g) = homTo V (f ≫ g) := rfl
    rw [this, forgetEnrichment_comp, Category.assoc, tensorHom_eComp_op_eq,
      leftUnitor_inv_braiding_assoc, ← unitors_inv_equal, ← Category.assoc]
    congr 1

/-- The functor going from the opposite of the underlying category of `C` to the underlying
category of `Cᵒᵖ`. -/
def ForgetEnrichment.Opposite.fromOp : (ForgetEnrichment V C)ᵒᵖ ⥤ ForgetEnrichment V Cᵒᵖ where
  obj x := x
  map {x y} f := f.unop
  map_comp {x y z} f g := by
    have : g.unop ≫ f.unop = homTo V (g.unop ≫ f.unop) := rfl
    dsimp
    rw [this, forgetEnrichment_comp, Category.assoc, unitors_inv_equal,
      ← leftUnitor_inv_braiding_assoc]
    have : (β_ _ _).hom ≫ (homTo V g.unop ⊗ homTo V f.unop) ≫
        eComp V («to» V z.unop) («to» V y.unop) («to» V x.unop) =
        ((homTo V f.unop) ⊗ (homTo V g.unop)) ≫ eComp V x y z :=
      by exact (tensorHom_eComp_op_eq V _ _).symm
    rw [this, ← Category.assoc]
    congr 1

/-- The identity functor on `ForgetEnrichment V (Cᵒᵖ)` is naturally isomorphic to the composite
functor from `ForgetEnrichment V (Cᵒᵖ)` to `(ForgetEnrichment V C)ᵒᵖ` and
back to `ForgetEnrichment V (Cᵒᵖ)`. -/
def ForgetEnrichment.Opposite.toFromNatIso :
    𝟭 (ForgetEnrichment V Cᵒᵖ) ≅ toOp V C ⋙ fromOp V C where
  hom := {app := 𝟙}
  inv := {
    app := 𝟙
    naturality := fun ⦃X Y⦄ f => by
      dsimp
      have :  𝟙 ((fromOp V C).obj ((toOp V C).obj Y)) = 𝟙 Y := rfl
      rw [← this, Category.comp_id, Category.id_comp f]
      congr 1
  }

/-- The composite functor from `(ForgetEnrichment V C)ᵒᵖ` to `ForgetEnrichment V (Cᵒᵖ)` and
back to `(ForgetEnrichment V C)ᵒᵖ` is naturally isomorphic to the identity functor. -/
def ForgetEnrichment.Opposite.fromToNatIso :
    fromOp V C ⋙ toOp V C ≅ 𝟭 (ForgetEnrichment V C)ᵒᵖ where
  hom := {
    app := 𝟙
    naturality := fun ⦃X Y⦄ f => by
      dsimp
      have :  𝟙 ((toOp V C).obj ((fromOp V C).obj Y)) = 𝟙 Y := rfl
      rw [← this, Category.comp_id, Category.id_comp f]
      congr 1
  }
  inv := {app := 𝟙}

/-- The equivalence between the underlying category of `Cᵒᵖ` and the opposite of the underlying
category of `C`. -/
def ForgetEnrichment.Opposite.equiv : ForgetEnrichment V Cᵒᵖ ≌ (ForgetEnrichment V C)ᵒᵖ :=
  Equivalence.mk (toOp V C) (fromOp V C) (toFromNatIso V C) (fromToNatIso V C)

/-- If `D` is an enriched ordinary category then `Dᵒᵖ` is an enriched ordinary category. -/
instance EnrichedOrdinaryCategory.Opposite {D : Type u} [Category.{v} D]
    [EnrichedOrdinaryCategory V D] : EnrichedOrdinaryCategory V Dᵒᵖ where
  toEnrichedCategory := inferInstanceAs (EnrichedCategory V Dᵒᵖ)
  homEquiv := Quiver.Hom.opEquiv.symm.trans homEquiv
  homEquiv_id x := homEquiv_id (x.unop)
  homEquiv_comp f g := by
    simp only [unop_comp, tensorHom_eComp_op_eq, leftUnitor_inv_braiding_assoc, ← unitors_inv_equal]
    exact homEquiv_comp g.unop f.unop

end

end CategoryTheory
