/-
Copyright (c) 2026 Amogh Parab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amogh Parab
-/
module

public import Mathlib.CategoryTheory.Monoidal.Discrete
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Categorical Groups

A categorical group is a monoidal category equipped with a negator,
and cancellation isomorphisms called the unit and counit isomorphisms.
The unit and counit isomorphisms must
satisfy coherence axioms.

With the coherence axioms, we can show that the negator extends to a functor and
the unit and counit isomorphisms are natural.

## Implementation note


We make `CategoricalGroup` as a typeclass with
MonoidalCategory, Groupoid, and RightRigidCategory as subclasses with no additional conditions.
Right rigidity gives the negator (right dual),
the counit morphism (coevaluation), and the unit morphism (evaluation).
With the groupoid structure, we can construct the unit and counit isomorphisms from the unit and
counit morphisms.

From RightRigidity, we also get the coherence axioms of the unit and counit isomorphisms
(evaluation-coevaluation and coevaluation-evaluation).
Again, with the groupoid structure, we extend these to
the coherence axioms of the unit and counit isomorphisms.

For consistency, we will use the terms "evaluation" and "coevaluation"
to refer to the unit and counit isomorphisms of a categorical group. This also avoids confusion
with the unit object.

## Future work

* Extend `negatorObj` to a functor `negator : C ⥤ C` and
unit and counit isomorphisms to natural isomorphisms.
* Add basic lemmas.
* Extend categorical groups to symmetric categorical groups by adding a braiding.

## References

* John C. Baez and Aaron D. Lauda. Higher-dimensional algebra V: 2-groups. Theory
Appl. Categ., 12:423–491, 2004

-/

@[expose] public section

universe u v

namespace CategoryTheory

open Category MonoidalCategory CategoryTheory

namespace CategoricalGroup

variable {C : Type u} [Groupoid.{v} C]
  [MonoidalCategory.{v} C] [RightRigidCategory C]

/--
Negator of an object in a categorical group is the right dual of the object.
-/
def negatorObj (X : C) : C := Xᘁ

/--
The unit (evaluation) isomorphism of a categorical group.
-/
def evaluationIso (X : C) : Xᘁ ⊗ X ≅ 𝟙_ C where
  hom := ε_ X Xᘁ
  inv := Groupoid.inv (ε_ X Xᘁ)
  hom_inv_id := Groupoid.comp_inv (ε_ X Xᘁ)
  inv_hom_id := Groupoid.inv_comp (ε_ X Xᘁ)

/--
The counit (coevaluation) isomorphism of a categorical group.
-/
def coevaluationIso (X : C) : 𝟙_ C ≅ X ⊗ Xᘁ where
  hom := η_ X Xᘁ
  inv := Groupoid.inv (η_ X Xᘁ)
  hom_inv_id := Groupoid.comp_inv (η_ X Xᘁ)
  inv_hom_id := Groupoid.inv_comp (η_ X Xᘁ)

/--
The zig-zag axiom 1: Elevating the coevaluation-evaluation axiom to an equality of isomorphism.
-/
lemma coevaluation_evaluation_iso (X : C) : 
    (whiskerLeftIso Xᘁ (coevaluationIso X)) ≪≫ (α_ Xᘁ X Xᘁ).symm ≪≫ 
      whiskerRightIso (evaluationIso X) Xᘁ = ρ_ Xᘁ ≪≫ (λ_ Xᘁ).symm := by
  ext
  simp only [Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, whiskerRightIso_hom]
  exact ExactPairing.coevaluation_evaluation X Xᘁ

/--
The zig-zag axiom 2: Elevating the evaluation-coevaluation axiom to an equality of isomorphism.
-/
lemma evaluation_coevaluation_iso (X : C) : (whiskerRightIso (coevaluationIso X) X) ≪≫
(α_ X Xᘁ X) ≪≫
whiskerLeftIso X (evaluationIso X)
=
(λ_ X) ≪≫ (ρ_ X).symm := by
  ext
  simp only [Iso.trans_hom, whiskerRightIso_hom, Iso.symm_hom, whiskerLeftIso_hom]
  exact ExactPairing.evaluation_coevaluation X Xᘁ



instance ExactPairing.of_rightDual_self (X : C) : ExactPairing Xᘁ X where
  coevaluation' := (evaluationIso X).inv

  evaluation' := (coevaluationIso X).inv

  coevaluation_evaluation' := by
    have : whiskerLeftIso X (evaluationIso X).symm ≪≫
    (α_ X Xᘁ X).symm ≪≫ whiskerRightIso (coevaluationIso X).symm X
    = (ρ_ X) ≪≫ (λ_ X).symm := by
      apply_fun (fun f => f.symm)
      · simp only [Iso.trans_symm, whiskerRightIso_symm, Iso.symm_symm_eq, whiskerLeftIso_symm,
        Iso.trans_assoc]
        exact evaluation_coevaluation_iso X
      · simp only [Iso.symm_bijective.injective]
    apply_fun (fun f => f.hom) at this
    simp only [Iso.trans_hom, whiskerRightIso_hom, Iso.symm_hom, whiskerLeftIso_hom] at this
    exact this


  evaluation_coevaluation' := by
    have : whiskerRightIso (evaluationIso X).symm Xᘁ ≪≫
    (α_ Xᘁ X Xᘁ) ≪≫ whiskerLeftIso Xᘁ (coevaluationIso X).symm
    = (λ_ Xᘁ) ≪≫ (ρ_ Xᘁ).symm := by
      apply_fun (fun f => f.symm)
      · simp only [Iso.trans_symm, whiskerLeftIso_symm, Iso.symm_symm_eq, whiskerRightIso_symm,
        Iso.trans_assoc]
        exact coevaluation_evaluation_iso X
      · simp only [Iso.symm_bijective.injective]
    apply_fun (fun f => f.hom) at this
    simp only [Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, whiskerRightIso_hom] at this
    exact this

/--
In a categorical group, the right dual of an object is also its left dual.
-/
instance HasLeftDual.of_CategoricalGroup (X : C) : HasLeftDual X where
  leftDual := Xᘁ
  exact := ExactPairing.of_rightDual_self X

instance LeftRigidCategory.of_CategoricalGroup : LeftRigidCategory C where
  leftDual := fun X => HasLeftDual.of_CategoricalGroup X

instance RigidCategory.of_CategoricalGroup : RigidCategory C where
  toRightRigidCategory := inferInstance
  toLeftRigidCategory := LeftRigidCategory.of_CategoricalGroup


end CategoricalGroup


end CategoryTheory
