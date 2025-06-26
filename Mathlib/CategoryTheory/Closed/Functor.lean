/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Cartesian closed functors

Define the exponential comparison morphisms for a functor which preserves binary products, and use
them to define a cartesian closed functor: one which (naturally) preserves exponentials.

Define the Frobenius morphism, and show it is an isomorphism iff the exponential comparison is an
isomorphism.

## TODO
Some of the results here are true more generally for closed objects and for closed monoidal
categories, and these could be generalised.

## References
https://ncatlab.org/nlab/show/cartesian+closed+functor
https://ncatlab.org/nlab/show/Frobenius+reciprocity

## Tags
Frobenius reciprocity, cartesian closed functor

-/


noncomputable section

namespace CategoryTheory

open Category CartesianClosed MonoidalCategory CartesianMonoidalCategory TwoSquare

universe v u u'

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v} D]
variable [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
variable (F : C ⥤ D) {L : D ⥤ C}

/-- The Frobenius morphism for an adjunction `L ⊣ F` at `A` is given by the morphism

    L(FA ⨯ B) ⟶ LFA ⨯ LB ⟶ A ⨯ LB

natural in `B`, where the first morphism is the product comparison and the latter uses the counit
of the adjunction.

We will show that if `C` and `D` are cartesian closed, then this morphism is an isomorphism for all
`A` iff `F` is a cartesian closed functor, i.e. it preserves exponentials.
-/
def frobeniusMorphism (h : L ⊣ F) (A : C) : TwoSquare (tensorLeft (F.obj A)) L L (tensorLeft A) :=
  prodComparisonNatTrans L (F.obj A) ≫ whiskerLeft _ ((curriedTensor C).map (h.counit.app _))

/-- If `F` is full and faithful and has a left adjoint `L` which preserves binary products, then the
Frobenius morphism is an isomorphism.
-/
instance frobeniusMorphism_iso_of_preserves_binary_products (h : L ⊣ F) (A : C)
    [Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) L] [F.Full] [F.Faithful] :
    IsIso (frobeniusMorphism F h A).natTrans :=
  suffices ∀ (X : D), IsIso ((frobeniusMorphism F h A).natTrans.app X) from
    NatIso.isIso_of_isIso_app _
  fun B ↦ by dsimp [frobeniusMorphism]; infer_instance

variable [CartesianClosed C] [CartesianClosed D]
variable [Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) F]

/-- The exponential comparison map.
`F` is a cartesian closed functor if this is an iso for all `A`.
-/
def expComparison (A : C) : TwoSquare (exp A) F F (exp (F.obj A)) :=
  mateEquiv (exp.adjunction A) (exp.adjunction (F.obj A)) (prodComparisonNatIso F A).inv

theorem expComparison_ev (A B : C) :
    F.obj A ◁ ((expComparison F A).natTrans.app B) ≫ (exp.ev (F.obj A)).app (F.obj B) =
      inv (prodComparison F _ _) ≫ F.map ((exp.ev _).app _) := by
  convert mateEquiv_counit _ _ (prodComparisonNatIso F A).inv B using 2
  apply IsIso.inv_eq_of_hom_inv_id -- Porting note: was `ext`
  simp only [prodComparisonNatTrans_app, prodComparisonNatIso_inv, asIso_inv, NatIso.isIso_inv_app,
    IsIso.hom_inv_id]

theorem coev_expComparison (A B : C) :
    F.map ((exp.coev A).app B) ≫ (expComparison F A).natTrans.app (A ⊗ B) =
      (exp.coev _).app (F.obj B) ≫ (exp (F.obj A)).map (inv (prodComparison F A B)) := by
  convert unit_mateEquiv _ _ (prodComparisonNatIso F A).inv B using 3
  apply IsIso.inv_eq_of_hom_inv_id -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): was `ext`
  simp

theorem uncurry_expComparison (A B : C) :
    CartesianClosed.uncurry ((expComparison F A).natTrans.app B) =
      inv (prodComparison F _ _) ≫ F.map ((exp.ev _).app _) := by
  rw [uncurry_eq, expComparison_ev]

/-- The exponential comparison map is natural in `A`. -/
theorem expComparison_whiskerLeft {A A' : C} (f : A' ⟶ A) :
    (expComparison F A).whiskerBottom (pre (F.map f)) =
      (expComparison F A').whiskerTop (pre f) := by
  unfold expComparison pre
  have vcomp1 := mateEquiv_conjugateEquiv_vcomp
    (exp.adjunction A) (exp.adjunction (F.obj A)) (exp.adjunction (F.obj A'))
    ((prodComparisonNatIso F A).inv) (((curriedTensor D).map (F.map f)))
  have vcomp2 := conjugateEquiv_mateEquiv_vcomp
    (exp.adjunction A) (exp.adjunction A') (exp.adjunction (F.obj A'))
    (((curriedTensor C).map f)) ((prodComparisonNatIso F A').inv)
  rw [← vcomp1, ← vcomp2]
  unfold TwoSquare.whiskerLeft TwoSquare.whiskerRight
  congr 1
  apply congr_arg
  ext B
  simp only [Functor.comp_obj, curriedTensor_obj_obj, prodComparisonNatIso_inv, asIso_inv,
    NatTrans.comp_app, whiskerLeft_app, curriedTensor_map_app, NatIso.isIso_inv_app,
    whiskerRight_app, IsIso.eq_inv_comp, prodComparisonNatTrans_app]
  rw [← prodComparison_inv_natural_whiskerRight F f]
  simp

/-- The functor `F` is cartesian closed (ie preserves exponentials) if each natural transformation
`exp_comparison F A` is an isomorphism
-/
class CartesianClosedFunctor : Prop where
  comparison_iso : ∀ A, IsIso (expComparison F A).natTrans

attribute [instance] CartesianClosedFunctor.comparison_iso

theorem frobeniusMorphism_mate (h : L ⊣ F) (A : C) :
    conjugateEquiv (h.comp (exp.adjunction A)) ((exp.adjunction (F.obj A)).comp h)
        (frobeniusMorphism F h A).natTrans = (expComparison F A).natTrans := by
  unfold expComparison frobeniusMorphism
  have conjeq := iterated_mateEquiv_conjugateEquiv h h
    (exp.adjunction (F.obj A)) (exp.adjunction A)
    (prodComparisonNatTrans L (F.obj A) ≫ whiskerLeft L ((curriedTensor C).map (h.counit.app A)))
  rw [← conjeq]
  congr 1
  apply congr_arg
  ext B
  unfold mateEquiv
  simp only [Functor.comp_obj, curriedTensor_obj_obj, Functor.id_obj, Equiv.coe_fn_mk,
    whiskerLeft_comp, whiskerLeft_twice, whiskerRight_comp, assoc, NatTrans.comp_app,
    whiskerLeft_app, curriedTensor_obj_obj, whiskerRight_app, prodComparisonNatTrans_app,
    curriedTensor_map_app, Functor.comp_map, curriedTensor_obj_map, prodComparisonNatIso_inv,
    asIso_inv, NatIso.isIso_inv_app]
  rw [← F.map_comp, ← F.map_comp]
  simp only [Functor.map_comp]
  apply IsIso.eq_inv_of_inv_hom_id
  simp only [assoc, Functor.associator_inv_app, Functor.associator_hom_app, Functor.comp_obj,
    curriedTensor_obj_obj, curriedTensor_obj_obj, Functor.map_id, id_comp]
  rw [prodComparison_natural_whiskerLeft, prodComparison_natural_whiskerRight_assoc]
  slice_lhs 2 3 => rw [← prodComparison_comp]
  simp only [assoc]
  unfold prodComparison
  have ηlemma : (h.unit.app (F.obj A ⊗ F.obj B) ≫
    lift ((L ⋙ F).map (fst _ _)) ((L ⋙ F).map (snd _ _))) =
      (h.unit.app (F.obj A)) ⊗ₘ (h.unit.app (F.obj B)) := by
    ext <;> simp
  slice_lhs 1 2 => rw [ηlemma]
  simp only [Functor.id_obj, Functor.comp_obj, assoc, ← whisker_exchange, ← tensorHom_def']
  ext <;> simp

/--
If the exponential comparison transformation (at `A`) is an isomorphism, then the Frobenius morphism
at `A` is an isomorphism.
-/
theorem frobeniusMorphism_iso_of_expComparison_iso (h : L ⊣ F) (A : C)
    [i : IsIso (expComparison F A).natTrans] : IsIso (frobeniusMorphism F h A).natTrans := by
  rw [← frobeniusMorphism_mate F h] at i
  exact @conjugateEquiv_of_iso _ _ _ _ _ _ _ _ _ _ _ i

/--
If the Frobenius morphism at `A` is an isomorphism, then the exponential comparison transformation
(at `A`) is an isomorphism.
-/
theorem expComparison_iso_of_frobeniusMorphism_iso (h : L ⊣ F) (A : C)
    [i : IsIso (frobeniusMorphism F h A)] : IsIso (expComparison F A).natTrans := by
  rw [← frobeniusMorphism_mate F h]; infer_instance

open Limits in
/-- If `F` is full and faithful, and has a left adjoint which preserves binary products, then it is
cartesian closed.

TODO: Show the converse, that if `F` is cartesian closed and its left adjoint preserves binary
products, then it is full and faithful.
-/
theorem cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts (h : L ⊣ F) [F.Full] [F.Faithful]
    [PreservesLimitsOfShape (Discrete WalkingPair) L] : CartesianClosedFunctor F where
  comparison_iso _ := expComparison_iso_of_frobeniusMorphism_iso F h _

end CategoryTheory
