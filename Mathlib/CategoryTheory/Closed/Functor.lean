/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

#align_import category_theory.closed.functor from "leanprover-community/mathlib"@"cea27692b3fdeb328a2ddba6aabf181754543184"

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

open Category Limits CartesianClosed

universe v u u'

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v} D]
variable [HasFiniteProducts C] [HasFiniteProducts D]
variable (F : C ⥤ D) {L : D ⥤ C}

/-- The Frobenius morphism for an adjunction `L ⊣ F` at `A` is given by the morphism

    L(FA ⨯ B) ⟶ LFA ⨯ LB ⟶ A ⨯ LB

natural in `B`, where the first morphism is the product comparison and the latter uses the counit
of the adjunction.

We will show that if `C` and `D` are cartesian closed, then this morphism is an isomorphism for all
`A` iff `F` is a cartesian closed functor, i.e. it preserves exponentials.
-/
def frobeniusMorphism (h : L ⊣ F) (A : C) :
    prod.functor.obj (F.obj A) ⋙ L ⟶ L ⋙ prod.functor.obj A :=
  prodComparisonNatTrans L (F.obj A) ≫ whiskerLeft _ (prod.functor.map (h.counit.app _))
#align category_theory.frobenius_morphism CategoryTheory.frobeniusMorphism

/-- If `F` is full and faithful and has a left adjoint `L` which preserves binary products, then the
Frobenius morphism is an isomorphism.
-/
instance frobeniusMorphism_iso_of_preserves_binary_products (h : L ⊣ F) (A : C)
    [PreservesLimitsOfShape (Discrete WalkingPair) L] [F.Full] [F.Faithful] :
    IsIso (frobeniusMorphism F h A) :=
  suffices ∀ (X : D), IsIso ((frobeniusMorphism F h A).app X) from NatIso.isIso_of_isIso_app _
  fun B ↦ by dsimp [frobeniusMorphism]; infer_instance
#align category_theory.frobenius_morphism_iso_of_preserves_binary_products CategoryTheory.frobeniusMorphism_iso_of_preserves_binary_products

variable [CartesianClosed C] [CartesianClosed D]
variable [PreservesLimitsOfShape (Discrete WalkingPair) F]

/-- The exponential comparison map.
`F` is a cartesian closed functor if this is an iso for all `A`.
-/
def expComparison (A : C) : exp A ⋙ F ⟶ F ⋙ exp (F.obj A) :=
  transferNatTrans (exp.adjunction A) (exp.adjunction (F.obj A)) (prodComparisonNatIso F A).inv
#align category_theory.exp_comparison CategoryTheory.expComparison

theorem expComparison_ev (A B : C) :
    Limits.prod.map (𝟙 (F.obj A)) ((expComparison F A).app B) ≫ (exp.ev (F.obj A)).app (F.obj B) =
      inv (prodComparison F _ _) ≫ F.map ((exp.ev _).app _) := by
  convert transferNatTrans_counit _ _ (prodComparisonNatIso F A).inv B using 2
  apply IsIso.inv_eq_of_hom_inv_id -- Porting note: was `ext`
  simp only [Limits.prodComparisonNatIso_inv, asIso_inv, NatIso.isIso_inv_app, IsIso.hom_inv_id]
#align category_theory.exp_comparison_ev CategoryTheory.expComparison_ev

theorem coev_expComparison (A B : C) :
    F.map ((exp.coev A).app B) ≫ (expComparison F A).app (A ⨯ B) =
      (exp.coev _).app (F.obj B) ≫ (exp (F.obj A)).map (inv (prodComparison F A B)) := by
  convert unit_transferNatTrans _ _ (prodComparisonNatIso F A).inv B using 3
  apply IsIso.inv_eq_of_hom_inv_id -- Porting note: was `ext`
  dsimp
  simp
#align category_theory.coev_exp_comparison CategoryTheory.coev_expComparison

theorem uncurry_expComparison (A B : C) :
    CartesianClosed.uncurry ((expComparison F A).app B) =
      inv (prodComparison F _ _) ≫ F.map ((exp.ev _).app _) := by
  rw [uncurry_eq, expComparison_ev]
#align category_theory.uncurry_exp_comparison CategoryTheory.uncurry_expComparison

/-- The exponential comparison map is natural in `A`. -/
theorem expComparison_whiskerLeft {A A' : C} (f : A' ⟶ A) :
    expComparison F A ≫ whiskerLeft _ (pre (F.map f)) =
      whiskerRight (pre f) _ ≫ expComparison F A' := by
  ext B
  dsimp
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left, uncurry_expComparison, uncurry_pre,
    prod.map_swap_assoc, ← F.map_id, expComparison_ev, ← F.map_id, ←
    prodComparison_inv_natural_assoc, ← prodComparison_inv_natural_assoc, ← F.map_comp, ←
    F.map_comp, prod_map_pre_app_comp_ev]
#align category_theory.exp_comparison_whisker_left CategoryTheory.expComparison_whiskerLeft

/-- The functor `F` is cartesian closed (ie preserves exponentials) if each natural transformation
`exp_comparison F A` is an isomorphism
-/
class CartesianClosedFunctor : Prop where
  comparison_iso : ∀ A, IsIso (expComparison F A)
#align category_theory.cartesian_closed_functor CategoryTheory.CartesianClosedFunctor

attribute [instance] CartesianClosedFunctor.comparison_iso

theorem frobeniusMorphism_mate (h : L ⊣ F) (A : C) :
    transferNatTransSelf (h.comp (exp.adjunction A)) ((exp.adjunction (F.obj A)).comp h)
        (frobeniusMorphism F h A) =
      expComparison F A := by
  rw [← Equiv.eq_symm_apply]
  ext B : 2
  dsimp [frobeniusMorphism, transferNatTransSelf, transferNatTrans, Adjunction.comp]
  simp only [id_comp, comp_id]
  rw [← L.map_comp_assoc, prod.map_id_comp, assoc]
  -- Porting note: need to use `erw` here.
  -- https://github.com/leanprover-community/mathlib4/issues/5164
  erw [expComparison_ev]
  rw [prod.map_id_comp, assoc, ← F.map_id, ← prodComparison_inv_natural_assoc, ← F.map_comp]
  -- Porting note: need to use `erw` here.
  -- https://github.com/leanprover-community/mathlib4/issues/5164
  erw [exp.ev_coev]
  rw [F.map_id (A ⨯ L.obj B), comp_id]
  ext
  · rw [assoc, assoc, ← h.counit_naturality, ← L.map_comp_assoc, assoc, inv_prodComparison_map_fst]
    simp
  · rw [assoc, assoc, ← h.counit_naturality, ← L.map_comp_assoc, assoc, inv_prodComparison_map_snd]
    simp
#align category_theory.frobenius_morphism_mate CategoryTheory.frobeniusMorphism_mate

/--
If the exponential comparison transformation (at `A`) is an isomorphism, then the Frobenius morphism
at `A` is an isomorphism.
-/
theorem frobeniusMorphism_iso_of_expComparison_iso (h : L ⊣ F) (A : C)
    [i : IsIso (expComparison F A)] : IsIso (frobeniusMorphism F h A) := by
  rw [← frobeniusMorphism_mate F h] at i
  exact @transferNatTransSelf_of_iso _ _ _ _ _ _ _ _ _ _ _ i
#align category_theory.frobenius_morphism_iso_of_exp_comparison_iso CategoryTheory.frobeniusMorphism_iso_of_expComparison_iso

/--
If the Frobenius morphism at `A` is an isomorphism, then the exponential comparison transformation
(at `A`) is an isomorphism.
-/
theorem expComparison_iso_of_frobeniusMorphism_iso (h : L ⊣ F) (A : C)
    [i : IsIso (frobeniusMorphism F h A)] : IsIso (expComparison F A) := by
  rw [← frobeniusMorphism_mate F h]; infer_instance
#align category_theory.exp_comparison_iso_of_frobenius_morphism_iso CategoryTheory.expComparison_iso_of_frobeniusMorphism_iso

/-- If `F` is full and faithful, and has a left adjoint which preserves binary products, then it is
cartesian closed.

TODO: Show the converse, that if `F` is cartesian closed and its left adjoint preserves binary
products, then it is full and faithful.
-/
theorem cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts (h : L ⊣ F) [F.Full] [F.Faithful]
    [PreservesLimitsOfShape (Discrete WalkingPair) L] : CartesianClosedFunctor F where
  comparison_iso _ := expComparison_iso_of_frobeniusMorphism_iso F h _
#align category_theory.cartesian_closed_functor_of_left_adjoint_preserves_binary_products CategoryTheory.cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts

end CategoryTheory
