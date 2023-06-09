/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer

! This file was ported from Lean 3 source module algebra.category.fgModule.basic
! leanprover-community/mathlib commit 74403a3b2551b0970855e14ef5e8fd0d6af1bfc2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.LinearAlgebra.Coevaluation
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

/-!
# The category of finitely generated modules over a ring

This introduces `FGModuleCat R`, the category of finitely generated modules over a ring `R`.
It is implemented as a full subcategory on a subtype of `ModuleCat R`.

When `K` is a field,
`FGModuleCatCat K` is the category of finite dimensional vector spaces over `K`.

We first create the instance as a preadditive category.
When `R` is commutative we then give the structure as an `R`-linear monoidal category.
When `R` is a field we give it the structure of a closed monoidal category
and then as a right-rigid monoidal category.

## Future work

* Show that `FGModuleCat R` is abelian when `R` is (left)-noetherian.

-/

set_option linter.uppercaseLean3 false

noncomputable section

open CategoryTheory ModuleCat.monoidalCategory

open scoped Classical BigOperators

universe u

section Ring

variable (R : Type u) [Ring R]

/-- Define `FGModuleCat` as the subtype of `ModuleCat.{u} R` of finitely generated modules. -/
def FGModuleCat :=
  FullSubcategory fun V : ModuleCat.{u} R => Module.Finite R V
-- Porting note: still no derive handler via `dsimp`.
-- deriving LargeCategory, ConcreteCategory,Preadditive
#align fgModule FGModuleCat

instance : LargeCategory (FGModuleCat R) := by
  dsimp [FGModuleCat]
  infer_instance

instance : ConcreteCategory (FGModuleCat R) := by
  dsimp [FGModuleCat]
  infer_instance

instance : Preadditive (FGModuleCat R) := by
  dsimp [FGModuleCat]
  infer_instance

end Ring

namespace FGModuleCat

section Ring

variable (R : Type u) [Ring R]

instance finite (V : FGModuleCat R) : Module.Finite R V.obj :=
  V.property
#align fgModule.finite FGModuleCat.finite

instance : Inhabited (FGModuleCat R) :=
  ⟨⟨ModuleCat.of R R, Module.Finite.self R⟩⟩

/-- Lift an unbundled finitely generated module to `FGModuleCat R`. -/
def of (V : Type u) [AddCommGroup V] [Module R V] [Module.Finite R V] : FGModuleCat R :=
  ⟨ModuleCat.of R V, by change Module.Finite R V; infer_instance⟩
#align fgModule.of FGModuleCat.of

instance (V : FGModuleCat R) : Module.Finite R V.obj :=
  V.property

instance : HasForget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R) := by
  dsimp [FGModuleCat]
  infer_instance

instance : Full (forget₂ (FGModuleCat R) (ModuleCat.{u} R)) where
  preimage f := f

variable {R}

/-- Converts and isomorphism in the category `FGModuleCat R` to
a `linear_equiv` between the underlying modules. -/
def isoToLinearEquiv {V W : FGModuleCat R} (i : V ≅ W) : V.obj ≃ₗ[R] W.obj :=
  ((forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).mapIso i).toLinearEquiv
#align fgModule.iso_to_linear_equiv FGModuleCat.isoToLinearEquiv

/-- Converts a `linear_equiv` to an isomorphism in the category `FGModuleCat R`. -/
@[simps]
def _root_.LinearEquiv.toFGModuleCatIso
    {V W : Type u} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [AddCommGroup W] [Module R W] [Module.Finite R W] (e : V ≃ₗ[R] W) :
    FGModuleCat.of R V ≅ FGModuleCat.of R W where
  hom := e.toLinearMap
  inv := e.symm.toLinearMap
  hom_inv_id := by ext x; exact e.left_inv x
  inv_hom_id := by ext x; exact e.right_inv x
#align linear_equiv.to_fgModule_iso LinearEquiv.toFGModuleCatIso

end Ring

section CommRing

variable (R : Type u) [CommRing R]

instance : Linear R (FGModuleCat R) := by
  dsimp [FGModuleCat]
  infer_instance

instance monoidalPredicate_module_finite :
    MonoidalCategory.MonoidalPredicate fun V : ModuleCat.{u} R => Module.Finite R V where
  prop_id := Module.Finite.self R
  prop_tensor := @fun X Y _ _ => Module.Finite.tensorProduct R X Y
#align fgModule.monoidal_predicate_module_finite FGModuleCat.monoidalPredicate_module_finite

instance : MonoidalCategory (FGModuleCat R) := by
  dsimp [FGModuleCat]
  infer_instance

instance : SymmetricCategory (FGModuleCat R) := by
  dsimp [FGModuleCat]
  infer_instance

instance : MonoidalPreadditive (FGModuleCat R) := by
  dsimp [FGModuleCat]
  infer_instance

instance : MonoidalLinear R (FGModuleCat R) := by
  dsimp [FGModuleCat]
  infer_instance

/-- The forgetful functor `FGModuleCat R ⥤ Module R` as a monoidal functor. -/
def forget₂Monoidal : MonoidalFunctor (FGModuleCat R) (ModuleCat.{u} R) :=
  MonoidalCategory.fullMonoidalSubcategoryInclusion _
#align fgModule.forget₂_monoidal FGModuleCat.forget₂Monoidal

instance forget₂Monoidal_faithful : Faithful (forget₂Monoidal R).toFunctor := by
  dsimp [forget₂Monoidal]
  infer_instance
#align fgModule.forget₂_monoidal_faithful FGModuleCat.forget₂Monoidal_faithful

instance forget₂Monoidal_additive : (forget₂Monoidal R).toFunctor.Additive := by
  dsimp [forget₂Monoidal]
  infer_instance
#align fgModule.forget₂_monoidal_additive FGModuleCat.forget₂Monoidal_additive

instance forget₂Monoidal_linear : (forget₂Monoidal R).toFunctor.Linear R := by
  dsimp [forget₂Monoidal]
  infer_instance
#align fgModule.forget₂_monoidal_linear FGModuleCat.forget₂Monoidal_linear

theorem Iso.conj_eq_conj {V W : FGModuleCat R} (i : V ≅ W) (f : End V) :
    Iso.conj i f = LinearEquiv.conj (isoToLinearEquiv i) f :=
  rfl
#align fgModule.iso.conj_eq_conj FGModuleCat.Iso.conj_eq_conj

end CommRing

section Field

variable (K : Type u) [Field K]

instance (V W : FGModuleCat K) : Module.Finite K (V ⟶ W) :=
  (by infer_instance : Module.Finite K (V.obj →ₗ[K] W.obj))

instance closedPredicateModuleFinite :
    MonoidalCategory.ClosedPredicate fun V : ModuleCat.{u} K => Module.Finite K V where
  prop_ihom := @fun X Y hX hY => @Module.Finite.linearMap K X Y _ _ _ _ _ _ _ hX hY
#align fgModule.closed_predicate_module_finite FGModuleCat.closedPredicateModuleFinite

instance : MonoidalClosed (FGModuleCat K) := by
  dsimp [FGModuleCat]
  infer_instance

variable (V W : FGModuleCat K)

@[simp]
theorem ihom_obj : (ihom V).obj W = FGModuleCat.of K (V.obj →ₗ[K] W.obj) :=
  rfl
#align fgModule.ihom_obj FGModuleCat.ihom_obj

/-- The dual module is the dual in the rigid monoidal category `FGModuleCat K`. -/
def FGModuleCatDual : FGModuleCat K :=
  ⟨ModuleCat.of K (Module.Dual K V.obj), Subspace.Module.Dual.finiteDimensional⟩
#align fgModule.fgModule_dual FGModuleCat.FGModuleCatDual

open CategoryTheory.MonoidalCategory

/-- The coevaluation map is defined in `linear_algebra.coevaluation`. -/
def FGModuleCatCoevaluation : 𝟙_ (FGModuleCat K) ⟶ V ⊗ FGModuleCatDual K V := by
  apply coevaluation K V.obj
#align fgModule.fgModule_coevaluation FGModuleCat.FGModuleCatCoevaluation

theorem FGModuleCatCoevaluation_apply_one :
    FGModuleCatCoevaluation K V (1 : K) =
      ∑ i : Basis.ofVectorSpaceIndex K V.obj,
        (Basis.ofVectorSpace K V.obj) i ⊗ₜ[K] (Basis.ofVectorSpace K V.obj).coord i :=
  by apply coevaluation_apply_one K V.obj
#align fgModule.fgModule_coevaluation_apply_one FGModuleCat.FGModuleCatCoevaluation_apply_one

/-- The evaluation morphism is given by the contraction map. -/
def FGModuleCatEvaluation : FGModuleCatDual K V ⊗ V ⟶ 𝟙_ (FGModuleCat K) := by
  apply contractLeft K V.obj
#align fgModule.fgModule_evaluation FGModuleCat.FGModuleCatEvaluation

@[simp]
theorem FGModuleCatEvaluation_apply (f : (FGModuleCatDual K V).obj) (x : V.obj) :
    (FGModuleCatEvaluation K V) (f ⊗ₜ x) = f.toFun x := by apply contractLeft_apply f x
#align fgModule.fgModule_evaluation_apply FGModuleCat.FGModuleCatEvaluation_apply

private theorem coevaluation_evaluation :
    let V' : FGModuleCat K := FGModuleCatDual K V
    (𝟙 V' ⊗ FGModuleCatCoevaluation K V) ≫ (α_ V' V V').inv ≫ (FGModuleCatEvaluation K V ⊗ 𝟙 V') =
      (ρ_ V').hom ≫ (λ_ V').inv :=
  by apply contractLeft_assoc_coevaluation K V.obj

private theorem evaluation_coevaluation :
    (FGModuleCatCoevaluation K V ⊗ 𝟙 V) ≫
        (α_ V (FGModuleCatDual K V) V).hom ≫ (𝟙 V ⊗ FGModuleCatEvaluation K V) =
      (λ_ V).hom ≫ (ρ_ V).inv :=
  by apply contractLeft_assoc_coevaluation' K V.obj

instance exactPairing : ExactPairing V (FGModuleCatDual K V) where
  coevaluation' := FGModuleCatCoevaluation K V
  evaluation' := FGModuleCatEvaluation K V
  coevaluation_evaluation' := coevaluation_evaluation K V
  evaluation_coevaluation' := evaluation_coevaluation K V
#align fgModule.exact_pairing FGModuleCat.exactPairing

instance rightDual : HasRightDual V :=
  ⟨FGModuleCatDual K V⟩
#align fgModule.right_dual FGModuleCat.rightDual

instance rightRigidCategory : RightRigidCategory (FGModuleCat K) where
#align fgModule.right_rigid_category FGModuleCat.rightRigidCategory

end Field

end FGModuleCat
