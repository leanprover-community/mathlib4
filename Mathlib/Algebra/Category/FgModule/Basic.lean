/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer

! This file was ported from Lean 3 source module algebra.category.fgModule.basic
! leanprover-community/mathlib commit 74403a3b2551b0970855e14ef5e8fd0d6af1bfc2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Monoidal.Rigid.Basic
import Mathbin.CategoryTheory.Monoidal.Subcategory
import Mathbin.LinearAlgebra.Coevaluation
import Mathbin.LinearAlgebra.FreeModule.Finite.Matrix
import Mathbin.Algebra.Category.Module.Monoidal.Closed

/-!
# The category of finitely generated modules over a ring

This introduces `fgModule R`, the category of finitely generated modules over a ring `R`.
It is implemented as a full subcategory on a subtype of `Module R`.

When `K` is a field, `fgModule K` is the category of finite dimensional vector spaces over `K`.

We first create the instance as a preadditive category.
When `R` is commutative we then give the structure as an `R`-linear monoidal category.
When `R` is a field we give it the structure of a closed monoidal category
and then as a right-rigid monoidal category.

## Future work

* Show that `fgModule R` is abelian when `R` is (left)-noetherian.

-/


noncomputable section

open CategoryTheory ModuleCat.monoidalCategory

open scoped Classical BigOperators

universe u

section Ring

variable (R : Type u) [Ring R]

/-- Define `fgModule` as the subtype of `Module.{u} R` of finitely generated modules. -/
def FgModule :=
  FullSubcategory fun V : ModuleCat.{u} R => Module.Finite R V
deriving LargeCategory, ConcreteCategory, Preadditive
#align fgModule FgModule

end Ring

namespace FgModule

section Ring

variable (R : Type u) [Ring R]

instance finite (V : FgModule R) : Module.Finite R V.obj :=
  V.property
#align fgModule.finite FgModule.finite

instance : Inhabited (FgModule R) :=
  ⟨⟨ModuleCat.of R R, Module.Finite.self R⟩⟩

/-- Lift an unbundled finitely generated module to `fgModule R`. -/
def of (V : Type u) [AddCommGroup V] [Module R V] [Module.Finite R V] : FgModule R :=
  ⟨ModuleCat.of R V, by change Module.Finite R V; infer_instance⟩
#align fgModule.of FgModule.of

instance (V : FgModule R) : Module.Finite R V.obj :=
  V.property

instance : HasForget₂ (FgModule.{u} R) (ModuleCat.{u} R) := by dsimp [FgModule]; infer_instance

instance : Full (forget₂ (FgModule R) (ModuleCat.{u} R)) where preimage X Y f := f

variable {R}

/-- Converts and isomorphism in the category `fgModule R` to a `linear_equiv` between the underlying
modules. -/
def isoToLinearEquiv {V W : FgModule R} (i : V ≅ W) : V.obj ≃ₗ[R] W.obj :=
  ((forget₂ (FgModule.{u} R) (ModuleCat.{u} R)).mapIso i).toLinearEquiv
#align fgModule.iso_to_linear_equiv FgModule.isoToLinearEquiv

/-- Converts a `linear_equiv` to an isomorphism in the category `fgModule R`. -/
@[simps]
def LinearEquiv.toFgModuleIso {V W : Type u} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [AddCommGroup W] [Module R W] [Module.Finite R W] (e : V ≃ₗ[R] W) :
    FgModule.of R V ≅ FgModule.of R W
    where
  Hom := e.toLinearMap
  inv := e.symm.toLinearMap
  hom_inv_id' := by ext; exact e.left_inv x
  inv_hom_id' := by ext; exact e.right_inv x
#align linear_equiv.to_fgModule_iso LinearEquiv.toFgModuleIso

end Ring

section CommRing

variable (R : Type u) [CommRing R]

instance : Linear R (FgModule R) := by dsimp_result => dsimp [FgModule]; infer_instance

instance monoidalPredicate_module_finite :
    MonoidalCategory.MonoidalPredicate fun V : ModuleCat.{u} R => Module.Finite R V
    where
  prop_id' := Module.Finite.self R
  prop_tensor' X Y hX hY := Module.Finite.tensorProduct R X Y
#align fgModule.monoidal_predicate_module_finite FgModule.monoidalPredicate_module_finite

instance : MonoidalCategory (FgModule R) := by dsimp_result => dsimp [FgModule]; infer_instance

instance : SymmetricCategory (FgModule R) := by dsimp_result => dsimp [FgModule]; infer_instance

instance : MonoidalPreadditive (FgModule R) := by dsimp_result => dsimp [FgModule]; infer_instance

instance : MonoidalLinear R (FgModule R) := by dsimp_result => dsimp [FgModule]; infer_instance

/-- The forgetful functor `fgModule R ⥤ Module R` as a monoidal functor. -/
def forget₂Monoidal : MonoidalFunctor (FgModule R) (ModuleCat.{u} R) :=
  MonoidalCategory.fullMonoidalSubcategoryInclusion _
#align fgModule.forget₂_monoidal FgModule.forget₂Monoidal

instance forget₂Monoidal_faithful : Faithful (forget₂Monoidal R).toFunctor := by
  dsimp [forget₂_monoidal]; infer_instance
#align fgModule.forget₂_monoidal_faithful FgModule.forget₂Monoidal_faithful

instance forget₂Monoidal_additive : (forget₂Monoidal R).toFunctor.Additive := by
  dsimp [forget₂_monoidal]; infer_instance
#align fgModule.forget₂_monoidal_additive FgModule.forget₂Monoidal_additive

instance forget₂Monoidal_linear : (forget₂Monoidal R).toFunctor.Linear R := by
  dsimp [forget₂_monoidal]; infer_instance
#align fgModule.forget₂_monoidal_linear FgModule.forget₂Monoidal_linear

theorem Iso.conj_eq_conj {V W : FgModule R} (i : V ≅ W) (f : End V) :
    Iso.conj i f = LinearEquiv.conj (isoToLinearEquiv i) f :=
  rfl
#align fgModule.iso.conj_eq_conj FgModule.Iso.conj_eq_conj

end CommRing

section Field

variable (K : Type u) [Field K]

instance (V W : FgModule K) : Module.Finite K (V ⟶ W) :=
  (by infer_instance : Module.Finite K (V.obj →ₗ[K] W.obj))

instance closedPredicateModuleFinite :
    MonoidalCategory.ClosedPredicate fun V : ModuleCat.{u} K => Module.Finite K V
    where prop_ihom' X Y hX hY := @Module.Finite.linearMap K X Y _ _ _ _ _ _ _ hX hY
#align fgModule.closed_predicate_module_finite FgModule.closedPredicateModuleFinite

instance : MonoidalClosed (FgModule K) := by dsimp_result => dsimp [FgModule]; infer_instance

variable (V W : FgModule K)

@[simp]
theorem ihom_obj : (ihom V).obj W = FgModule.of K (V.obj →ₗ[K] W.obj) :=
  rfl
#align fgModule.ihom_obj FgModule.ihom_obj

/-- The dual module is the dual in the rigid monoidal category `fgModule K`. -/
def fgModuleDual : FgModule K :=
  ⟨ModuleCat.of K (Module.Dual K V.obj), Subspace.Module.Dual.finiteDimensional⟩
#align fgModule.fgModule_dual FgModule.fgModuleDual

open CategoryTheory.MonoidalCategory

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The coevaluation map is defined in `linear_algebra.coevaluation`. -/
def fgModuleCoevaluation : 𝟙_ (FgModule K) ⟶ V ⊗ fgModuleDual K V := by apply coevaluation K V.obj
#align fgModule.fgModule_coevaluation FgModule.fgModuleCoevaluation

theorem fgModuleCoevaluation_apply_one :
    fgModuleCoevaluation K V (1 : K) =
      ∑ i : Basis.ofVectorSpaceIndex K V.obj,
        (Basis.ofVectorSpace K V.obj) i ⊗ₜ[K] (Basis.ofVectorSpace K V.obj).Coord i :=
  by apply coevaluation_apply_one K V.obj
#align fgModule.fgModule_coevaluation_apply_one FgModule.fgModuleCoevaluation_apply_one

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The evaluation morphism is given by the contraction map. -/
def fgModuleEvaluation : fgModuleDual K V ⊗ V ⟶ 𝟙_ (FgModule K) := by apply contractLeft K V.obj
#align fgModule.fgModule_evaluation FgModule.fgModuleEvaluation

@[simp]
theorem fgModuleEvaluation_apply (f : (fgModuleDual K V).obj) (x : V.obj) :
    (fgModuleEvaluation K V) (f ⊗ₜ x) = f.toFun x := by apply contractLeft_apply f x
#align fgModule.fgModule_evaluation_apply FgModule.fgModuleEvaluation_apply

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
private theorem coevaluation_evaluation :
    let V' : FgModule K := fgModuleDual K V
    (𝟙 V' ⊗ fgModuleCoevaluation K V) ≫ (α_ V' V V').inv ≫ (fgModuleEvaluation K V ⊗ 𝟙 V') =
      (ρ_ V').Hom ≫ (λ_ V').inv :=
  by apply contractLeft_assoc_coevaluation K V.obj

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
private theorem evaluation_coevaluation :
    (fgModuleCoevaluation K V ⊗ 𝟙 V) ≫
        (α_ V (fgModuleDual K V) V).Hom ≫ (𝟙 V ⊗ fgModuleEvaluation K V) =
      (λ_ V).Hom ≫ (ρ_ V).inv :=
  by apply contractLeft_assoc_coevaluation' K V.obj

instance exactPairing : ExactPairing V (fgModuleDual K V)
    where
  coevaluation := fgModuleCoevaluation K V
  evaluation := fgModuleEvaluation K V
  coevaluation_evaluation' := coevaluation_evaluation K V
  evaluation_coevaluation' := evaluation_coevaluation K V
#align fgModule.exact_pairing FgModule.exactPairing

instance rightDual : HasRightDual V :=
  ⟨fgModuleDual K V⟩
#align fgModule.right_dual FgModule.rightDual

instance rightRigidCategory : RightRigidCategory (FgModule K) where
#align fgModule.right_rigid_category FgModule.rightRigidCategory

end Field

end FgModule

