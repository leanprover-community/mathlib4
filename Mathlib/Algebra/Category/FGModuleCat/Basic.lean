/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.LinearAlgebra.Coevaluation
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.TensorProduct.Finite

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


noncomputable section

open CategoryTheory

universe u

section Ring

variable (R : Type u) [Ring R]

/-- Define `FGModuleCat` as the subtype of `ModuleCat.{u} R` of finitely generated modules. -/
def FGModuleCat :=
  FullSubcategory fun V : ModuleCat.{u} R => Module.Finite R V
-- The `LargeCategory, HasForget, Preadditive` instances should be constructed by a deriving
-- handler.
-- https://github.com/leanprover-community/mathlib4/issues/380

variable {R}

/-- A synonym for `M.obj.carrier`, which we can mark with `@[coe]`. -/
def FGModuleCat.carrier (M : FGModuleCat R) : Type u := M.obj.carrier

instance : CoeSort (FGModuleCat R) (Type u) :=
  ⟨FGModuleCat.carrier⟩

attribute [coe] FGModuleCat.carrier

@[simp] lemma FGModuleCat.obj_carrier (M : FGModuleCat R) : M.obj.carrier = M.carrier := rfl

instance (M : FGModuleCat R) : AddCommGroup M := by
  change AddCommGroup M.obj
  infer_instance

instance (M : FGModuleCat R) : Module R M := by
  change Module R M.obj
  infer_instance

instance : LargeCategory (FGModuleCat R) := by
  dsimp [FGModuleCat]
  infer_instance

instance : ConcreteCategory (FGModuleCat R) (· →ₗ[R] ·) := by
  dsimp [FGModuleCat]
  infer_instance

instance : Preadditive (FGModuleCat R) := by
  dsimp [FGModuleCat]
  infer_instance

end Ring

namespace FGModuleCat

section Ring

variable (R : Type u) [Ring R]

@[simp] lemma hom_comp (A B C : FGModuleCat R) (f : A ⟶ B) (g : B ⟶ C) :
  (f ≫ g).hom = g.hom.comp f.hom := rfl

@[simp] lemma hom_id (A : FGModuleCat R) : (𝟙 A : A ⟶ A).hom = LinearMap.id := rfl

instance finite (V : FGModuleCat R) : Module.Finite R V :=
  V.property

instance : Inhabited (FGModuleCat R) :=
  ⟨⟨ModuleCat.of R R, Module.Finite.self R⟩⟩

/-- Lift an unbundled finitely generated module to `FGModuleCat R`. -/
abbrev of (V : Type u) [AddCommGroup V] [Module R V] [Module.Finite R V] : FGModuleCat R :=
  ⟨ModuleCat.of R V, by change Module.Finite R V; infer_instance⟩

@[simp]
lemma of_carrier (V : Type u) [AddCommGroup V] [Module R V] [Module.Finite R V] :
  of R V = V := rfl

variable {R} in
/-- Lift a linear map between finitely generated modules to `FGModuleCat R`. -/
abbrev ofHom {V W : Type u} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [AddCommGroup W] [Module R W] [Module.Finite R W]
    (f : V →ₗ[R] W) : of R V ⟶ of R W :=
  ModuleCat.ofHom f

variable {R} in
@[ext] lemma hom_ext {V W : FGModuleCat R} {f g : V ⟶ W} (h : f.hom = g.hom) : f = g :=
  ModuleCat.hom_ext h

instance (V : FGModuleCat R) : Module.Finite R V :=
  V.property

instance : HasForget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R) := by
  dsimp [FGModuleCat]
  infer_instance

instance : (forget₂ (FGModuleCat R) (ModuleCat.{u} R)).Full where
  map_surjective f := ⟨f, rfl⟩

variable {R}

/-- Converts and isomorphism in the category `FGModuleCat R` to
a `LinearEquiv` between the underlying modules. -/
def isoToLinearEquiv {V W : FGModuleCat R} (i : V ≅ W) : V ≃ₗ[R] W :=
  ((forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).mapIso i).toLinearEquiv

/-- Converts a `LinearEquiv` to an isomorphism in the category `FGModuleCat R`. -/
@[simps]
def _root_.LinearEquiv.toFGModuleCatIso
    {V W : Type u} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [AddCommGroup W] [Module R W] [Module.Finite R W] (e : V ≃ₗ[R] W) :
    FGModuleCat.of R V ≅ FGModuleCat.of R W where
  hom := ModuleCat.ofHom e.toLinearMap
  inv := ModuleCat.ofHom e.symm.toLinearMap
  hom_inv_id := by ext x; exact e.left_inv x
  inv_hom_id := by ext x; exact e.right_inv x

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

instance instMonoidalCategory : MonoidalCategory (FGModuleCat R) := by
  dsimp [FGModuleCat]
  infer_instance

open MonoidalCategory

@[simp] lemma tensorUnit_obj : (𝟙_ (FGModuleCat R)).obj = 𝟙_ (ModuleCat R) := rfl
@[simp] lemma tensorObj_obj (M N : FGModuleCat.{u} R) : (M ⊗ N).obj = (M.obj ⊗ N.obj) := rfl

instance : SymmetricCategory (FGModuleCat R) := by
  dsimp [FGModuleCat]
  infer_instance

instance : MonoidalPreadditive (FGModuleCat R) := by
  dsimp [FGModuleCat]
  infer_instance

instance : MonoidalLinear R (FGModuleCat R) := by
  dsimp [FGModuleCat]
  infer_instance

/-- The forgetful functor `FGModuleCat R ⥤ Module R` is a monoidal functor. -/
instance : (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).Monoidal :=
  fullSubcategoryInclusionMonoidal _

instance : (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).Additive where
instance : (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).Linear R where

theorem Iso.conj_eq_conj {V W : FGModuleCat R} (i : V ≅ W) (f : End V) :
    Iso.conj i f = FGModuleCat.ofHom (LinearEquiv.conj (isoToLinearEquiv i) f.hom) :=
  rfl

theorem Iso.conj_hom_eq_conj {V W : FGModuleCat R} (i : V ≅ W) (f : End V) :
    (Iso.conj i f).hom = (LinearEquiv.conj (isoToLinearEquiv i) f.hom) :=
  rfl

end CommRing

section Field

variable (K : Type u) [Field K]

instance (V W : FGModuleCat K) : Module.Finite K (V ⟶ W) :=
  (inferInstanceAs <| Module.Finite K (V →ₗ[K] W)).equiv ModuleCat.homLinearEquiv.symm

instance closedPredicateModuleFinite :
    MonoidalCategory.ClosedPredicate fun V : ModuleCat.{u} K ↦ Module.Finite K V where
  prop_ihom {X Y} _ _ :=
    (inferInstanceAs <| Module.Finite K (X →ₗ[K] Y)).equiv ModuleCat.homLinearEquiv.symm

instance : MonoidalClosed (FGModuleCat K) := by
  dsimp [FGModuleCat]
  infer_instance

variable (V W : FGModuleCat K)

@[simp]
theorem ihom_obj : (ihom V).obj W = FGModuleCat.of K (V ⟶ W) :=
  rfl

/-- The dual module is the dual in the rigid monoidal category `FGModuleCat K`. -/
def FGModuleCatDual : FGModuleCat K :=
  ⟨ModuleCat.of K (Module.Dual K V), Subspace.instModuleDualFiniteDimensional⟩

@[simp] lemma FGModuleCatDual_obj : (FGModuleCatDual K V).obj = ModuleCat.of K (Module.Dual K V) :=
  rfl
@[simp] lemma FGModuleCatDual_coe : (FGModuleCatDual K V : Type u) = Module.Dual K V := rfl

open CategoryTheory.MonoidalCategory

/-- The coevaluation map is defined in `LinearAlgebra.coevaluation`. -/
def FGModuleCatCoevaluation : 𝟙_ (FGModuleCat K) ⟶ V ⊗ FGModuleCatDual K V :=
  ModuleCat.ofHom <| coevaluation K V

theorem FGModuleCatCoevaluation_apply_one :
    (FGModuleCatCoevaluation K V).hom (1 : K) =
      ∑ i : Basis.ofVectorSpaceIndex K V,
        (Basis.ofVectorSpace K V) i ⊗ₜ[K] (Basis.ofVectorSpace K V).coord i :=
  coevaluation_apply_one K V

/-- The evaluation morphism is given by the contraction map. -/
def FGModuleCatEvaluation : FGModuleCatDual K V ⊗ V ⟶ 𝟙_ (FGModuleCat K) :=
  ModuleCat.ofHom <| contractLeft K V

theorem FGModuleCatEvaluation_apply (f : FGModuleCatDual K V) (x : V) :
    (FGModuleCatEvaluation K V).hom (f ⊗ₜ x) = f.toFun x :=
  contractLeft_apply f x

/-- `@[simp]`-normal form of `FGModuleCatEvaluation_apply`, where the carriers have been unfolded.
-/
@[simp]
theorem FGModuleCatEvaluation_apply' (f : FGModuleCatDual K V) (x : V) :
    DFunLike.coe
      (F := ((ModuleCat.of K (Module.Dual K V) ⊗ V.obj).carrier →ₗ[K] (𝟙_ (ModuleCat K))))
      (FGModuleCatEvaluation K V).hom (f ⊗ₜ x) = f.toFun x :=
  contractLeft_apply f x

private theorem coevaluation_evaluation :
    letI V' : FGModuleCat K := FGModuleCatDual K V
    V' ◁ FGModuleCatCoevaluation K V ≫ (α_ V' V V').inv ≫ FGModuleCatEvaluation K V ▷ V' =
      (ρ_ V').hom ≫ (λ_ V').inv := by
  ext : 1
  apply contractLeft_assoc_coevaluation K V

private theorem evaluation_coevaluation :
    FGModuleCatCoevaluation K V ▷ V ≫
        (α_ V (FGModuleCatDual K V) V).hom ≫ V ◁ FGModuleCatEvaluation K V =
      (λ_ V).hom ≫ (ρ_ V).inv := by
  ext : 1
  apply contractLeft_assoc_coevaluation' K V

instance exactPairing : ExactPairing V (FGModuleCatDual K V) where
  coevaluation' := FGModuleCatCoevaluation K V
  evaluation' := FGModuleCatEvaluation K V
  coevaluation_evaluation' := coevaluation_evaluation K V
  evaluation_coevaluation' := evaluation_coevaluation K V

instance rightDual : HasRightDual V :=
  ⟨FGModuleCatDual K V⟩

instance rightRigidCategory : RightRigidCategory (FGModuleCat K) where

end Field

end FGModuleCat

/-!
`@[simp]` lemmas for `LinearMap.comp` and categorical identities.
-/

@[simp] theorem LinearMap.comp_id_fgModuleCat
    {R} [Ring R] {G : FGModuleCat.{u} R} {H : Type u} [AddCommGroup H] [Module R H]
    (f : G →ₗ[R] H) : f.comp (ModuleCat.Hom.hom (𝟙 G)) = f :=
  ModuleCat.hom_ext_iff.mp <| Category.id_comp (ModuleCat.ofHom f)

@[simp] theorem LinearMap.id_fgModuleCat_comp
    {R} [Ring R] {G : Type u} [AddCommGroup G] [Module R G] {H : FGModuleCat.{u} R}
    (f : G →ₗ[R] H) : LinearMap.comp (ModuleCat.Hom.hom (𝟙 H)) f = f :=
  ModuleCat.hom_ext_iff.mp <| Category.comp_id (ModuleCat.ofHom f)
