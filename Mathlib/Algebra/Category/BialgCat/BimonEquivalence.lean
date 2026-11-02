/-
Copyright (c) 2026 Yacine Benmeuraiem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yacine Benmeuraiem
-/
module

public import Mathlib.Algebra.Category.BialgCat.Basic
public import Mathlib.Algebra.Category.CoalgCat.ComonEquivalence
public import Mathlib.CategoryTheory.Monoidal.Bimon_
public import Mathlib.CategoryTheory.Monoidal.Internal.Module

import Aesop.Frontend.Tactic
import Aesop.Main
import Mathlib.Tactic.Lemma

-- set_option profiler true

/-! # Equivalence of categories `BialgCat R ≌ Bimon (ModuleCat R)` -/

@[expose] public section

-- #check CoalgCat.comonEquivalence
-- #check ModuleCat.monModuleEquivalenceAlgebra

universe u v

open CategoryTheory ModuleCat MonoidalCategory MonObj BimonObj MonModuleEquivalenceAlgebra


variable {R : Type u} [CommRing R] (A : Type v) [Semiring A] [Bialgebra R A]

section lemmas

variable (R) in
@[simp]
lemma tensorProductMul (X : Type v) [Semiring X] [Algebra R X] :
    TensorProduct.map (LinearMap.mul' R X) (LinearMap.mul' R X) ∘ₗ
      (TensorProduct.tensorTensorTensorComm R X X X X) =
    LinearMap.mul' R (TensorProduct R X X) := by
  ext
  simp

@[simp]
lemma tensorProductMul_apply (X : Type v) [Semiring X] [Algebra R X] (x) :
    TensorProduct.map (LinearMap.mul' R X) (LinearMap.mul' R X)
      (TensorProduct.tensorTensorTensorComm R X X X X x) =
    LinearMap.mul' R (TensorProduct R X X) x :=
  congr($(tensorProductMul R X) x)

@[simp]
lemma tensorProductMul' (X : ModuleCat R) [MonObj X] :
    TensorProduct.map (LinearMap.mul' R X) (LinearMap.mul' R X) ∘ₗ
      (tensorμ X X X X).hom =
    LinearMap.mul' R (TensorProduct R X X) := by
  simp only [tensorObj_carrier, tensorμ_eq_tensorTensorTensorComm,
    hom_ofHom, tensorProductMul]

@[simp]
lemma tensorProductMul_apply' (X : ModuleCat R) [MonObj X] (x) :
    TensorProduct.map (LinearMap.mul' R X) (LinearMap.mul' R X)
      ((tensorμ X X X X).hom x) =
    LinearMap.mul' R (TensorProduct R X X) x :=
  congr($(tensorProductMul' X) x)

-- @[simp]
lemma mul'_eq_μ_hom (X : ModuleCat R) [MonObj X] : LinearMap.mul' R X = Hom.hom μ[X] := by
  ext
  rfl

end lemmas

namespace CategoryTheory.BialgCat

@[simps! one mul]
noncomputable instance (X : BialgCat R) : MonObj (ModuleCat.of R X) :=
  (ModuleCat.MonModuleEquivalenceAlgebra.inverse.obj ((forget₂ _ _).obj X)).mon

@[simps! counit comul]
noncomputable instance (X : BialgCat R) : ComonObj (ModuleCat.of R X) :=
  ((CoalgCat.toComon R).obj ((forget₂ _ _).obj X)).comon

noncomputable instance (X : BialgCat R) : BimonObj (ModuleCat.of R X) where
  mul_comul := by
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro x y
      simp [ModuleCat.MonoidalCategory.tensorHom_def, tensorObj_carrier,
      ModuleCat.MonoidalCategory.tensorμ_eq_tensorTensorTensorComm]
  one_comul := by
      ext
      simp [tensorObj.one_def, leftUnitor_def, ModuleCat.MonoidalCategory.tensorHom_def,
        tensorUnit_carrier, tensorObj_carrier, Algebra.TensorProduct.one_def]
  mul_counit := by
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro x y
      simp [leftUnitor_def, ModuleCat.MonoidalCategory.tensorHom_def,
        tensorUnit_carrier, tensorObj_carrier]
  one_counit := by aesop

variable (R) in
/-- The natural functor from `R`-bialgebras to bimonoid objects in the category of `R`-modules. -/
@[simps]
noncomputable def toBimon : BialgCat R ⥤ Bimon (ModuleCat R) where
  obj X := ⟨ModuleCat.of R X⟩
  map f := {
    hom := ModuleCat.ofHom f.toBialgHom
    isBimonHom_hom := {
      one_hom := ModuleCat.hom_ext <| LinearMap.ext (AlgHom.ofClass f.1).commutes
      mul_hom := ModuleCat.hom_ext <| TensorProduct.ext <| LinearMap.ext₂ <|
        map_mul (AlgHom.ofClass f.1)
      hom_counit := (ModuleCat.hom_ext f.toBialgHom'.counit_comp)
      hom_comul := (ModuleCat.hom_ext f.toBialgHom'.map_comp_comul.symm)
    }
  }

/-- A bimonoid object in the category of `R`-modules has a natural comultiplication
and counit. -/
@[simp]
noncomputable instance ofBimonObjBialgebra (X : ModuleCat R) [BimonObj X] : Bialgebra R X where
  __ := (CoalgCat.ofComonObj X).instCoalgebra
  -- __ := ModuleCat.MonModuleEquivalenceAlgebra.functor.obj ⟨X⟩
  counit_one := congr($(one_counit X) 1) -- wish there were simps for CoalgCat.ofComonObj
  mul_compr₂_counit := by
    ext x y
    exact congr($(BimonObj.mul_counit X) (x ⊗ₜ y))
  comul_one := congr($(BimonObj.one_comul X) 1)
  mul_compr₂_comul := by
    ext x y
    apply congr($(BimonObj.mul_comul X) (x ⊗ₜ y)).trans
    simp only [tensorObj_carrier, ModuleCat.MonoidalCategory.tensorHom_def, ← mul'_eq_μ_hom,
      ModuleCat.hom_comp, hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
      TensorProduct.map_tmul]
    rw [tensorProductMul_apply']
    rfl

-- /-- A bimonoid object in the category of `R`-modules has a natural `R`-bialgebra
-- structure. -/
-- noncomputable abbrev ofBimonObj (X : ModuleCat R) [BimonObj X] : BialgCat R := .of R X

variable (R) in
/-- The natural functor from bimonoid objects in the category of `R`-modules to `R`-bialgebras. -/
@[simp]
noncomputable def ofBimon : Bimon (ModuleCat R) ⥤ BialgCat R where
  obj X := .of R X.X
  map f := {
    toBialgHom' := {
      f.hom.hom with
      counit_comp := ModuleCat.hom_ext_iff.mp (IsComonHom.hom_counit f.hom)
      map_comp_comul := ModuleCat.hom_ext_iff.mp ((IsComonHom.hom_comul f.hom).symm)
      map_one' := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (IsMonHom.one_hom f.hom)) (1 : R)
      map_mul' := fun x y =>
        LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (IsMonHom.mul_hom f.hom)) (x ⊗ₜ y)
    }
  }

@[simps]
def bimonEquivalence_unit (X : BialgCat R) :
    (𝟭 (BialgCat R)).obj X ≅ (toBimon R ⋙ ofBimon R).obj X where
  hom := {
    toBialgHom' := {
      toFun := id
      map_add' x y := rfl
      map_smul' x y := rfl
      counit_comp := rfl
      map_comp_comul := by
        ext (x : X)
        exact DFunLike.congr_fun (TensorProduct.map_id (M := X) (N := X)) _
        -- erw [TensorProduct.map_id]
        -- rfl
      map_one' := (algebraMap R X).map_one.symm
      map_mul' x y := rfl
    }
  }
  inv := {
    toBialgHom' := {
      toFun := id
      map_add' x y := rfl
      map_smul' x y := rfl
      counit_comp := rfl
      map_comp_comul := by
        ext (x : X)
        exact DFunLike.congr_fun (TensorProduct.map_id (M := X) (N := X)) _
        -- erw [TensorProduct.map_id]
        -- rfl
      map_one' := (algebraMap R X).map_one
      map_mul' x y := rfl
    }
  }
  hom_inv_id := rfl
  inv_hom_id := rfl

@[simps]
noncomputable def bimonEquivalence_counit (X : Bimon (ModuleCat R)) :
    (ofBimon R ⋙ toBimon R).obj X ≅ (𝟭 (Bimon (ModuleCat R))).obj X where
  hom := {
    hom := 𝟙 _
    isBimonHom_hom := {
      one_hom := rfl
      mul_hom := by
        apply ModuleCat.MonoidalCategory.tensor_ext
        intro x y
        rfl
      hom_counit := rfl
      hom_comul := by
        ext (x : X.X)
        -- simp only [Functor.id_obj, tensorObj_carrier, ofBimon, ofBimonObj_carrier, of_coe,
          -- Lean.Elab.WF.paramLet, toBimon, Functor.comp_obj, coe_of, ModuleCat.hom_comp,
          -- ModuleCat.MonoidalCategory.tensorHom_def, hom_ofHom]
        symm
        exact DFunLike.congr_fun (TensorProduct.map_id (M := X.X) (N := X.X)) _
        -- erw [TensorProduct.map_id (M:=X.X) (N:=X.X)]
        -- rfl
    }
  }
  inv := {
    hom := 𝟙 _
    isBimonHom_hom := {
      one_hom := rfl
      mul_hom := by
        apply ModuleCat.MonoidalCategory.tensor_ext
        intro x y
        rfl
      hom_counit := rfl
      hom_comul := by
        ext (x : X.X)
        -- simp only [Functor.id_obj, tensorObj_carrier, ofBimon, ofBimonObj_carrier, of_coe,
          -- Lean.Elab.WF.paramLet, toBimon, Functor.comp_obj, coe_of, ModuleCat.hom_comp,
          -- ModuleCat.MonoidalCategory.tensorHom_def, hom_ofHom]
        symm
        exact DFunLike.congr_fun (TensorProduct.map_id (M := X.X) (N := X.X)) _
        -- simp
        -- erw [TensorProduct.map_id (M:=X.X) (N:=X.X)]
        -- rfl
    }
  }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The natural category equivalence between `R`-bialgebras and bimonoid objects in the
category of `R`-modules. -/
@[simps]
noncomputable def bimonEquivalence : BialgCat R ≌ Bimon (ModuleCat R) where
  functor := toBimon R
  inverse := ofBimon R
  unitIso := NatIso.ofComponents bimonEquivalence_unit
  counitIso := NatIso.ofComponents bimonEquivalence_counit

end CategoryTheory.BialgCat
