/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.CategoryTheory.Monoidal.Braided.Opposite
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.CategoryTheory.Monoidal.Comon_
import Mathlib.Algebra.Category.CoalgebraCat.Basic

/-!
# The category equivalence between `R`-coalgebras and comonoid objects in `R-Mod`

Given a commutative ring `R`, this file defines the equivalence of categories between
`R`-coalgebras and comonoid objects in the category of `R`-modules.

We then use this to set up boilerplate for the `Coalgebra` instance on a tensor product of
coalgebras defined in `Mathlib.RingTheory.Coalgebra.TensorProduct`.

## Implementation notes

We make the definition `CoalgebraCat.instMonoidalCategoryAux` in this file, which is the
monoidal structure on `CoalgebraCat` induced by the equivalence with `Comon(R-Mod)`. We
use this to show the comultiplication and counit on a tensor product of coalgebras satisfy
the coalgebra axioms, but our actual `MonoidalCategory` instance on `CoalgebraCat` is
constructed in `Mathlib.Algebra.Category.CoalgebraCat.Monoidal` in #11976 to have better
definitional equalities.

-/
universe v u

namespace CoalgebraCat

open CategoryTheory MonoidalCategory

variable {R : Type u} [CommRing R]

/-- An `R`-coalgebra is a comonoid object in the category of `R`-modules. -/
@[simps] def toComonObj (X : CoalgebraCat R) : Comon_ (ModuleCat R) where
  X := ModuleCat.of R X
  counit := ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ Coalgebra.counit)
  comul := ModuleCat.ofHom Coalgebra.comul
  counit_comul := by
    ext x
    show LinearMap.rTensor _ (_ ∘ₗ _) _ = _
    rw [LinearMap.rTensor_comp]
    exact congr(LinearMap.rTensor _ ULift.moduleEquiv.symm.toLinearMap
      $(Coalgebra.rTensor_counit_comul (A := X.toModuleCat) x))
  comul_counit := by
    ext x
    show LinearMap.lTensor _ (_ ∘ₗ _) _ = _
    rw [LinearMap.lTensor_comp]
    exact congr(LinearMap.lTensor _ ULift.moduleEquiv.symm.toLinearMap
      $(Coalgebra.lTensor_counit_comul (A := X.toModuleCat) x))
  comul_assoc := by simp_rw [ModuleCat.of_coe]; exact Coalgebra.coassoc.symm

variable (R) in
/-- The natural functor from `R`-coalgebras to comonoid objects in the category of `R`-modules. -/
@[simps]
def toComon : CoalgebraCat R ⥤ Comon_ (ModuleCat R) where
  obj X := toComonObj X
  map {X Y} f :=
    { hom := ModuleCat.ofHom f.1
      hom_counit := by
        ext x
        exact congr((ULift.moduleEquiv (R := R)).symm
          $(CoalgHomClass.counit_comp_apply (A := X) (B := Y) f.1 x))
      hom_comul := f.1.map_comp_comul.symm }

/-- A comonoid object in the category of `R`-modules has a natural comultiplication
and counit. -/
@[simps]
instance ofComonObjCoalgebraStruct (X : Comon_ (ModuleCat R)) :
    CoalgebraStruct R X.X where
  comul := X.comul
  counit := ULift.moduleEquiv.toLinearMap ∘ₗ X.counit

/-- A comonoid object in the category of `R`-modules has a natural `R`-coalgebra
structure. -/
def ofComonObj (X : Comon_ (ModuleCat R)) : CoalgebraCat R where
  carrier := X.X
  instCoalgebra :=
    { ofComonObjCoalgebraStruct X with
      coassoc := X.comul_assoc.symm
      rTensor_counit_comp_comul := by
        ext x
        simp only [ofComonObjCoalgebraStruct_counit, LinearMap.rTensor_comp]
        exact congr((LinearMap.rTensor X.X ULift.moduleEquiv.toLinearMap)
          $(LinearMap.congr_fun X.counit_comul x))
      lTensor_counit_comp_comul := by
        ext x
        simp only [ofComonObjCoalgebraStruct_counit, LinearMap.lTensor_comp]
        exact congr((LinearMap.lTensor X.X ULift.moduleEquiv.toLinearMap)
          $(LinearMap.congr_fun X.comul_counit x)) }

variable (R)

/-- The natural functor from comonoid objects in the category of `R`-modules to `R`-coalgebras. -/
def ofComon : Comon_ (ModuleCat R) ⥤ CoalgebraCat R where
  obj X := ofComonObj X
  map f :=
    { toCoalgHom :=
      { f.hom with
        counit_comp := by
          ext x
          exact congr(ULift.moduleEquiv (R := R) $(LinearMap.congr_fun f.hom_counit x))
        map_comp_comul := f.hom_comul.symm }}

/-- The natural category equivalence between `R`-coalgebras and comonoid objects in the
category of `R`-modules. -/
@[simps]
noncomputable def comonEquivalence : CoalgebraCat R ≌ Comon_ (ModuleCat R) where
  functor := toComon R
  inverse := ofComon R
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by rfl
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by rfl

variable {R}

/-- The monoidal category structure on the category of `R`-coalgebras induced by the
equivalence with `Comon(R-Mod)`. This is just an auxiliary definition; the `MonoidalCategory`
instance we make in `Mathlib.Algebra.Category.CoalgebraCat.Monoidal` in #11976 will have better
definitional equalities. -/
noncomputable def instMonoidalCategoryAux : MonoidalCategory (CoalgebraCat R) :=
  Monoidal.transport (comonEquivalence R).symm

namespace MonoidalCategoryAux

variable {M N P Q : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R P] [Module R Q] [Coalgebra R M] [Coalgebra R N]
    [Coalgebra R P] [Coalgebra R Q]

attribute [local instance] instMonoidalCategoryAux

open MonoidalCategory ModuleCat.MonoidalCategory

theorem tensorObj_comul (K L : CoalgebraCat R) :
    Coalgebra.comul (R := R) (A := (K ⊗ L : CoalgebraCat R))
      = (TensorProduct.tensorTensorTensorComm R K K L L).toLinearMap
      ∘ₗ TensorProduct.map Coalgebra.comul Coalgebra.comul := by
  rw [ofComonObjCoalgebraStruct_comul]
  dsimp [ModuleCat.ofHom, -Mon_.monMonoidalStruct_tensorObj_X,
    instMonoidalCategoryStruct_tensorHom, ModuleCat.comp_def]
  simp only [BraidedCategory.unop_tensor_μ, tensor_μ_eq_tensorTensorTensorComm]

theorem tensorHom_toLinearMap (f : M →ₗc[R] N) (g : P →ₗc[R] Q) :
    (CoalgebraCat.ofHom f ⊗ CoalgebraCat.ofHom g).1.toLinearMap
      = TensorProduct.map f.toLinearMap g.toLinearMap := rfl

theorem associator_hom_toLinearMap :
    (α_ (CoalgebraCat.of R M) (CoalgebraCat.of R N) (CoalgebraCat.of R P)).hom.1.toLinearMap
      = (TensorProduct.assoc R M N P).toLinearMap :=
  TensorProduct.ext <| TensorProduct.ext <| by ext; rfl

theorem leftUnitor_hom_toLinearMap :
    (λ_ (CoalgebraCat.of R M)).hom.1.toLinearMap
      = (LinearEquiv.rTensor M ULift.moduleEquiv ≪≫ₗ TensorProduct.lid R M).toLinearMap :=
  TensorProduct.ext <| by ext; rfl

theorem rightUnitor_hom_toLinearMap :
    (ρ_ (CoalgebraCat.of R M)).hom.1.toLinearMap
      = (LinearEquiv.lTensor M ULift.moduleEquiv ≪≫ₗ TensorProduct.rid R M).toLinearMap :=
  TensorProduct.ext <| by ext; rfl

open TensorProduct

theorem comul_tensorObj :
    Coalgebra.comul (R := R) (A := (CoalgebraCat.of R M ⊗ CoalgebraCat.of R N : CoalgebraCat R))
      = Coalgebra.comul (A := M ⊗[R] N) := by
  rw [ofComonObjCoalgebraStruct_comul]
  dsimp [- Mon_.monMonoidalStruct_tensorObj_X, instMonoidalCategoryStruct_tensorHom,
    ModuleCat.comp_def, ModuleCat.ofHom, ModuleCat.of]
  simp only [BraidedCategory.unop_tensor_μ, tensor_μ_eq_tensorTensorTensorComm]

theorem comul_tensorObj_tensorObj_right :
    Coalgebra.comul (R := R) (A := (CoalgebraCat.of R M ⊗
      (CoalgebraCat.of R N ⊗ CoalgebraCat.of R P) : CoalgebraCat R))
      = Coalgebra.comul (A := M ⊗[R] N ⊗[R] P) := by
  rw [ofComonObjCoalgebraStruct_comul]
  dsimp [- Mon_.monMonoidalStruct_tensorObj_X, instMonoidalCategoryStruct_tensorHom,
    ModuleCat.comp_def, ModuleCat.ofHom, ModuleCat.of]
  rw [ofComonObjCoalgebraStruct_comul]
  dsimp [- Mon_.monMonoidalStruct_tensorObj_X, instMonoidalCategoryStruct_tensorHom,
    ModuleCat.comp_def, ModuleCat.ofHom, ModuleCat.of]
  simp only [instMonoidalCategoryStruct_tensorObj, ModuleCat.MonoidalCategory.tensorObj,
    ModuleCat.coe_of, BraidedCategory.unop_tensor_μ, tensor_μ_eq_tensorTensorTensorComm]
  rfl

theorem comul_tensorObj_tensorObj_left :
    Coalgebra.comul (R := R)
      (A := ((CoalgebraCat.of R M ⊗ CoalgebraCat.of R N) ⊗ CoalgebraCat.of R P : CoalgebraCat R))
      = Coalgebra.comul (A := (M ⊗[R] N) ⊗[R] P) := by
  rw [ofComonObjCoalgebraStruct_comul]
  dsimp [- Mon_.monMonoidalStruct_tensorObj_X, instMonoidalCategoryStruct_tensorHom,
    ModuleCat.comp_def, ModuleCat.ofHom, ModuleCat.of]
  rw [ofComonObjCoalgebraStruct_comul]
  dsimp [- Mon_.monMonoidalStruct_tensorObj_X, instMonoidalCategoryStruct_tensorHom,
    ModuleCat.comp_def, ModuleCat.ofHom, ModuleCat.of]
  simp only [instMonoidalCategoryStruct_tensorObj, ModuleCat.MonoidalCategory.tensorObj,
    ModuleCat.coe_of, BraidedCategory.unop_tensor_μ, tensor_μ_eq_tensorTensorTensorComm]
  rfl

theorem counit_tensorObj :
    Coalgebra.counit (R := R) (A := (CoalgebraCat.of R M ⊗ CoalgebraCat.of R N : CoalgebraCat R))
      = Coalgebra.counit (A := M ⊗[R] N) :=
  TensorProduct.ext rfl

theorem counit_tensorObj_tensorObj_right :
    Coalgebra.counit (R := R)
      (A := (CoalgebraCat.of R M ⊗ (CoalgebraCat.of R N ⊗ CoalgebraCat.of R P) : CoalgebraCat R))
      = Coalgebra.counit (A := M ⊗[R] (N ⊗[R] P)) :=
  TensorProduct.ext <| LinearMap.ext fun _ => TensorProduct.ext rfl

theorem counit_tensorObj_tensorObj_left :
    Coalgebra.counit (R := R)
      (A := ((CoalgebraCat.of R M ⊗ CoalgebraCat.of R N) ⊗ CoalgebraCat.of R P : CoalgebraCat R))
      = Coalgebra.counit (A := (M ⊗[R] N) ⊗[R] P) :=
  TensorProduct.ext <| TensorProduct.ext <| LinearMap.ext fun _ => by dsimp; rfl

end CoalgebraCat.MonoidalCategoryAux
