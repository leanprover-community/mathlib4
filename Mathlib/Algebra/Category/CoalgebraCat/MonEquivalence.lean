/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.CategoryTheory.Monoidal.Braided.Opposite
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.CategoryTheory.Monoidal.Comon_
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.Algebra.Category.CoalgebraCat.Basic

/-!
# The category equivalence between `R`-coalgebras and monoid objects in `R-Modᵒᵖ`

Given a commutative ring `R`, this file defines the equivalence of categories between
`R`-coalgebras and monoid objects in the opposite category of `R`-modules.

We then use this to set up boilerplate for the `Coalgebra` instance on a tensor product of
coalgebras defined in `Mathlib.RingTheory.Coalgebra.TensorProduct`.

## Implementation notes

We make the definiton `CoalgebraCat.instMonoidalCategoryAux` in this file, which is the
monoidal structure on `CoalgebraCat` induced by the equivalence with `Mon(R-Modᵒᵖ)`. We
use this to show the comultiplication and counit on a tensor product of coalgebras satisfy
the coalgebra axioms, but our actual `MonoidalCategory` instance on `CoalgebraCat` is
constructed in `Mathlib.Algebra.Category.CoalgebraCat.Monoidal` to have better
definitional equalities.

-/
universe v u

namespace CoalgebraCat
open CategoryTheory MonoidalCategory
variable {R : Type u} [CommRing R]

/-- An `R`-coalgebra is a monoid object in the opposite category of `R`-modules. -/
@[simps] def toMonObj (X : CoalgebraCat R) : Mon_ (ModuleCat R)ᵒᵖ where
  X := Opposite.op (ModuleCat.of R X)
  one := (ModuleCat.ofHom Coalgebra.counit).op
  mul := (ModuleCat.ofHom Coalgebra.comul).op
  one_mul := by
    simp only [MonoidalCategory.whiskerRight, ← op_comp, ModuleCat.of_coe]
    congr 1
    exact Coalgebra.rTensor_counit_comp_comul
  mul_one := by
    simp only [MonoidalCategory.whiskerLeft, ← op_comp, ModuleCat.of_coe]
    congr 1
    exact Coalgebra.lTensor_counit_comp_comul
  mul_assoc := by
    simp only [MonoidalCategory.whiskerRight, MonoidalCategory.whiskerLeft, ← op_comp,
      MonoidalCategory.associator, Iso.op_hom, Iso.symm_hom, ModuleCat.of_coe]
    congr 1
    simp only [← Category.assoc, Iso.eq_comp_inv]
    exact Coalgebra.coassoc

/-- `CoalgebraCat.toMonObj` is functorial. -/
@[simps] def toMonMap {X Y : CoalgebraCat R} (f : X ⟶ Y) : toMonObj Y ⟶ toMonObj X where
  hom := (ModuleCat.ofHom f.1).op
  one_hom := by
    simp only [toMonObj_one, ← op_comp]
    congr
    exact f.1.counit_comp
  mul_hom := by
    simp only [toMonObj_mul, Opposite.unop_op, ← op_comp]
    congr 1
    exact f.1.map_comp_comul.symm

variable (R)

/-- The natural functor from `R`-coalgebras to monoid objects in the opposite
category of `R`-modules. -/
@[simps] def toMon : (CoalgebraCat R)ᵒᵖ ⥤ Mon_ (ModuleCat R)ᵒᵖ where
  obj := fun X => toMonObj X.unop
  map := fun f => toMonMap f.unop

variable {R}

/-- A monoid object in the opposite category of `R`-modules has a natural comultiplication
and counit. -/
@[simps]
instance ofMonObjCoalgebraStruct (X : Mon_ (ModuleCat R)ᵒᵖ) :
    CoalgebraStruct R X.X.unop where
  comul := X.mul.unop
  counit := X.one.unop

/-- A monoid object in the opposite category of `R`-modules has a natural `R`-coalgebra
structure. -/
@[simps! carrier isCoalgebra_comul isCoalgebra_counit]
def ofMonObj (X : Mon_ (ModuleCat R)ᵒᵖ) : CoalgebraCat R where
  carrier := X.X.unop
  isAddCommGroup := by infer_instance
  isModule := by infer_instance
  isCoalgebra :=
  { ofMonObjCoalgebraStruct X with
    coassoc := by
      ext
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        ← LinearEquiv.eq_symm_apply]
      exact LinearMap.ext_iff.1 (congr_arg Quiver.Hom.unop X.mul_assoc) _
    rTensor_counit_comp_comul := by exact congr_arg Quiver.Hom.unop X.one_mul
    lTensor_counit_comp_comul := by exact congr_arg Quiver.Hom.unop X.mul_one }

/-- `CoalgebraCat.ofMonObj` is functorial. -/
def ofMonMap {X Y : Mon_ (ModuleCat R)ᵒᵖ} (f : X ⟶ Y) : ofMonObj Y ⟶ ofMonObj X :=
  ⟨{ f.hom.unop with
    counit_comp := by
      show f.hom.unop ≫ X.one.unop = Y.one.unop
      simp only [← unop_comp, Mon_.Hom.one_hom]
    map_comp_comul := by
      show Y.mul.unop ≫ tensorHom f.hom.unop f.hom.unop = f.hom.unop ≫ X.mul.unop
      simp only [← unop_comp, Mon_.Hom.mul_hom]
      rfl }⟩

variable (R)

/-- The natural functor from monoid objects in the opposite
category of `R`-modules to `R`-coalgebras. -/
@[simps]
def ofMon : Mon_ (ModuleCat R)ᵒᵖ ⥤ (CoalgebraCat R)ᵒᵖ where
  obj := fun X => Opposite.op (ofMonObj X)
  map := fun f => (ofMonMap f).op

/-- The natural category equivalence between `R`-coalgebras and monoid objects in the
category of `R`-modules. -/
@[simps]
noncomputable def monEquivalence : (CoalgebraCat R)ᵒᵖ ≌ Mon_ (ModuleCat R)ᵒᵖ where
  functor := toMon R
  inverse := ofMon R
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- The monoidal category structure on the category of `R`-coalgebras induced by the
equivalence with `Mon(R-Modᵒᵖ)`. This is just an auxiliary definition; the `MonoidalCategory`
instance we make in `Mathlib.Algebra.Category.CoalgebraCat.Monoidal` will have better
definitional equalities. -/
noncomputable def instMonoidalCategoryAux : MonoidalCategory (CoalgebraCat R) :=
  Monoidal.transport ((monEquivalence R).symm.op.trans (opOpEquivalence _))

namespace MonoidalCategoryAux

variable {M N P Q : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R P] [Module R Q] [Coalgebra R M] [Coalgebra R N]
    [Coalgebra R P] [Coalgebra R Q]

attribute [local instance] instMonoidalCategoryAux

open MonoidalCategory

theorem tensorObj_comul (K L : CoalgebraCat R) :
    Coalgebra.comul (R := R) (A := (K ⊗ L : CoalgebraCat R))
      = (TensorProduct.tensorTensorTensorComm R K K L L).toLinearMap
      ∘ₗ TensorProduct.map Coalgebra.comul Coalgebra.comul := by
  simp [- Mon_.monMonoidalStruct_tensorObj_X,
    ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorHom,
    ModuleCat.comp_def, ModuleCat.ofHom, ModuleCat.of]

theorem tensorHom_toLinearMap (f : M →ₗc[R] N) (g : P →ₗc[R] Q) :
    (CoalgebraCat.ofHom f ⊗ CoalgebraCat.ofHom g).1.toLinearMap
      = TensorProduct.map f.toLinearMap g.toLinearMap := rfl

theorem associator_hom_toLinearMap :
    (α_ (CoalgebraCat.of R M) (CoalgebraCat.of R N) (CoalgebraCat.of R P)).hom.1.toLinearMap
      = (TensorProduct.assoc R M N P).toLinearMap :=
  TensorProduct.ext <| TensorProduct.ext <| by ext; rfl

theorem leftUnitor_hom_toLinearMap :
    (λ_ (CoalgebraCat.of R M)).hom.1.toLinearMap = (TensorProduct.lid R M).toLinearMap :=
  TensorProduct.ext <| by ext; rfl

theorem rightUnitor_hom_toLinearMap :
    (ρ_ (CoalgebraCat.of R M)).hom.1.toLinearMap = (TensorProduct.rid R M).toLinearMap :=
  TensorProduct.ext <| by ext; rfl

open TensorProduct

theorem comul_tensorObj :
    Coalgebra.comul (R := R) (A := (CoalgebraCat.of R M ⊗ CoalgebraCat.of R N : CoalgebraCat R))
      = Coalgebra.comul (A := M ⊗[R] N) := by
  simp [- Mon_.monMonoidalStruct_tensorObj_X,
    ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorHom,
    ModuleCat.comp_def, ModuleCat.ofHom, ModuleCat.of]

theorem comul_tensorObj_tensorObj_right :
    Coalgebra.comul (R := R) (A := (CoalgebraCat.of R M ⊗
      (CoalgebraCat.of R N ⊗ CoalgebraCat.of R P) : CoalgebraCat R))
      = Coalgebra.comul (A := M ⊗[R] N ⊗[R] P) := by
  dsimp [- Mon_.monMonoidalStruct_tensorObj_X]
  simp [ModuleCat.ofHom, ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorHom,
    ModuleCat.comp_def, ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj,
    ModuleCat.MonoidalCategory.tensorObj, ModuleCat.coe_of]

theorem comul_tensorObj_tensorObj_left :
    Coalgebra.comul (R := R)
      (A := ((CoalgebraCat.of R M ⊗ CoalgebraCat.of R N) ⊗ CoalgebraCat.of R P : CoalgebraCat R))
      = Coalgebra.comul (A := (M ⊗[R] N) ⊗[R] P) := by
  dsimp [- Mon_.monMonoidalStruct_tensorObj_X]
  simp [ModuleCat.ofHom, ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorHom,
    ModuleCat.comp_def, ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj,
    ModuleCat.MonoidalCategory.tensorObj, ModuleCat.coe_of]

theorem counit_tensorObj :
    Coalgebra.counit (R := R) (A := (CoalgebraCat.of R M ⊗ CoalgebraCat.of R N : CoalgebraCat R))
      = Coalgebra.counit (A := M ⊗[R] N) := by
  rfl

theorem counit_tensorObj_tensorObj_right :
    Coalgebra.counit (R := R)
      (A := (CoalgebraCat.of R M ⊗ (CoalgebraCat.of R N ⊗ CoalgebraCat.of R P) : CoalgebraCat R))
      = Coalgebra.counit (A := M ⊗[R] (N ⊗[R] P)) := by
  ext; rfl

theorem counit_tensorObj_tensorObj_left :
    Coalgebra.counit (R := R)
      (A := ((CoalgebraCat.of R M ⊗ CoalgebraCat.of R N) ⊗ CoalgebraCat.of R P : CoalgebraCat R))
      = Coalgebra.counit (A := (M ⊗[R] N) ⊗[R] P) := by
  ext; rfl

end CoalgebraCat.MonoidalCategoryAux
