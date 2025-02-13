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
constructed in `Mathlib.Algebra.Category.CoalgebraCat.Monoidal` to have better
definitional equalities.

-/
universe v u

namespace CoalgebraCat

open CategoryTheory MonoidalCategory

variable {R : Type u} [CommRing R]

/-- An `R`-coalgebra is a comonoid object in the category of `R`-modules. -/
@[simps X counit comul] def toComonObj (X : CoalgebraCat R) : Comon_ (ModuleCat R) where
  X := ModuleCat.of R X
  counit := ModuleCat.ofHom Coalgebra.counit
  comul := ModuleCat.ofHom Coalgebra.comul
  counit_comul := ModuleCat.hom_ext <| by simpa using Coalgebra.rTensor_counit_comp_comul
  comul_counit := ModuleCat.hom_ext <| by simpa using Coalgebra.lTensor_counit_comp_comul
  comul_assoc := ModuleCat.hom_ext <| by simp_rw [ModuleCat.of_coe]; exact Coalgebra.coassoc.symm

variable (R) in
/-- The natural functor from `R`-coalgebras to comonoid objects in the category of `R`-modules. -/
@[simps]
def toComon : CoalgebraCat R ⥤ Comon_ (ModuleCat R) where
  obj X := toComonObj X
  map f :=
    { hom := ModuleCat.ofHom f.1
      hom_counit := ModuleCat.hom_ext f.1.counit_comp
      hom_comul := ModuleCat.hom_ext f.1.map_comp_comul.symm }

/-- A comonoid object in the category of `R`-modules has a natural comultiplication
and counit. -/
@[simps]
instance ofComonObjCoalgebraStruct (X : Comon_ (ModuleCat R)) :
    CoalgebraStruct R X.X where
  comul := X.comul.hom
  counit := X.counit.hom

/-- A comonoid object in the category of `R`-modules has a natural `R`-coalgebra
structure. -/
def ofComonObj (X : Comon_ (ModuleCat R)) : CoalgebraCat R :=
  { ModuleCat.of R X.X with
    instCoalgebra :=
      { ofComonObjCoalgebraStruct X with
        coassoc := ModuleCat.hom_ext_iff.mp X.comul_assoc.symm
        rTensor_counit_comp_comul := ModuleCat.hom_ext_iff.mp X.counit_comul
        lTensor_counit_comp_comul := ModuleCat.hom_ext_iff.mp X.comul_counit } }

variable (R)

/-- The natural functor from comonoid objects in the category of `R`-modules to `R`-coalgebras. -/
def ofComon : Comon_ (ModuleCat R) ⥤ CoalgebraCat R where
  obj X := ofComonObj X
  map f :=
    { toCoalgHom' :=
      { f.hom.hom with
        counit_comp := ModuleCat.hom_ext_iff.mp f.hom_counit
        map_comp_comul := ModuleCat.hom_ext_iff.mp f.hom_comul.symm }}

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
instance we make in `Mathlib.Algebra.Category.CoalgebraCat.Monoidal` has better
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
  dsimp only [Equivalence.symm_inverse, comonEquivalence_functor, toComon_obj]
  simp only [Comon_.monoidal_tensorObj_comul, toComonObj_X, ModuleCat.of_coe, toComonObj_comul,
    tensorμ_eq_tensorTensorTensorComm]
  rfl

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
  rw [ofComonObjCoalgebraStruct_comul]
  dsimp only [Equivalence.symm_inverse, comonEquivalence_functor, toComon_obj,
    instCoalgebraStruct_comul]
  simp only [Comon_.monoidal_tensorObj_comul, toComonObj_X,
    toComonObj_comul, tensorμ_eq_tensorTensorTensorComm]
  rfl

theorem comul_tensorObj_tensorObj_right :
    Coalgebra.comul (R := R) (A := (CoalgebraCat.of R M ⊗
      (CoalgebraCat.of R N ⊗ CoalgebraCat.of R P) : CoalgebraCat R))
      = Coalgebra.comul (A := M ⊗[R] N ⊗[R] P) := by
  rw [ofComonObjCoalgebraStruct_comul]
  dsimp only [Equivalence.symm_inverse, comonEquivalence_functor, toComon_obj,
    instCoalgebraStruct_comul]
  simp only [Comon_.monoidal_tensorObj_comul, toComonObj_X, ModuleCat.of_coe, toComonObj_comul]
  rw [ofComonObjCoalgebraStruct_comul]
  dsimp only [Equivalence.symm_inverse, comonEquivalence_functor, toComon_obj]
  simp only [instMonoidalCategoryStruct_tensorObj, ModuleCat.MonoidalCategory.tensorObj,
    ModuleCat.coe_of, Comon_.monoidal_tensorObj_comul, toComonObj_X, toComonObj_comul,
    tensorμ_eq_tensorTensorTensorComm]
  rfl

theorem comul_tensorObj_tensorObj_left :
    Coalgebra.comul (R := R)
      (A := ((CoalgebraCat.of R M ⊗ CoalgebraCat.of R N) ⊗ CoalgebraCat.of R P : CoalgebraCat R))
      = Coalgebra.comul (A := (M ⊗[R] N) ⊗[R] P) := by
  rw [ofComonObjCoalgebraStruct_comul]
  dsimp only [Equivalence.symm_inverse, comonEquivalence_functor, toComon_obj,
    instCoalgebraStruct_comul]
  simp only [Comon_.monoidal_tensorObj_comul, toComonObj_X, ModuleCat.of_coe, toComonObj_comul]
  rw [ofComonObjCoalgebraStruct_comul]
  dsimp only [Equivalence.symm_inverse, comonEquivalence_functor, toComon_obj]
  simp only [instMonoidalCategoryStruct_tensorObj, ModuleCat.MonoidalCategory.tensorObj,
    ModuleCat.coe_of, Comon_.monoidal_tensorObj_comul, toComonObj_X, toComonObj_comul,
    tensorμ_eq_tensorTensorTensorComm]
  rfl

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
