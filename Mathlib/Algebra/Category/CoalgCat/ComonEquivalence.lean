/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Category.CoalgCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.CategoryTheory.Monoidal.Braided.Opposite
import Mathlib.CategoryTheory.Monoidal.Comon_
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Coalgebra.TensorProduct

/-!
# The category equivalence between `R`-coalgebras and comonoid objects in `R-Mod`

Given a commutative ring `R`, this file defines the equivalence of categories between
`R`-coalgebras and comonoid objects in the category of `R`-modules.

We then use this to set up boilerplate for the `Coalgebra` instance on a tensor product of
coalgebras defined in `Mathlib/RingTheory/Coalgebra/TensorProduct.lean`.

## Implementation notes

We make the definition `CoalgCat.instMonoidalCategoryAux` in this file, which is the
monoidal structure on `CoalgCat` induced by the equivalence with `Comon(R-Mod)`. We
use this to show the comultiplication and counit on a tensor product of coalgebras satisfy
the coalgebra axioms, but our actual `MonoidalCategory` instance on `CoalgCat` is
constructed in `Mathlib/Algebra/Category/CoalgCat/Monoidal.lean` to have better
definitional equalities.

-/

suppress_compilation

universe v u

namespace CoalgCat

open CategoryTheory MonoidalCategory ComonObj

variable {R : Type u} [CommRing R]

@[simps counit comul]
noncomputable instance (X : CoalgCat R) : ComonObj (ModuleCat.of R X) where
  counit := ModuleCat.ofHom Coalgebra.counit
  comul := ModuleCat.ofHom Coalgebra.comul
  counit_comul := ModuleCat.hom_ext <| by simpa using Coalgebra.rTensor_counit_comp_comul
  comul_counit := ModuleCat.hom_ext <| by simpa using Coalgebra.lTensor_counit_comp_comul
  comul_assoc := ModuleCat.hom_ext <| by simp_rw [ModuleCat.of_coe]; exact Coalgebra.coassoc.symm

/-- An `R`-coalgebra is a comonoid object in the category of `R`-modules. -/
@[simps X]
noncomputable def toComonObj (X : CoalgCat R) : Comon (ModuleCat R) := ⟨ModuleCat.of R X⟩

variable (R) in
/-- The natural functor from `R`-coalgebras to comonoid objects in the category of `R`-modules. -/
@[simps]
def toComon : CoalgCat R ⥤ Comon (ModuleCat R) where
  obj X := toComonObj X
  map f :=
    { hom := ModuleCat.ofHom f.1
      isComonHom_hom :=
        { hom_counit := ModuleCat.hom_ext f.1.counit_comp
          hom_comul := ModuleCat.hom_ext f.1.map_comp_comul.symm } }

/-- A comonoid object in the category of `R`-modules has a natural comultiplication
and counit. -/
@[simps]
noncomputable instance ofComonObjCoalgebraStruct (X : ModuleCat R) [ComonObj X] :
    CoalgebraStruct R X where
  comul := Δ[X].hom
  counit := ε[X].hom

/-- A comonoid object in the category of `R`-modules has a natural `R`-coalgebra
structure. -/
noncomputable def ofComonObj (X : ModuleCat R) [ComonObj X] : CoalgCat R :=
  { ModuleCat.of R X with
    instCoalgebra :=
      { ofComonObjCoalgebraStruct X with
        coassoc := ModuleCat.hom_ext_iff.mp (comul_assoc X).symm
        rTensor_counit_comp_comul := ModuleCat.hom_ext_iff.mp (counit_comul X)
        lTensor_counit_comp_comul := ModuleCat.hom_ext_iff.mp (comul_counit X) } }

variable (R)

/-- The natural functor from comonoid objects in the category of `R`-modules to `R`-coalgebras. -/
noncomputable def ofComon : Comon (ModuleCat R) ⥤ CoalgCat R where
  obj X := ofComonObj X.X
  map f :=
    { toCoalgHom' :=
      { f.hom.hom with
        counit_comp := ModuleCat.hom_ext_iff.mp (IsComonHom.hom_counit f.hom)
        map_comp_comul := ModuleCat.hom_ext_iff.mp ((IsComonHom.hom_comul f.hom).symm) } }

/-- The natural category equivalence between `R`-coalgebras and comonoid objects in the
category of `R`-modules. -/
@[simps]
def comonEquivalence : CoalgCat R ≌ Comon (ModuleCat R) where
  functor := toComon R
  inverse := ofComon R
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by rfl
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by rfl

variable {R}

/-- The monoidal category structure on the category of `R`-coalgebras induced by the
equivalence with `Comon(R-Mod)`. This is just an auxiliary definition; the `MonoidalCategory`
instance we make in `Mathlib/Algebra/Category/CoalgCat/Monoidal.lean` has better
definitional equalities. -/
noncomputable def instMonoidalCategoryAux : MonoidalCategory (CoalgCat R) :=
  Monoidal.transport (comonEquivalence R).symm

namespace MonoidalCategoryAux

variable {M N P Q : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R P] [Module R Q] [Coalgebra R M] [Coalgebra R N]
    [Coalgebra R P] [Coalgebra R Q]

attribute [local instance] instMonoidalCategoryAux

open MonoidalCategory ModuleCat.MonoidalCategory

theorem tensorObj_comul (K L : CoalgCat R) :
    Coalgebra.comul (R := R) (A := (K ⊗ L : CoalgCat R))
      = (TensorProduct.tensorTensorTensorComm R K K L L).toLinearMap
      ∘ₗ TensorProduct.map Coalgebra.comul Coalgebra.comul := by
  rw [ofComonObjCoalgebraStruct_comul]
  simp only [Comon.monoidal_tensorObj_comon_comul, Equivalence.symm_inverse,
    comonEquivalence_functor, toComon_obj, toComonObj_X, ModuleCat.of_coe,
    MonObj.tensorObj.mul_def, unop_comp, unop_tensorObj, unop_tensorHom,
    BraidedCategory.unop_tensorμ, tensorμ_eq_tensorTensorTensorComm, ModuleCat.hom_comp,
    ModuleCat.hom_ofHom, LinearEquiv.comp_toLinearMap_eq_iff]
  rfl

theorem tensorHom_toLinearMap (f : M →ₗc[R] N) (g : P →ₗc[R] Q) :
    (CoalgCat.ofHom f ⊗ₘ CoalgCat.ofHom g).1.toLinearMap
      = TensorProduct.map f.toLinearMap g.toLinearMap := rfl

theorem associator_hom_toLinearMap :
    (α_ (CoalgCat.of R M) (CoalgCat.of R N) (CoalgCat.of R P)).hom.1.toLinearMap
      = (TensorProduct.assoc R M N P).toLinearMap :=
  TensorProduct.ext <| TensorProduct.ext <| by ext; rfl

theorem leftUnitor_hom_toLinearMap :
    (λ_ (CoalgCat.of R M)).hom.1.toLinearMap = (TensorProduct.lid R M).toLinearMap :=
  TensorProduct.ext <| by ext; rfl

theorem rightUnitor_hom_toLinearMap :
    (ρ_ (CoalgCat.of R M)).hom.1.toLinearMap = (TensorProduct.rid R M).toLinearMap :=
  TensorProduct.ext <| by ext; rfl

open TensorProduct

attribute [local simp] MonObj.tensorObj.one_def MonObj.tensorObj.mul_def in
theorem comul_tensorObj :
    Coalgebra.comul (R := R) (A := (CoalgCat.of R M ⊗ CoalgCat.of R N : CoalgCat R))
      = Coalgebra.comul (A := M ⊗[R] N) := by
  rw [ofComonObjCoalgebraStruct_comul]
  simp [tensorμ_eq_tensorTensorTensorComm, TensorProduct.comul_def,
    AlgebraTensorModule.tensorTensorTensorComm_eq]
  rfl

attribute [local simp] MonObj.tensorObj.one_def MonObj.tensorObj.mul_def in
theorem comul_tensorObj_tensorObj_right :
    Coalgebra.comul (R := R) (A := (CoalgCat.of R M ⊗
      (CoalgCat.of R N ⊗ CoalgCat.of R P) : CoalgCat R))
      = Coalgebra.comul (A := M ⊗[R] (N ⊗[R] P)) := by
  rw [ofComonObjCoalgebraStruct_comul]
  simp only [Comon.monoidal_tensorObj_comon_comul]
  simp [tensorμ_eq_tensorTensorTensorComm, TensorProduct.comul_def,
    AlgebraTensorModule.tensorTensorTensorComm_eq]
  rfl

attribute [local simp] MonObj.tensorObj.one_def MonObj.tensorObj.mul_def in
theorem comul_tensorObj_tensorObj_left :
    Coalgebra.comul (R := R)
      (A := ((CoalgCat.of R M ⊗ CoalgCat.of R N) ⊗ CoalgCat.of R P : CoalgCat R))
      = Coalgebra.comul (A := M ⊗[R] N ⊗[R] P) := by
  rw [ofComonObjCoalgebraStruct_comul]
  dsimp
  simp only [toComonObj]
  simp [tensorμ_eq_tensorTensorTensorComm, TensorProduct.comul_def,
    AlgebraTensorModule.tensorTensorTensorComm_eq]
  rfl

theorem counit_tensorObj :
    Coalgebra.counit (R := R) (A := (CoalgCat.of R M ⊗ CoalgCat.of R N : CoalgCat R))
      = Coalgebra.counit (A := M ⊗[R] N) := by
  rw [ofComonObjCoalgebraStruct_counit]
  simp [TensorProduct.counit_def, TensorProduct.AlgebraTensorModule.rid_eq_rid, ← lid_eq_rid]
  rfl

theorem counit_tensorObj_tensorObj_right :
    Coalgebra.counit (R := R)
      (A := (CoalgCat.of R M ⊗ (CoalgCat.of R N ⊗ CoalgCat.of R P) : CoalgCat R))
      = Coalgebra.counit (A := M ⊗[R] (N ⊗[R] P)) := by
  rw [ofComonObjCoalgebraStruct_counit]
  simp [TensorProduct.counit_def, TensorProduct.AlgebraTensorModule.rid_eq_rid, ← lid_eq_rid]
  rfl

theorem counit_tensorObj_tensorObj_left :
    Coalgebra.counit (R := R)
      (A := ((CoalgCat.of R M ⊗ CoalgCat.of R N) ⊗ CoalgCat.of R P : CoalgCat R))
      = Coalgebra.counit (A := (M ⊗[R] N) ⊗[R] P) := by
  rw [ofComonObjCoalgebraStruct_counit]
  simp [TensorProduct.counit_def, TensorProduct.AlgebraTensorModule.rid_eq_rid, ← lid_eq_rid]
  rfl

end CoalgCat.MonoidalCategoryAux
