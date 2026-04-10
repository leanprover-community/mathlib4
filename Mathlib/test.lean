import Mathlib

variable {R : Type*} [CommRing R]
example :
    (ModuleCat.instCommRingCarrierTensorUnit.toRing :
      Ring ↑(CategoryTheory.MonoidalCategoryStruct.tensorUnit (ModuleCat R))) =
    ModuleCat.MonModuleEquivalenceAlgebra.MonObj.toRing
      (CategoryTheory.MonoidalCategoryStruct.tensorUnit (ModuleCat R)) := rfl  -- fails
