import Mathlib.RingTheory.Flat
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.CategoryTheory.Functor.Basic
--import Mathlib.CategoryTheory.Limits.Preserves.Finite


import Mathlib.LinearAlgebra.DirectSum.TensorProduct

universe u v

open TensorProduct

open CategoryTheory

open CategoryTheory.Limits

open LinearMap (rTensor lTensor)

namespace ModuleCat

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

noncomputable def rTensorFunctor : ModuleCat.{v} R ⥤ ModuleCat.{v} R where
  obj := fun N => of R (N ⊗[R] M)
  map := fun f => ofHom <| rTensor M f
  map_id := by
    intro N
    simp
    sorry
  map_comp := sorry

noncomputable def lTensorFunctor : ModuleCat.{v} R ⥤ ModuleCat.{v} R where
  obj := fun N => of R (M ⊗[R] N)
  map := fun f => ofHom <| lTensor M f
  map_id := sorry
  map_comp := sorry

instance rTensorFunctorRightExact : PreservesFiniteColimits (rTensorFunctor R M) := sorry

instance lTensorFunctorRightExact : PreservesFiniteColimits (lTensorFunctor R M) := sorry

-- lemma iff_rTensorFunctorLeftExact :  Module.Flat R M ↔
--   CategoryTheory.Limits.PreservesFiniteLimits (rTensorFunctor R M) := by
--   sorry

end ModuleCat
