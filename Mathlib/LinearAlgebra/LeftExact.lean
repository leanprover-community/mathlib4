/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Exact
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# The Left Exactness of Hom


If `M1 → M2 → M3 → 0` is an exact sequence of `R`-modules and `N` is a `R`-module,
then `0 → (M3 →ₗ[R] N) → (M2 →ₗ[R] N) → (M1 →ₗ[R] N)` is exact. In this file, we
show the exactness at `M2 →ₗ[R] N` (`exact_lcomp_of_exact_of_surjective`);
the injectivity part is `LinearMap.lcomp_injective_of_surjective` in the file
`Mathlib.LinearAlgebra.BilinearMap`.


-/

@[expose] public section

namespace LinearMap

variable {R : Type*} [CommRing R] {M1 M2 M3 : Type*} (N : Type*)
  [AddCommGroup M1] [AddCommGroup M2] [AddCommGroup M3] [AddCommGroup N]
  [Module R M1] [Module R M2] [Module R M3] [Module R N]

lemma exact_lcomp_of_exact_of_surjective {f : M1 →ₗ[R] M2} {g : M2 →ₗ[R] M3}
    (exac : Function.Exact f g) (surj : Function.Surjective g) :
    Function.Exact (LinearMap.lcomp R N g) (LinearMap.lcomp R N f) := by
  intro h
  simp only [LinearMap.lcomp_apply', Set.mem_range]
  refine ⟨fun hh ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩
  · use ((LinearMap.range f).liftQ h (LinearMap.range_le_ker_iff.mpr hh)).comp
      (exac.linearEquivOfSurjective surj).symm.toLinearMap
    ext x
    simp
  · rw [← hy, LinearMap.comp_assoc, exac.linearMap_comp_eq_zero, LinearMap.comp_zero y]

end LinearMap
