/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Lie.Abelian

/-!
# Central extensions of Lie algebras

Given a Lie algebra `L` over a commutative ring `R`, and an abelian Lie algebra `C` over `R`, a
central extension of `L` by `C` is a Lie algebra `M` over `R` equipped with a surjective
homomorphism `f : M →ₗ[R] L` and an `R`-isomorphism from `C` to the kernel of `f`. A central
extension is `R`-split if the structure maps on `M` induce an `R`-module decomposition into a direct
sum of `L` and `C`. In this case, we can describe `M` as a direct sum with bracket given by a
2-cocycle. Two `R`-split central extensions are isomorphic if and only if the 2-cocycles differ by
a coboundary.

A projective `R`-linear representation of a Lie algebra `L` over `R` is an `R`-module `M` with a
linear map `ρ : L → End R M` such that `ρ [x,y] = c(x,y) ρ x ρ y` or something.

## Main definitions (Todo for now)

* Central extension
* `R`-split
* split
* projective representations

## Main results

* cocycle description
* cohomological criterion for triviality

## References

* [N. Bourbaki, *Lie groups and {L}ie algebras. {C}hapters 1--3*][bourbaki1975]
-- extensions are chapter 1 section 7, cohomology is Exercises section 3 (p116, near end of book)


## Tags

lie ring, lie algebra, central extension
-/

suppress_compilation

open scoped TensorProduct

variable {R L M : Type*}

namespace LieAlgebra

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

/-- A Lie algebra homomorphism is a central extension if it is surjective and the kernel lies in the
center. The center condition is equivalent to the kernel being a trivial module for the adjoint
adjoint action. -/
class IsCentralExtension (f : M →ₗ⁅R⁆ L) : Prop where
  protected surjective : Function.Surjective f
  protected central : LieModule.IsTrivial M f.ker

lemma surjective_of_central_extension (f : M →ₗ⁅R⁆ L) [IsCentralExtension f] :
    Function.Surjective f := IsCentralExtension.surjective

lemma central_of_central_extension (f : M →ₗ⁅R⁆ L) [IsCentralExtension f] :
    LieModule.IsTrivial M f.ker := IsCentralExtension.central

/-- A module-splitting is a surjective Lie algebra homomorphism equipped with a linear isomorphism
from the source to the direct sum of the kernel and the target. This should be revised to the usual
notion of splitting of a surjection. -/
structure ModuleSplitting (f : M →ₗ⁅R⁆ L) where
/-- The map `f` is surjective. -/
  protected surjective : Prop := Function.Surjective f
/-- The source splits as an `R`-module. -/
  protected splitting : M ≃ₗ[R] L × f.ker
/-- The splitting is compatible with `f`. -/
  protected compatible : Prop := (LinearMap.fst R L f.ker) ∘ₗ splitting = (f : M →ₗ[R] L)

/-!

/-- Make a cocycle from a module-split central extendion-/
def cocycle_of_splitting (f : M →ₗ⁅R⁆ L) [IsCentralExtension f] [ModuleSplitting f] :
    L [⋀^(Fin 2)]→ₗ[R] f.ker where
  toFun g := LinearMap.snd
    ⁅ModuleSplitting.splitting.symm (LinearMap.inl R L f.ker (g 0)), ModuleSplitting.splitting.symm
      (LinearMap.inl R L f.ker (g 1))⁆
    -- [(a,b),(c,d)] = (cocycle(b,d),[b, d]) : use splitting.symm ∘ₗ LinearMap.inl
  map_add' := sorry
  map_smul' := sorry
  map_eq_zero_of_eq' := sorry

-- /--Make a module-split central extension from a 2-cocycle (with trivial coefficients)-/
--def splitting_of_cocycle (f : 2-cocycle L V) : L × V →ₗ⁅R⁆ L where

-/

end LieAlgebra
