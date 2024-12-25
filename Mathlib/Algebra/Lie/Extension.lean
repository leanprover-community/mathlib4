/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Lie.Submodule

/-!
# Extensions of Lie algebras
This file defines extensions of Lie algebras. They are implemented as a structure, rather than the
proposition that a Lie algebra homomorphism is surjective.

## Main definitions
 * `LieExtension`: The structure giving an extension of Lie algebras.
 * `LieExtension.ofSurjection`: A way to build an extension from a surjective Lie algebra
   homomorphism.
 * `LieExtension.Splitting`: A section of a surjective Lie algebra homomorphism.

## TODO
 * `IsCentral` - central extensions
 * `Equiv` - equivalence of extensions
 * `ofTwoCocycle` - construction of extensions from 2-cocycles

## References
* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*](bourbaki1975)



-/

variable (R N L M : Type*)

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing N] [LieAlgebra R N] [LieRing M]
  [LieAlgebra R M]

/-- `LieExtension N E G` is a short exact sequence of Lie algebra homomorphisms
`0 → N → L → M → 0`. -/
structure LieExtension where
  /-- The inclusion homomorphism `N →ₗ⁅R⁆ L` -/
  inl : N →ₗ⁅R⁆ L
  /-- The projection homomorphism `L →ₗ⁅R⁆ M` -/
  rightHom : L →ₗ⁅R⁆ M
  /-- The inclusion map is injective. -/
  inl_injective : Function.Injective inl
  /-- The range of the inclusion map is equal to the kernel of the projection map. -/
  range_inl_eq_ker_rightHom : LinearMap.range inl.toLinearMap = LinearMap.ker rightHom.toLinearMap
  /-- The projection map is surjective. -/
  rightHom_surjective : Function.Surjective rightHom

namespace LieExtension

variable {R L M N}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing N] [LieAlgebra R N] [LieRing M]
  [LieAlgebra R M] (S : LieExtension R N L M)

/-- Construct an extension from a surjective Lie algebra homomorphism. -/
@[simps!]
def ofSurjection (f : L →ₗ⁅R⁆ M) (hf : Function.Surjective f) :
    LieExtension R (LieHom.ker f) L M where
  inl := f.ker.incl
  rightHom := f
  inl_injective := LieIdeal.incl_injective f.ker
  range_inl_eq_ker_rightHom := by aesop
  rightHom_surjective := hf

/-- `Splitting` of a Lie extension is a section homomorphism. -/
structure Splitting where
  /-- A section homomorphism -/
  sectionHom : M →ₗ⁅R⁆ L
  /-- The section is a left inverse of the projection map. -/
  rightHom_comp_sectionHom : S.rightHom.comp sectionHom = LieHom.id

instance : FunLike S.Splitting M L where
  coe s := s.sectionHom
  coe_injective' := by
    intro ⟨_, _⟩ ⟨_, _⟩ h
    congr
    exact DFunLike.coe_injective h

instance : LinearMapClass S.Splitting R M L where
  map_add f := f.sectionHom.map_add'
  map_smulₛₗ f := f.sectionHom.map_smul'

end LieExtension
