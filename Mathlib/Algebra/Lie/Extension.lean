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
 * `LieAlgebra.IsExtension`: A `Prop`-valued class characterizing an extension of Lie algebras.
 * `LieAlgebra.Extension`: A bundled structure giving an extension of Lie algebras.
 * `LieAlgebra.ofSurjection`: A way to build an extension from a surjective Lie algebra
   homomorphism.

## TODO
 * `IsCentral` - central extensions
 * `Equiv` - equivalence of extensions
 * `ofTwoCocycle` - construction of extensions from 2-cocycles

## References
* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*](bourbaki1975)

-/

namespace LieAlgebra

variable {R N L M : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing N] [LieAlgebra R N] [LieRing M]
  [LieAlgebra R M]

/-- A sequence of two Lie algebra homomorphisms is an extension if it is short exact. -/
class IsExtension (i : N →ₗ⁅R⁆ L) (p : L →ₗ⁅R⁆ M) : Prop where
  ker_eq_bot : i.ker = ⊥
  range_eq_top : p.range = ⊤
  exact : i.range = p.ker

/-- A bundled version of `IsExtension`, giving a short exact sequence of Lie algebra homomorphisms
`0 → N → L → M → 0`. -/
structure Extension where
  /-- The inclusion homomorphism `N →ₗ⁅R⁆ L` -/
  incl : N →ₗ⁅R⁆ L
  /-- The projection homomorphism `L →ₗ⁅R⁆ M` -/
  proj : L →ₗ⁅R⁆ M
  IsExtension : IsExtension incl proj

/-- A surjective Lie algebra homomorphism yields an extension. -/
theorem isExtension_of_surjective (f : L →ₗ⁅R⁆ M) (hf : Function.Surjective f) :
    IsExtension f.ker.incl f where
  ker_eq_bot := LieIdeal.ker_incl f.ker
  range_eq_top := (LieHom.range_eq_top f).mpr hf
  exact := LieIdeal.incl_range f.ker

end LieAlgebra
