/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Lie.Cocycle

/-!
# The Chevalley-Eilenberg complex

Given a Lie algebra `L` over a commutative ring `R`, and an `L`-module `M`, we construct the cochain
complex of alternating multilinear maps from `L^p` to `M`.

## Main definitions (Todo for now)

* Write the Chevalley-Eilenberg dg-algebra for a Lie algebra, then define homology and cohomology
as Ext and Tor?  We get commutativity from alternating property and associativity from Jacobi.
Also, I think this gives an equivalence between dg Lie algebras and CDGAs with suitable grading.
* Standard cochain complex
* cohomology

## Main results



## References

* [N. Bourbaki, *Lie groups and {L}ie algebras. {C}hapters 1--3*][bourbaki1975]
-- cohomology is Exercises section 3 (p116, near end of book)
-/

namespace LieAlgebra

open ModuleCat

variable {L M R : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M]
/-!

/-- The differential of a cochain. -/
def differentialCE (i : ℕ) :(L [⋀^Fin i]→ₗ[R] M) →ₗ[R] (L [⋀^Fin (i + 1)]→ₗ[R] M) where
  toFun f := sorry
  map_add' := sorry
  map_smul' := sorry

/-! Things that don't use ModuleCat should go in a different file, like `Cochains.lean`-/

/-- The standard complex for Lie algebra cohomology. -/
def CochainComplex (L M R) [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
    [LieRingModule L M] : CochainComplex (ModuleCat R) ℕ where
  X n := of R (L [⋀^(Fin n)]→ₗ[R] M)
  d i j := sorry
-/

end LieAlgebra
