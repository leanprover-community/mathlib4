/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.Star.LinearMap
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!

# The eigenspace of the intrinsic star applied to an operator

-/

namespace Module.End
variable {R V : Type*} [InvolutiveStar R] [AddCommGroup V] [StarAddMonoid V]

open scoped IntrinsicStar
open LinearMap

theorem mem_eigenspace_intrinsicStar_iff [CommRing R] [Module R V] [StarModule R V]
    (f : End R V) (α : R) (x : V) :
    x ∈ (star f).eigenspace α ↔ star x ∈ f.eigenspace (star α) := by
  simp_rw [mem_eigenspace_iff, intrinsicStar_apply, star_eq_iff_star_eq, star_smul, eq_comm]

theorem spectrum_intrinsicStar [CommSemiring R] [Module R V] [StarModule R V] (f : End R V) :
    spectrum R (star f) = star (spectrum R f) := by
  ext x
  simp_rw [Set.mem_star, spectrum.mem_iff, not_iff_not, Algebra.algebraMap_eq_smul_one]
  rw [← isUnit_intrinsicStar_iff, star_sub, star_star, star_smul, one_eq_id, intrinsicStar_id]

end Module.End
