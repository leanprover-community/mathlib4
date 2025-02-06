/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Hom.Lattice
import Mathlib.Order.SymmDiff

/-!
# Lattice homomorphisms between Boolean algebras

-/

open Function OrderDual

variable {F α β : Type*}

section BooleanAlgebra

variable [BooleanAlgebra α] [BooleanAlgebra β] [FunLike F α β] [BoundedLatticeHomClass F α β]
variable (f : F)

/-- Special case of `map_compl` for boolean algebras. -/
theorem map_compl' (a : α) : f aᶜ = (f a)ᶜ :=
  (isCompl_compl.map _).compl_eq.symm

/-- Special case of `map_sdiff` for boolean algebras. -/
theorem map_sdiff' (a b : α) : f (a \ b) = f a \ f b := by
  rw [sdiff_eq, sdiff_eq, map_inf, map_compl']

open scoped symmDiff in
/-- Special case of `map_symmDiff` for boolean algebras. -/
theorem map_symmDiff' (a b : α) : f (a ∆ b) = f a ∆ f b := by
  rw [symmDiff, symmDiff, map_sup, map_sdiff', map_sdiff']

end BooleanAlgebra
