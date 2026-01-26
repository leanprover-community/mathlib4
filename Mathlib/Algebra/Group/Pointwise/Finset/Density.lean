import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Theorems about the density of pointwise operations on finsets.
-/

public section

open scoped Pointwise

variable {α β : Type*}

namespace Finset

variable [DecidableEq α] [InvolutiveInv α] {s : Finset α} {a : α} in
@[to_additive (attr := simp)]
lemma dens_inv [Fintype α] (s : Finset α) : s⁻¹.dens = s.dens := by simp [dens]

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β} in
@[to_additive (attr := simp)]
lemma dens_smul_finset [Fintype β] (a : α) (s : Finset β) : (a • s).dens = s.dens := by simp [dens]

end Finset
