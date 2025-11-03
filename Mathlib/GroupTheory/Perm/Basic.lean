/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.End
import Mathlib.Logic.Equiv.Set
import Mathlib.Tactic.Common

/-!
# Extra lemmas about permutations

This file proves miscellaneous lemmas about `Equiv.Perm`.

## TODO

Most of the content of this file was moved to `Algebra.Group.End` in
https://github.com/leanprover-community/mathlib4/pull/22141.
It would be good to merge the remaining lemmas with other files, e.g.
`GroupTheory.Perm.ViaEmbedding` looks like it could benefit from such a treatment (splitting into
the algebra and non-algebra parts).
-/


universe u v

namespace Equiv

variable {α : Type u} {β : Type v}

namespace Perm

@[simp] lemma image_inv (f : Perm α) (s : Set α) : ↑f⁻¹ '' s = f ⁻¹' s := f⁻¹.image_eq_preimage _

@[simp] lemma preimage_inv (f : Perm α) (s : Set α) : ↑f⁻¹ ⁻¹' s = f '' s :=
  (f.image_eq_preimage _).symm

end Perm

section Swap

variable [DecidableEq α]

@[simp]
theorem swap_smul_self_smul [MulAction (Perm α) β] (i j : α) (x : β) :
    swap i j • swap i j • x = x := by simp [smul_smul]

theorem swap_smul_involutive [MulAction (Perm α) β] (i j : α) :
    Function.Involutive (swap i j • · : β → β) := swap_smul_self_smul i j

end Swap
end Equiv

open Equiv Function

namespace Set
variable {α : Type*} {f : Perm α} {s : Set α}

lemma BijOn.perm_inv (hf : BijOn f s s) : BijOn ↑(f⁻¹) s s := hf.symm f.invOn

lemma MapsTo.perm_pow : MapsTo f s s → ∀ n : ℕ, MapsTo (f ^ n) s s := by
  simp_rw [Equiv.Perm.coe_pow]; exact MapsTo.iterate
lemma SurjOn.perm_pow : SurjOn f s s → ∀ n : ℕ, SurjOn (f ^ n) s s := by
  simp_rw [Equiv.Perm.coe_pow]; exact SurjOn.iterate
lemma BijOn.perm_pow : BijOn f s s → ∀ n : ℕ, BijOn (f ^ n) s s := by
  simp_rw [Equiv.Perm.coe_pow]; exact BijOn.iterate

lemma BijOn.perm_zpow (hf : BijOn f s s) : ∀ n : ℤ, BijOn (f ^ n) s s
  | Int.ofNat n => hf.perm_pow n
  | Int.negSucc n => (hf.perm_pow (n + 1)).perm_inv

end Set
