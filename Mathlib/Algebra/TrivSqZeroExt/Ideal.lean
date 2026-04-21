/-
Copyright (c) 2026 Antoine Chambert-Loir, María-Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María-Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# The square zero ideal of the trivial square-zero extension

- `TrivSqZeroExt.kerIdeal`: the ideal in the trivial square-zero extension

- `TrivSqZeroExt.kerIdeal_sq `: this ideal has square zero.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace TrivSqZeroExt

open Ideal

variable (R M : Type*)
  [CommSemiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

/-- The kernel of the `AlgHom` `fstHom R R M` -/
def kerIdeal : Ideal (TrivSqZeroExt R M) := RingHom.ker (fstHom R R M)

theorem mem_kerIdeal_iff_inr (x : TrivSqZeroExt R M) : x ∈ kerIdeal R M ↔ x = inr x.snd := by
  obtain ⟨r, m⟩ := x
  simp only [kerIdeal, RingHom.mem_ker, fstHom_apply, fst_mk]
  exact ⟨fun hr => by rw [hr]; rfl, fun hrm => by rw [← fst_mk r m, hrm, fst_inr]⟩

@[simp] theorem kerIdeal_sq : kerIdeal R M ^ 2 = ⊥ := by
  simp only [pow_two, eq_bot_iff, mul_le, mem_kerIdeal_iff_inr]
  rintro x hx y hy
  rw [hx, hy, mem_bot, inr_mul_inr]

end TrivSqZeroExt

end
