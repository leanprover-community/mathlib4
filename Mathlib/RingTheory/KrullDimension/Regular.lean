/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.Regular.RegularSequence

/-!

# Krull Dimension of quotient regular sequence

-/

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

namespace Module

open RingTheory Sequence IsLocalRing Submodule

theorem supportDim_quotSMulTop_succ_eq_supportDim (x : R) (reg : IsSMulRegular M x)
    (mem : x ∈ maximalIdeal R): supportDim R (QuotSMulTop x M) + 1 = supportDim R M := by
  sorry

theorem supportDim_regular_sequence_add_length_eq_supportDim (rs : List R)
    (reg : IsRegular M rs) :
    supportDim R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) + rs.length = supportDim R M := by
  generalize len : rs.length = n
  induction' n with n hn generalizing M rs
  · rw [List.length_eq_zero_iff.mp len, Ideal.ofList_nil, Submodule.bot_smul]
    simpa using supportDim_eq_of_equiv R _ _ (Submodule.quotEquivOfEqBot ⊥ rfl)
  · match rs with
    | [] => simp at len
    | x :: rs' =>
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      have : IsSMulRegular M x := ((isRegular_cons_iff M _ _).mp reg).1
      have mem : x ∈ maximalIdeal R := by
        simp only [mem_maximalIdeal, mem_nonunits_iff]
        by_contra isu
        absurd reg.2
        simp [Ideal.span_singleton_eq_top.mpr isu]
      rw [supportDim_eq_of_equiv R _ _ (quotOfListConsSMulTopEquivQuotSMulTopInner M x rs'),
        ← supportDim_quotSMulTop_succ_eq_supportDim x this mem,
        ← hn rs' ((isRegular_cons_iff M _ _).mp reg).2 len, add_assoc]

end Module
