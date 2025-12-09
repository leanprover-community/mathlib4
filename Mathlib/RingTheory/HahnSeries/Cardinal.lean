/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# Cardinality of Hahn series

We define `HahnSeries.card` as the cardinality of the support of a Hahn series. We find bounds on
the cardinalities of different expressions, and build corresponding substructures.
-/

@[expose] public section

open Cardinal

-- TODO: move
open Function in
@[to_additive]
lemma Pi.subsingleton_mulSupport_mulSingle {M ι : Type*} [DecidableEq ι] [One M]
    {i : ι} {a : M} : (mulSupport (mulSingle i a)).Subsingleton := by
  classical
  rw [mulSupport_mulSingle]
  split_ifs with h <;> simp

namespace HahnSeries

variable {Γ R A : Type*} [PartialOrder Γ] [Zero R]

/-- The cardinality of the support of a Hahn series. -/
def card (x : HahnSeries Γ R) : Cardinal :=
  #x.support

@[simp]
theorem card_zero : card (0 : HahnSeries Γ R) = 0 := by
  simp [card]

theorem card_single_of_ne (a : Γ) {r : R} (h : r ≠ 0) : card (single a r) = 1 := by
  rw [card, support_single_of_ne h, mk_singleton]

theorem card_single_le (a : Γ) (r : R) : card (single a r) ≤ 1 := by
  classical exact mk_le_one_iff_set_subsingleton.2 Pi.subsingleton_support_single

end HahnSeries
