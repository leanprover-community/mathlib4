/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Order.Interval.Finset.Gaps
/-!
# Sum of gaps

This file proves that given a function `g` on `[a, b]`, `g b - g a` can be split according to a
given finite collection of pairwise disjoint closed subintervals of `[a, b]`. It is the sum of two
terms:
- the sum of `g y - g x` for `[x, y]` in the collection,
- the sum of `g y - g x` for `[x, y]` in the complement (modulo endpoints) of the union of the
collection in `[a, b]`.

We use `Finset.intervalGapsWithin` to encode the complement.

We provide the multiplication versions in `Finset.prod_intervalGapsWithin_mul_prod_eq_div`,
`Finset.prod_intervalGapsWithin_eq_div_div_prod`, and the additive versions in
`Finset.sum_intervalGapsWithin_add_sum_eq_sub`, `Finset.sum_intervalGapsWithin_eq_sub_sub_sum`.

Technically, we don't require pairwise disjointness or endpoints to be within `[a, b]` or even
require that `a ≤ b`, but it makes the most sense if they are actually satisfied.
-/

@[expose] public section

open Fin Fin.NatCast

variable {α β : Type*} [LinearOrder α] [CommGroup β]
  (F : Finset (α × α)) {k : ℕ} (h : F.card = k) {a b : α}
  (g : α → β)

@[to_additive]
theorem Finset.prod_intervalGapsWithin_mul_prod_eq_div :
    (∏ i, g (F.intervalGapsWithin h a b i).2 / g (F.intervalGapsWithin h a b i).1) *
      ∏ z ∈ F, g z.2 / g z.1 = g b / g a := by
  set p := F.intervalGapsWithin h a b
  have : ∏ z ∈ F, g z.2 / g z.1 = ∏ i ∈ range k, g (p (Nat.succ i)).1 / g (p i).2 := by
    symm
    apply prod_bij (fun (i : ℕ) hi ↦ ((p i).2, (p (Nat.succ i)).1))
    · intro i hi
      rw [mem_range] at hi
      convert F.intervalGapsWithin_mapsTo h a b (x := ⟨i, hi⟩) trivial
      · ext
        suffices i < k + 1 by simp [*]
        omega
      · ext; simp [hi]
    · intro i hi j hj hij
      rw [mem_range] at hi hj
      by_cases hk : k = 0
      · grind
      have : NeZero k := { out := hk }
      suffices (i : Fin k) = (j : Fin k) by
        rw [← mk_eq_mk (h := hi) (h' := hj)]
        convert this
        · rw [val_cast_of_lt hi]
        · rw [val_cast_of_lt hj]
      apply F.intervalGapsWithin_injective h a b
      convert hij <;> ext
      · rw [val_castSucc, val_cast_of_lt hi, val_cast_of_lt (by omega)]
      · rw [val_succ, val_cast_of_lt hi,  val_cast_of_lt (by omega)]
      · rw [val_castSucc, val_cast_of_lt hj, val_cast_of_lt (by omega)]
      · rw [val_succ, val_cast_of_lt hj,  val_cast_of_lt (by omega)]
    · intro z hz
      obtain ⟨i, _, hi⟩ := F.intervalGapsWithin_surjOn h a b hz
      refine ⟨i, by simp [mem_range], ?_⟩
      convert hi
      · exact coe_eq_castSucc
      · ext; simp
    · simp
  rw [this,
      prod_congr rfl (g := fun (i : Fin (k + 1)) ↦ g (p (i : ℕ)).2 / g (p (i : ℕ)).1)
        (fun i _ ↦ by congr <;> simp),
      ← prod_range (f := fun i ↦ g (p i).2 / g (p i).1), mul_comm,
      prod_range_succ, ← mul_assoc,
      ← prod_mul_distrib,
      prod_congr rfl (fun _ _ ↦ div_mul_div_cancel _ _ _),
      prod_range_div (fun i ↦ g (F.intervalGapsWithin h a b i).1)]
  have : ((0 : ℕ) : Fin (k + 1)) = 0 := (eq_of_val_eq rfl).symm
  simp [p, this]

@[to_additive]
theorem Finset.prod_intervalGapsWithin_eq_div_div_prod :
    ∏ i, g (F.intervalGapsWithin h a b i).2 / g (F.intervalGapsWithin h a b i).1 =
    g b / g a / ∏ z ∈ F, g z.2 / g z.1 :=
  eq_div_iff_mul_eq'.mpr (F.prod_intervalGapsWithin_mul_prod_eq_div h g)
