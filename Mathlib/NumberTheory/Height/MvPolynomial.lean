/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.Height.Basic

import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Data.Fintype.Order
import all Mathlib.NumberTheory.Height.Basic

/-!
# Height bounds for linear and polynomial maps

We prove an upper bound for the height of the image of a tuple under a linear map.

We also prove upper and lower bounds for the height of `fun i ↦ eval P i x`, where `P` is a family
of homogeneous polynomials over the field `K` of the same degree `N` and `x : ι → K`
with `ι` finite.
-/

public section

section aux

namespace IsNonarchimedean

variable {R α : Type*} [CommRing R]

/-- The ultrametric triangle inequality for finite sums. -/
lemma apply_sum_le {v : AbsoluteValue R ℝ} (hv : IsNonarchimedean v) {l : α → R} {s : Finset α} :
    v (∑ i ∈ s, l i) ≤ ⨆ i : s, v (l i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    grw [hv .., ih]
    refine max_le ?_ ?_
    · exact Finite.le_ciSup_of_le ⟨_, s.mem_insert_self a⟩ le_rfl
    · rcases isEmpty_or_nonempty s with hs | hs
      · simpa using Real.iSup_nonneg_of_nonnegHomClass v _
      exact ciSup_le fun i ↦ Finite.le_ciSup_of_le (⟨i.val, Finset.mem_insert_of_mem i.prop⟩) le_rfl

end IsNonarchimedean

end aux

/-!
### Upper bound for the height of the image under a linear map
-/

namespace Height

variable {K : Type*} [Field K] {ι ι' : Type*} [Fintype ι] [Finite ι']

-- The "local" version of the bound for (archimedean) absolute values.
lemma linearMap_apply_bound [Nonempty ι'] (v : AbsoluteValue K ℝ) (A : ι' × ι → K) (x : ι → K) :
    ⨆ j, v (∑ i, A (j, i) * x i) ≤ Nat.card ι * (⨆ ji, v (A ji)) * ⨆ i, v (x i) := by
  refine ciSup_le fun j ↦ ?_
  grw [v.sum_le]
  simp only [map_mul]
  grw [Finset.sum_le_sum (g := fun _ ↦ (⨆ ji, v (A ji)) * ⨆ i, v (x i)) fun i _ ↦ ?h]
  case h =>
    simp only
    gcongr
    · exact Real.iSup_nonneg_of_nonnegHomClass v _
    · exact Finite.le_ciSup_of_le (j, i) le_rfl
    · exact Finite.le_ciSup_of_le i le_rfl
  rw [Finset.sum_const, nsmul_eq_mul, mul_assoc, Finset.card_univ, Nat.card_eq_fintype_card]

-- The "local" version of the bound for nonarchimedean absolute values.
lemma linearMap_apply_bound_of_isNonarchimedean {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) (A : ι' × ι → K) (x : ι → K) :
    ⨆ j, v (∑ i, A (j, i) * x i) ≤ (⨆ ji, v (A ji)) * ⨆ i, v (x i) := by
  rcases isEmpty_or_nonempty ι
  · simp
  rcases isEmpty_or_nonempty ι'
  · simp
  refine ciSup_le fun j ↦ ?_
  grw [hv.apply_sum_le]
  simp only [map_mul]
  have (f : ι → ℝ) : ⨆ i : ↥Finset.univ, f i.val = ⨆ i, f i :=
    Function.Surjective.iSup_comp (fun i ↦ ⟨⟨i, Finset.mem_univ i⟩, rfl⟩) f
  rw [this fun i ↦ v (A (j, i)) * v (x i)]
  refine ciSup_le fun i ↦ ?_
  gcongr
  · exact Real.iSup_nonneg_of_nonnegHomClass v _
  · exact Finite.le_ciSup_of_le (j, i) le_rfl
  · exact Finite.le_ciSup_of_le i le_rfl

variable [AdmissibleAbsValues K]

open AdmissibleAbsValues

open Multiset in
/-- Let `A : ι' × ι → K`, which we can interpret as a linear map from `ι → K` to `ι' → K`.
Let `x : ι → K` be a tuple. Then the multiplicative height of `A x` is bounded by
`#ι ^ totalWeight K * mulHeight A * mulHeight x` (if `ι` is nonempty).

Note: We use the uncurried form of `A` so that we can write `mulHeight A`. -/
theorem mulHeight_linearMap_apply_le [Nonempty ι] (A : ι' × ι → K) (x : ι → K) :
    mulHeight (fun j ↦ ∑ i, A (j, i) * x i) ≤
      Nat.card ι ^ totalWeight K * mulHeight A * mulHeight x := by
  have H₀ : 1 ≤ Nat.card ι ^ totalWeight K * mulHeight A * mulHeight x := by
    rw [show (1 : ℝ) = 1 * 1 * 1 by ring]
    gcongr
    · exact_mod_cast Nat.one_le_pow _ _ Nat.card_pos
    · exact one_le_mulHeight _
    · exact one_le_mulHeight _
  rcases isEmpty_or_nonempty ι' with hι' | hι'
  · simpa only [mulHeight_eq_one_of_subsingleton, mul_one] using H₀
  rcases eq_or_ne (fun j ↦ ∑ i, A (j, i) * x i) 0 with h | h
  · simpa only [h, mulHeight_zero] using H₀
  rcases eq_or_ne A 0 with rfl | hA
  · simpa using H₀
  rcases eq_or_ne x 0 with rfl | hx
  · simpa using H₀
  rw [mulHeight_eq h, mulHeight_eq hA, mulHeight_eq hx, mul_mul_mul_comm, ← mul_assoc, ← mul_assoc,
    mul_assoc (_ * _ * _)]
  gcongr
  · exact finprod_nonneg fun v ↦ Real.iSup_nonneg_of_nonnegHomClass v.val _
  · refine mul_nonneg (mul_nonneg (by simp) ?_) ?_ <;>
      exact prod_map_nonneg fun v _ ↦ Real.iSup_nonneg_of_nonnegHomClass v _
  · -- archimedean part: reduce to "local" statement `linearMap_apply_bound`
    rw [mul_assoc, ← prod_map_mul, ← prod_replicate, totalWeight, ← map_const', ← prod_map_mul]
    refine prod_map_le_prod_map₀ _ _ (fun v _ ↦ Real.iSup_nonneg_of_nonnegHomClass v _) fun v _ ↦ ?_
    rw [mul_comm (iSup _), ← mul_assoc]
    exact linearMap_apply_bound v A x
  · -- nonarchimedean part: reduce to "local" statement `linearMap_apply_bound_of_isNonarchimedean`
    rw [← finprod_mul_distrib (mulSupport_iSup_nonarchAbsVal_finite hA)
      (mulSupport_iSup_nonarchAbsVal_finite hx)]
    refine finprod_le_finprod (mulSupport_iSup_nonarchAbsVal_finite h)
      (fun v ↦ Real.iSup_nonneg_of_nonnegHomClass v.val _) ?_ fun v ↦ ?_
    · exact ((mulSupport_iSup_nonarchAbsVal_finite hA).union
        (mulSupport_iSup_nonarchAbsVal_finite hx)).subset <| Function.mulSupport_mul ..
    · exact linearMap_apply_bound_of_isNonarchimedean (isNonarchimedean _ v.prop) A x

open Real in
/-- Let `A : ι' × ι → K`, which we can interpret as a linear map from `ι → K` to `ι' → K`.
Let `x : ι → K` be a tuple. Then the logarithmic height of `A x` is bounded by
`totalWeight K * log #ι + logHeight A + logHeight x`.

(Note that here we do not need to assume that `ι` is nonempty, due to the convenient
junk value `log 0 = 0`.) -/
theorem logHeight_linearMap_apply_le (A : ι' × ι → K) (x : ι → K) :
    logHeight (fun j ↦ ∑ i, A (j, i) * x i) ≤
      totalWeight K * log (Nat.card ι) + logHeight A + logHeight x := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · suffices 0 ≤ logHeight A + logHeight x by simp
    positivity
  simp only [logHeight_eq_log_mulHeight]
  have : (Nat.card ι : ℝ) ^ totalWeight K ≠ 0 := by simp
  pull (disch := first | assumption | positivity) log
  exact (log_le_log <| by positivity) <| mulHeight_linearMap_apply_le ..

end Height

end
