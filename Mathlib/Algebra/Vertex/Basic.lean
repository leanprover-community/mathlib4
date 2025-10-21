/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/

import Mathlib.Algebra.Vertex.Defs

/-!
# Basic results on Vertex algebras
In this file we prove some basic results about vertex algebras.
## Main results
* Associativity is equivalent to a special case of the Borcherds identity.
* The commutator formula is equivalent to a special case of the Borcherds identity.
## To do
In the non-unital setting:
* Locality is equivalent to a special case of the Borcherds identity.
* Weak associativity is equivalent to a special case of the Borcherds identity.
* Borcherds identity from (commutator or locality) and (associativity or weak associativity)
In the unital setting:
* Skew-symmetry is equivalent to a special case of the Borcherds identity.
* Hasse-Schmidt differential
* creative fields?
* reconstruction?
## References
G. Mason `Vertex rings and Pierce bundles` ArXiv 1707.00328
Matsuo-Nagatomo `On axioms for a vertex algebra and the locality of quantum fields` ArXiv
  hep-th/9706118
Borcherds
-/

theorem Int.toNat_sub_eq_zero_leq {m n : ℤ} : Int.toNat (-m - n) = 0 ↔ -n ≤ m := by
  simp only [Int.toNat_eq_zero, tsub_le_iff_right, zero_add]
  exact neg_le

theorem Int.neg_sub_one_sub_nat (i : ℕ) (r s t : ℤ) (h : i ≤ t) :
    -r - s - ↑(Int.toNat t - i) = ↑i - (r + Int.toNat t) - s := by
  rw [Nat.cast_sub ((Int.le_toNat (le_trans (Int.natCast_nonneg i) h)).mpr h),
    sub_eq_sub_iff_add_eq_add, Int.sub_add_cancel, sub_add_sub_cancel', sub_add_cancel_right]

theorem Int.neg_one_pow_sub (n i : ℕ) (hi : i ≤ n) : (-1) ^ (n - i) = (-1) ^ n * (-1) ^ i := by
  refine Int.eq_of_mul_eq_one ?_
  rw [← pow_add, ← pow_add, add_rotate', Nat.add_sub_of_le hi, Even.neg_pow (Even.add_self n),
    one_pow]

--#find_home Int.neg_sub_one_sub_nat

/-! Perhaps this theorem should wait until we have more API for formal power series.
theorem conv_pow_succ_X_sub_Y (A : Type*) [AddCommGroup A] (k l n : ℕ) (f : ℤ → ℤ → A) :
    (Finset.sum (Finset.antidiagonal (n + 1)) fun m ↦ (-1) ^ m.2 • Nat.choose (n + 1) m.2 •
    f (k - ↑m.1) (l - ↑m.2)) = Finset.sum (Finset.antidiagonal n) fun m ↦ (-1) ^ m.2 •
    Nat.choose n m.2 • f (k - ↑m.1 - 1) (l - ↑m.2) - Finset.sum (Finset.antidiagonal n) fun m ↦
    (-1) ^ m.2 • Nat.choose n m.2 • f (k - ↑m.1) (l - ↑m.2 - 1) := by
  -- left side is convolution with `(X-Y)^{n+1}`, right side is with `(X-Y)^n` then `(X-Y)`.
  sorry
-/
variable {R : Type*} {V : Type*}

namespace VertexAlg

open HVertexOperator VertexOperator

section VertexOperator

variable [CommRing R] [AddCommGroup V] [Module R V]

end VertexOperator

section NonUnital

variable [CommRing R] [AddCommGroup V] [Module R V] (Y : stateField R V)

theorem associativity_left (a b c : V) (s t : ℤ) : Borcherds_sum_1 Y a b c 0 s t =
    ncoeff (Y (ncoeff (Y a) t b)) s c := by
  unfold Borcherds_sum_1
  cases h : (Int.toNat (-t - order Y a b)) with
    | zero =>
      rw [Finset.range_zero, Finset.sum_empty]
      rw [ncoeff_zero_if_neg_order_leq Y a b t (Int.toNat_sub_eq_zero_leq.mp h), LinearMap.map_zero]
      exact rfl
    | succ n =>
      rw [Finset.eventually_constant_sum ?_ (Nat.one_le_iff_ne_zero.mpr
        (Nat.succ_ne_zero n)), Finset.sum_range_one, zero_add, Ring.choose_zero_right (0 : ℤ),
        one_smul, Nat.cast_zero, add_zero, sub_zero]
      intro i hi
      rw [Ring.choose_zero_pos ℤ (Nat.ne_zero_iff_zero_lt.mp <| Nat.one_le_iff_ne_zero.mp <| hi),
          zero_smul]

theorem associativity_right (a b c : V) (s t : ℤ) : Borcherds_sum_2 Y a b c 0 s t +
    Borcherds_sum_3 Y a b c 0 s t = Finset.sum (Finset.range (Int.toNat (-s - order Y b c)))
    (fun i ↦ (-1)^i • (Ring.choose (t : ℤ) i) • ncoeff (Y a) (t-i) (ncoeff (Y b) (s+i) c)) +
    Finset.sum (Finset.range (Int.toNat (- order Y a c))) (fun i ↦ (-1: ℤˣ)^(t+i+1) •
    (Ring.choose t i) • ncoeff (Y b) (s+t-i) (ncoeff (Y a) i c)) := by
  unfold Borcherds_sum_2 Borcherds_sum_3
  simp only [neg_zero, zero_sub, zero_add]

theorem Borcherds_id_at_zero_iff_associativity (a b c : V) (s t : ℤ) :
    Borcherds_id Y a b c 0 s t ↔ associativity Y a b c s t := by
  unfold Borcherds_id
  rw [associativity_left, associativity_right]
  exact Eq.congr rfl rfl

theorem commutator_right_2 (a b c : V) (r s : ℤ) : Borcherds_sum_2 Y a b c r s 0 =
    ncoeff (Y a) r (ncoeff (Y b) s c) := by
  unfold Borcherds_sum_2
  cases h : (Int.toNat (-s - order Y b c)) with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty]
    rw [ncoeff_zero_if_neg_order_leq Y b c s (Int.toNat_sub_eq_zero_leq.mp h), LinearMap.map_zero]
  | succ n =>
    rw [Finset.eventually_constant_sum ?_ (Nat.one_le_iff_ne_zero.mpr
        (Nat.succ_ne_zero n)), Finset.sum_range_one, add_zero, Ring.choose_zero_right (0 : ℤ),
        one_smul, Nat.cast_zero, add_zero, sub_zero, pow_zero, one_smul]
    intro i hi
    rw [Ring.choose_zero_pos ℤ (Nat.ne_zero_iff_zero_lt.mp <| Nat.one_le_iff_ne_zero.mp <| hi),
      zero_smul, smul_zero]

theorem commutator_right_3 (a b c : V) (r s : ℤ) : Borcherds_sum_3 Y a b c r s 0 =
    -ncoeff (Y b) s (ncoeff (Y a) r c) := by
  unfold Borcherds_sum_3
  cases h : (Int.toNat (-r - order Y a c)) with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty, ncoeff_zero_if_neg_order_leq Y a c r
      (Int.toNat_sub_eq_zero_leq.mp h), LinearMap.map_zero, neg_zero]
  | succ n =>
    rw [Finset.eventually_constant_sum ?_ (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)),
        Finset.sum_range_one, add_zero, Ring.choose_zero_right (0 : ℤ), one_smul, Nat.cast_zero,
        add_zero, sub_zero, zero_add, add_zero, zpow_one, Units.neg_smul, one_smul]
    intro i hi
    rw [Ring.choose_zero_pos ℤ (Nat.ne_zero_iff_zero_lt.mp <| Nat.one_le_iff_ne_zero.mp <| hi),
        zero_smul, smul_zero]

theorem Borcherds_id_at_zero_iff_commutator_formula (a b c : V) (r s : ℤ) :
    Borcherds_id Y a b c r s 0 ↔ commutator_formula Y a b c r s := by
  unfold Borcherds_id commutator_formula Borcherds_sum_1
  rw [commutator_right_2, commutator_right_3, ← sub_eq_add_neg, neg_zero, zero_sub]
  simp_rw [zero_add]
  exact eq_comm

theorem Borcherds_sum_1_eq_zero (a b c : V) (r s t : ℤ) (h : -order Y a b ≤ t) :
    Borcherds_sum_1 Y a b c r s t = 0 := by
  unfold Borcherds_sum_1
  have hrange : Int.toNat (-t - order Y a b) = 0 := by
    rw [Int.toNat_eq_zero, tsub_le_iff_right, zero_add, neg_le]
    exact h
  rw [hrange, Finset.range_zero, Finset.sum_empty]

theorem locality_left_eq_Borcherds_sum_2 (a b c : V) (r s : ℤ) :
    (Finset.sum (Finset.antidiagonal (Int.toNat (-s - order Y b c))) fun m ↦
    (-1) ^ m.2 • Nat.choose (Int.toNat (-s - order Y b c)) m.2 •
    (HVertexOperator.coeff (Y a) (-r - 1 - m.1))
    ((HVertexOperator.coeff (Y b) (-s - 1 - m.2)) c)) =
    Borcherds_sum_2 Y a b c r s (Int.toNat (-s - order Y b c)) := by
  unfold Borcherds_sum_2 ncoeff
  rw [Finset.Nat.antidiagonal_eq_map']
  simp_all only [Finset.sum_map, Function.Embedding.coeFn_mk]
  rw [Finset.eventually_constant_sum ?_ (Nat.le_succ (Int.toNat (-s - order Y b c)))]
  · refine Finset.sum_congr rfl ?_
    intro i hi
    simp_all only [Finset.mem_range, Int.reduceNeg, neg_sub, LinearMap.coe_mk, AddHom.coe_mk]
    congr 1
    rw [Ring.choose_natCast, natCast_zsmul]
    congr 1
    rw [Int.neg_sub_one_sub_nat i r 1 (-s - order Y b c) (le_of_lt (Int.lt_toNat.mp hi)),
      show -s - 1 - i = -i + -s - 1 by omega]
    congr 1
    rw [Int.neg_add, Int.add_comm]
  intro i hi
  have h : (HVertexOperator.coeff (Y b) (-s - 1 - ↑i)) c = 0 := by
    refine coeff_zero_if_lt_order Y b c ?_ ?_
    simp_all only [ge_iff_le, Int.toNat_le, tsub_le_iff_right]
    linarith
  rw [h, LinearMap.map_zero, smul_zero, smul_zero]

theorem locality_right_eq_Borcherds_sum_3 (a b c : V) (r s : ℤ) : Finset.sum (Finset.antidiagonal
    (Int.toNat (-r - order Y a c))) (fun m => -(-1)^(m.2) • (Nat.choose (Int.toNat
    (-r - order Y a c)) m.2) • HVertexOperator.coeff (Y b) (-s - 1 - m.2)
    (HVertexOperator.coeff (Y a) (-r - 1 - m.1) c)) =
    Borcherds_sum_3 Y a b c r s (Int.toNat (-r - order Y a c)) := by
  unfold Borcherds_sum_3 ncoeff
  rw [Finset.Nat.antidiagonal_eq_map]
  simp_all only [Finset.sum_map, Function.Embedding.coeFn_mk]
  rw [Finset.eventually_constant_sum ?_ (Nat.le_succ (Int.toNat (-r - order Y a c)))]
  · refine Finset.sum_congr rfl ?_
    intro i hi
    simp_all only [Finset.mem_range, Int.reduceNeg, coeff_apply_apply, neg_smul,
      LinearMap.coe_mk, AddHom.coe_mk, neg_sub, neg_add_rev]
    have : (-1) ^ ((-r - order Y a c).toNat - i) = (-1) ^ (-r - order Y a c).toNat * (-1) ^ i :=
      Int.neg_one_pow_sub (-r - order Y a c).toNat i <| Nat.le_of_succ_le hi
    rw [this, ← Units.coe_neg_one]
    simp only [← Int.negOnePow_def]
    rw [Int.negOnePow_add, mul_comm _ (Int.negOnePow 1), ← smul_smul (Int.negOnePow 1),
      Int.negOnePow_one]
    simp only [Units.val_neg, Units.val_one, Int.reduceNeg, Units.neg_smul, one_smul, neg_inj]
    congr 1
    · rw [Int.negOnePow_add]
      rfl
    · rw [Ring.choose_natCast]
      norm_cast
      congr 1
      · rw [Nat.choose_symm (Nat.le_of_succ_le hi)]
      · rw [Int.neg_sub_one_sub_nat i s 1 (-r - order Y a c) (le_of_lt (Int.lt_toNat.mp hi)),
          show -r - 1 - i = -i + -r - 1 by linarith]
  intro i hi
  have h : (HVertexOperator.coeff (Y a) (-r - 1 - ↑i)) c = 0 := by
    refine coeff_zero_if_lt_order Y a c ?_ ?_
    simp_all only [ge_iff_le, Int.toNat_le, tsub_le_iff_right]
    linarith
  rw [h, LinearMap.map_zero, smul_zero, smul_zero]

/-!
theorem locality_if_Borcherds_sums_2_3_eq (a b : V) (h : ∀ (c : V) (r s : ℤ)
    (t : ℕ), Int.toNat (-s - order R b c) ≤ t → Int.toNat (-r - order R a c) ≤ t →
    Borcherds_sum_2 R a b c r s t = Borcherds_sum_3 R a b c r s t) : locality R a b := by
  unfold locality isLocal isLocalToOrderLeq
  --
--  rw [locality_right_eq_Borcherds_sum_3 a b c ]
  sorry
theorem Borcherds_sums_2_3_eq_if_locality (a b c : V) (r s t : ℤ)
    (h₂ : Int.toNat (-s - order R b c) ≤ t) (h₃ : Int.toNat (-r - order R a c) ≤ t)
    (h : locality R a b) : Borcherds_sum_2 R a b c r s t = Borcherds_sum_3 R a b c r s t := by
  --rw [← locality_right_eq_Borcherds_sum_3, ]
  sorry
theorem Borcherds_id_at_large_t_iff_locality (a b c : V) (r s t : ℤ) (h : - order R a b ≤ t) :
    Borcherds_id R a b c r s t ↔ locality R a b := by
  unfold Borcherds_id locality isLocal
  rw [locality_left a b c r s t h]
  --need more
  exact eq_comm
-/

theorem weak_assoc_right (a b c : V) (r s t : ℤ) (h : r ≥ -order Y a c) :
    Borcherds_sum_3 Y a b c r s t = 0 := by
  unfold Borcherds_sum_3
  have hrange : Int.toNat (-r - order Y a c) = 0 := by
    rw [Int.toNat_eq_zero, tsub_le_iff_right, zero_add, neg_le]
    exact h
  rw [hrange, Finset.range_zero, Finset.sum_empty]

-- need to revise weak associativity : pairs of fields are weakly associative

theorem Borcherds_id_at_large_r_iff_weak_assoc (a b c : V) (r s t : ℤ) (h : r ≥ -order Y a c) :
    Borcherds_id Y a b c r s t ↔ weak_associativity Y a b c r s t := by
  unfold Borcherds_id weak_associativity
  rw [weak_assoc_right Y a b c r s t h, add_zero]

theorem toNat_eq_sub_toNat_add (t : ℤ) (n : ℕ) (h : Int.toNat t = Nat.succ n) :
    Int.toNat t = Int.toNat (t - 1) + 1 := by
  rw [Int.pred_toNat, h, Nat.succ_sub_succ_eq_sub, tsub_zero]

theorem toNat_neg_sub_eq_zero (x y : ℤ) (h : Int.toNat (-x - y) = Nat.zero) :
    Int.toNat (-(x + 1) - y) = 0 := by
  rw [Int.toNat_eq_zero] at h
  rw [Int.toNat_eq_zero]
  linarith

theorem toNat_neg_succ_sub_eq_Nat (x y : ℤ) (n : ℕ) (h : Int.toNat (-x - y) = n.succ) :
    Int.toNat (-(x + 1) - y) = n := by
  rw [toNat_eq_sub_toNat_add _ n h, ← Nat.add_one, Nat.add_right_cancel_iff] at h
  rw [neg_add', sub_right_comm]
  exact h

/-!
theorem borcherds1Recursion
    (a b c : V) (r s t : ℤ) : Borcherds_sum_1 R a b c (r + 1) s t =
    Borcherds_sum_1 R a b c r (s + 1) t + Borcherds_sum_1 R a b c r s (t + 1) := by
  unfold Borcherds_sum_1
  cases h : (Int.toNat (-t - order R a b)) with
  | zero =>
    simp only [toNat_neg_sub_eq_zero t _ h, Finset.range_zero, Finset.sum_empty, zero_add]
  | succ n =>
    simp_rw [Finset.sum_range_succ', Nat.add_one, Ring.choose_succ_succ, add_smul]
    rw [Finset.sum_add_distrib, add_assoc, add_comm]
    have h1 : (-1 + -t - order R a b).toNat = n := by omega
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_assoc r 1 s,
      Ring.choose_zero_right', pow_zero, CharP.cast_eq_zero, add_zero, sub_zero, one_smul,
      add_comm s 1, neg_add_rev, Int.reduceNeg, h1, add_assoc t 1, add_right_inj]
    congr
    ext n
    have h2 : r + (1 + s) - (n + 1) = r + s - n := by omega
    rw [h2, add_comm _ 1]

theorem borcherds2Recursion
    (a b c : V) (r s t : ℤ) : Borcherds_sum_2 R a b c (r + 1) s t =
    Borcherds_sum_2 R a b c r (s + 1) t + Borcherds_sum_2 R a b c r s (t + 1) := by
  unfold Borcherds_sum_2
  cases h : (Int.toNat (-s - order R b c)) with
    | zero =>
      simp only [toNat_neg_sub_eq_zero s _ h, Finset.range_zero, Finset.sum_empty, zero_add]
    | succ n =>
      simp_rw [Finset.sum_range_succ', Nat.add_one, Ring.choose_succ_succ, add_smul, smul_add]
      rw [Finset.sum_add_distrib, ← add_assoc]
      simp
      · refine eq_add_of_sub_eq' ?_
        rw [sub_eq_neg_add]
        refine Mathlib.Tactic.LinearCombination.add_pf ?_ ?_
        · rw [← Finset.sum_neg_distrib]
          rw [← toNat_neg_succ_sub_eq_Nat _ _ _ h]
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [Nat.cast_succ, smul_algebra_smul_comm, smul_algebra_smul_comm,
            ← neg_smul, ← Nat.add_one k, add_comm k 1, pow_add, pow_one, neg_one_mul]
          have h₂ : r + (t + 1) - (k + 1) = r + t - k := by linarith
          rw [h₂, add_assoc, add_comm 1 _] -- end first sum
        rw [add_assoc, add_comm 1 t] --end second sum
      rw [Ring.choose_zero_right (t + 1), Ring.choose_zero_right t, add_assoc, add_comm 1 t]

theorem borcherds3Recursion
    (a b c : V) (r s t : ℤ) : Borcherds_sum_3 R a b c (r + 1) s t =
    Borcherds_sum_3 R a b c r (s + 1) t + Borcherds_sum_3 R a b c r s (t + 1) := by
  unfold Borcherds_sum_3
  cases h : (Int.toNat (-r - order R a c)) with
    | zero =>
      simp only [toNat_neg_sub_eq_zero r _ h, Finset.range_zero, Finset.sum_empty, zero_add]
    | succ n =>
      rw [add_assoc]
      refine eq_add_of_sub_eq' ?_
      simp_rw [Finset.sum_range_succ', Nat.add_one, Ring.choose_succ_succ, add_smul, smul_add]
      rw [Finset.sum_add_distrib, sub_eq_add_neg, neg_add, neg_add, add_assoc, add_assoc]
      refine Mathlib.Tactic.LinearCombination.add_pf ?_ ?_
      · rw [← neg_add, toNat_neg_succ_sub_eq_Nat _ _ _ h]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [← Nat.add_one, Nat.cast_add, Nat.cast_one, show (-1:ℤˣ)^(t + 1 + (i + 1) + 1) =
          (-1)^(t + i + 1) by simp only [zpow_add, zpow_one, mul_neg, mul_one, zpow_natCast,
          neg_mul, neg_neg], show r + 1 + i =r + (i + 1) by linarith,
          show s + (t + 1) - (i + 1) = s + t - i by linarith] -- end first sum
      refine Mathlib.Tactic.LinearCombination.add_pf ?_ ?_
      · rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [← Nat.add_one, Nat.cast_add, Nat.cast_one, ← Units.neg_smul, neg_eq_neg_one_mul,
          mul_self_zpow, add_comm 1 t, add_right_comm t 1 _] -- end second sum
      rw [← Units.neg_smul, neg_eq_neg_one_mul, mul_self_zpow, add_comm 1 t]
      simp only [Ring.choose_zero_right, Nat.cast_zero, add_zero, zero_add] -- end third sum
-/
-- theorem Borcherds on r s+1 t, r s t+1 implies r+1 s t (and two other versions)

-- theorem Borcherds_on_r_hyperplane_implies_r_half_space (and two other versions)

-- theorem Borcherds_on_two_transverse_half_spaces_implies Borcherds_everywhere
  -- induct on maximal distance from r s t to union of half-spaces?
  -- Or, use induction on ℕ × ℕ


--theorem te (t : ℤ) (i : ℕ) : -1 * (-1) ^ (t + (i + 1) + 1) = (-1:ℤˣ) ^ (t + 1 + (i + 1) + 1) := by


end NonUnital

section Unital

/-!
theorem vacuum_derivative_is_zero [AddCommGroup V] [UnboundedVertexMul V] [NonunitalVertexRing V] :
    T 1 1 = 0 := by
--  refine NonunitalVertexRing.borcherds_id vac vac vac -1 -1 -1
-- set u=v=w = vac, r=s=t=-1 to get
  vac_{-2}vac = vac_{-2}(vac_{-1}vac) + vac_{-2}(vac_{-1}vac) = 2vac_{-2}vac
-- theorem vacuum_products_vanish : Y n vac vac = 0 when n ≠-1: for n ≥ 0, this is from van_vac.
For n < -1, we use induction: u=v=w=vac, r=s = -1, t=n.
-- theorem left identity : Y n vac u = u if n = -1, and 0 if not := Borcherds with v = w = vac,
r = -1, t = 0.
-- theorem unit_left (R : Type v) [CommRing R] [AddCommGroupWithOne V] [VertexAlgebra R V] (a : V) :
theorem skew_symmetry_iff_Borcherds_at_zero
-/
end Unital

end VertexAlg
