/-
Copyright (c) 2024 F. Nuccio, H. Zheng, W. He, S. Wu, Y. Yuan, W. Jiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Huanyu Zheng, Sihan Wu, Wanyi He, Weichen Jiao, Yi Yuan
-/
import Mathlib.Algebra.CharP.LinearMaps
import Mathlib.Algebra.CharP.Subring
import Mathlib.Algebra.Field.Power
import Mathlib.FieldTheory.PurelyInseparable

/-!
# The Jacobson-Noether theorem

This file contains a proof of the Jacobson-Noether theorem and some auxiliary lemmas.
Here we discuss different cases of characteristics of
the noncommutative division algebra `D` with center `k`.

## Main Results

- `exists_separable_mem_of_not_central` : (Jacobson-Noether theorem) For a
  non-commutative algebraic division algebra `D` (with base ring
  being its center `k`), if `k ≠ D`, then there exist an element `x` of
  `D \ k` that is separable over its center.
- `exists_separable_mem_of_not_central'` : (Jacobson-Noether theorem) For a
  non-commutative algebraic division algebra `D` (with base ring
  being a field `L`), if the center of `D` over `L` is `L` and `L ≠ D`,
  then there exist an element `x` of `D \ L` that is separable over `L`.

## Notations

- `D` is a noncommutative division algebra
- `k` is the center of `D`

## Implementation Notes

Mathematically, `exists_separable_mem_of_not_central` and `exists_separable_mem_of_not_central'`
are equivalent.

The difference however, is that the former takes `D` as the only variable
and fixing `D` would forces `k`. Whereas the later takes `D` and `L` as
separate variables constrained by certain relations.

## Reference
* <https://ysharifi.wordpress.com/2011/09/30/the-jacobson-noether-theorem/>
-/

namespace JacobsonNoether

variable {D : Type*} [DivisionRing D]

open LinearMap

local notation3 "k" => (Subring.center D)
private def δ : D → D →ₗ[k] D := mulLeft k - mulRight k

private lemma δ_def (a x : D) : δ a x = mulLeft k a x - mulRight k a x := rfl

private lemma l_pow (a : D) (n : ℕ) : ∀ x : D, ((mulLeft k a) ^ n) x = (a ^ n) * x := by
  intro x
  rw [pow_apply]
  induction n with
  | zero => rw [Function.iterate_zero, id_eq, pow_zero, one_mul]
  | succ _ h => rw [Function.iterate_succ', Function.comp_apply, h,
    pow_succ', mul_assoc, mulLeft_apply]

private lemma r_pow (a : D) (n : ℕ) : ∀ x : D, ((mulRight k a) ^ n) x = x * (a ^ n) := by
  intro x
  rw [pow_apply]
  induction n with
  | zero => rw [Function.iterate_zero, id_eq, pow_zero, mul_one]
  | succ _ h => rw [Function.iterate_succ', Function.comp_apply, h,
    pow_add, pow_one, mulRight_apply, mul_assoc]

private lemma δ_iterate_succ (x y : D) (n : ℕ) :
    δ x (((δ x) ^ n) y) = ((δ x) ^ (n + 1)) y := by
  simp only [pow_apply, δ_def, mulLeft_apply, mulRight_apply, Function.iterate_succ_apply']

variable [Algebra.IsAlgebraic (Subring.center D) D]

open Polynomial

/-- If `D` is a purely inseparable extension of `k` with characteristic `p`,
  then for every element `a` of `D`, there exists a natural number `n`
  such that `a ^ (p ^ n)` is contained in `k`. -/
lemma exists_pow_mem_center_of_inseparable (p : ℕ) [hchar : ExpChar D p] (a : D)
    (hinsep : ∀ x : D, IsSeparable k x → x ∈ k) : ∃ n, a ^ (p ^ n) ∈ k := by
  have := (@isPurelyInseparable_iff_pow_mem k D _ _ _ _ p (ExpChar.center_expChar_iff.1 hchar)).1
  have pure : IsPurelyInseparable k D := ⟨Algebra.IsAlgebraic.isIntegral, fun x hx ↦ by
    rw [RingHom.mem_range, Subtype.exists]
    exact ⟨x, ⟨(hinsep x hx), rfl⟩⟩⟩
  obtain ⟨n, ⟨m, hm⟩⟩ := (this pure) a
  have := Subalgebra.range_subset (R := k) ⟨(k).toSubsemiring, by intro r; exact r.2⟩
  exact ⟨n, Set.mem_of_subset_of_mem this <| Set.mem_range.2 ⟨m, hm⟩⟩

/-- If `D` is a purely inseparable extension of `k` with characteristic `p`,
  then for every element `a` of `D \ k`, there exists a natural number `n`
  **greater than 0** such that `a ^ (p ^ n)` is contained in `k`. -/
lemma exists_pow_mem_center_of_inseparable' (p : ℕ) [ExpChar D p] {a : D}
    (ha : a ∉ k) (hinsep : ∀ x : D, IsSeparable k x → x ∈ k) : ∃ n ≥ 1, a ^ (p ^ n) ∈ k := by
  obtain ⟨n, hn⟩ := exists_pow_mem_center_of_inseparable p a hinsep
  by_cases nzero : n = 0
  · rw [nzero, pow_zero, pow_one] at hn
    exact (ha hn).elim
  · exact ⟨n, ⟨by omega, hn⟩⟩

/-- If `D` is a purely inseparable extension of `k` of characteristic `p`,
  then for every element `a` of `D \ k`, there exists a natural number `m`
  greater than 0 such that `(a * x - x * a) ^ n = 0` (as linear maps) for
  every `n` greater than `(p ^ m)`. -/
lemma exist_pow_eq_zero_of_le (p : ℕ) [hchar : ExpChar D p]
    {a : D} (ha : a ∉ k) (hinsep : ∀ x : D, IsSeparable k x → x ∈ k):
  ∃ m ≥ 1, ∀ n ≥ (p ^ m), (δ a) ^ n = 0 := by
  obtain ⟨m, hm⟩ := exists_pow_mem_center_of_inseparable' p ha hinsep
  refine ⟨m, ⟨hm.1, fun n hn ↦ ?_⟩⟩
  have inter : (δ a) ^ (p ^ m) = 0 := by
    ext x
    rw [δ, Pi.sub_apply, sub_pow_expChar_pow_of_commute p m (commute_mulLeft_right a a)]
    rw [sub_apply, l_pow, r_pow, sub_eq_zero_of_eq]; rfl
    suffices h : a ^ (p ^ m) ∈ k from (Subring.mem_center_iff.1 h x).symm
    exact hm.2
  rw [((Nat.sub_eq_iff_eq_add hn).1 rfl), pow_add, inter, mul_zero]

variable (D) in
/-- Jacobson-Noether theorem: For a non-commutative algebraic
  division algebra `D` (with base ring being its center `k`), if `k ≠ D`, then
  there exist an element `x` of `D \ k` that is separable over its center.-/
theorem exists_separable_mem_of_not_central (H : k ≠ (⊤ : Subring D)) :
    ∃ x : D, x ∉ k ∧ IsSeparable k x := by
  obtain ⟨p, hp⟩ := ExpChar.exists D
  by_contra! insep
  replace insep : ∀ x : D, IsSeparable k x → x ∈ k :=
    fun x h ↦ Classical.byContradiction fun hx ↦ insep x hx h
  -- The element `a` below is in `D` but not in `k`.
  obtain ⟨a, ha⟩ := not_forall.mp <| mt (Subring.eq_top_iff' k).mpr H
  have ha₀ : a ≠ 0 := fun nh ↦ nh ▸ ha <| Subring.zero_mem k
  -- We construct another element `b` that does not commute with `a`.
  obtain ⟨b, hb1⟩ : ∃ b : D , (δ a) b ≠ 0 := by
    rw [Subring.mem_center_iff, not_forall] at ha
    use ha.choose
    show a * ha.choose - ha.choose * a ≠ 0
    simpa only [ne_eq, sub_eq_zero] using Ne.symm ha.choose_spec
  -- We find a maximum natural number `n` such that `(δ a) ^ n b ≠ 0`.
  obtain ⟨n, hn, hb⟩ : ∃ n, (0 < n) ∧ ((δ a) ^ n) b ≠ 0 ∧ ((δ a) ^ (n + 1)) b = 0 := by
    obtain ⟨m, -, hm2⟩ := exist_pow_eq_zero_of_le p ha insep
    have h_exist : ∃ n > 0, ((δ a) ^ (n + 1)) b = 0 := ⟨(p ^ m),
      ⟨expChar_pow_pos D p m, by rw [hm2 (p ^ m + 1) (by omega)]; rfl⟩⟩
    classical
    refine ⟨Nat.find h_exist, ⟨(Nat.find_spec h_exist).1, ?_, (Nat.find_spec h_exist).2⟩⟩
    set t := (Nat.find h_exist - 1 : ℕ) with ht
    by_cases h_pos : 0 < t
    · convert (ne_eq _ _) ▸ not_and.mp (Nat.find_min h_exist (m := t) (by omega)) h_pos
      omega
    · suffices h_find: Nat.find h_exist = 1 by
        rwa [h_find, pow_one]
      rw [not_lt, Nat.le_zero, ht, Nat.sub_eq_zero_iff_le] at h_pos
      linarith [(Nat.find_spec h_exist).1]
  -- We define `c` to be the value that we proved above to be non-zero.
  set c := ((δ a) ^ n) b with hc_def
  letI : Invertible c := ⟨c⁻¹, inv_mul_cancel₀ (hb.1), mul_inv_cancel₀ (hb.1)⟩
  -- We prove that `c` commutes with `a`.
  have hc : a * c = c * a := by
    apply eq_of_sub_eq_zero
    rw [← mulLeft_apply (R := k), ← mulRight_apply (R := k),
      ← δ_def, δ_iterate_succ a b n, hb.2]
  -- We now make some computation to obtain the final equation.
  set d := c⁻¹ * a * ((δ a) ^ (n - 1)) b with hd_def
  have hc': c⁻¹ * a = a * c⁻¹ := by
    apply_fun (c⁻¹ * · * c⁻¹) at hc
    rw [mul_assoc, mul_assoc, mul_inv_cancel₀ hb.1, mul_one, ← mul_assoc,
      inv_mul_cancel₀ hb.1, one_mul] at hc
    exact hc
  have c_eq : a * ((δ a) ^ (n - 1)) b - ((δ a) ^ (n - 1)) b * a = c := by
    rw [hc_def, ← Nat.sub_add_cancel hn, ← δ_iterate_succ, δ_def]; rfl
  have eq1 : c⁻¹ * a * ((δ a)^ (n - 1)) b - c⁻¹ * ((δ a) ^ (n - 1)) b * a = 1 := by
    simp_rw [mul_assoc, (mul_sub_left_distrib c⁻¹ _ _).symm, c_eq, inv_mul_cancel_of_invertible]
  -- We show that `a` commutes with `d`.
  have deq : a * d - d * a = a := by
    nth_rw 3 [← mul_one a]
    rw [hd_def, ← eq1, mul_sub, mul_assoc _ _ a, sub_right_inj, hc',
      ← mul_assoc, ← mul_assoc, ← mul_assoc]
  -- This then derives a contradiction.
  apply_fun (a⁻¹ * · ) at deq
  rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ ha₀, one_mul, ← mul_assoc, sub_eq_iff_eq_add] at deq
  obtain ⟨r, hr⟩ := (exists_pow_mem_center_of_inseparable p d insep)
  apply_fun (· ^ (p ^ r)) at deq
  rw [add_pow_expChar_pow_of_commute p r (Commute.one_left _) , one_pow,
    ← DivisionSemiring.conj_pow ha₀, ← hr.comm, mul_assoc, inv_mul_cancel₀ ha₀, mul_one,
    self_eq_add_left] at deq
  exact one_ne_zero deq

open Subring Algebra in
/-- Jacobson-Noether theorem: For a non-commutative algebraic
  division algebra `D` (with base ring being a field `L`), if the center of
  `D` over `L` is `L` and `L ≠ D`, then there exist an element `x` of `D \ L`
  that is separable over `L`.-/
theorem exists_separable_mem_of_not_central' {L D : Type*} [Field L] [DivisionRing D]
    [Algebra L D] [Algebra.IsAlgebraic L D]
    (hcenter : Subalgebra.center L D = ⊥) (hneq : (⊥ : Subalgebra L D) ≠ ⊤) :
    ∃ x : D, x ∉ (⊥ : Subalgebra L D) ∧ IsSeparable L x := by
  have ntrivial : center D ≠ ⊤ :=
    congr(Subalgebra.toSubring $hcenter).trans_ne (Subalgebra.toSubring_injective.ne hneq)
  set φ := Subalgebra.equivOfEq (⊥ : Subalgebra L D) (Subalgebra.center L D) hcenter.symm
  set equiv : L ≃+* (center D) := (((botEquiv L D).symm).trans φ).toRingEquiv
  letI : Algebra L (center D) := equiv.toRingHom.toAlgebra
  letI : Algebra (center D) L := equiv.symm.toRingHom.toAlgebra
  haveI : IsScalarTower L (center D) D := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower (center D) L D := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply L (center D)]
    congr
    exact (equiv.apply_symm_apply x).symm
  haveI : Algebra.IsAlgebraic (center D) D := .tower_top (K := L) _
  obtain ⟨x, hxd, hx⟩ := exists_separable_mem_of_not_central D ntrivial
  refine ⟨x, ⟨by rwa [← Subalgebra.center_toSubring L, hcenter] at hxd, IsSeparable.tower_top _ hx⟩⟩

end JacobsonNoether
