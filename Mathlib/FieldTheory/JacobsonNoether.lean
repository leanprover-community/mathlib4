/-
Copyright (c) 2024 Filippo A. E. Nuccio, Huanyu Zheng, Wanyi He, Sihan Wu, Weichen Jiao, Yi Yuan.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Huanyu Zheng, Sihan Wu, Wanyi He, Weichen Jiao, Yi Yuan
-/
import Mathlib.RingTheory.Algebraic
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.CharP.Subring
import Mathlib.Algebra.CharP.LinearMaps

/-!
# The Jacobson-Noether theorem

This file contains a proof of the Jacobson-Noether theorem and some auxiliary lemmas.
Here we discuss different cases of characteristics of
the noncommutative division algebra `D` with the center `k`.

## Main Results

- `Jacobson_Noether` : Let `D` be a noncommutative division algebra with the center `k`.
  If `D` is algebraic over `k`,
  then there exists an element of `D \ k` which is separable over `k`.

## Notations

- `D` is a noncommutative division algebra
- `k` is the center of `D`

## Implementation Notes

## Reference
* <https://ysharifi.wordpress.com/2011/09/30/the-jacobson-noether-theorem/>
-/


/-- a⁻¹ * d ^ s * a = (a⁻¹ * d * a) ^ s when a is not zero -/
lemma conj_nonComm_Algebra {D : Type*} [DivisionRing D] (s : ℕ) (a d : D) (ha : a ≠ 0) :
    a⁻¹ * d ^ s * a = (a⁻¹ * d * a) ^ s := by
  let u : Dˣ := ⟨a, a⁻¹, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha⟩
  exact (Units.conj_pow' u d s).symm

namespace JacobsonNoether

variable {D : Type*} [DivisionRing D]

local notation3 "k" => (Subring.center D)

instance : Algebra (Subring.center D) D := Algebra.ofModule smul_mul_assoc mul_smul_comm

private def f (a : D) : D →ₗ[k] D := {
  toFun := fun x ↦ a * x
  map_add' := fun x y ↦ LeftDistribClass.left_distrib a x y
  map_smul' := fun m x ↦ by simp only [mul_smul_comm, RingHom.id_apply]
}

@[simp]
private lemma f_def (a x : D) : f a x = a * x := rfl

private def g (a : D) : D →ₗ[k] D := {
  toFun := fun x ↦ x * a
  map_add' := fun x y ↦ RightDistribClass.right_distrib x y a
  map_smul' := fun m x ↦ by simp only [smul_mul_assoc, RingHom.id_apply]
}

@[simp]
private lemma g_def (a x : D) : g a x = x * a := rfl

private def δ (a : D) : D →ₗ[k] D := {
  toFun := f a - g a
  map_add' := fun x y ↦ by simp only [Pi.sub_apply, map_add, map_add, add_sub_add_comm]
  map_smul' := fun m x ↦ by simp only [Pi.sub_apply, map_smul, RingHom.id_apply, smul_sub]
}

@[simp]
private lemma δ_def (a x : D) : δ a x = f a x - g a x := rfl

@[simp]
private lemma δ_def' (a : D) : δ a = f a - g a := rfl

private lemma fg_comm (a : D) : Commute (f a) (g a) := by
  rw [commute_iff_eq, LinearMap.mk.injEq, AddHom.mk.injEq]
  exact funext fun x ↦ (mul_assoc a x a).symm

private lemma f_pow (a : D) (n : ℕ) : ∀ x : D, ((f a) ^ n).1 x = (a ^ n) * x := by
  intro x
  rw [LinearMap.coe_toAddHom, LinearMap.pow_apply]
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq, pow_zero, one_mul]
  | succ _ _ => simp only [Subring.center_toSubsemiring, f, LinearMap.coe_mk, AddHom.coe_mk,
      Function.iterate_succ', mul_left_iterate, Function.comp_apply, pow_succ', mul_assoc]

private lemma g_pow (a : D) (n : ℕ) : ∀ x : D, ((g a) ^ n).1 x = x * (a ^ n) := by
  intro x
  rw [LinearMap.coe_toAddHom, LinearMap.pow_apply]
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq, pow_zero, mul_one]
  | succ _ _ => simp only [Subring.center_toSubsemiring, g, LinearMap.coe_mk, AddHom.coe_mk,
      Function.iterate_succ', mul_right_iterate, Function.comp_apply, pow_succ, ← mul_assoc]

private lemma δ_iterate_succ (x y : D) (n : ℕ) :
    δ x (((δ x) ^ n) y) = ((δ x) ^ (n + 1)) y := by
  simp only [LinearMap.pow_apply, δ_def, f_def, g_def, Function.iterate_succ_apply']

variable [Algebra.IsAlgebraic (Subring.center D) D]

open Polynomial Classical

/-- Any inseparable extension is an extension by some p^n th -root -/
lemma exists_pow_mem_center_ofInseparable (p : ℕ) [Fact p.Prime] [CharP D p] (a : D)
    (hinsep : ∀ x : D, IsSeparable k x → x ∈ k) : ∃ n, a ^ (p ^ n) ∈ k := by
  obtain ⟨n, g, hg, geqf⟩ := @exists_separable_of_irreducible k _ p _ (minpoly k a)
    (minpoly.irreducible (Algebra.IsIntegral.isIntegral a)) ((NeZero.ne' p).symm)
  have h1 : (aeval (a ^ p ^ n)) g = 0 := by
    rw [← expand_aeval, congrArg (⇑(aeval a)) geqf, minpoly.aeval k a]
  refine ⟨n, hinsep (a ^ p ^ n) (Separable.of_dvd hg (minpoly.dvd_iff.2 h1))⟩

lemma exists_pow_mem_center_ofInseparable' (p : ℕ) [Fact p.Prime] [CharP D p] {a : D}
    (ha : a ∉ k) (hinsep : ∀ x : D, IsSeparable k x → x ∈ k) : ∃ n ≥ 1, a ^ (p ^ n) ∈ k := by
  obtain ⟨n, hn⟩ := exists_pow_mem_center_ofInseparable p a hinsep
  by_cases nzero : n = 0
  · rw [nzero, pow_zero, pow_one] at hn
    exact False.elim <| ha hn
  · refine ⟨n, ⟨by omega, hn⟩⟩

lemma exist_pow_eq_zero_of_le (p : ℕ) [Fact p.Prime] [CharP D p]
    {a : D} (ha : a ∉ k) (hinsep : ∀ x : D, IsSeparable k x → x ∈ k):
  ∃ m ≥ 1, ∀ n ≥ (p ^ m), (δ a) ^ n = 0 := by
  obtain ⟨m, hm⟩ := exists_pow_mem_center_ofInseparable' p ha hinsep
  refine ⟨m, ⟨hm.1, ?_⟩⟩
  intro n hn
  have inter : (δ a) ^ (p ^ m) = 0 := by
    refine LinearMap.ext_iff.2 ?_
    intro x
    rw [δ_def' a, sub_pow_char_pow_of_commute (D →ₗ[k] D) (f a) (g a) (fg_comm a) (p := p) (n := m)]
    show ((f a) ^ (p ^ m)).1 x - ((g a) ^ (p ^ m)).1 x = 0
    rw [f_pow, g_pow, sub_eq_zero_of_eq]
    suffices h : a ^ (p ^ m) ∈ k from (Subring.mem_center_iff.1 h x).symm
    exact hm.2
  rw [((Nat.sub_eq_iff_eq_add hn).1 rfl), pow_add, inter, mul_zero]

/-- Jacobson-Noether theorem in the `CharP D 0` case -/
theorem JacobsonNoether_charZero [CharP D 0] (h : k ≠ (⊤ : Subring D)) :
    ∃ x : D, x ∉ k ∧ IsSeparable k x := by
  let _ : CharZero k := (CharP.charP_zero_iff_charZero k).mp (by infer_instance)
  obtain ⟨a, ha⟩ := not_forall.mp <| mt (Subring.eq_top_iff' k).mpr h
  exact ⟨a, ⟨ha, (minpoly.irreducible (Algebra.IsIntegral.isIntegral a)).separable⟩⟩

/-- Jacobson-Noether theorem in the `CharP D p` case -/
theorem JacobsonNoether_charP (p : ℕ) [Fact p.Prime] [CharP D p]
    (h : k ≠ (⊤ : Subring D)) : ∃ x : D, x ∉ k ∧ IsSeparable k x := by
  by_contra! insep
  have hinsep : ∀ x : D, IsSeparable k x → x ∈ k :=
    fun x h ↦ Classical.byContradiction fun hx ↦ insep x hx h
  -- The element `a` below is in `D` but not in `k`.
  obtain ⟨a, ha⟩ := not_forall.mp <| mt (Subring.eq_top_iff' k).mpr h
  have ha₀ : a ≠ 0 := fun nh ↦ nh ▸ ha <| Subring.zero_mem k
  -- We construct another element `b` that does not commute with `a`.
  obtain ⟨b, hb1⟩ : ∃ b : D , (δ a) b ≠ 0 := by
    rw [Subring.mem_center_iff, not_forall] at ha
    use ha.choose
    show a * ha.choose - ha.choose * a ≠ 0
    simpa only [ne_eq, sub_eq_zero] using Ne.symm ha.choose_spec
  -- We find a maximum natural number `n` such that `(δ a) ^ n b ≠ 0`.
  obtain ⟨n, hn, hb⟩ : ∃ n > 0, ((δ a) ^ n) b ≠ 0 ∧ ((δ a) ^ (n + 1)) b = 0 := by
    obtain ⟨m, -, hm2⟩ := exist_pow_eq_zero_of_le p ha hinsep
    have exist : ∃ n > 0, ((δ a) ^ (n + 1)) b = 0 := by
      refine ⟨p ^ m, ⟨pow_pos (Nat.Prime.pos (@Fact.out _ _)) m, ?_ ⟩⟩
      simp only [hm2 (p^ m + 1) (by linarith), LinearMap.zero_apply]
    refine ⟨Nat.find exist, ⟨(Nat.find_spec exist).1, ?_, (Nat.find_spec exist).2⟩⟩
    set t := (Nat.find exist - 1 : ℕ) with ht
    by_cases choice : 0 < t
    · have := @Nat.find_min (H := exist) _ t ?_
      · exact (@Nat.sub_add_cancel (Nat.find exist) 1 (by omega) ▸ ht ▸ not_and.1 this) choice
      · exact Nat.sub_one_lt <| ne_of_gt (Nat.find_spec exist).1
    · rw [not_lt, Nat.le_zero] at choice
      have := Nat.eq_add_of_sub_eq (Nat.find_spec exist).1 ht.symm
      simp only [gt_iff_lt, choice, Nat.succ_eq_add_one, zero_add] at this
      rw [this]
      simp only [Function.iterate_one, ne_eq]
      exact hb1
  -- We define `c` to be the value that we proved above to be non-zero.
  set c := ((δ a) ^ n) b with hc_def
  letI : Invertible c := ⟨c⁻¹, inv_mul_cancel₀ (hb.1), mul_inv_cancel₀ (hb.1)⟩
  have hc : c * a = a * c := by
    rw [← f_def a c, ← g_def a c, ← zero_add (g a c)]
    apply add_eq_of_eq_add_neg
    rw[← sub_eq_add_neg, ← δ_def, hc_def, δ_iterate_succ a b n, hb.2]
  -- We now make some computation to obtain the *absurd* equation `final_eq`, contradiction.
  set d := c⁻¹ * a * (δ a) ^[n-1] b with hd_def
  have hc': c⁻¹ * a = a * c⁻¹ := by
    apply_fun (c⁻¹ * · * c⁻¹) at hc
    rw [← mul_assoc, inv_mul_cancel₀ hb.1, one_mul, mul_assoc, mul_assoc,
      mul_inv_cancel₀ hb.1, mul_one] at hc
    exact hc.symm

  have c_eq : a * (δ a) ^[n - 1] b - (δ a) ^[n - 1] b * a = c := by
    rw [hc_def, ← (LinearMap.pow_apply (δ a) (n - 1) b), ← Nat.sub_add_cancel hn,
      show (δ a ^ (n - 1 + 1)) b = (δ a) ((δ a ^ (n - 1)) b) by rw [δ_iterate_succ]]
    simp only [add_tsub_cancel_right, δ_def, f_def, g_def]
  have eq1 : c⁻¹ * a * (δ a)^[n - 1] b - c⁻¹ * (δ a)^[n - 1] b * a = 1 := by
    simp_rw [mul_assoc, (mul_sub_left_distrib c⁻¹ _ _).symm, c_eq, inv_mul_cancel_of_invertible]

  have deq : a * d - d * a = a := by
    calc
      _ = a * ((c⁻¹ * a * (δ a) ^[n - 1] b) - (c⁻¹ * (δ a) ^[n - 1] b * a)) := by
        simp_rw [hd_def, hc', mul_assoc, ← mul_sub_left_distrib]
      _ = _ := by simp only [eq1, mul_one]
  apply_fun (a⁻¹ * · ) at deq
  rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ ha₀, one_mul, ← mul_assoc, sub_eq_iff_eq_add] at deq
  obtain ⟨r, hr⟩ := (exists_pow_mem_center_ofInseparable p d hinsep)
  apply_fun fun x => x ^ (p ^ r) at deq
  rw [add_pow_char_pow_of_commute D 1 _ (Commute.one_left _) , one_pow,
    ← conj_nonComm_Algebra (ha := ha₀), ← hr.comm, mul_assoc, inv_mul_cancel₀ ha₀, mul_one,
    self_eq_add_left] at deq
  exact one_ne_zero deq

variable (D) in
/-- For a non-commutative finite dimensional division algebra D (with base ring being its center),
  there exist a separable element xover its center-/
theorem Jacobson_Noether (H : k ≠ (⊤ : Subring D)) :
    ∃ x : D, x ∉ k ∧ IsSeparable k x := by
  obtain ⟨p, hp⟩ := CharP.exists D
  rcases CharP.char_is_prime_or_zero D p with h | h
  · let _ := Fact.mk h
    apply JacobsonNoether_charP p H
  · rw [h] at hp
    exact JacobsonNoether_charZero H

end JacobsonNoether
