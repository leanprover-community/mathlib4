/-
Copyright (c) 2024 **ALL YOUR NAMES**, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: **ALL YOUR NAMES** Filippo A. E. Nuccio
-/

import Mathlib.RingTheory.Algebraic
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.CharP.Subring

-- *Filippo* This should probably not be here
lemma conj_nonComm_Algebra {D : Type*} [DivisionRing D] (s : ℕ) (a d : D) (ha : a ≠ 0) :
    a⁻¹ * d ^ s * a = (a⁻¹ * d * a) ^ s := by
  let u : Dˣ := ⟨a, a⁻¹, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha⟩
  exact (Units.conj_pow' u d s).symm

namespace JacobsonNoether

open Classical

variable {D : Type*} [DivisionRing D]

local notation3 "k" => (Subring.center D)

private def f (a : D) : D →ₗ[k] D := {
  toFun := fun x ↦ a * x
  map_add' := fun x y ↦ LeftDistribClass.left_distrib a x y
  map_smul' := by
    intro m x
    simp only [Algebra.mul_smul_comm, RingHom.id_apply]
}

@[simp]
private lemma f_def (a x : D) : f a x = a * x := rfl

private def g (a : D) : D →ₗ[k] D := {
  toFun := fun x ↦ x * a
  map_add' := fun x y ↦ RightDistribClass.right_distrib x y a
  map_smul' := by
    intro m x
    simp only [Algebra.smul_mul_assoc, RingHom.id_apply]
}

@[simp]
private lemma g_def (a x : D) : g a x = x * a := rfl

private def δ (a : D) : D →ₗ[k] D := {
  toFun := f a - g a
  map_add' := by
    intro x y
    simp only [Pi.sub_apply, map_add, add_sub_add_comm]
  map_smul' := by
    intro m x
    simp only [Pi.sub_apply, map_smul, RingHom.id_apply, smul_sub]
}

@[simp]
private lemma δ_def (a x : D) : δ a x = f a x - g a x := rfl

-- *Filippo* Change name
private lemma comm_fg (a : D) : Commute (f a) (g a) := by
  rw [commute_iff_eq, LinearMap.mk.injEq, AddHom.mk.injEq]
  funext x
  dsimp [f, g]; exact Eq.symm (mul_assoc a x a)

-- *Filippo* Change name
private lemma aux1 (a : D) : δ a = f a - g a := rfl

lemma f_pow (a : D) (n : ℕ) : ∀ x : D, ((f a) ^ n).1 x = (a ^ n) * x := by
  intro x
  rw [LinearMap.coe_toAddHom, LinearMap.pow_apply]
  induction n
  · simp only [Function.iterate_zero, id_eq, pow_zero, one_mul]
  · simp only [Function.iterate_succ', Function.comp_apply, *]
    rename_i n h
    rw [pow_succ', mul_assoc]; rfl

lemma g_pow (a : D) (n : ℕ) : ∀ x : D, ((g a) ^ n).1 x = x * (a ^ n) := by
  intro x
  rw [LinearMap.coe_toAddHom, LinearMap.pow_apply]
  induction n
  · simp only [Function.iterate_zero, id_eq, pow_zero, mul_one]
  · simp only [Function.iterate_succ', Function.comp_apply, *]
    rename_i n h
    show (x * a ^ n) * a = x * a ^ (n + 1)
    rw [pow_add, pow_one, mul_assoc]

-- *Filippo* : Please change the name!
lemma important (x y : D) (n : ℕ) :
    δ x (((δ x) ^ n) y) = ((δ x) ^ (n + 1)) y := by
  simp only [LinearMap.pow_apply, δ_def, f_def, g_def, Function.iterate_succ_apply']

variable [Algebra.IsAlgebraic (Subring.center D) D]

-- *Filippo* Change name
-- This *should not* be private
lemma exists_pow_mem_center_ofInseparable (p : ℕ) [Fact p.Prime] [CharP D p] (a : D)
   (hinsep : ∀ x : D, IsSeparable k x → x ∈ k) : ∃ n, a ^ (p ^ n) ∈ k := by
  obtain ⟨n, g, hg, geqf⟩ := @Polynomial.exists_separable_of_irreducible k _ p _ (minpoly k a)
    (minpoly.irreducible (Algebra.IsIntegral.isIntegral a)) ((NeZero.ne' p).symm)
  have h1 : (Polynomial.aeval a) ((Polynomial.expand k (p ^ n)) g) = 0 := by
    rw [congrArg (⇑(Polynomial.aeval a)) geqf, minpoly.aeval k a]
  simp only [Polynomial.expand_aeval] at h1
  use n
  apply hinsep (a ^ p ^ n) (Polynomial.Separable.of_dvd hg (minpoly.dvd_iff.mpr h1))

lemma exists_pow_mem_center_ofInseparable' (p : ℕ) [Fact p.Prime] [CharP D p] {a : D}
    (ha : a ∉ k) (hinsep : ∀ x : D, IsSeparable k x → x ∈ k) : ∃ n ≥ 1, a ^ (p ^ n) ∈ k := by
  obtain ⟨n, g, hg, geqf⟩ := @Polynomial.exists_separable_of_irreducible k _ p _ (minpoly k a)
    (minpoly.irreducible (Algebra.IsIntegral.isIntegral a)) ((NeZero.ne' p).symm)
  by_cases nzero : n = 0
  · rw [nzero, pow_zero, Polynomial.expand_one] at geqf
    rw [geqf] at hg
    tauto
  use n
  have h1 : (Polynomial.aeval a) ((Polynomial.expand k (p ^ n)) g) = 0 := by
    rw [congrArg (⇑(Polynomial.aeval a)) geqf, minpoly.aeval k a]
  simp only [Polynomial.expand_aeval] at h1
  constructor
  · exact Nat.one_le_iff_ne_zero.mpr nzero
  exact hinsep (a ^ p ^ n) (Polynomial.Separable.of_dvd hg (minpoly.dvd_iff.mpr h1))

-- Not private but better name
lemma final_aux (p : ℕ) [Fact p.Prime] [CharP D p]
    {a : D} (ha : a ∉ k) (hinsep : ∀ x : D, IsSeparable k x → x ∈ k):
  ∃ m ≥ 1, ∀ n ≥ (p ^ m), (δ a) ^ n = 0 := by
  obtain ⟨m, hm⟩ := exists_pow_mem_center_ofInseparable' p ha hinsep
  use m
  constructor
  · exact hm.1
  · intro n hn
    have inter1 : (δ a) ^ (p ^ m) = (f a) ^ (p ^ m) - (g a) ^ (p ^ m) :=
      sub_pow_char_pow_of_commute (D →ₗ[k] D) (f a) (g a) (comm_fg a)
    have inter2 : ∀ x : D, ((δ a) ^ (p ^ m)).1 x = 0 := by
      intro x
      rw [congrArg LinearMap.toAddHom inter1]
      show ((f a) ^ (p ^ m)).1 x - ((g a) ^ (p ^ m)).1 x = 0
      rw [f_pow, g_pow]
      apply sub_eq_zero_of_eq
      suffices h : a ^ (p ^ m) ∈ k by
        rw [Subring.mem_center_iff] at h; exact (h x).symm
      exact hm.2
    have inter3 : (δ a) ^ (p ^ m) = 0 := LinearMap.ext_iff.mpr inter2
    have boring : n = (n - (p ^ m)) + p ^ m := (Nat.sub_eq_iff_eq_add hn).mp rfl
    rw [boring, pow_add, inter3, mul_zero]


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
    obtain ⟨m, -, hm2⟩ := final_aux p ha hinsep
    have exist : ∃ n > 0, ((δ a) ^ (n + 1)) b = 0 := by
      refine ⟨ p ^ m, ⟨pow_pos (Nat.Prime.pos (@Fact.out _ _)) m, ?_ ⟩ ⟩
      simp only [hm2 (p^ m + 1) (by linarith), LinearMap.zero_apply]
    refine ⟨Nat.find exist, ⟨(Nat.find_spec exist).1, ?_, (Nat.find_spec exist).2⟩⟩
    set t := (Nat.find exist - 1 : ℕ) with ht
    by_cases choice : 0 < t
    · have := @Nat.find_min (H := exist) _ t ?_
      · rw [not_and, ht, Nat.sub_add_cancel] at this
        · exact this choice
        · replace choice : 1 ≤ t := Nat.one_le_of_lt choice
          apply le_trans choice
          exact Nat.sub_le (Nat.find exist) 1
      · rw [ht]
        apply Nat.sub_one_lt
        apply ne_of_gt
        exact (Nat.find_spec exist).1
    · rw [not_lt, Nat.le_zero] at choice
      have := Nat.eq_add_of_sub_eq (Nat.find_spec exist).1 ht.symm
      simp only [gt_iff_lt, choice, Nat.succ_eq_add_one, zero_add] at this
      rw [this]
      simp only [Function.iterate_one, ne_eq]
      exact hb1
  -- We define `c` to be the value that we proved above to be non-zero.
  set c := ((δ a) ^ n) b with hc_def
  letI : Invertible c := ⟨c⁻¹, inv_mul_cancel₀ (hb.1), mul_inv_cancel₀ (hb.1)⟩
  -- have important : δ a (((δ a) ^ n) b) = ((δ a) ^ (n + 1)) b := by
  --   simp only [LinearMap.pow_apply, δ_def, f_def, g_def,
  --     Function.iterate_succ_apply']
  have hc : c * a = a * c := by
    rw [← show (f a) c = a * c by rfl, ← show (g a) c = c * a by rfl, ← zero_add (g a c)]
    apply add_eq_of_eq_add_neg
    have temp := important a b n
    simp only [δ_def, f_def, g_def] at temp
    simp only [temp, f_def, g_def, ← sub_eq_add_neg]
    exact hb.2.symm
  -- We now make some computation to obtain the *absurd* equation `final_eq`, contradiction.
  /-
  **The "Ring Tactic" must be use on a CommRing, there is no efficient Tactic if on none CommRing**
  **And the progress is a piece of SHIT**
  **I use so many "rw" Tactic similar to the beginning learning of Lean**
  -/
  set d := c⁻¹ * a * (δ a) ^[n-1] b with hd_def
  have hc': c⁻¹ * a = a * c⁻¹ := by
    calc
      _ = c⁻¹ * a * (c * c⁻¹) := by simp only [mul_inv_cancel_of_invertible, mul_one]
      _ = c⁻¹ * (a * c) * c⁻¹ := by simp_rw [mul_assoc]
      _ = c⁻¹ * (c * a) * c⁻¹ := by rw [hc]
      _ = (c⁻¹ * c) * a * c⁻¹ := by simp_rw [mul_assoc]
      _ = _ := by simp only [inv_mul_cancel_of_invertible, one_mul]
  have c_eq : a * (δ a) ^[n - 1] b - (δ a) ^[n - 1] b * a = c := by
    rw [hc_def, ← (LinearMap.pow_apply (δ a) (n - 1) b), ← Nat.sub_add_cancel hn,
      show (δ a ^ (n - 1 + 1)) b = (δ a) ((δ a ^ (n - 1)) b) by rw [important]]
    simp only [add_tsub_cancel_right, δ_def, f_def, g_def]
  have eq1 : c⁻¹ * a * (δ a)^[n - 1] b - c⁻¹ * (δ a)^[n - 1] b * a = 1 := by
    calc
      _ = c⁻¹ * (a * (δ a)^[n - 1] b) - c⁻¹ * ((δ a)^[n - 1] b * a) := by simp_rw [mul_assoc]
      _ = c⁻¹ * (a * (δ a)^[n - 1] b - (δ a)^[n - 1] b * a) := (mul_sub_left_distrib c⁻¹ _ _).symm
      _ = c⁻¹ * c := by rw [c_eq]
      _ = _ := by simp only [inv_mul_cancel_of_invertible]

  have deq : a * d - d * a = a := by
    calc
      _ = a * (c⁻¹ * a * (δ a)^[n - 1] b) - (c⁻¹ * a * (δ a)^[n - 1] b) * a := by rw [hd_def]
      _ = a * (c⁻¹ * a * (δ a)^[n - 1] b) - a * c⁻¹ * (δ a)^[n - 1] b * a := by rw [hc']
      _ = a * (c⁻¹ * a * (δ a)^[n - 1] b) - a * (c⁻¹ * (δ a)^[n - 1] b * a) := by simp_rw [mul_assoc]
      _ = a * ((c⁻¹ * a * (δ a)^[n - 1] b) - (c⁻¹ * (δ a)^[n - 1] b * a)) := by rw [← mul_sub_left_distrib]
      _ = _ := by simp only [eq1, mul_one]
  -- *Filippo* Find a better name!
  have tired : 1 + a⁻¹ * d * a = d := by
    calc
      _ = (a⁻¹ * a) + a⁻¹ * d * a := by simp only [add_left_inj, inv_mul_cancel₀ ha₀]
      _ = a⁻¹ * a + a⁻¹ * (d * a) := by simp only [add_right_inj, mul_assoc]
      _ = a⁻¹ * (a * d - d * a + d * a) := by rw [left_distrib, deq]
      _ = (a⁻¹ * a) * d := by rw [sub_add_cancel, mul_assoc]
      _ = _ := by simp only [inv_mul_cancel₀ ha₀, one_mul]
  -- The natural `r` below is such that `d ^ (p ^ r) ∈ k`.
  obtain ⟨r, hr⟩ := (exists_pow_mem_center_ofInseparable p d hinsep)

  have final_eq : d ^ (p ^ r) = 1 + d ^ (p ^ r) := by
    calc
      _ = (1 + a⁻¹ * d * a) ^ (p ^ r) := by rw [tired]
      _ = 1 ^ (p ^ r) + (a⁻¹ * d * a) ^ (p ^ r) := by
        rw [add_pow_char_pow_of_commute]
        exact Commute.one_left _
      _ = 1 + a⁻¹ * d ^ (p ^ r) * a := by
        simpa only [one_pow, add_right_inj] using(conj_nonComm_Algebra (p^r) a d ha₀).symm
      _ = _ := by
        simp only [add_right_inj]
        calc
          _ = a⁻¹ * (d ^ p ^ r * a) := by simp_rw [mul_assoc]
          _ = a⁻¹ * (a * d ^ p ^ r) := by rw [hr.comm]
          _ = (a⁻¹ * a) * d ^ p ^ r := by simp_rw [mul_assoc]
          _ = _ := by simp only [inv_mul_cancel₀ ha₀, one_mul]
  simp only [self_eq_add_left, one_ne_zero] at final_eq

variable (D) in
theorem Jacobson_Noether (H : k ≠ (⊤ : Subring D)) :
    ∃ x : D, x ∉ k ∧ IsSeparable k x := by
  obtain ⟨p, hp⟩ := CharP.exists D
  rcases CharP.char_is_prime_or_zero D p with h | h
  · let _ := Fact.mk h
    apply JacobsonNoether_charP p H
  · rw [h] at hp
    exact JacobsonNoether_charZero H

end JacobsonNoether
