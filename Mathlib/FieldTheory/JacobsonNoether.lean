/-
Copyright (c) 2024 F. Nuccio, H. Zheng, W. He, S. Wu, Y. Yuan, W. Jiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Huanyu Zheng, Sihan Wu, Wanyi He, Weichen Jiao, Yi Yuan
-/
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.CharP.LinearMaps
import Mathlib.Algebra.Field.Power
import Mathlib.FieldTheory.PurelyInseparable
import Mathlib.Algebra.CharP.ExpChar

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

namespace JacobsonNoether

variable {D : Type*} [DivisionRing D]

local notation3 "k" => (Subring.center D)
local notation3 "f" => (LinearMap.mulLeft k)
local notation3 "g" => (LinearMap.mulRight k)
private def δ : D → D →ₗ[k] D := f - g

private lemma δ_def (a x : D) : δ a x = f a x - g a x := rfl

private lemma δ_def' (a : D) : δ a = f a - g a := rfl

private lemma fg_comm (a : D) : Commute (f a) (g a) := LinearMap.commute_mulLeft_right a a

private lemma f_pow (a : D) (n : ℕ) : ∀ x : D, ((f a) ^ n).1 x = (a ^ n) * x := by
  intro x
  rw [LinearMap.coe_toAddHom, LinearMap.pow_apply]
  induction n with
  | zero => rw [Function.iterate_zero, id_eq, pow_zero, one_mul]
  | succ _ h => rw [Function.iterate_succ', Function.comp_apply, h,
    pow_succ', mul_assoc, LinearMap.mulLeft_apply]

private lemma g_pow (a : D) (n : ℕ) : ∀ x : D, ((g a) ^ n).1 x = x * (a ^ n) := by
  intro x
  rw [LinearMap.coe_toAddHom, LinearMap.pow_apply]
  induction n with
  | zero => rw [Function.iterate_zero, id_eq, pow_zero, mul_one]
  | succ _ h => rw [Function.iterate_succ', Function.comp_apply, h,
    pow_add, pow_one, LinearMap.mulRight_apply, mul_assoc]

private lemma δ_iterate_succ (x y : D) (n : ℕ) :
    δ x (((δ x) ^ n) y) = ((δ x) ^ (n + 1)) y := by
  simp only [LinearMap.pow_apply, δ_def, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, Function.iterate_succ_apply']

variable [Algebra.IsAlgebraic (Subring.center D) D]

open Polynomial

/-- If `D` is a purely inseparable extension of `k` with characteristic `p`,
  then for every element `a` of `D`, there exists a natural number `n`
  such that `a ^ (p ^ n)` is contained in `k`. -/
lemma exists_pow_mem_center_ofInseparable (p : ℕ) [hchar : ExpChar D p] (a : D)
    (hinsep : ∀ x : D, IsSeparable k x → x ∈ k) : ∃ n, a ^ (p ^ n) ∈ k := by
  have := (@isPurelyInseparable_iff_pow_mem k D _ _ _ _ p (center_expChar_eq_iff.1 hchar)).1
  -- **`bridge` and `bridge'` could also be useful somewhere else.**
  have bridge : ∀ x : k, (algebraMap k D) x = x := fun _ ↦ rfl
  have bridge' : k = (algebraMap k D).range := Subring.ext_iff.mpr <| fun x ↦
    ⟨fun hx ↦ Set.mem_range.mpr (Exists.intro ⟨x, hx⟩ rfl),
    fun hx ↦ Exists.casesOn hx fun y hy ↦ (bridge y ▸ hy) ▸ y.2⟩
  have pure : IsPurelyInseparable k D := ⟨Algebra.IsAlgebraic.isIntegral, (bridge' ▸ hinsep)⟩
  obtain ⟨n, ⟨m, hm⟩⟩ := (this pure) a
  have := Subalgebra.range_subset (R := k) ⟨(k).toSubsemiring, by intro r; exact r.2⟩
  exact ⟨n, Set.mem_of_subset_of_mem this <| Set.mem_range.2 ⟨m, hm⟩⟩

/-- If `D` is a purely inseparable extension of `k` with characteristic `p`,
  then for every element `a` of `D\k`, there exists a natural number `n`
  **greater than 0** such that `a ^ (p ^ n)` is contained in `k`. -/
lemma exists_pow_mem_center_ofInseparable' (p : ℕ) [ExpChar D p] {a : D}
    (ha : a ∉ k) (hinsep : ∀ x : D, IsSeparable k x → x ∈ k) : ∃ n ≥ 1, a ^ (p ^ n) ∈ k := by
  obtain ⟨n, hn⟩ := exists_pow_mem_center_ofInseparable p a hinsep
  by_cases nzero : n = 0
  · rw [nzero, pow_zero, pow_one] at hn
    exact False.elim <| ha hn
  · exact ⟨n, ⟨by omega, hn⟩⟩

/-- If `D` is a purely inseparable extension of `k` with characteristic `p`,
  then for every element `a` of `D\k`, there exists a natural number `m`
  greater than 0 such that linear map `(a * x - x * a) ^ n = 0` for
  any `n` greater than `(p ^ n)`. -/
lemma exist_pow_eq_zero_of_le (p : ℕ) [hchar : ExpChar D p]
    {a : D} (ha : a ∉ k) (hinsep : ∀ x : D, IsSeparable k x → x ∈ k):
  ∃ m ≥ 1, ∀ n ≥ (p ^ m), (δ a) ^ n = 0 := by
  obtain ⟨m, hm⟩ := exists_pow_mem_center_ofInseparable' p ha hinsep
  refine ⟨m, ⟨hm.1, ?_⟩⟩
  intro n hn
  have inter : (δ a) ^ (p ^ m) = 0 := by
    refine LinearMap.ext_iff.2 ?_
    intro x
    rw [δ_def' a, @sub_pow_expChar_pow_of_commute (D →ₗ[k] D) _ p _ m (f a) (g a) (fg_comm a)]
    show ((f a) ^ (p ^ m)).1 x - ((g a) ^ (p ^ m)).1 x = 0
    rw [f_pow, g_pow, sub_eq_zero_of_eq]
    suffices h : a ^ (p ^ m) ∈ k from (Subring.mem_center_iff.1 h x).symm
    exact hm.2
  rw [((Nat.sub_eq_iff_eq_add hn).1 rfl), pow_add, inter, mul_zero]

variable (D) in
/-- For a non-commutative finite dimensional division algebra D (with base ring being its center),
  there exist a separable element xover its center-/
theorem Jacobson_Noether (H : k ≠ (⊤ : Subring D)) :
    ∃ x : D, x ∉ k ∧ IsSeparable k x := by
  obtain ⟨p, hp⟩ := ExpChar.exists D
  by_contra! insep
  have hinsep : ∀ x : D, IsSeparable k x → x ∈ k :=
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
  obtain ⟨n, hn, hb⟩ : ∃ n > 0, ((δ a) ^ n) b ≠ 0 ∧ ((δ a) ^ (n + 1)) b = 0 := by
    obtain ⟨m, -, hm2⟩ := exist_pow_eq_zero_of_le p ha hinsep
    have exist : ∃ n > 0, ((δ a) ^ (n + 1)) b = 0 := by
      refine ⟨(p ^ m), ⟨expChar_pow_pos D p m, by rw [hm2 (p ^ m + 1) (by omega)]; rfl⟩⟩
    classical
    refine ⟨Nat.find exist, ⟨(Nat.find_spec exist).1, ?_, (Nat.find_spec exist).2⟩⟩
    set t := (Nat.find exist - 1 : ℕ) with ht
    by_cases choice : 0 < t
    · have := @Nat.find_min (H := exist) _ t ?_
      · exact (@Nat.sub_add_cancel (Nat.find exist) 1 (by omega) ▸ ht ▸ not_and.1 this) choice
      · exact Nat.sub_one_lt <| ne_of_gt (Nat.find_spec exist).1
    · rw [not_lt, Nat.le_zero] at choice
      have := Nat.eq_add_of_sub_eq (Nat.find_spec exist).1 ht.symm
      simp only [gt_iff_lt, choice, Nat.succ_eq_add_one, zero_add] at this
      rw [this, pow_one]
      exact hb1
    -- We define `c` to be the value that we proved above to be non-zero.
  set c := ((δ a) ^ n) b with hc_def
  letI : Invertible c := ⟨c⁻¹, inv_mul_cancel₀ (hb.1), mul_inv_cancel₀ (hb.1)⟩
  -- We prove that `c` is commute with `a`.
  have hc : c * a = a * c := by
    symm; apply eq_of_sub_eq_zero
    rw [← LinearMap.mulLeft_apply (R := k), ← LinearMap.mulRight_apply (R := k),
      ← δ_def, δ_iterate_succ a b n, hb.2]
  -- We now make some computation to obtain the final equation.
  set d := c⁻¹ * a * ((δ a) ^ (n - 1)) b with hd_def
  have hc': c⁻¹ * a = a * c⁻¹ := by
    apply_fun (c⁻¹ * · * c⁻¹) at hc
    rw [← mul_assoc, inv_mul_cancel₀ hb.1, one_mul, mul_assoc, mul_assoc,
      mul_inv_cancel₀ hb.1, mul_one] at hc
    exact hc.symm
  have c_eq : a * ((δ a) ^ (n - 1)) b - ((δ a) ^ (n - 1)) b * a = c := by
    rw [hc_def, ← Nat.sub_add_cancel hn, ← δ_iterate_succ, δ_def]; rfl
  have eq1 : c⁻¹ * a * ((δ a)^ (n - 1)) b - c⁻¹ * ((δ a) ^ (n - 1)) b * a = 1 := by
    simp_rw [mul_assoc, (mul_sub_left_distrib c⁻¹ _ _).symm, c_eq, inv_mul_cancel_of_invertible]
  -- We show that `a` is commute with `d`.
  have deq : a * d - d * a = a := by
    nth_rw 3 [← mul_one a]
    rw [hd_def, ← eq1, mul_sub, mul_assoc _ _ a, sub_right_inj, hc',
      ← mul_assoc, ← mul_assoc, ← mul_assoc]
  -- This then derives a contradiction.
  apply_fun (a⁻¹ * · ) at deq
  rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ ha₀, one_mul, ← mul_assoc, sub_eq_iff_eq_add] at deq
  obtain ⟨r, hr⟩ := (exists_pow_mem_center_ofInseparable p d hinsep)
  apply_fun (· ^ (p ^ r)) at deq
  rw [add_pow_expChar_pow_of_commute D 1 _ (Commute.one_left _) , one_pow,
    ← conj_nonComm_Algebra (ha := ha₀), ← hr.comm, mul_assoc, inv_mul_cancel₀ ha₀, mul_one,
    self_eq_add_left] at deq
  exact one_ne_zero deq

open Subring Algebra in
theorem Jacobson_Noether' {L D : Type*} [Field L] [DivisionRing D]
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
  obtain ⟨x, hxd, hx⟩ := Jacobson_Noether D ntrivial
  refine ⟨x, ⟨by rwa [← Subalgebra.center_toSubring L, hcenter] at hxd, IsSeparable.tower_top _ hx⟩⟩

end JacobsonNoether

#exit
namespace test

#help tactic infer
open Algebra

example {L D : Type*} [Field L] [DivisionRing D] [Algebra L D] [Algebra.IsAlgebraic L D]
    (hcenter : Subalgebra.center L D = ⊥) (hneq : (⊥ : Subalgebra L D) ≠ ⊤) :
    ∃ x : D, x ∉ (⊥ : Subalgebra L D) ∧ IsSeparable L x := by
  -- have aux : Algebra.IsAlgebraic L D := inferInstance
  -- let cmm1 : CommRing (⊥ : Subalgebra L D) := by
  --   rw [← hcenter]
  --   infer_instance
  set a := Subring.center D with ha
  have hac : (⊥ : Subalgebra L D).toSubring = a := by
    · rw [← hcenter]
      rfl
  set φ := RingEquiv.subringCongr (hac).symm with hφ
  let cmm2 : CommRing (⊥ : Subalgebra L D) := (φ.symm).commRing
  -- have check : cmm1 = cmm2 := rfl
  -- have : Algebra (⊥ : Subalgebra L D) D := by
    -- have := (φ.toRingHom).toAlgebra

  -- set c := @(Algebra.ofId L D).range with hc
  -- set a := Subring.center D with ha
  set ψ : L ≃+* (⊥ : Subalgebra L D) := by
    · use ((Algebra.botEquiv L D).toRingEquiv).symm
      · intro x y
        simp only [Equiv.toFun_as_coe, EquivLike.coe_coe, map_mul]
      · intro x y
        simp only [Equiv.toFun_as_coe, EquivLike.coe_coe, map_add]



  -- let comm : CommSemiring (⊥ : Subalgebra L D) := ψ.symm.commSemiring

  let _ : Algebra L a := by
    use (ψ.trans φ.symm).toRingHom.toAlgebra
    -- · have := @RingHom.toAlgebra L (⊥ : Subalgebra L D) _ comm ψ.toRingHom
    -- · have := Algebra L (⊥ : Subalgebra L D)

      --use Algebra.ofId L D
  let _ : IsScalarTower L a D := sorry
  have aux2 : Algebra.IsAlgebraic a D := by
    · apply Algebra.IsAlgebraic.tower_top_of_injective (R := L) (S := a) (A := D)
      sorry
  have := @JacobsonNoether.Jacobson_Noether D _ aux2

    -- · rw [hc]
  have hcc : c = ⊥ := rfl
  have aux' := aux.1
  have hab : a = b := rfl
  rw [hcenter] at hb
  have : Algebra.IsAlgebraic a D := by
    constructor
    intro x
    have : IsAlgebraic L x := by
      sorry
    convert this





  set k' := (⊥ : Subalgebra k D).toSubring with hk'
  have hcenter' : k' = Subring.center D := by apply (hcenter.symm) ▸ hk'
  have aux1 : (⊤ : Subring D) = (⊤ : Subalgebra k D).toSubring := rfl
  have ntrivial : k' ≠ ⊤ := by
    refine Ne.intro ?_
    exact fun heq ↦
      hneq <| Algebra.toSubring_eq_top.mp <| aux1 ▸ hk' ▸ heq
  -- have := @JacobsonNoether.Jacobson_Noether D _ _ ntrivial

    -- infer_instance
    -- rw [← hcenter']
    sorry
  obtain ⟨x, hx⟩ := @JacobsonNoether.Jacobson_Noether D _ _ (hcenter' ▸ ntrivial)
  use x
  constructor
  · simp_rw [← hcenter', hk'] at hx
    exact hx.1
  · have base := hx.2
    sorry

end test
