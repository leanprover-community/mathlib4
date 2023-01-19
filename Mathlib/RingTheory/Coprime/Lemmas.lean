/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Ken Lee, Chris Hughes

! This file was ported from Lean 3 source module ring_theory.coprime.lemmas
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Ring
import Mathbin.Data.Fintype.Basic
import Mathbin.Data.Int.Gcd
import Mathbin.RingTheory.Coprime.Basic

/-!
# Additional lemmas about elements of a ring satisfying `is_coprime`

These lemmas are in a separate file to the definition of `is_coprime` as they require more imports.

Notably, this includes lemmas about `finset.prod` as this requires importing big_operators, and
lemmas about `has_pow` since these are easiest to prove via `finset.prod`.

-/


universe u v

variable {R : Type u} {I : Type v} [CommSemiring R] {x y z : R} {s : I → R} {t : Finset I}

open BigOperators

section

open Classical

theorem Nat.is_coprime_iff_coprime {m n : ℕ} : IsCoprime (m : ℤ) n ↔ Nat.Coprime m n :=
  ⟨fun ⟨a, b, H⟩ =>
    Nat.eq_one_of_dvd_one <|
      Int.coe_nat_dvd.1 <| by
        rw [Int.ofNat_one, ← H]
        exact
          dvd_add (dvd_mul_of_dvd_right (Int.coe_nat_dvd.2 <| Nat.gcd_dvd_left m n) _)
            (dvd_mul_of_dvd_right (Int.coe_nat_dvd.2 <| Nat.gcd_dvd_right m n) _),
    fun H =>
    ⟨Nat.gcdA m n, Nat.gcdB m n, by
      rw [mul_comm _ (m : ℤ), mul_comm _ (n : ℤ), ← Nat.gcd_eq_gcd_ab, show _ = _ from H,
        Int.ofNat_one]⟩⟩
#align nat.is_coprime_iff_coprime Nat.is_coprime_iff_coprime

alias Nat.is_coprime_iff_coprime ↔ IsCoprime.nat_coprime Nat.Coprime.is_coprime
#align is_coprime.nat_coprime IsCoprime.nat_coprime
#align nat.coprime.is_coprime Nat.Coprime.is_coprime

theorem IsCoprime.prod_left : (∀ i ∈ t, IsCoprime (s i) x) → IsCoprime (∏ i in t, s i) x :=
  Finset.induction_on t (fun _ => isCoprime_one_left) fun b t hbt ih H =>
    by
    rw [Finset.prod_insert hbt]
    rw [Finset.forall_mem_insert] at H
    exact H.1.mul_left (ih H.2)
#align is_coprime.prod_left IsCoprime.prod_left

theorem IsCoprime.prod_right : (∀ i ∈ t, IsCoprime x (s i)) → IsCoprime x (∏ i in t, s i) := by
  simpa only [isCoprime_comm] using IsCoprime.prod_left
#align is_coprime.prod_right IsCoprime.prod_right

theorem IsCoprime.prod_left_iff : IsCoprime (∏ i in t, s i) x ↔ ∀ i ∈ t, IsCoprime (s i) x :=
  Finset.induction_on t (iff_of_true isCoprime_one_left fun _ => False.elim) fun b t hbt ih => by
    rw [Finset.prod_insert hbt, IsCoprime.mul_left_iff, ih, Finset.forall_mem_insert]
#align is_coprime.prod_left_iff IsCoprime.prod_left_iff

theorem IsCoprime.prod_right_iff : IsCoprime x (∏ i in t, s i) ↔ ∀ i ∈ t, IsCoprime x (s i) := by
  simpa only [isCoprime_comm] using IsCoprime.prod_left_iff
#align is_coprime.prod_right_iff IsCoprime.prod_right_iff

theorem IsCoprime.of_prod_left (H1 : IsCoprime (∏ i in t, s i) x) (i : I) (hit : i ∈ t) :
    IsCoprime (s i) x :=
  IsCoprime.prod_left_iff.1 H1 i hit
#align is_coprime.of_prod_left IsCoprime.of_prod_left

theorem IsCoprime.of_prod_right (H1 : IsCoprime x (∏ i in t, s i)) (i : I) (hit : i ∈ t) :
    IsCoprime x (s i) :=
  IsCoprime.prod_right_iff.1 H1 i hit
#align is_coprime.of_prod_right IsCoprime.of_prod_right

theorem Finset.prod_dvd_of_coprime :
    ∀ (Hs : (t : Set I).Pairwise (IsCoprime on s)) (Hs1 : ∀ i ∈ t, s i ∣ z), (∏ x in t, s x) ∣ z :=
  Finset.induction_on t (fun _ _ => one_dvd z)
    (by
      intro a r har ih Hs Hs1
      rw [Finset.prod_insert har]
      have aux1 : a ∈ (↑(insert a r) : Set I) := Finset.mem_insert_self a r
      refine'
        (IsCoprime.prod_right fun i hir =>
              Hs aux1 (Finset.mem_insert_of_mem hir) <|
                by
                rintro rfl
                exact har hir).mul_dvd
          (Hs1 a aux1) (ih (Hs.mono _) fun i hi => Hs1 i <| Finset.mem_insert_of_mem hi)
      simp only [Finset.coe_insert, Set.subset_insert])
#align finset.prod_dvd_of_coprime Finset.prod_dvd_of_coprime

theorem Fintype.prod_dvd_of_coprime [Fintype I] (Hs : Pairwise (IsCoprime on s))
    (Hs1 : ∀ i, s i ∣ z) : (∏ x, s x) ∣ z :=
  Finset.prod_dvd_of_coprime (Hs.set_pairwise _) fun i _ => Hs1 i
#align fintype.prod_dvd_of_coprime Fintype.prod_dvd_of_coprime

end

open Finset

theorem exists_sum_eq_one_iff_pairwise_coprime [DecidableEq I] (h : t.Nonempty) :
    (∃ μ : I → R, (∑ i in t, μ i * ∏ j in t \ {i}, s j) = 1) ↔
      Pairwise (IsCoprime on fun i : t => s i) :=
  by
  refine' h.cons_induction _ _ <;> clear t h
  · simp only [Pairwise, sum_singleton, Finset.sdiff_self, prod_empty, mul_one,
      exists_apply_eq_apply, Ne.def, true_iff_iff]
    rintro a ⟨i, hi⟩ ⟨j, hj⟩ h
    rw [Finset.mem_singleton] at hi hj
    simpa [hi, hj] using h
  intro a t hat h ih
  rw [pairwise_cons']
  have mem : ∀ x ∈ t, a ∈ insert a t \ {x} := fun x hx =>
    by
    rw [mem_sdiff, mem_singleton]
    exact ⟨mem_insert_self _ _, fun ha => hat (ha.symm.cases_on hx)⟩
  constructor
  · rintro ⟨μ, hμ⟩
    rw [sum_cons, cons_eq_insert, sdiff_singleton_eq_erase, erase_insert hat] at hμ
    refine' ⟨ih.mp ⟨Pi.single h.some (μ a * s h.some) + μ * fun _ => s a, _⟩, fun b hb => _⟩
    · rw [prod_eq_mul_prod_diff_singleton h.some_spec, ← mul_assoc, ←
        @if_pos _ _ h.some_spec R (_ * _) 0, ← sum_pi_single', ← sum_add_distrib] at hμ
      rw [← hμ, sum_congr rfl]
      intro x hx
      convert @add_mul R _ _ _ _ _ _ using 2
      · by_cases hx : x = h.some
        · rw [hx, Pi.single_eq_same, Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne hx, Pi.single_eq_of_ne hx, zero_mul]
      · convert (mul_assoc _ _ _).symm
        convert prod_eq_mul_prod_diff_singleton (mem x hx) _ using 3
        convert sdiff_sdiff_comm
        rw [sdiff_singleton_eq_erase, erase_insert hat]
    · have : IsCoprime (s b) (s a) :=
        ⟨μ a * ∏ i in t \ {b}, s i, ∑ i in t, μ i * ∏ j in t \ {i}, s j, _⟩
      · exact ⟨this.symm, this⟩
      rw [mul_assoc, ← prod_eq_prod_diff_singleton_mul hb, sum_mul, ← hμ, sum_congr rfl]
      intro x hx
      convert mul_assoc _ _ _
      convert prod_eq_prod_diff_singleton_mul (mem x hx) _ using 3
      convert sdiff_sdiff_comm
      rw [sdiff_singleton_eq_erase, erase_insert hat]
  · rintro ⟨hs, Hb⟩
    obtain ⟨μ, hμ⟩ := ih.mpr hs
    obtain ⟨u, v, huv⟩ := IsCoprime.prod_left fun b hb => (Hb b hb).right
    use fun i => if i = a then u else v * μ i
    have hμ' : (∑ i in t, v * ((μ i * ∏ j in t \ {i}, s j) * s a)) = v * s a := by
      rw [← mul_sum, ← sum_mul, hμ, one_mul]
    rw [sum_cons, cons_eq_insert, sdiff_singleton_eq_erase, erase_insert hat, if_pos rfl, ← huv, ←
      hμ', sum_congr rfl]
    intro x hx
    rw [mul_assoc, if_neg fun ha : x = a => hat (ha.casesOn hx)]
    convert mul_assoc _ _ _
    convert (prod_eq_prod_diff_singleton_mul (mem x hx) _).symm using 3
    convert sdiff_sdiff_comm
    rw [sdiff_singleton_eq_erase, erase_insert hat]
#align exists_sum_eq_one_iff_pairwise_coprime exists_sum_eq_one_iff_pairwise_coprime

theorem exists_sum_eq_one_iff_pairwise_coprime' [Fintype I] [Nonempty I] [DecidableEq I] :
    (∃ μ : I → R, (∑ i : I, μ i * ∏ j in {i}ᶜ, s j) = 1) ↔ Pairwise (IsCoprime on s) :=
  by
  convert exists_sum_eq_one_iff_pairwise_coprime Finset.univ_nonempty using 1
  simp only [Function.onFun, pairwise_subtype_iff_pairwise_finset', coe_univ, Set.pairwise_univ]
  assumption
#align exists_sum_eq_one_iff_pairwise_coprime' exists_sum_eq_one_iff_pairwise_coprime'

theorem pairwise_coprime_iff_coprime_prod [DecidableEq I] :
    Pairwise (IsCoprime on fun i : t => s i) ↔ ∀ i ∈ t, IsCoprime (s i) (∏ j in t \ {i}, s j) :=
  by
  refine' ⟨fun hp i hi => is_coprime.prod_right_iff.mpr fun j hj => _, fun hp => _⟩
  · rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
    obtain ⟨hj, ji⟩ := hj
    exact @hp ⟨i, hi⟩ ⟨j, hj⟩ fun h => ji (congr_arg coe h).symm
  · rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    apply is_coprime.prod_right_iff.mp (hp i hi)
    exact finset.mem_sdiff.mpr ⟨hj, fun f => h <| Subtype.ext (finset.mem_singleton.mp f).symm⟩
#align pairwise_coprime_iff_coprime_prod pairwise_coprime_iff_coprime_prod

variable {m n : ℕ}

theorem IsCoprime.pow_left (H : IsCoprime x y) : IsCoprime (x ^ m) y :=
  by
  rw [← Finset.card_range m, ← Finset.prod_const]
  exact IsCoprime.prod_left fun _ _ => H
#align is_coprime.pow_left IsCoprime.pow_left

theorem IsCoprime.pow_right (H : IsCoprime x y) : IsCoprime x (y ^ n) :=
  by
  rw [← Finset.card_range n, ← Finset.prod_const]
  exact IsCoprime.prod_right fun _ _ => H
#align is_coprime.pow_right IsCoprime.pow_right

theorem IsCoprime.pow (H : IsCoprime x y) : IsCoprime (x ^ m) (y ^ n) :=
  H.pow_left.pow_right
#align is_coprime.pow IsCoprime.pow

theorem IsCoprime.pow_left_iff (hm : 0 < m) : IsCoprime (x ^ m) y ↔ IsCoprime x y :=
  by
  refine' ⟨fun h => _, IsCoprime.pow_left⟩
  rw [← Finset.card_range m, ← Finset.prod_const] at h
  exact h.of_prod_left 0 (finset.mem_range.mpr hm)
#align is_coprime.pow_left_iff IsCoprime.pow_left_iff

theorem IsCoprime.pow_right_iff (hm : 0 < m) : IsCoprime x (y ^ m) ↔ IsCoprime x y :=
  isCoprime_comm.trans <| (IsCoprime.pow_left_iff hm).trans <| isCoprime_comm
#align is_coprime.pow_right_iff IsCoprime.pow_right_iff

theorem IsCoprime.pow_iff (hm : 0 < m) (hn : 0 < n) : IsCoprime (x ^ m) (y ^ n) ↔ IsCoprime x y :=
  (IsCoprime.pow_left_iff hm).trans <| IsCoprime.pow_right_iff hn
#align is_coprime.pow_iff IsCoprime.pow_iff

