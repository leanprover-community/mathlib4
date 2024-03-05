/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Ken Lee, Chris Hughes
-/
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Basic

#align_import ring_theory.coprime.lemmas from "leanprover-community/mathlib"@"509de852e1de55e1efa8eacfa11df0823f26f226"

/-!
# Additional lemmas about elements of a ring satisfying `IsCoprime`
and elements of a monoid satisfying `IsRelPrime`

These lemmas are in a separate file to the definition of `IsCoprime` or `IsRelPrime`
as they require more imports.

Notably, this includes lemmas about `Finset.prod` as this requires importing BigOperators, and
lemmas about `HasPow` since these are easiest to prove via `Finset.prod`.

-/

universe u v

open scoped BigOperators

section IsCoprime

variable {R : Type u} {I : Type v} [CommSemiring R] {x y z : R} {s : I → R} {t : Finset I}

section

theorem Int.isCoprime_iff_gcd_eq_one {m n : ℤ} : IsCoprime m n ↔ Int.gcd m n = 1 := by
  constructor
  · rintro ⟨a, b, h⟩
    have : 1 = m * a + n * b := by rwa [mul_comm m, mul_comm n, eq_comm]
    exact Nat.dvd_one.mp (Int.gcd_dvd_iff.mpr ⟨a, b, this⟩)
  · rw [← Int.ofNat_inj, IsCoprime, Int.gcd_eq_gcd_ab, mul_comm m, mul_comm n, Nat.cast_one]
    intro h
    exact ⟨_, _, h⟩

theorem Nat.isCoprime_iff_coprime {m n : ℕ} : IsCoprime (m : ℤ) n ↔ Nat.Coprime m n := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.coe_nat_gcd]
#align nat.is_coprime_iff_coprime Nat.isCoprime_iff_coprime

alias ⟨IsCoprime.nat_coprime, Nat.Coprime.isCoprime⟩ := Nat.isCoprime_iff_coprime
#align is_coprime.nat_coprime IsCoprime.nat_coprime
#align nat.coprime.is_coprime Nat.Coprime.isCoprime

theorem Nat.Coprime.cast {R : Type*} [CommRing R] {a b : ℕ} (h : Nat.Coprime a b) :
    IsCoprime (a : R) (b : R) := by
  rw [← isCoprime_iff_coprime] at h
  rw [← Int.cast_ofNat a, ← Int.cast_ofNat b]
  exact IsCoprime.intCast h

theorem ne_zero_or_ne_zero_of_nat_coprime {A : Type u} [CommRing A] [Nontrivial A] {a b : ℕ}
    (h : Nat.Coprime a b) : (a : A) ≠ 0 ∨ (b : A) ≠ 0 :=
  IsCoprime.ne_zero_or_ne_zero (R := A) <| by
    simpa only [map_natCast] using IsCoprime.map (Nat.Coprime.isCoprime h) (Int.castRingHom A)

theorem IsCoprime.prod_left : (∀ i ∈ t, IsCoprime (s i) x) → IsCoprime (∏ i in t, s i) x := by
  classical
  refine Finset.induction_on t (fun _ ↦ isCoprime_one_left) fun b t hbt ih H ↦ ?_
  rw [Finset.prod_insert hbt]
  rw [Finset.forall_mem_insert] at H
  exact H.1.mul_left (ih H.2)
#align is_coprime.prod_left IsCoprime.prod_left

theorem IsCoprime.prod_right : (∀ i ∈ t, IsCoprime x (s i)) → IsCoprime x (∏ i in t, s i) := by
  simpa only [isCoprime_comm] using IsCoprime.prod_left (R := R)
#align is_coprime.prod_right IsCoprime.prod_right

theorem IsCoprime.prod_left_iff : IsCoprime (∏ i in t, s i) x ↔ ∀ i ∈ t, IsCoprime (s i) x := by
  classical
  refine Finset.induction_on t (iff_of_true isCoprime_one_left fun _ ↦ by simp) fun b t hbt ih ↦ ?_
  rw [Finset.prod_insert hbt, IsCoprime.mul_left_iff, ih, Finset.forall_mem_insert]
#align is_coprime.prod_left_iff IsCoprime.prod_left_iff

theorem IsCoprime.prod_right_iff : IsCoprime x (∏ i in t, s i) ↔ ∀ i ∈ t, IsCoprime x (s i) := by
  simpa only [isCoprime_comm] using IsCoprime.prod_left_iff (R := R)
#align is_coprime.prod_right_iff IsCoprime.prod_right_iff

theorem IsCoprime.of_prod_left (H1 : IsCoprime (∏ i in t, s i) x) (i : I) (hit : i ∈ t) :
    IsCoprime (s i) x :=
  IsCoprime.prod_left_iff.1 H1 i hit
#align is_coprime.of_prod_left IsCoprime.of_prod_left

theorem IsCoprime.of_prod_right (H1 : IsCoprime x (∏ i in t, s i)) (i : I) (hit : i ∈ t) :
    IsCoprime x (s i) :=
  IsCoprime.prod_right_iff.1 H1 i hit
#align is_coprime.of_prod_right IsCoprime.of_prod_right

-- Porting note: removed names of things due to linter, but they seem helpful
theorem Finset.prod_dvd_of_coprime :
    (t : Set I).Pairwise (IsCoprime on s) → (∀ i ∈ t, s i ∣ z) → (∏ x in t, s x) ∣ z := by
  classical
  exact Finset.induction_on t (fun _ _ ↦ one_dvd z)
    (by
      intro a r har ih Hs Hs1
      rw [Finset.prod_insert har]
      have aux1 : a ∈ (↑(insert a r) : Set I) := Finset.mem_insert_self a r
      refine'
        (IsCoprime.prod_right fun i hir ↦
              Hs aux1 (Finset.mem_insert_of_mem hir) <| by
                rintro rfl
                exact har hir).mul_dvd
          (Hs1 a aux1) (ih (Hs.mono _) fun i hi ↦ Hs1 i <| Finset.mem_insert_of_mem hi)
      simp only [Finset.coe_insert, Set.subset_insert])
#align finset.prod_dvd_of_coprime Finset.prod_dvd_of_coprime

theorem Fintype.prod_dvd_of_coprime [Fintype I] (Hs : Pairwise (IsCoprime on s))
    (Hs1 : ∀ i, s i ∣ z) : (∏ x, s x) ∣ z :=
  Finset.prod_dvd_of_coprime (Hs.set_pairwise _) fun i _ ↦ Hs1 i
#align fintype.prod_dvd_of_coprime Fintype.prod_dvd_of_coprime

end

open Finset

theorem exists_sum_eq_one_iff_pairwise_coprime [DecidableEq I] (h : t.Nonempty) :
    (∃ μ : I → R, (∑ i in t, μ i * ∏ j in t \ {i}, s j) = 1) ↔
      Pairwise (IsCoprime on fun i : t ↦ s i) := by
  refine' h.cons_induction _ _
  · simp only [sum_singleton, Finset.sdiff_self, prod_empty, mul_one, exists_apply_eq,
               Pairwise, Ne.def, true_iff_iff]
    rintro a ⟨i, hi⟩ ⟨j, hj⟩ h
    rw [Finset.mem_singleton] at hi hj
    simp [hi, hj] at h
  intro a t hat h ih
  rw [pairwise_cons']
  have mem : ∀ x ∈ t, a ∈ insert a t \ {x} := fun x hx ↦ by
    rw [mem_sdiff, mem_singleton]
    exact ⟨mem_insert_self _ _, fun ha ↦ hat (ha ▸ hx)⟩
  constructor
  · rintro ⟨μ, hμ⟩
    rw [sum_cons, cons_eq_insert, sdiff_singleton_eq_erase, erase_insert hat] at hμ
    refine' ⟨ih.mp ⟨Pi.single h.choose (μ a * s h.choose) + μ * fun _ ↦ s a, ?_⟩, fun b hb ↦ ?_⟩
    · rw [prod_eq_mul_prod_diff_singleton h.choose_spec, ← mul_assoc, ←
        @if_pos _ _ h.choose_spec R (_ * _) 0, ← sum_pi_single', ← sum_add_distrib] at hμ
      rw [← hμ, sum_congr rfl]
      intro x hx
      dsimp -- Porting note: terms were showing as sort of `HAdd.hadd` instead of `+`
      -- this whole proof pretty much breaks and has to be rewritten from scratch
      rw [add_mul]
      congr 1
      · by_cases hx : x = h.choose
        · rw [hx, Pi.single_eq_same, Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne hx, Pi.single_eq_of_ne hx, zero_mul]
      · rw [mul_assoc]
        congr
        rw [prod_eq_prod_diff_singleton_mul (mem x hx) _, mul_comm]
        congr 2
        rw [sdiff_sdiff_comm, sdiff_singleton_eq_erase a, erase_insert hat]
    · have : IsCoprime (s b) (s a) :=
        ⟨μ a * ∏ i in t \ {b}, s i, ∑ i in t, μ i * ∏ j in t \ {i}, s j, ?_⟩
      · exact ⟨this.symm, this⟩
      rw [mul_assoc, ← prod_eq_prod_diff_singleton_mul hb, sum_mul, ← hμ, sum_congr rfl]
      intro x hx
      rw [mul_assoc]
      congr
      rw [prod_eq_prod_diff_singleton_mul (mem x hx) _]
      congr 2
      rw [sdiff_sdiff_comm, sdiff_singleton_eq_erase a, erase_insert hat]
  · rintro ⟨hs, Hb⟩
    obtain ⟨μ, hμ⟩ := ih.mpr hs
    obtain ⟨u, v, huv⟩ := IsCoprime.prod_left fun b hb ↦ (Hb b hb).right
    use fun i ↦ if i = a then u else v * μ i
    have hμ' : (∑ i in t, v * ((μ i * ∏ j in t \ {i}, s j) * s a)) = v * s a := by
      rw [← mul_sum, ← sum_mul, hμ, one_mul]
    rw [sum_cons, cons_eq_insert, sdiff_singleton_eq_erase, erase_insert hat, if_pos rfl,
      ← huv, ← hμ', sum_congr rfl]
    intro x hx
    rw [mul_assoc, if_neg fun ha : x = a ↦ hat (ha.casesOn hx)]
    rw [mul_assoc]
    congr
    rw [prod_eq_prod_diff_singleton_mul (mem x hx) _]
    congr 2
    rw [sdiff_sdiff_comm, sdiff_singleton_eq_erase a, erase_insert hat]
#align exists_sum_eq_one_iff_pairwise_coprime exists_sum_eq_one_iff_pairwise_coprime

theorem exists_sum_eq_one_iff_pairwise_coprime' [Fintype I] [Nonempty I] [DecidableEq I] :
    (∃ μ : I → R, (∑ i : I, μ i * ∏ j in {i}ᶜ, s j) = 1) ↔ Pairwise (IsCoprime on s) := by
  convert exists_sum_eq_one_iff_pairwise_coprime Finset.univ_nonempty (s := s) using 1
  simp only [Function.onFun, pairwise_subtype_iff_pairwise_finset', coe_univ, Set.pairwise_univ]
#align exists_sum_eq_one_iff_pairwise_coprime' exists_sum_eq_one_iff_pairwise_coprime'

-- Porting note: a lot of the capitalization wasn't working
theorem pairwise_coprime_iff_coprime_prod [DecidableEq I] :
    Pairwise (IsCoprime on fun i : t ↦ s i) ↔ ∀ i ∈ t, IsCoprime (s i) (∏ j in t \ {i}, s j) := by
  refine' ⟨fun hp i hi ↦ IsCoprime.prod_right_iff.mpr fun j hj ↦ ?_, fun hp ↦ ?_⟩
  · rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
    obtain ⟨hj, ji⟩ := hj
    refine @hp ⟨i, hi⟩ ⟨j, hj⟩ fun h ↦ ji (congrArg Subtype.val h).symm
    -- Porting note: is there a better way compared to the old `congr_arg coe h`?
  · rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    apply IsCoprime.prod_right_iff.mp (hp i hi)
    exact Finset.mem_sdiff.mpr ⟨hj, fun f ↦ h <| Subtype.ext (Finset.mem_singleton.mp f).symm⟩
#align pairwise_coprime_iff_coprime_prod pairwise_coprime_iff_coprime_prod

variable {m n : ℕ}

theorem IsCoprime.pow_left (H : IsCoprime x y) : IsCoprime (x ^ m) y := by
  rw [← Finset.card_range m, ← Finset.prod_const]
  exact IsCoprime.prod_left fun _ _ ↦ H
#align is_coprime.pow_left IsCoprime.pow_left

theorem IsCoprime.pow_right (H : IsCoprime x y) : IsCoprime x (y ^ n) := by
  rw [← Finset.card_range n, ← Finset.prod_const]
  exact IsCoprime.prod_right fun _ _ ↦ H
#align is_coprime.pow_right IsCoprime.pow_right

theorem IsCoprime.pow (H : IsCoprime x y) : IsCoprime (x ^ m) (y ^ n) :=
  H.pow_left.pow_right
#align is_coprime.pow IsCoprime.pow

theorem IsCoprime.pow_left_iff (hm : 0 < m) : IsCoprime (x ^ m) y ↔ IsCoprime x y := by
  refine' ⟨fun h ↦ _, IsCoprime.pow_left⟩
  rw [← Finset.card_range m, ← Finset.prod_const] at h
  exact h.of_prod_left 0 (Finset.mem_range.mpr hm)
  -- Porting note: I'm not sure why `finset` didn't get corrected automatically to `Finset`
  -- by Mathport, nor whether this is an issue
#align is_coprime.pow_left_iff IsCoprime.pow_left_iff

theorem IsCoprime.pow_right_iff (hm : 0 < m) : IsCoprime x (y ^ m) ↔ IsCoprime x y :=
  isCoprime_comm.trans <| (IsCoprime.pow_left_iff hm).trans <| isCoprime_comm
#align is_coprime.pow_right_iff IsCoprime.pow_right_iff

theorem IsCoprime.pow_iff (hm : 0 < m) (hn : 0 < n) : IsCoprime (x ^ m) (y ^ n) ↔ IsCoprime x y :=
  (IsCoprime.pow_left_iff hm).trans <| IsCoprime.pow_right_iff hn
#align is_coprime.pow_iff IsCoprime.pow_iff

end IsCoprime

section RelPrime

variable {α I} [CommMonoid α] [DecompositionMonoid α] {x y z : α} {s : I → α} {t : Finset I}

theorem IsRelPrime.prod_left : (∀ i ∈ t, IsRelPrime (s i) x) → IsRelPrime (∏ i in t, s i) x := by
  classical
  refine Finset.induction_on t (fun _ ↦ isRelPrime_one_left) fun b t hbt ih H ↦ ?_
  rw [Finset.prod_insert hbt]
  rw [Finset.forall_mem_insert] at H
  exact H.1.mul_left (ih H.2)

theorem IsRelPrime.prod_right : (∀ i ∈ t, IsRelPrime x (s i)) → IsRelPrime x (∏ i in t, s i) := by
  simpa only [isRelPrime_comm] using IsRelPrime.prod_left (α := α)

theorem IsRelPrime.prod_left_iff : IsRelPrime (∏ i in t, s i) x ↔ ∀ i ∈ t, IsRelPrime (s i) x := by
  classical
  refine Finset.induction_on t (iff_of_true isRelPrime_one_left fun _ ↦ by simp) fun b t hbt ih ↦ ?_
  rw [Finset.prod_insert hbt, IsRelPrime.mul_left_iff, ih, Finset.forall_mem_insert]

theorem IsRelPrime.prod_right_iff : IsRelPrime x (∏ i in t, s i) ↔ ∀ i ∈ t, IsRelPrime x (s i) := by
  simpa only [isRelPrime_comm] using IsRelPrime.prod_left_iff (α := α)

theorem IsRelPrime.of_prod_left (H1 : IsRelPrime (∏ i in t, s i) x) (i : I) (hit : i ∈ t) :
    IsRelPrime (s i) x :=
  IsRelPrime.prod_left_iff.1 H1 i hit

theorem IsRelPrime.of_prod_right (H1 : IsRelPrime x (∏ i in t, s i)) (i : I) (hit : i ∈ t) :
    IsRelPrime x (s i) :=
  IsRelPrime.prod_right_iff.1 H1 i hit

theorem Finset.prod_dvd_of_isRelPrime :
    (t : Set I).Pairwise (IsRelPrime on s) → (∀ i ∈ t, s i ∣ z) → (∏ x in t, s x) ∣ z := by
  classical
  exact Finset.induction_on t (fun _ _ ↦ one_dvd z)
    (by
      intro a r har ih Hs Hs1
      rw [Finset.prod_insert har]
      have aux1 : a ∈ (↑(insert a r) : Set I) := Finset.mem_insert_self a r
      refine'
        (IsRelPrime.prod_right fun i hir ↦
              Hs aux1 (Finset.mem_insert_of_mem hir) <| by
                rintro rfl
                exact har hir).mul_dvd
          (Hs1 a aux1) (ih (Hs.mono _) fun i hi ↦ Hs1 i <| Finset.mem_insert_of_mem hi)
      simp only [Finset.coe_insert, Set.subset_insert])

theorem Fintype.prod_dvd_of_isRelPrime [Fintype I] (Hs : Pairwise (IsRelPrime on s))
    (Hs1 : ∀ i, s i ∣ z) : (∏ x, s x) ∣ z :=
  Finset.prod_dvd_of_isRelPrime (Hs.set_pairwise _) fun i _ ↦ Hs1 i

theorem pairwise_isRelPrime_iff_isRelPrime_prod [DecidableEq I] :
    Pairwise (IsRelPrime on fun i : t ↦ s i) ↔ ∀ i ∈ t, IsRelPrime (s i) (∏ j in t \ {i}, s j) := by
  refine' ⟨fun hp i hi ↦ IsRelPrime.prod_right_iff.mpr fun j hj ↦ ?_, fun hp ↦ ?_⟩
  · rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
    obtain ⟨hj, ji⟩ := hj
    exact @hp ⟨i, hi⟩ ⟨j, hj⟩ fun h ↦ ji (congrArg Subtype.val h).symm
  · rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    apply IsRelPrime.prod_right_iff.mp (hp i hi)
    exact Finset.mem_sdiff.mpr ⟨hj, fun f ↦ h <| Subtype.ext (Finset.mem_singleton.mp f).symm⟩

namespace IsRelPrime

variable {m n : ℕ}

theorem pow_left (H : IsRelPrime x y) : IsRelPrime (x ^ m) y := by
  rw [← Finset.card_range m, ← Finset.prod_const]
  exact IsRelPrime.prod_left fun _ _ ↦ H

theorem pow_right (H : IsRelPrime x y) : IsRelPrime x (y ^ n) := by
  rw [← Finset.card_range n, ← Finset.prod_const]
  exact IsRelPrime.prod_right fun _ _ ↦ H

theorem pow (H : IsRelPrime x y) : IsRelPrime (x ^ m) (y ^ n) :=
  H.pow_left.pow_right

theorem pow_left_iff (hm : 0 < m) : IsRelPrime (x ^ m) y ↔ IsRelPrime x y := by
  refine' ⟨fun h ↦ _, IsRelPrime.pow_left⟩
  rw [← Finset.card_range m, ← Finset.prod_const] at h
  exact h.of_prod_left 0 (Finset.mem_range.mpr hm)

theorem pow_right_iff (hm : 0 < m) : IsRelPrime x (y ^ m) ↔ IsRelPrime x y :=
  isRelPrime_comm.trans <| (IsRelPrime.pow_left_iff hm).trans <| isRelPrime_comm

theorem pow_iff (hm : 0 < m) (hn : 0 < n) :
    IsRelPrime (x ^ m) (y ^ n) ↔ IsRelPrime x y :=
  (IsRelPrime.pow_left_iff hm).trans (IsRelPrime.pow_right_iff hn)

end IsRelPrime

end RelPrime
