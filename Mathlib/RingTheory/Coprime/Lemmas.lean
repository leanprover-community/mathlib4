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

These lemmas are in a separate file to the definition of `IsCoprime` as they require more imports.

Notably, this includes lemmas about `Finset.prod` as this requires importing big_operators, and
lemmas about `HasPow` since these are easiest to prove via `Finset.prod`.

-/

universe u v

variable {R : Type u} {I : Type v} [CommSemiring R] {x y z : R} {s : I → R} {t : Finset I}

open BigOperators

section

open Classical

theorem Int.isCoprime_iff_gcd_eq_one {m n : ℤ} : IsCoprime m n ↔ Int.gcd m n = 1 := by
  constructor
  -- ⊢ IsCoprime m n → gcd m n = 1
  · rintro ⟨a, b, h⟩
    -- ⊢ gcd m n = 1
    have : 1 = m * a + n * b := by rwa [mul_comm m, mul_comm n, eq_comm]
    -- ⊢ gcd m n = 1
    exact Nat.dvd_one.mp (Int.gcd_dvd_iff.mpr ⟨a, b, this⟩)
    -- 🎉 no goals
  · rw [← Int.ofNat_inj, IsCoprime, Int.gcd_eq_gcd_ab, mul_comm m, mul_comm n, Nat.cast_one]
    -- ⊢ gcdA m n * m + gcdB m n * n = 1 → ∃ a b, a * m + b * n = 1
    intro h
    -- ⊢ ∃ a b, a * m + b * n = 1
    exact ⟨_, _, h⟩
    -- 🎉 no goals

theorem Nat.isCoprime_iff_coprime {m n : ℕ} : IsCoprime (m : ℤ) n ↔ Nat.coprime m n := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.coe_nat_gcd]
  -- 🎉 no goals
#align nat.is_coprime_iff_coprime Nat.isCoprime_iff_coprime

alias ⟨IsCoprime.nat_coprime, Nat.coprime.isCoprime⟩ := Nat.isCoprime_iff_coprime
#align is_coprime.nat_coprime IsCoprime.nat_coprime
#align nat.coprime.is_coprime Nat.coprime.isCoprime

theorem ne_zero_or_ne_zero_of_nat_coprime {A : Type u} [CommRing A] [Nontrivial A] {a b : ℕ}
    (h : Nat.coprime a b) : (a : A) ≠ 0 ∨ (b : A) ≠ 0 :=
  IsCoprime.ne_zero_or_ne_zero (R := A) <| by
    simpa only [map_natCast] using IsCoprime.map (Nat.coprime.isCoprime h) (Int.castRingHom A)
    -- 🎉 no goals

theorem IsCoprime.prod_left : (∀ i ∈ t, IsCoprime (s i) x) → IsCoprime (∏ i in t, s i) x :=
  Finset.induction_on t (fun _ ↦ isCoprime_one_left) fun b t hbt ih H ↦ by
    rw [Finset.prod_insert hbt]
    -- ⊢ IsCoprime (s b * ∏ x in t, s x) x
    rw [Finset.forall_mem_insert] at H
    -- ⊢ IsCoprime (s b * ∏ x in t, s x) x
    exact H.1.mul_left (ih H.2)
    -- 🎉 no goals
#align is_coprime.prod_left IsCoprime.prod_left

theorem IsCoprime.prod_right : (∀ i ∈ t, IsCoprime x (s i)) → IsCoprime x (∏ i in t, s i) := by
  simpa only [isCoprime_comm] using IsCoprime.prod_left (R := R)
  -- 🎉 no goals
#align is_coprime.prod_right IsCoprime.prod_right

theorem IsCoprime.prod_left_iff : IsCoprime (∏ i in t, s i) x ↔ ∀ i ∈ t, IsCoprime (s i) x :=
  Finset.induction_on t (iff_of_true isCoprime_one_left fun _ ↦ by simp) fun b t hbt ih ↦ by
                                                                   -- 🎉 no goals
    rw [Finset.prod_insert hbt, IsCoprime.mul_left_iff, ih, Finset.forall_mem_insert]
    -- 🎉 no goals
#align is_coprime.prod_left_iff IsCoprime.prod_left_iff

theorem IsCoprime.prod_right_iff : IsCoprime x (∏ i in t, s i) ↔ ∀ i ∈ t, IsCoprime x (s i) := by
  simpa only [isCoprime_comm] using IsCoprime.prod_left_iff (R := R)
  -- 🎉 no goals
#align is_coprime.prod_right_iff IsCoprime.prod_right_iff

theorem IsCoprime.of_prod_left (H1 : IsCoprime (∏ i in t, s i) x) (i : I) (hit : i ∈ t) :
    IsCoprime (s i) x :=
  IsCoprime.prod_left_iff.1 H1 i hit
#align is_coprime.of_prod_left IsCoprime.of_prod_left

theorem IsCoprime.of_prod_right (H1 : IsCoprime x (∏ i in t, s i)) (i : I) (hit : i ∈ t) :
    IsCoprime x (s i) :=
  IsCoprime.prod_right_iff.1 H1 i hit
#align is_coprime.of_prod_right IsCoprime.of_prod_right

-- porting note: removed names of things due to linter, but they seem helpful
theorem Finset.prod_dvd_of_coprime :
    ∀ (_ : (t : Set I).Pairwise (IsCoprime on s)) (_ : ∀ i ∈ t, s i ∣ z), (∏ x in t, s x) ∣ z :=
  Finset.induction_on t (fun _ _ ↦ one_dvd z)
    (by
      intro a r har ih Hs Hs1
      -- ⊢ ∏ x in insert a r, s x ∣ z
      rw [Finset.prod_insert har]
      -- ⊢ s a * ∏ x in r, s x ∣ z
      have aux1 : a ∈ (↑(insert a r) : Set I) := Finset.mem_insert_self a r
      -- ⊢ s a * ∏ x in r, s x ∣ z
      refine'
        (IsCoprime.prod_right fun i hir ↦
              Hs aux1 (Finset.mem_insert_of_mem hir) <| by
                rintro rfl
                exact har hir).mul_dvd
          (Hs1 a aux1) (ih (Hs.mono _) fun i hi ↦ Hs1 i <| Finset.mem_insert_of_mem hi)
      simp only [Finset.coe_insert, Set.subset_insert])
      -- 🎉 no goals
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
  -- ⊢ ∀ (a : I), (∃ μ, ∑ i in {a}, μ i * ∏ j in {a} \ {i}, s j = 1) ↔ Pairwise (Is …
  · simp only [sum_singleton, Finset.sdiff_self, prod_empty, mul_one, exists_apply_eq,
               Pairwise, Ne.def, true_iff_iff]
    rintro a ⟨i, hi⟩ ⟨j, hj⟩ h
    -- ⊢ (IsCoprime on fun i => s ↑i) { val := i, property := hi } { val := j, proper …
    rw [Finset.mem_singleton] at hi hj
    -- ⊢ (IsCoprime on fun i => s ↑i) { val := i, property := hi✝ } { val := j, prope …
    simp [hi, hj] at h
    -- 🎉 no goals
  intro a t hat h ih
  -- ⊢ (∃ μ, ∑ i in cons a t hat, μ i * ∏ j in cons a t hat \ {i}, s j = 1) ↔ Pairw …
  rw [pairwise_cons']
  -- ⊢ (∃ μ, ∑ i in cons a t hat, μ i * ∏ j in cons a t hat \ {i}, s j = 1) ↔ Pairw …
  have mem : ∀ x ∈ t, a ∈ insert a t \ {x} := fun x hx ↦ by
    rw [mem_sdiff, mem_singleton]
    refine ⟨mem_insert_self _ _, fun ha ↦ hat (ha ▸ hx)⟩
  constructor
  -- ⊢ (∃ μ, ∑ i in cons a t hat, μ i * ∏ j in cons a t hat \ {i}, s j = 1) → Pairw …
  · rintro ⟨μ, hμ⟩
    -- ⊢ Pairwise (IsCoprime on fun a => s ↑a) ∧ ∀ (b : I), b ∈ t → IsCoprime (s a) ( …
    rw [sum_cons, cons_eq_insert, sdiff_singleton_eq_erase, erase_insert hat] at hμ
    -- ⊢ Pairwise (IsCoprime on fun a => s ↑a) ∧ ∀ (b : I), b ∈ t → IsCoprime (s a) ( …
    refine' ⟨ih.mp ⟨Pi.single h.choose (μ a * s h.choose) + μ * fun _ ↦ s a, ?_⟩, fun b hb ↦ ?_⟩
    -- ⊢ ∑ i in t, (Pi.single (Exists.choose h) (μ a * s (Exists.choose h)) + μ * fun …
    · rw [prod_eq_mul_prod_diff_singleton h.choose_spec, ← mul_assoc, ←
        @if_pos _ _ h.choose_spec R (_ * _) 0, ← sum_pi_single', ← sum_add_distrib] at hμ
      rw [← hμ, sum_congr rfl]
      -- ⊢ ∀ (x : I), x ∈ t → (Pi.single (Exists.choose h) (μ a * s (Exists.choose h))  …
      intro x hx
      -- ⊢ (Pi.single (Exists.choose h) (μ a * s (Exists.choose h)) + μ * fun x => s a) …
      dsimp -- porting note: terms were showing as sort of `HAdd.hadd` instead of `+`
      -- ⊢ (Pi.single (Exists.choose h) (μ a * s (Exists.choose h)) x + μ x * s a) * ∏  …
      -- this whole proof pretty much breaks and has to be rewritten from scratch
      rw [add_mul]
      -- ⊢ Pi.single (Exists.choose h) (μ a * s (Exists.choose h)) x * ∏ j in t \ {x},  …
      congr 1
      -- ⊢ Pi.single (Exists.choose h) (μ a * s (Exists.choose h)) x * ∏ j in t \ {x},  …
      · by_cases hx : x = h.choose
        -- ⊢ Pi.single (Exists.choose h) (μ a * s (Exists.choose h)) x * ∏ j in t \ {x},  …
        · rw [hx, Pi.single_eq_same, Pi.single_eq_same]
          -- 🎉 no goals
        · rw [Pi.single_eq_of_ne hx, Pi.single_eq_of_ne hx, zero_mul]
          -- 🎉 no goals
      · rw [mul_assoc]
        -- ⊢ μ x * (s a * ∏ j in t \ {x}, s j) = μ x * ∏ j in insert a t \ {x}, s j
        congr
        -- ⊢ s a * ∏ j in t \ {x}, s j = ∏ j in insert a t \ {x}, s j
        rw [prod_eq_prod_diff_singleton_mul (mem x hx) _, mul_comm]
        -- ⊢ (∏ j in t \ {x}, s j) * s a = (∏ x in (insert a t \ {x}) \ {a}, s x) * s a
        congr 2
        -- ⊢ t \ {x} = (insert a t \ {x}) \ {a}
        rw [sdiff_sdiff_comm, sdiff_singleton_eq_erase a, erase_insert hat]
        -- 🎉 no goals
    · have : IsCoprime (s b) (s a) :=
        ⟨μ a * ∏ i in t \ {b}, s i, ∑ i in t, μ i * ∏ j in t \ {i}, s j, ?_⟩
      · exact ⟨this.symm, this⟩
        -- 🎉 no goals
      rw [mul_assoc, ← prod_eq_prod_diff_singleton_mul hb, sum_mul, ← hμ, sum_congr rfl]
      -- ⊢ ∀ (x : I), x ∈ t → (μ x * ∏ j in t \ {x}, s j) * s a = μ x * ∏ j in insert a …
      intro x hx
      -- ⊢ (μ x * ∏ j in t \ {x}, s j) * s a = μ x * ∏ j in insert a t \ {x}, s j
      rw [mul_assoc]
      -- ⊢ μ x * ((∏ j in t \ {x}, s j) * s a) = μ x * ∏ j in insert a t \ {x}, s j
      congr
      -- ⊢ (∏ j in t \ {x}, s j) * s a = ∏ j in insert a t \ {x}, s j
      rw [prod_eq_prod_diff_singleton_mul (mem x hx) _]
      -- ⊢ (∏ j in t \ {x}, s j) * s a = (∏ x in (insert a t \ {x}) \ {a}, s x) * s a
      congr 2
      -- ⊢ t \ {x} = (insert a t \ {x}) \ {a}
      rw [sdiff_sdiff_comm, sdiff_singleton_eq_erase a, erase_insert hat]
      -- 🎉 no goals
  · rintro ⟨hs, Hb⟩
    -- ⊢ ∃ μ, ∑ i in cons a t hat, μ i * ∏ j in cons a t hat \ {i}, s j = 1
    obtain ⟨μ, hμ⟩ := ih.mpr hs
    -- ⊢ ∃ μ, ∑ i in cons a t hat, μ i * ∏ j in cons a t hat \ {i}, s j = 1
    obtain ⟨u, v, huv⟩ := IsCoprime.prod_left fun b hb ↦ (Hb b hb).right
    -- ⊢ ∃ μ, ∑ i in cons a t hat, μ i * ∏ j in cons a t hat \ {i}, s j = 1
    use fun i ↦ if i = a then u else v * μ i
    -- ⊢ ∑ i in cons a t hat, (if i = a then u else v * μ i) * ∏ j in cons a t hat \  …
    have hμ' : (∑ i in t, v * ((μ i * ∏ j in t \ {i}, s j) * s a)) = v * s a := by
      rw [← mul_sum, ← sum_mul, hμ, one_mul]
    rw [sum_cons, cons_eq_insert, sdiff_singleton_eq_erase, erase_insert hat, if_pos rfl,
      ← huv, ← hμ', sum_congr rfl]
    intro x hx
    -- ⊢ (if x = a then u else v * μ x) * ∏ j in insert a t \ {x}, s j = v * ((μ x *  …
    rw [mul_assoc, if_neg fun ha : x = a ↦ hat (ha.casesOn hx)]
    -- ⊢ v * μ x * ∏ j in insert a t \ {x}, s j = v * (μ x * ((∏ j in t \ {x}, s j) * …
    rw [mul_assoc]
    -- ⊢ v * (μ x * ∏ j in insert a t \ {x}, s j) = v * (μ x * ((∏ j in t \ {x}, s j) …
    congr
    -- ⊢ ∏ j in insert a t \ {x}, s j = (∏ j in t \ {x}, s j) * s a
    rw [prod_eq_prod_diff_singleton_mul (mem x hx) _]
    -- ⊢ (∏ x in (insert a t \ {x}) \ {a}, s x) * s a = (∏ j in t \ {x}, s j) * s a
    congr 2
    -- ⊢ (insert a t \ {x}) \ {a} = t \ {x}
    rw [sdiff_sdiff_comm, sdiff_singleton_eq_erase a, erase_insert hat]
    -- 🎉 no goals
#align exists_sum_eq_one_iff_pairwise_coprime exists_sum_eq_one_iff_pairwise_coprime

theorem exists_sum_eq_one_iff_pairwise_coprime' [Fintype I] [Nonempty I] [DecidableEq I] :
    (∃ μ : I → R, (∑ i : I, μ i * ∏ j in {i}ᶜ, s j) = 1) ↔ Pairwise (IsCoprime on s) := by
  convert exists_sum_eq_one_iff_pairwise_coprime Finset.univ_nonempty (s := s) using 1
  -- ⊢ Pairwise (IsCoprime on s) ↔ Pairwise (IsCoprime on fun i => s ↑i)
  simp only [Function.onFun, pairwise_subtype_iff_pairwise_finset', coe_univ, Set.pairwise_univ]
  -- 🎉 no goals
#align exists_sum_eq_one_iff_pairwise_coprime' exists_sum_eq_one_iff_pairwise_coprime'

-- porting note: a lot of the capitalization wasn't working
theorem pairwise_coprime_iff_coprime_prod [DecidableEq I] :
    Pairwise (IsCoprime on fun i : t ↦ s i) ↔ ∀ i ∈ t, IsCoprime (s i) (∏ j in t \ {i}, s j) := by
  refine' ⟨fun hp i hi ↦ IsCoprime.prod_right_iff.mpr fun j hj ↦ ?_, fun hp ↦ ?_⟩
  -- ⊢ IsCoprime (s i) (s j)
  · rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
    -- ⊢ IsCoprime (s i) (s j)
    obtain ⟨hj, ji⟩ := hj
    -- ⊢ IsCoprime (s i) (s j)
    refine @hp ⟨i, hi⟩ ⟨j, hj⟩ fun h ↦ ji (congrArg Subtype.val h).symm
    -- 🎉 no goals
    -- porting note: is there a better way compared to the old `congr_arg coe h`?
  · rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    -- ⊢ (IsCoprime on fun i => s ↑i) { val := i, property := hi } { val := j, proper …
    apply IsCoprime.prod_right_iff.mp (hp i hi)
    -- ⊢ ↑{ val := j, property := hj } ∈ t \ {i}
    exact Finset.mem_sdiff.mpr ⟨hj, fun f ↦ h <| Subtype.ext (Finset.mem_singleton.mp f).symm⟩
    -- 🎉 no goals
#align pairwise_coprime_iff_coprime_prod pairwise_coprime_iff_coprime_prod

variable {m n : ℕ}

theorem IsCoprime.pow_left (H : IsCoprime x y) : IsCoprime (x ^ m) y := by
  rw [← Finset.card_range m, ← Finset.prod_const]
  -- ⊢ IsCoprime (∏ _x in range m, x) y
  exact IsCoprime.prod_left fun _ _ ↦ H
  -- 🎉 no goals
#align is_coprime.pow_left IsCoprime.pow_left

theorem IsCoprime.pow_right (H : IsCoprime x y) : IsCoprime x (y ^ n) := by
  rw [← Finset.card_range n, ← Finset.prod_const]
  -- ⊢ IsCoprime x (∏ _x in range n, y)
  exact IsCoprime.prod_right fun _ _ ↦ H
  -- 🎉 no goals
#align is_coprime.pow_right IsCoprime.pow_right

theorem IsCoprime.pow (H : IsCoprime x y) : IsCoprime (x ^ m) (y ^ n) :=
  H.pow_left.pow_right
#align is_coprime.pow IsCoprime.pow

theorem IsCoprime.pow_left_iff (hm : 0 < m) : IsCoprime (x ^ m) y ↔ IsCoprime x y := by
  refine' ⟨fun h ↦ _, IsCoprime.pow_left⟩
  -- ⊢ IsCoprime x y
  rw [← Finset.card_range m, ← Finset.prod_const] at h
  -- ⊢ IsCoprime x y
  exact h.of_prod_left 0 (Finset.mem_range.mpr hm)
  -- 🎉 no goals
  -- porting note: I'm not sure why `finset` didn't get corrected automatically to `Finset`
  -- by Mathport, nor whether this is an issue
#align is_coprime.pow_left_iff IsCoprime.pow_left_iff

theorem IsCoprime.pow_right_iff (hm : 0 < m) : IsCoprime x (y ^ m) ↔ IsCoprime x y :=
  isCoprime_comm.trans <| (IsCoprime.pow_left_iff hm).trans <| isCoprime_comm
#align is_coprime.pow_right_iff IsCoprime.pow_right_iff

theorem IsCoprime.pow_iff (hm : 0 < m) (hn : 0 < n) : IsCoprime (x ^ m) (y ^ n) ↔ IsCoprime x y :=
  (IsCoprime.pow_left_iff hm).trans <| IsCoprime.pow_right_iff hn
#align is_coprime.pow_iff IsCoprime.pow_iff
