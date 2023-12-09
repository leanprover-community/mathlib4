/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir
-/
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Choose.Sum

#align_import data.complex.exponential from "leanprover-community/mathlib"@"a8b2226cfb0a79f5986492053fc49b1a0c6aeffb"

/-!
# Exponential, trigonometric and hyperbolic trigonometric functions

This file contains the definitions of the real and complex exponential, sine, cosine, tangent,
hyperbolic sine, hyperbolic cosine, and hyperbolic tangent functions.

-/


@[inherit_doc]
local notation "abs'" => Abs.abs

open IsAbsoluteValue

open Classical BigOperators ComplexConjugate

section

open Real IsAbsoluteValue Finset

section

variable {α : Type*} {β : Type*} [Ring β] [LinearOrderedField α] [Archimedean α] {abv : β → α}
  [IsAbsoluteValue abv]

theorem isCauSeq_of_decreasing_bounded (f : ℕ → α) {a : α} {m : ℕ} (ham : ∀ n ≥ m, |f n| ≤ a)
    (hnm : ∀ n ≥ m, f n.succ ≤ f n) : IsCauSeq abs f := fun ε ε0 => by
  let ⟨k, hk⟩ := Archimedean.arch a ε0
  have h : ∃ l, ∀ n ≥ m, a - l • ε < f n :=
    ⟨k + k + 1, fun n hnm =>
      lt_of_lt_of_le
        (show a - (k + (k + 1)) • ε < -|f n| from
          lt_neg.1 <|
            lt_of_le_of_lt (ham n hnm)
              (by
                rw [neg_sub, lt_sub_iff_add_lt, add_nsmul, add_nsmul, one_nsmul]
                exact add_lt_add_of_le_of_lt hk (lt_of_le_of_lt hk (lt_add_of_pos_right _ ε0))))
        (neg_le.2 <| abs_neg (f n) ▸ le_abs_self _)⟩
  let l := Nat.find h
  have hl : ∀ n : ℕ, n ≥ m → f n > a - l • ε := Nat.find_spec h
  have hl0 : l ≠ 0 := fun hl0 =>
    not_lt_of_ge (ham m le_rfl)
      (lt_of_lt_of_le (by have := hl m (le_refl m); simpa [hl0] using this) (le_abs_self (f m)))
  cases' not_forall.1 (Nat.find_min h (Nat.pred_lt hl0)) with i hi
  rw [not_imp, not_lt] at hi
  exists i
  intro j hj
  have hfij : f j ≤ f i := (Nat.rel_of_forall_rel_succ_of_le_of_le (· ≥ ·) hnm hi.1 hj).le
  rw [abs_of_nonpos (sub_nonpos.2 hfij), neg_sub, sub_lt_iff_lt_add']
  calc
    f i ≤ a - Nat.pred l • ε := hi.2
    _ = a - l • ε + ε := by
      conv =>
        rhs
        rw [← Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hl0), succ_nsmul', sub_add,
          add_sub_cancel]
    _ < f j + ε := add_lt_add_right (hl j (le_trans hi.1 hj)) _
#align is_cau_of_decreasing_bounded isCauSeq_of_decreasing_bounded

theorem isCauSeq_of_mono_bounded (f : ℕ → α) {a : α} {m : ℕ} (ham : ∀ n ≥ m, |f n| ≤ a)
    (hnm : ∀ n ≥ m, f n ≤ f n.succ) : IsCauSeq abs f := by
  refine'
    @Eq.ndrecOn (ℕ → α) _ (IsCauSeq abs) _ _
      (-⟨_, @isCauSeq_of_decreasing_bounded _ _ _ (fun n => -f n) a m (by simpa) (by simpa)⟩ :
          CauSeq α abs).2
  ext
  exact neg_neg _
#align is_cau_of_mono_bounded isCauSeq_of_mono_bounded

end

section NoArchimedean

variable {α : Type*} {β : Type*} [Ring β] [LinearOrderedField α] {abv : β → α}
  [IsAbsoluteValue abv]

theorem isCauSeq_series_of_abv_le_of_isCauSeq {f : ℕ → β} {g : ℕ → α} (n : ℕ) :
    (∀ m, n ≤ m → abv (f m) ≤ g m) →
      (IsCauSeq abs fun n => ∑ i in range n, g i) → IsCauSeq abv fun n => ∑ i in range n, f i := by
  intro hm hg ε ε0
  cases' hg (ε / 2) (div_pos ε0 (by norm_num)) with i hi
  exists max n i
  intro j ji
  have hi₁ := hi j (le_trans (le_max_right n i) ji)
  have hi₂ := hi (max n i) (le_max_right n i)
  have sub_le :=
    abs_sub_le (∑ k in range j, g k) (∑ k in range i, g k) (∑ k in range (max n i), g k)
  have := add_lt_add hi₁ hi₂
  rw [abs_sub_comm (∑ k in range (max n i), g k), add_halves ε] at this
  refine' lt_of_le_of_lt (le_trans (le_trans _ (le_abs_self _)) sub_le) this
  generalize hk : j - max n i = k
  clear this hi₂ hi₁ hi ε0 ε hg sub_le
  rw [tsub_eq_iff_eq_add_of_le ji] at hk
  rw [hk]
  dsimp only
  clear hk ji j
  induction' k with k' hi
  · simp [abv_zero abv]
  · simp only [Nat.succ_add, Nat.succ_eq_add_one, Finset.sum_range_succ_comm]
    simp only [add_assoc, sub_eq_add_neg]
    refine le_trans (abv_add _ _ _) ?_
    simp only [sub_eq_add_neg] at hi
    refine add_le_add (hm _ (le_add_of_nonneg_of_le (Nat.zero_le _) (le_max_left _ _))) hi
#align is_cau_series_of_abv_le_cau isCauSeq_series_of_abv_le_of_isCauSeq

theorem isCauSeq_series_of_abv_isCauSeq {f : ℕ → β} :
    (IsCauSeq abs fun m => ∑ n in range m, abv (f n)) → IsCauSeq abv fun m => ∑ n in range m, f n :=
  isCauSeq_series_of_abv_le_of_isCauSeq 0 fun _ _ => le_rfl
#align is_cau_series_of_abv_cau isCauSeq_series_of_abv_isCauSeq

end NoArchimedean

section

variable {α : Type*} [LinearOrderedField α] [Archimedean α]

theorem isCauSeq_geo_series {β : Type*} [Ring β] [Nontrivial β] {abv : β → α} [IsAbsoluteValue abv]
    (x : β) (hx1 : abv x < 1) : IsCauSeq abv fun n => ∑ m in range n, x ^ m :=
  have hx1' : abv x ≠ 1 := fun h => by simp [h, lt_irrefl] at hx1
  isCauSeq_series_of_abv_isCauSeq
    (by
      simp only [abv_pow abv, geom_sum_eq hx1']
      conv in _ / _ => rw [← neg_div_neg_eq, neg_sub, neg_sub]
      have : 0 < 1 - abv x := sub_pos.2 hx1
      refine' @isCauSeq_of_mono_bounded _ _ _ _ ((1 : α) / (1 - abv x)) 0 _ _
      · intro n _
        rw [abs_of_nonneg]
        gcongr
        · exact sub_le_self _ (abv_pow abv x n ▸ abv_nonneg _ _)
        refine' div_nonneg (sub_nonneg.2 _) (sub_nonneg.2 <| le_of_lt hx1)
        exact pow_le_one _ (by positivity) hx1.le
      · intro n _
        rw [←one_mul (abv x ^ n), pow_succ]
        gcongr)
#align is_cau_geo_series isCauSeq_geo_series

theorem isCauSeq_geo_series_const (a : α) {x : α} (hx1 : |x| < 1) :
    IsCauSeq abs fun m => ∑ n in range m, (a * x ^ n) := by
  have : IsCauSeq abs fun m => a * ∑ n in range m, (x ^ n) :=
    (CauSeq.const abs a *
      (show CauSeq α abs from ⟨fun n => ∑ m in range n, x ^ m, isCauSeq_geo_series x hx1⟩)).2
  simpa [mul_sum] using this
#align is_cau_geo_series_const isCauSeq_geo_series_const

variable {β : Type*} [Ring β] {abv : β → α} [IsAbsoluteValue abv]

theorem series_ratio_test {f : ℕ → β} (n : ℕ) (r : α) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ m, n ≤ m → abv (f m.succ) ≤ r * abv (f m)) :
    IsCauSeq abv fun m => ∑ n in range m, f n := by
  have har1 : |r| < 1 := by rwa [abs_of_nonneg hr0]
  refine'
    isCauSeq_series_of_abv_le_of_isCauSeq n.succ _
      (isCauSeq_geo_series_const (abv (f n.succ) * r⁻¹ ^ n.succ) har1)
  intro m hmn
  cases' Classical.em (r = 0) with r_zero r_ne_zero
  · have m_pos := lt_of_lt_of_le (Nat.succ_pos n) hmn
    have := h m.pred (Nat.le_of_succ_le_succ (by rwa [Nat.succ_pred_eq_of_pos m_pos]))
    simpa [r_zero, Nat.succ_pred_eq_of_pos m_pos, pow_succ] using this
  generalize hk : m - n.succ = k
  have r_pos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm r_ne_zero)
  replace hk : m = k + n.succ := (tsub_eq_iff_eq_add_of_le hmn).1 hk
  induction' k with k ih generalizing m n
  · rw [hk, Nat.zero_add, mul_right_comm, inv_pow _ _, ← div_eq_mul_inv, mul_div_cancel]
    exact (ne_of_lt (pow_pos r_pos _)).symm
  · have kn : k + n.succ ≥ n.succ := by
      rw [← zero_add n.succ]; exact add_le_add (Nat.zero_le _) (by simp)
    erw [hk, Nat.succ_add, pow_succ' r, ← mul_assoc]
    refine
      le_trans (by rw [mul_comm] <;> exact h _ (Nat.le_of_succ_le kn))
        (mul_le_mul_of_nonneg_right ?_ hr0)
    exact ih _ h _ (by simp) rfl
#align series_ratio_test series_ratio_test

theorem sum_range_diag_flip {α : Type*} [AddCommMonoid α] (n : ℕ) (f : ℕ → ℕ → α) :
    (∑ m in range n, ∑ k in range (m + 1), f k (m - k)) =
      ∑ m in range n, ∑ k in range (n - m), f m k := by
  rw [sum_sigma', sum_sigma']
  exact
    sum_bij (fun a _ => ⟨a.2, a.1 - a.2⟩)
      (fun a ha =>
        have h₁ : a.1 < n := mem_range.1 (mem_sigma.1 ha).1
        have h₂ : a.2 < Nat.succ a.1 := mem_range.1 (mem_sigma.1 ha).2
        mem_sigma.2
          ⟨mem_range.2 (lt_of_lt_of_le h₂ h₁),
            mem_range.2 ((tsub_lt_tsub_iff_right (Nat.le_of_lt_succ h₂)).2 h₁)⟩)
      (fun _ _ => rfl)
      (fun ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ha hb h =>
        have ha : a₁ < n ∧ a₂ ≤ a₁ :=
          ⟨mem_range.1 (mem_sigma.1 ha).1, Nat.le_of_lt_succ (mem_range.1 (mem_sigma.1 ha).2)⟩
        have hb : b₁ < n ∧ b₂ ≤ b₁ :=
          ⟨mem_range.1 (mem_sigma.1 hb).1, Nat.le_of_lt_succ (mem_range.1 (mem_sigma.1 hb).2)⟩
        have h : a₂ = b₂ ∧ _ := by simpa using h
        have h' : a₁ = b₁ - b₂ + a₂ := (tsub_eq_iff_eq_add_of_le ha.2).1 (eq_of_heq h.2)
        Sigma.mk.inj_iff.2 ⟨tsub_add_cancel_of_le hb.2 ▸ h'.symm ▸ h.1 ▸ rfl, heq_of_eq h.1⟩)
      fun ⟨a₁, a₂⟩ ha =>
      have ha : a₁ < n ∧ a₂ < n - a₁ :=
        ⟨mem_range.1 (mem_sigma.1 ha).1, mem_range.1 (mem_sigma.1 ha).2⟩
      ⟨⟨a₂ + a₁, a₁⟩,
        ⟨mem_sigma.2
            ⟨mem_range.2 (lt_tsub_iff_right.1 ha.2),
              mem_range.2 (Nat.lt_succ_of_le (Nat.le_add_left _ _))⟩,
          Sigma.mk.inj_iff.2 ⟨rfl, heq_of_eq (add_tsub_cancel_right _ _).symm⟩⟩⟩
#align sum_range_diag_flip sum_range_diag_flip

end

section NoArchimedean

variable {α : Type*} {β : Type*} [LinearOrderedField α] {abv : β → α}

section

variable [Semiring β] [IsAbsoluteValue abv]

theorem abv_sum_le_sum_abv {γ : Type*} (f : γ → β) (s : Finset γ) :
    abv (∑ k in s, f k) ≤ ∑ k in s, abv (f k) :=
  haveI := Classical.decEq γ
  Finset.induction_on s (by simp [abv_zero abv]) fun a s has ih => by
    rw [sum_insert has, sum_insert has]; exact le_trans (abv_add abv _ _) (add_le_add_left ih _)
#align abv_sum_le_sum_abv abv_sum_le_sum_abv

end

section

variable [Ring β] [IsAbsoluteValue abv]

theorem cauchy_product {a b : ℕ → β} (ha : IsCauSeq abs fun m => ∑ n in range m, abv (a n))
    (hb : IsCauSeq abv fun m => ∑ n in range m, b n) (ε : α) (ε0 : 0 < ε) :
    ∃ i : ℕ,
      ∀ j ≥ i,
        abv
            (((∑ k in range j, a k) * ∑ k in range j, b k) -
              ∑ n in range j, ∑ m in range (n + 1), a m * b (n - m)) <
          ε :=
  let ⟨Q, hQ⟩ := CauSeq.bounded ⟨_, hb⟩
  let ⟨P, hP⟩ := CauSeq.bounded ⟨_, ha⟩
  have hP0 : 0 < P := lt_of_le_of_lt (abs_nonneg _) (hP 0)
  have hPε0 : 0 < ε / (2 * P) := div_pos ε0 (mul_pos (show (2 : α) > 0 by norm_num) hP0)
  let ⟨N, hN⟩ := CauSeq.cauchy₂ ⟨_, hb⟩ hPε0
  have hQε0 : 0 < ε / (4 * Q) :=
    div_pos ε0 (mul_pos (show (0 : α) < 4 by norm_num) (lt_of_le_of_lt (abv_nonneg _ _) (hQ 0)))
  let ⟨M, hM⟩ := CauSeq.cauchy₂ ⟨_, ha⟩ hQε0
  ⟨2 * (max N M + 1), fun K hK => by
    have h₁ :
      (∑ m in range K, ∑ k in range (m + 1), a k * b (m - k)) =
        ∑ m in range K, ∑ n in range (K - m), a m * b n :=
      by simpa using sum_range_diag_flip K fun m n => a m * b n
    have h₂ :
      (fun i => ∑ k in range (K - i), a i * b k) = fun i => a i * ∑ k in range (K - i), b k := by
      simp [Finset.mul_sum]
    have h₃ :
      (∑ i in range K, a i * ∑ k in range (K - i), b k) =
        (∑ i in range K, a i * ((∑ k in range (K - i), b k) - ∑ k in range K, b k)) +
          ∑ i in range K, a i * ∑ k in range K, b k :=
      by rw [← sum_add_distrib]; simp [(mul_add _ _ _).symm]
    have two_mul_two : (4 : α) = 2 * 2 := by norm_num
    have hQ0 : Q ≠ 0 := fun h => by simp [h, lt_irrefl] at hQε0
    have h2Q0 : 2 * Q ≠ 0 := mul_ne_zero two_ne_zero hQ0
    have hε : ε / (2 * P) * P + ε / (4 * Q) * (2 * Q) = ε := by
      rw [← div_div, div_mul_cancel _ (Ne.symm (ne_of_lt hP0)), two_mul_two, mul_assoc, ← div_div,
        div_mul_cancel _ h2Q0, add_halves]
    have hNMK : max N M + 1 < K :=
      lt_of_lt_of_le (by rw [two_mul]; exact lt_add_of_pos_left _ (Nat.succ_pos _)) hK
    have hKN : N < K :=
      calc
        N ≤ max N M := le_max_left _ _
        _ < max N M + 1 := (Nat.lt_succ_self _)
        _ < K := hNMK

    have hsumlesum :
      (∑ i in range (max N M + 1),
          abv (a i) * abv ((∑ k in range (K - i), b k) - ∑ k in range K, b k)) ≤
        ∑ i in range (max N M + 1), abv (a i) * (ε / (2 * P))
    · gcongr with m hmJ
      exact le_of_lt
            (hN (K - m)
              (le_tsub_of_add_le_left
                (le_trans
                  (by
                    rw [two_mul]
                    gcongr
                    · exact le_of_lt (mem_range.1 hmJ)
                    · exact le_trans (le_max_left _ _) (le_of_lt (lt_add_one _)))
                  hK))
              K (le_of_lt hKN))
    have hsumltP : (∑ n in range (max N M + 1), abv (a n)) < P :=
      calc
        (∑ n in range (max N M + 1), abv (a n)) = |∑ n in range (max N M + 1), abv (a n)| :=
          Eq.symm (abs_of_nonneg (sum_nonneg fun x _ => abv_nonneg abv (a x)))
        _ < P := hP (max N M + 1)

    rw [h₁, h₂, h₃, sum_mul, ← sub_sub, sub_right_comm, sub_self, zero_sub, abv_neg abv]
    refine' lt_of_le_of_lt (abv_sum_le_sum_abv _ _) _
    suffices
      (∑ i in range (max N M + 1),
            abv (a i) * abv ((∑ k in range (K - i), b k) - ∑ k in range K, b k)) +
          ((∑ i in range K, abv (a i) * abv ((∑ k in range (K - i), b k) - ∑ k in range K, b k)) -
            ∑ i in range (max N M + 1),
              abv (a i) * abv ((∑ k in range (K - i), b k) - ∑ k in range K, b k)) <
        ε / (2 * P) * P + ε / (4 * Q) * (2 * Q) by
      rw [hε] at this
      simpa [abv_mul abv] using this
    gcongr
    · exact lt_of_le_of_lt hsumlesum
          (by rw [← sum_mul, mul_comm]; gcongr)
    rw [sum_range_sub_sum_range (le_of_lt hNMK)]
    calc
      (∑ i in (range K).filter fun k => max N M + 1 ≤ k,
            abv (a i) * abv ((∑ k in range (K - i), b k) - ∑ k in range K, b k)) ≤
          ∑ i in (range K).filter fun k => max N M + 1 ≤ k, abv (a i) * (2 * Q) := by
          gcongr
          rw [sub_eq_add_neg]
          refine' le_trans (abv_add _ _ _) _
          rw [two_mul, abv_neg abv]
          gcongr <;> exact le_of_lt (hQ _)
      _ < ε / (4 * Q) * (2 * Q) := by
          rw [← sum_mul, ← sum_range_sub_sum_range (le_of_lt hNMK)]
          have := lt_of_le_of_lt (abv_nonneg _ _) (hQ 0)
          gcongr
          refine'
               lt_of_le_of_lt (le_abs_self _)
                (hM _ (le_trans (Nat.le_succ_of_le (le_max_right _ _)) (le_of_lt hNMK)) _
                  (Nat.le_succ_of_le (le_max_right _ _)))
      ⟩
#align cauchy_product cauchy_product

end

end NoArchimedean

end

open Finset

open CauSeq

namespace Complex

theorem isCauSeq_abs_exp (z : ℂ) :
    IsCauSeq Abs.abs fun n => ∑ m in range n, abs (z ^ m / m.factorial) :=
  let ⟨n, hn⟩ := exists_nat_gt (abs z)
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (abs.nonneg _) hn
  series_ratio_test n (abs z / n) (div_nonneg (abs.nonneg _) (le_of_lt hn0))
    (by rwa [div_lt_iff hn0, one_mul]) fun m hm => by
      rw [abs_abs, abs_abs, Nat.factorial_succ, pow_succ, mul_comm m.succ, Nat.cast_mul, ← div_div,
        mul_div_assoc, mul_div_right_comm, map_mul, map_div₀, abs_natCast]
      gcongr
      exact le_trans hm (Nat.le_succ _)
#align complex.is_cau_abs_exp Complex.isCauSeq_abs_exp

noncomputable section

theorem isCauSeq_exp (z : ℂ) : IsCauSeq abs fun n => ∑ m in range n, z ^ m / m.factorial :=
  isCauSeq_series_of_abv_isCauSeq (isCauSeq_abs_exp z)
#align complex.is_cau_exp Complex.isCauSeq_exp

/-- The Cauchy sequence consisting of partial sums of the Taylor series of
the complex exponential function -/
----@[pp_nodot] Porting note: removed Porting note: removed
def exp' (z : ℂ) : CauSeq ℂ Complex.abs :=
  ⟨fun n => ∑ m in range n, z ^ m / m.factorial, isCauSeq_exp z⟩
#align complex.exp' Complex.exp'

/-- The complex exponential function, defined via its Taylor series -/
--@[pp_nodot] Porting note: removed
--Porting note: removed `irreducible` attribute, so I can prove things
def exp (z : ℂ) : ℂ :=
  CauSeq.lim (exp' z)
#align complex.exp Complex.exp

/-- The complex sine function, defined via `exp` -/
--@[pp_nodot] Porting note: removed
def sin (z : ℂ) : ℂ :=
  (exp (-z * I) - exp (z * I)) * I / 2
#align complex.sin Complex.sin

/-- The complex cosine function, defined via `exp` -/
--@[pp_nodot] Porting note: removed
def cos (z : ℂ) : ℂ :=
  (exp (z * I) + exp (-z * I)) / 2
#align complex.cos Complex.cos

/-- The complex tangent function, defined as `sin z / cos z` -/
--@[pp_nodot] Porting note: removed
def tan (z : ℂ) : ℂ :=
  sin z / cos z
#align complex.tan Complex.tan

/-- The complex hyperbolic sine function, defined via `exp` -/
--@[pp_nodot] Porting note: removed
def sinh (z : ℂ) : ℂ :=
  (exp z - exp (-z)) / 2
#align complex.sinh Complex.sinh

/-- The complex hyperbolic cosine function, defined via `exp` -/
--@[pp_nodot] Porting note: removed
def cosh (z : ℂ) : ℂ :=
  (exp z + exp (-z)) / 2
#align complex.cosh Complex.cosh

/-- The complex hyperbolic tangent function, defined as `sinh z / cosh z` -/
--@[pp_nodot] Porting note: removed
def tanh (z : ℂ) : ℂ :=
  sinh z / cosh z
#align complex.tanh Complex.tanh

/-- scoped notation for the complex exponential function -/
scoped notation "cexp" => Complex.exp

end

end Complex

namespace Real

open Complex

noncomputable section

/-- The real exponential function, defined as the real part of the complex exponential -/
--@[pp_nodot] Porting note: removed
nonrec def exp (x : ℝ) : ℝ :=
  (exp x).re
#align real.exp Real.exp

/-- The real sine function, defined as the real part of the complex sine -/
--@[pp_nodot] Porting note: removed
nonrec def sin (x : ℝ) : ℝ :=
  (sin x).re
#align real.sin Real.sin

/-- The real cosine function, defined as the real part of the complex cosine -/
--@[pp_nodot] Porting note: removed
nonrec def cos (x : ℝ) : ℝ :=
  (cos x).re
#align real.cos Real.cos

/-- The real tangent function, defined as the real part of the complex tangent -/
--@[pp_nodot] Porting note: removed
nonrec def tan (x : ℝ) : ℝ :=
  (tan x).re
#align real.tan Real.tan

/-- The real hypebolic sine function, defined as the real part of the complex hyperbolic sine -/
--@[pp_nodot] Porting note: removed
nonrec def sinh (x : ℝ) : ℝ :=
  (sinh x).re
#align real.sinh Real.sinh

/-- The real hypebolic cosine function, defined as the real part of the complex hyperbolic cosine -/
--@[pp_nodot] Porting note: removed
nonrec def cosh (x : ℝ) : ℝ :=
  (cosh x).re
#align real.cosh Real.cosh

/-- The real hypebolic tangent function, defined as the real part of
the complex hyperbolic tangent -/
--@[pp_nodot] Porting note: removed
nonrec def tanh (x : ℝ) : ℝ :=
  (tanh x).re
#align real.tanh Real.tanh

/-- scoped notation for the real exponential function -/
scoped notation "rexp" => Real.exp

end

end Real

namespace Complex

variable (x y : ℂ)

@[simp]
theorem exp_zero : exp 0 = 1 := by
  rw [exp]
  refine' lim_eq_of_equiv_const fun ε ε0 => ⟨1, fun j hj => _⟩
  convert (config := .unfoldSameFun) ε0 -- porting note: ε0 : ε > 0 but goal is _ < ε
  cases' j with j j
  · exact absurd hj (not_le_of_gt zero_lt_one)
  · dsimp [exp']
    induction' j with j ih
    · dsimp [exp']; simp [show Nat.succ 0 = 1 from rfl]
    · rw [← ih (by simp [show 1 = Nat.succ 0 from rfl, Nat.succ_le_succ])]
      simp only [sum_range_succ, pow_succ]
      simp
#align complex.exp_zero Complex.exp_zero

theorem exp_add : exp (x + y) = exp x * exp y := by
  have hj : ∀ j : ℕ, (∑ m in range j, (x + y) ^ m / m.factorial) =
        ∑ i in range j, ∑ k in range (i + 1), x ^ k / k.factorial *
          (y ^ (i - k) / (i - k).factorial) := by
    intro j
    refine' Finset.sum_congr rfl fun m _ => _
    rw [add_pow, div_eq_mul_inv, sum_mul]
    refine' Finset.sum_congr rfl fun I hi => _
    have h₁ : (m.choose I : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 (pos_iff_ne_zero.1 (Nat.choose_pos (Nat.le_of_lt_succ (mem_range.1 hi))))
    have h₂ := Nat.choose_mul_factorial_mul_factorial (Nat.le_of_lt_succ <| Finset.mem_range.1 hi)
    rw [← h₂, Nat.cast_mul, Nat.cast_mul, mul_inv, mul_inv]
    simp only [mul_left_comm (m.choose I : ℂ), mul_assoc, mul_left_comm (m.choose I : ℂ)⁻¹,
      mul_comm (m.choose I : ℂ)]
    rw [inv_mul_cancel h₁]
    simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
  simp_rw [exp, exp', lim_mul_lim]
  apply (lim_eq_lim_of_equiv _).symm
  simp only [hj]
  exact cauchy_product (isCauSeq_abs_exp x) (isCauSeq_exp y)
#align complex.exp_add Complex.exp_add

--Porting note: New definition
/-- the exponential function as a monoid hom from `Multiplicative ℂ` to `ℂ` -/
noncomputable def expMonoidHom : MonoidHom (Multiplicative ℂ) ℂ :=
  { toFun := fun z => exp (Multiplicative.toAdd z),
    map_one' := by simp,
    map_mul' := by simp [exp_add] }

theorem exp_list_sum (l : List ℂ) : exp l.sum = (l.map exp).prod :=
  @MonoidHom.map_list_prod (Multiplicative ℂ) ℂ _ _ expMonoidHom l
#align complex.exp_list_sum Complex.exp_list_sum

theorem exp_multiset_sum (s : Multiset ℂ) : exp s.sum = (s.map exp).prod :=
  @MonoidHom.map_multiset_prod (Multiplicative ℂ) ℂ _ _ expMonoidHom s
#align complex.exp_multiset_sum Complex.exp_multiset_sum

theorem exp_sum {α : Type*} (s : Finset α) (f : α → ℂ) :
    exp (∑ x in s, f x) = ∏ x in s, exp (f x) :=
  @map_prod (Multiplicative ℂ) α ℂ _ _ _ _ expMonoidHom f s
#align complex.exp_sum Complex.exp_sum

theorem exp_nat_mul (x : ℂ) : ∀ n : ℕ, exp (n * x) = exp x ^ n
  | 0 => by rw [Nat.cast_zero, zero_mul, exp_zero, pow_zero]
  | Nat.succ n => by rw [pow_succ', Nat.cast_add_one, add_mul, exp_add, ← exp_nat_mul _ n, one_mul]
#align complex.exp_nat_mul Complex.exp_nat_mul

theorem exp_ne_zero : exp x ≠ 0 := fun h =>
  zero_ne_one <| by rw [← exp_zero, ← add_neg_self x, exp_add, h]; simp
#align complex.exp_ne_zero Complex.exp_ne_zero

theorem exp_neg : exp (-x) = (exp x)⁻¹ := by
  rw [← mul_right_inj' (exp_ne_zero x), ← exp_add]; simp [mul_inv_cancel (exp_ne_zero x)]
#align complex.exp_neg Complex.exp_neg

theorem exp_sub : exp (x - y) = exp x / exp y := by
  simp [sub_eq_add_neg, exp_add, exp_neg, div_eq_mul_inv]
#align complex.exp_sub Complex.exp_sub

theorem exp_int_mul (z : ℂ) (n : ℤ) : Complex.exp (n * z) = Complex.exp z ^ n := by
  cases n
  · simp [exp_nat_mul]
  · simp [exp_add, add_mul, pow_add, exp_neg, exp_nat_mul]
#align complex.exp_int_mul Complex.exp_int_mul

@[simp]
theorem exp_conj : exp (conj x) = conj (exp x) := by
  dsimp [exp]
  rw [← lim_conj]
  refine' congr_arg CauSeq.lim (CauSeq.ext fun _ => _)
  dsimp [exp', Function.comp, isCauSeq_conj, cauSeqConj]
  rw [(starRingEnd _).map_sum]
  refine' sum_congr rfl fun n _ => _
  rw [map_div₀, map_pow, ← ofReal_nat_cast, conj_ofReal]
#align complex.exp_conj Complex.exp_conj

@[simp]
theorem ofReal_exp_ofReal_re (x : ℝ) : ((exp x).re : ℂ) = exp x :=
  conj_eq_iff_re.1 <| by rw [← exp_conj, conj_ofReal]
#align complex.of_real_exp_of_real_re Complex.ofReal_exp_ofReal_re

@[simp, norm_cast]
theorem ofReal_exp (x : ℝ) : (Real.exp x : ℂ) = exp x :=
  ofReal_exp_ofReal_re _
#align complex.of_real_exp Complex.ofReal_exp

@[simp]
theorem exp_ofReal_im (x : ℝ) : (exp x).im = 0 := by rw [← ofReal_exp_ofReal_re, ofReal_im]
#align complex.exp_of_real_im Complex.exp_ofReal_im

theorem exp_ofReal_re (x : ℝ) : (exp x).re = Real.exp x :=
  rfl
#align complex.exp_of_real_re Complex.exp_ofReal_re

theorem two_sinh : 2 * sinh x = exp x - exp (-x) :=
  mul_div_cancel' _ two_ne_zero
#align complex.two_sinh Complex.two_sinh

theorem two_cosh : 2 * cosh x = exp x + exp (-x) :=
  mul_div_cancel' _ two_ne_zero
#align complex.two_cosh Complex.two_cosh

@[simp]
theorem sinh_zero : sinh 0 = 0 := by simp [sinh]
#align complex.sinh_zero Complex.sinh_zero

@[simp]
theorem sinh_neg : sinh (-x) = -sinh x := by simp [sinh, exp_neg, (neg_div _ _).symm, add_mul]
#align complex.sinh_neg Complex.sinh_neg

private theorem sinh_add_aux {a b c d : ℂ} :
    (a - b) * (c + d) + (a + b) * (c - d) = 2 * (a * c - b * d) := by ring

theorem sinh_add : sinh (x + y) = sinh x * cosh y + cosh x * sinh y := by
  rw [← mul_right_inj' (two_ne_zero' ℂ), two_sinh, exp_add, neg_add, exp_add, eq_comm, mul_add, ←
    mul_assoc, two_sinh, mul_left_comm, two_sinh, ← mul_right_inj' (two_ne_zero' ℂ), mul_add,
    mul_left_comm, two_cosh, ← mul_assoc, two_cosh]
  exact sinh_add_aux
#align complex.sinh_add Complex.sinh_add

@[simp]
theorem cosh_zero : cosh 0 = 1 := by simp [cosh]
#align complex.cosh_zero Complex.cosh_zero

@[simp]
theorem cosh_neg : cosh (-x) = cosh x := by simp [add_comm, cosh, exp_neg]
#align complex.cosh_neg Complex.cosh_neg

private theorem cosh_add_aux {a b c d : ℂ} :
    (a + b) * (c + d) + (a - b) * (c - d) = 2 * (a * c + b * d) := by ring

theorem cosh_add : cosh (x + y) = cosh x * cosh y + sinh x * sinh y := by
  rw [← mul_right_inj' (two_ne_zero' ℂ), two_cosh, exp_add, neg_add, exp_add, eq_comm, mul_add, ←
    mul_assoc, two_cosh, ← mul_assoc, two_sinh, ← mul_right_inj' (two_ne_zero' ℂ), mul_add,
    mul_left_comm, two_cosh, mul_left_comm, two_sinh]
  exact cosh_add_aux
#align complex.cosh_add Complex.cosh_add

theorem sinh_sub : sinh (x - y) = sinh x * cosh y - cosh x * sinh y := by
  simp [sub_eq_add_neg, sinh_add, sinh_neg, cosh_neg]
#align complex.sinh_sub Complex.sinh_sub

theorem cosh_sub : cosh (x - y) = cosh x * cosh y - sinh x * sinh y := by
  simp [sub_eq_add_neg, cosh_add, sinh_neg, cosh_neg]
#align complex.cosh_sub Complex.cosh_sub

theorem sinh_conj : sinh (conj x) = conj (sinh x) := by
  rw [sinh, ← RingHom.map_neg, exp_conj, exp_conj, ← RingHom.map_sub, sinh, map_div₀]
  --Porting note: not nice
  simp [← one_add_one_eq_two]
#align complex.sinh_conj Complex.sinh_conj

@[simp]
theorem ofReal_sinh_ofReal_re (x : ℝ) : ((sinh x).re : ℂ) = sinh x :=
  conj_eq_iff_re.1 <| by rw [← sinh_conj, conj_ofReal]
#align complex.of_real_sinh_of_real_re Complex.ofReal_sinh_ofReal_re

@[simp, norm_cast]
theorem ofReal_sinh (x : ℝ) : (Real.sinh x : ℂ) = sinh x :=
  ofReal_sinh_ofReal_re _
#align complex.of_real_sinh Complex.ofReal_sinh

@[simp]
theorem sinh_ofReal_im (x : ℝ) : (sinh x).im = 0 := by rw [← ofReal_sinh_ofReal_re, ofReal_im]
#align complex.sinh_of_real_im Complex.sinh_ofReal_im

theorem sinh_ofReal_re (x : ℝ) : (sinh x).re = Real.sinh x :=
  rfl
#align complex.sinh_of_real_re Complex.sinh_ofReal_re

theorem cosh_conj : cosh (conj x) = conj (cosh x) := by
  rw [cosh, ← RingHom.map_neg, exp_conj, exp_conj, ← RingHom.map_add, cosh, map_div₀]
  --Porting note: not nice
  simp [← one_add_one_eq_two]
#align complex.cosh_conj Complex.cosh_conj

theorem ofReal_cosh_ofReal_re (x : ℝ) : ((cosh x).re : ℂ) = cosh x :=
  conj_eq_iff_re.1 <| by rw [← cosh_conj, conj_ofReal]
#align complex.of_real_cosh_of_real_re Complex.ofReal_cosh_ofReal_re

@[simp, norm_cast]
theorem ofReal_cosh (x : ℝ) : (Real.cosh x : ℂ) = cosh x :=
  ofReal_cosh_ofReal_re _
#align complex.of_real_cosh Complex.ofReal_cosh

@[simp]
theorem cosh_ofReal_im (x : ℝ) : (cosh x).im = 0 := by rw [← ofReal_cosh_ofReal_re, ofReal_im]
#align complex.cosh_of_real_im Complex.cosh_ofReal_im

@[simp]
theorem cosh_ofReal_re (x : ℝ) : (cosh x).re = Real.cosh x :=
  rfl
#align complex.cosh_of_real_re Complex.cosh_ofReal_re

theorem tanh_eq_sinh_div_cosh : tanh x = sinh x / cosh x :=
  rfl
#align complex.tanh_eq_sinh_div_cosh Complex.tanh_eq_sinh_div_cosh

@[simp]
theorem tanh_zero : tanh 0 = 0 := by simp [tanh]
#align complex.tanh_zero Complex.tanh_zero

@[simp]
theorem tanh_neg : tanh (-x) = -tanh x := by simp [tanh, neg_div]
#align complex.tanh_neg Complex.tanh_neg

theorem tanh_conj : tanh (conj x) = conj (tanh x) := by
  rw [tanh, sinh_conj, cosh_conj, ← map_div₀, tanh]
#align complex.tanh_conj Complex.tanh_conj

@[simp]
theorem ofReal_tanh_ofReal_re (x : ℝ) : ((tanh x).re : ℂ) = tanh x :=
  conj_eq_iff_re.1 <| by rw [← tanh_conj, conj_ofReal]
#align complex.of_real_tanh_of_real_re Complex.ofReal_tanh_ofReal_re

@[simp, norm_cast]
theorem ofReal_tanh (x : ℝ) : (Real.tanh x : ℂ) = tanh x :=
  ofReal_tanh_ofReal_re _
#align complex.of_real_tanh Complex.ofReal_tanh

@[simp]
theorem tanh_ofReal_im (x : ℝ) : (tanh x).im = 0 := by rw [← ofReal_tanh_ofReal_re, ofReal_im]
#align complex.tanh_of_real_im Complex.tanh_ofReal_im

theorem tanh_ofReal_re (x : ℝ) : (tanh x).re = Real.tanh x :=
  rfl
#align complex.tanh_of_real_re Complex.tanh_ofReal_re

@[simp]
theorem cosh_add_sinh : cosh x + sinh x = exp x := by
  rw [← mul_right_inj' (two_ne_zero' ℂ), mul_add, two_cosh, two_sinh, add_add_sub_cancel, two_mul]
#align complex.cosh_add_sinh Complex.cosh_add_sinh

@[simp]
theorem sinh_add_cosh : sinh x + cosh x = exp x := by rw [add_comm, cosh_add_sinh]
#align complex.sinh_add_cosh Complex.sinh_add_cosh

@[simp]
theorem exp_sub_cosh : exp x - cosh x = sinh x :=
  sub_eq_iff_eq_add.2 (sinh_add_cosh x).symm
#align complex.exp_sub_cosh Complex.exp_sub_cosh

@[simp]
theorem exp_sub_sinh : exp x - sinh x = cosh x :=
  sub_eq_iff_eq_add.2 (cosh_add_sinh x).symm
#align complex.exp_sub_sinh Complex.exp_sub_sinh

@[simp]
theorem cosh_sub_sinh : cosh x - sinh x = exp (-x) := by
  rw [← mul_right_inj' (two_ne_zero' ℂ), mul_sub, two_cosh, two_sinh, add_sub_sub_cancel, two_mul]
#align complex.cosh_sub_sinh Complex.cosh_sub_sinh

@[simp]
theorem sinh_sub_cosh : sinh x - cosh x = -exp (-x) := by rw [← neg_sub, cosh_sub_sinh]
#align complex.sinh_sub_cosh Complex.sinh_sub_cosh

@[simp]
theorem cosh_sq_sub_sinh_sq : cosh x ^ 2 - sinh x ^ 2 = 1 := by
  rw [sq_sub_sq, cosh_add_sinh, cosh_sub_sinh, ← exp_add, add_neg_self, exp_zero]
#align complex.cosh_sq_sub_sinh_sq Complex.cosh_sq_sub_sinh_sq

theorem cosh_sq : cosh x ^ 2 = sinh x ^ 2 + 1 := by
  rw [← cosh_sq_sub_sinh_sq x]
  ring
#align complex.cosh_sq Complex.cosh_sq

theorem sinh_sq : sinh x ^ 2 = cosh x ^ 2 - 1 := by
  rw [← cosh_sq_sub_sinh_sq x]
  ring
#align complex.sinh_sq Complex.sinh_sq

theorem cosh_two_mul : cosh (2 * x) = cosh x ^ 2 + sinh x ^ 2 := by rw [two_mul, cosh_add, sq, sq]
#align complex.cosh_two_mul Complex.cosh_two_mul

theorem sinh_two_mul : sinh (2 * x) = 2 * sinh x * cosh x := by
  rw [two_mul, sinh_add]
  ring
#align complex.sinh_two_mul Complex.sinh_two_mul

theorem cosh_three_mul : cosh (3 * x) = 4 * cosh x ^ 3 - 3 * cosh x := by
  have h1 : x + 2 * x = 3 * x := by ring
  rw [← h1, cosh_add x (2 * x)]
  simp only [cosh_two_mul, sinh_two_mul]
  have h2 : sinh x * (2 * sinh x * cosh x) = 2 * cosh x * sinh x ^ 2 := by ring
  rw [h2, sinh_sq]
  ring
#align complex.cosh_three_mul Complex.cosh_three_mul

theorem sinh_three_mul : sinh (3 * x) = 4 * sinh x ^ 3 + 3 * sinh x := by
  have h1 : x + 2 * x = 3 * x := by ring
  rw [← h1, sinh_add x (2 * x)]
  simp only [cosh_two_mul, sinh_two_mul]
  have h2 : cosh x * (2 * sinh x * cosh x) = 2 * sinh x * cosh x ^ 2 := by ring
  rw [h2, cosh_sq]
  ring
#align complex.sinh_three_mul Complex.sinh_three_mul

@[simp]
theorem sin_zero : sin 0 = 0 := by simp [sin]
#align complex.sin_zero Complex.sin_zero

@[simp]
theorem sin_neg : sin (-x) = -sin x := by
  simp [sin, sub_eq_add_neg, exp_neg, (neg_div _ _).symm, add_mul]
#align complex.sin_neg Complex.sin_neg

theorem two_sin : 2 * sin x = (exp (-x * I) - exp (x * I)) * I :=
  mul_div_cancel' _ two_ne_zero
#align complex.two_sin Complex.two_sin

theorem two_cos : 2 * cos x = exp (x * I) + exp (-x * I) :=
  mul_div_cancel' _ two_ne_zero
#align complex.two_cos Complex.two_cos

theorem sinh_mul_I : sinh (x * I) = sin x * I := by
  rw [← mul_right_inj' (two_ne_zero' ℂ), two_sinh, ← mul_assoc, two_sin, mul_assoc, I_mul_I,
    mul_neg_one, neg_sub, neg_mul_eq_neg_mul]
set_option linter.uppercaseLean3 false in
#align complex.sinh_mul_I Complex.sinh_mul_I

theorem cosh_mul_I : cosh (x * I) = cos x := by
  rw [← mul_right_inj' (two_ne_zero' ℂ), two_cosh, two_cos, neg_mul_eq_neg_mul]
set_option linter.uppercaseLean3 false in
#align complex.cosh_mul_I Complex.cosh_mul_I

theorem tanh_mul_I : tanh (x * I) = tan x * I := by
  rw [tanh_eq_sinh_div_cosh, cosh_mul_I, sinh_mul_I, mul_div_right_comm, tan]
set_option linter.uppercaseLean3 false in
#align complex.tanh_mul_I Complex.tanh_mul_I

theorem cos_mul_I : cos (x * I) = cosh x := by rw [← cosh_mul_I]; ring_nf; simp
set_option linter.uppercaseLean3 false in
#align complex.cos_mul_I Complex.cos_mul_I

theorem sin_mul_I : sin (x * I) = sinh x * I := by
  have h : I * sin (x * I) = -sinh x := by
    rw [mul_comm, ← sinh_mul_I]
    ring_nf
    simp
  rw [← neg_neg (sinh x), ← h]
  ext <;> simp
set_option linter.uppercaseLean3 false in
#align complex.sin_mul_I Complex.sin_mul_I

theorem tan_mul_I : tan (x * I) = tanh x * I := by
  rw [tan, sin_mul_I, cos_mul_I, mul_div_right_comm, tanh_eq_sinh_div_cosh]
set_option linter.uppercaseLean3 false in
#align complex.tan_mul_I Complex.tan_mul_I

theorem sin_add : sin (x + y) = sin x * cos y + cos x * sin y := by
  rw [← mul_left_inj' I_ne_zero, ← sinh_mul_I, add_mul, add_mul, mul_right_comm, ← sinh_mul_I,
    mul_assoc, ← sinh_mul_I, ← cosh_mul_I, ← cosh_mul_I, sinh_add]
#align complex.sin_add Complex.sin_add

@[simp]
theorem cos_zero : cos 0 = 1 := by simp [cos]
#align complex.cos_zero Complex.cos_zero

@[simp]
theorem cos_neg : cos (-x) = cos x := by simp [cos, sub_eq_add_neg, exp_neg, add_comm]
#align complex.cos_neg Complex.cos_neg

private theorem cos_add_aux {a b c d : ℂ} :
    (a + b) * (c + d) - (b - a) * (d - c) * -1 = 2 * (a * c + b * d) := by ring

theorem cos_add : cos (x + y) = cos x * cos y - sin x * sin y := by
  rw [← cosh_mul_I, add_mul, cosh_add, cosh_mul_I, cosh_mul_I, sinh_mul_I, sinh_mul_I,
    mul_mul_mul_comm, I_mul_I, mul_neg_one, sub_eq_add_neg]
#align complex.cos_add Complex.cos_add

theorem sin_sub : sin (x - y) = sin x * cos y - cos x * sin y := by
  simp [sub_eq_add_neg, sin_add, sin_neg, cos_neg]
#align complex.sin_sub Complex.sin_sub

theorem cos_sub : cos (x - y) = cos x * cos y + sin x * sin y := by
  simp [sub_eq_add_neg, cos_add, sin_neg, cos_neg]
#align complex.cos_sub Complex.cos_sub

theorem sin_add_mul_I (x y : ℂ) : sin (x + y * I) = sin x * cosh y + cos x * sinh y * I := by
  rw [sin_add, cos_mul_I, sin_mul_I, mul_assoc]
set_option linter.uppercaseLean3 false in
#align complex.sin_add_mul_I Complex.sin_add_mul_I

theorem sin_eq (z : ℂ) : sin z = sin z.re * cosh z.im + cos z.re * sinh z.im * I := by
  convert sin_add_mul_I z.re z.im; exact (re_add_im z).symm
#align complex.sin_eq Complex.sin_eq

theorem cos_add_mul_I (x y : ℂ) : cos (x + y * I) = cos x * cosh y - sin x * sinh y * I := by
  rw [cos_add, cos_mul_I, sin_mul_I, mul_assoc]
set_option linter.uppercaseLean3 false in
#align complex.cos_add_mul_I Complex.cos_add_mul_I

theorem cos_eq (z : ℂ) : cos z = cos z.re * cosh z.im - sin z.re * sinh z.im * I := by
  convert cos_add_mul_I z.re z.im; exact (re_add_im z).symm
#align complex.cos_eq Complex.cos_eq

theorem sin_sub_sin : sin x - sin y = 2 * sin ((x - y) / 2) * cos ((x + y) / 2) := by
  have s1 := sin_add ((x + y) / 2) ((x - y) / 2)
  have s2 := sin_sub ((x + y) / 2) ((x - y) / 2)
  rw [div_add_div_same, add_sub, add_right_comm, add_sub_cancel, half_add_self] at s1
  rw [div_sub_div_same, ← sub_add, add_sub_cancel', half_add_self] at s2
  rw [s1, s2]
  ring
#align complex.sin_sub_sin Complex.sin_sub_sin

theorem cos_sub_cos : cos x - cos y = -2 * sin ((x + y) / 2) * sin ((x - y) / 2) := by
  have s1 := cos_add ((x + y) / 2) ((x - y) / 2)
  have s2 := cos_sub ((x + y) / 2) ((x - y) / 2)
  rw [div_add_div_same, add_sub, add_right_comm, add_sub_cancel, half_add_self] at s1
  rw [div_sub_div_same, ← sub_add, add_sub_cancel', half_add_self] at s2
  rw [s1, s2]
  ring
#align complex.cos_sub_cos Complex.cos_sub_cos

theorem cos_add_cos : cos x + cos y = 2 * cos ((x + y) / 2) * cos ((x - y) / 2) := by
  calc
    cos x + cos y = cos ((x + y) / 2 + (x - y) / 2) + cos ((x + y) / 2 - (x - y) / 2) := ?_
    _ =
        cos ((x + y) / 2) * cos ((x - y) / 2) - sin ((x + y) / 2) * sin ((x - y) / 2) +
          (cos ((x + y) / 2) * cos ((x - y) / 2) + sin ((x + y) / 2) * sin ((x - y) / 2)) :=
      ?_
    _ = 2 * cos ((x + y) / 2) * cos ((x - y) / 2) := ?_

  · congr <;> field_simp
  · rw [cos_add, cos_sub]
  ring
#align complex.cos_add_cos Complex.cos_add_cos

theorem sin_conj : sin (conj x) = conj (sin x) := by
  rw [← mul_left_inj' I_ne_zero, ← sinh_mul_I, ← conj_neg_I, ← RingHom.map_mul, ← RingHom.map_mul,
    sinh_conj, mul_neg, sinh_neg, sinh_mul_I, mul_neg]
#align complex.sin_conj Complex.sin_conj

@[simp]
theorem ofReal_sin_ofReal_re (x : ℝ) : ((sin x).re : ℂ) = sin x :=
  conj_eq_iff_re.1 <| by rw [← sin_conj, conj_ofReal]
#align complex.of_real_sin_of_real_re Complex.ofReal_sin_ofReal_re

@[simp, norm_cast]
theorem ofReal_sin (x : ℝ) : (Real.sin x : ℂ) = sin x :=
  ofReal_sin_ofReal_re _
#align complex.of_real_sin Complex.ofReal_sin

@[simp]
theorem sin_ofReal_im (x : ℝ) : (sin x).im = 0 := by rw [← ofReal_sin_ofReal_re, ofReal_im]
#align complex.sin_of_real_im Complex.sin_ofReal_im

theorem sin_ofReal_re (x : ℝ) : (sin x).re = Real.sin x :=
  rfl
#align complex.sin_of_real_re Complex.sin_ofReal_re

theorem cos_conj : cos (conj x) = conj (cos x) := by
  rw [← cosh_mul_I, ← conj_neg_I, ← RingHom.map_mul, ← cosh_mul_I, cosh_conj, mul_neg, cosh_neg]
#align complex.cos_conj Complex.cos_conj

@[simp]
theorem ofReal_cos_ofReal_re (x : ℝ) : ((cos x).re : ℂ) = cos x :=
  conj_eq_iff_re.1 <| by rw [← cos_conj, conj_ofReal]
#align complex.of_real_cos_of_real_re Complex.ofReal_cos_ofReal_re

@[simp, norm_cast]
theorem ofReal_cos (x : ℝ) : (Real.cos x : ℂ) = cos x :=
  ofReal_cos_ofReal_re _
#align complex.of_real_cos Complex.ofReal_cos

@[simp]
theorem cos_ofReal_im (x : ℝ) : (cos x).im = 0 := by rw [← ofReal_cos_ofReal_re, ofReal_im]
#align complex.cos_of_real_im Complex.cos_ofReal_im

theorem cos_ofReal_re (x : ℝ) : (cos x).re = Real.cos x :=
  rfl
#align complex.cos_of_real_re Complex.cos_ofReal_re

@[simp]
theorem tan_zero : tan 0 = 0 := by simp [tan]
#align complex.tan_zero Complex.tan_zero

theorem tan_eq_sin_div_cos : tan x = sin x / cos x :=
  rfl
#align complex.tan_eq_sin_div_cos Complex.tan_eq_sin_div_cos

theorem tan_mul_cos {x : ℂ} (hx : cos x ≠ 0) : tan x * cos x = sin x := by
  rw [tan_eq_sin_div_cos, div_mul_cancel _ hx]
#align complex.tan_mul_cos Complex.tan_mul_cos

@[simp]
theorem tan_neg : tan (-x) = -tan x := by simp [tan, neg_div]
#align complex.tan_neg Complex.tan_neg

theorem tan_conj : tan (conj x) = conj (tan x) := by rw [tan, sin_conj, cos_conj, ← map_div₀, tan]
#align complex.tan_conj Complex.tan_conj

@[simp]
theorem ofReal_tan_ofReal_re (x : ℝ) : ((tan x).re : ℂ) = tan x :=
  conj_eq_iff_re.1 <| by rw [← tan_conj, conj_ofReal]
#align complex.of_real_tan_of_real_re Complex.ofReal_tan_ofReal_re

@[simp, norm_cast]
theorem ofReal_tan (x : ℝ) : (Real.tan x : ℂ) = tan x :=
  ofReal_tan_ofReal_re _
#align complex.of_real_tan Complex.ofReal_tan

@[simp]
theorem tan_ofReal_im (x : ℝ) : (tan x).im = 0 := by rw [← ofReal_tan_ofReal_re, ofReal_im]
#align complex.tan_of_real_im Complex.tan_ofReal_im

theorem tan_ofReal_re (x : ℝ) : (tan x).re = Real.tan x :=
  rfl
#align complex.tan_of_real_re Complex.tan_ofReal_re

theorem cos_add_sin_I : cos x + sin x * I = exp (x * I) := by
  rw [← cosh_add_sinh, sinh_mul_I, cosh_mul_I]
set_option linter.uppercaseLean3 false in
#align complex.cos_add_sin_I Complex.cos_add_sin_I

theorem cos_sub_sin_I : cos x - sin x * I = exp (-x * I) := by
  rw [neg_mul, ← cosh_sub_sinh, sinh_mul_I, cosh_mul_I]
set_option linter.uppercaseLean3 false in
#align complex.cos_sub_sin_I Complex.cos_sub_sin_I

@[simp]
theorem sin_sq_add_cos_sq : sin x ^ 2 + cos x ^ 2 = 1 :=
  Eq.trans (by rw [cosh_mul_I, sinh_mul_I, mul_pow, I_sq, mul_neg_one, sub_neg_eq_add, add_comm])
    (cosh_sq_sub_sinh_sq (x * I))
#align complex.sin_sq_add_cos_sq Complex.sin_sq_add_cos_sq

@[simp]
theorem cos_sq_add_sin_sq : cos x ^ 2 + sin x ^ 2 = 1 := by rw [add_comm, sin_sq_add_cos_sq]
#align complex.cos_sq_add_sin_sq Complex.cos_sq_add_sin_sq

theorem cos_two_mul' : cos (2 * x) = cos x ^ 2 - sin x ^ 2 := by rw [two_mul, cos_add, ← sq, ← sq]
#align complex.cos_two_mul' Complex.cos_two_mul'

theorem cos_two_mul : cos (2 * x) = 2 * cos x ^ 2 - 1 := by
  rw [cos_two_mul', eq_sub_iff_add_eq.2 (sin_sq_add_cos_sq x), ← sub_add, sub_add_eq_add_sub,
    two_mul]
#align complex.cos_two_mul Complex.cos_two_mul

theorem sin_two_mul : sin (2 * x) = 2 * sin x * cos x := by
  rw [two_mul, sin_add, two_mul, add_mul, mul_comm]
#align complex.sin_two_mul Complex.sin_two_mul

theorem cos_sq : cos x ^ 2 = 1 / 2 + cos (2 * x) / 2 := by
  simp [cos_two_mul, div_add_div_same, mul_div_cancel_left, two_ne_zero, -one_div]
#align complex.cos_sq Complex.cos_sq

theorem cos_sq' : cos x ^ 2 = 1 - sin x ^ 2 := by rw [← sin_sq_add_cos_sq x, add_sub_cancel']
#align complex.cos_sq' Complex.cos_sq'

theorem sin_sq : sin x ^ 2 = 1 - cos x ^ 2 := by rw [← sin_sq_add_cos_sq x, add_sub_cancel]
#align complex.sin_sq Complex.sin_sq

theorem inv_one_add_tan_sq {x : ℂ} (hx : cos x ≠ 0) : (1 + tan x ^ 2)⁻¹ = cos x ^ 2 := by
  rw [tan_eq_sin_div_cos, div_pow]
  field_simp
#align complex.inv_one_add_tan_sq Complex.inv_one_add_tan_sq

theorem tan_sq_div_one_add_tan_sq {x : ℂ} (hx : cos x ≠ 0) :
    tan x ^ 2 / (1 + tan x ^ 2) = sin x ^ 2 := by
  simp only [← tan_mul_cos hx, mul_pow, ← inv_one_add_tan_sq hx, div_eq_mul_inv, one_mul]
#align complex.tan_sq_div_one_add_tan_sq Complex.tan_sq_div_one_add_tan_sq

theorem cos_three_mul : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x := by
  have h1 : x + 2 * x = 3 * x := by ring
  rw [← h1, cos_add x (2 * x)]
  simp only [cos_two_mul, sin_two_mul, mul_add, mul_sub, mul_one, sq]
  have h2 : 4 * cos x ^ 3 = 2 * cos x * cos x * cos x + 2 * cos x * cos x ^ 2 := by ring
  rw [h2, cos_sq']
  ring
#align complex.cos_three_mul Complex.cos_three_mul

theorem sin_three_mul : sin (3 * x) = 3 * sin x - 4 * sin x ^ 3 := by
  have h1 : x + 2 * x = 3 * x := by ring
  rw [← h1, sin_add x (2 * x)]
  simp only [cos_two_mul, sin_two_mul, cos_sq']
  have h2 : cos x * (2 * sin x * cos x) = 2 * sin x * cos x ^ 2 := by ring
  rw [h2, cos_sq']
  ring
#align complex.sin_three_mul Complex.sin_three_mul

theorem exp_mul_I : exp (x * I) = cos x + sin x * I :=
  (cos_add_sin_I _).symm
set_option linter.uppercaseLean3 false in
#align complex.exp_mul_I Complex.exp_mul_I

theorem exp_add_mul_I : exp (x + y * I) = exp x * (cos y + sin y * I) := by rw [exp_add, exp_mul_I]
set_option linter.uppercaseLean3 false in
#align complex.exp_add_mul_I Complex.exp_add_mul_I

theorem exp_eq_exp_re_mul_sin_add_cos : exp x = exp x.re * (cos x.im + sin x.im * I) := by
  rw [← exp_add_mul_I, re_add_im]
#align complex.exp_eq_exp_re_mul_sin_add_cos Complex.exp_eq_exp_re_mul_sin_add_cos

theorem exp_re : (exp x).re = Real.exp x.re * Real.cos x.im := by
  rw [exp_eq_exp_re_mul_sin_add_cos]
  simp [exp_ofReal_re, cos_ofReal_re]
#align complex.exp_re Complex.exp_re

theorem exp_im : (exp x).im = Real.exp x.re * Real.sin x.im := by
  rw [exp_eq_exp_re_mul_sin_add_cos]
  simp [exp_ofReal_re, sin_ofReal_re]
#align complex.exp_im Complex.exp_im

@[simp]
theorem exp_ofReal_mul_I_re (x : ℝ) : (exp (x * I)).re = Real.cos x := by
  simp [exp_mul_I, cos_ofReal_re]
set_option linter.uppercaseLean3 false in
#align complex.exp_of_real_mul_I_re Complex.exp_ofReal_mul_I_re

@[simp]
theorem exp_ofReal_mul_I_im (x : ℝ) : (exp (x * I)).im = Real.sin x := by
  simp [exp_mul_I, sin_ofReal_re]
set_option linter.uppercaseLean3 false in
#align complex.exp_of_real_mul_I_im Complex.exp_ofReal_mul_I_im

/-- **De Moivre's formula** -/
theorem cos_add_sin_mul_I_pow (n : ℕ) (z : ℂ) :
    (cos z + sin z * I) ^ n = cos (↑n * z) + sin (↑n * z) * I := by
  rw [← exp_mul_I, ← exp_mul_I]
  induction' n with n ih
  · rw [pow_zero, Nat.cast_zero, zero_mul, zero_mul, exp_zero]
  · rw [pow_succ', ih, Nat.cast_succ, add_mul, add_mul, one_mul, exp_add]
set_option linter.uppercaseLean3 false in
#align complex.cos_add_sin_mul_I_pow Complex.cos_add_sin_mul_I_pow

end Complex

namespace Real

open Complex

variable (x y : ℝ)

@[simp]
theorem exp_zero : exp 0 = 1 := by simp [Real.exp]
#align real.exp_zero Real.exp_zero

nonrec theorem exp_add : exp (x + y) = exp x * exp y := by simp [exp_add, exp]
#align real.exp_add Real.exp_add

--Porting note: New definition
/-- the exponential function as a monoid hom from `Multiplicative ℝ` to `ℝ` -/
noncomputable def expMonoidHom : MonoidHom (Multiplicative ℝ) ℝ :=
  { toFun := fun x => exp (Multiplicative.toAdd x),
    map_one' := by simp,
    map_mul' := by simp [exp_add] }

theorem exp_list_sum (l : List ℝ) : exp l.sum = (l.map exp).prod :=
  @MonoidHom.map_list_prod (Multiplicative ℝ) ℝ _ _ expMonoidHom l
#align real.exp_list_sum Real.exp_list_sum

theorem exp_multiset_sum (s : Multiset ℝ) : exp s.sum = (s.map exp).prod :=
  @MonoidHom.map_multiset_prod (Multiplicative ℝ) ℝ _ _ expMonoidHom s
#align real.exp_multiset_sum Real.exp_multiset_sum

theorem exp_sum {α : Type*} (s : Finset α) (f : α → ℝ) :
    exp (∑ x in s, f x) = ∏ x in s, exp (f x) :=
  @map_prod (Multiplicative ℝ) α ℝ _ _ _ _ expMonoidHom f s
#align real.exp_sum Real.exp_sum

nonrec theorem exp_nat_mul (x : ℝ) (n : ℕ) : exp (n * x) = exp x ^ n :=
  ofReal_injective (by simp [exp_nat_mul])
#align real.exp_nat_mul Real.exp_nat_mul

nonrec theorem exp_ne_zero : exp x ≠ 0 := fun h =>
  exp_ne_zero x <| by rw [exp, ← ofReal_inj] at h; simp_all
#align real.exp_ne_zero Real.exp_ne_zero

nonrec theorem exp_neg : exp (-x) = (exp x)⁻¹ :=
  ofReal_injective <| by simp [exp_neg]
#align real.exp_neg Real.exp_neg

theorem exp_sub : exp (x - y) = exp x / exp y := by
  simp [sub_eq_add_neg, exp_add, exp_neg, div_eq_mul_inv]
#align real.exp_sub Real.exp_sub

@[simp]
theorem sin_zero : sin 0 = 0 := by simp [sin]
#align real.sin_zero Real.sin_zero

@[simp]
theorem sin_neg : sin (-x) = -sin x := by simp [sin, exp_neg, (neg_div _ _).symm, add_mul]
#align real.sin_neg Real.sin_neg

nonrec theorem sin_add : sin (x + y) = sin x * cos y + cos x * sin y :=
  ofReal_injective <| by simp [sin_add]
#align real.sin_add Real.sin_add

@[simp]
theorem cos_zero : cos 0 = 1 := by simp [cos]
#align real.cos_zero Real.cos_zero

@[simp]
theorem cos_neg : cos (-x) = cos x := by simp [cos, exp_neg]
#align real.cos_neg Real.cos_neg

@[simp]
theorem cos_abs : cos |x| = cos x := by
  cases le_total x 0 <;> simp only [*, _root_.abs_of_nonneg, abs_of_nonpos, cos_neg]
#align real.cos_abs Real.cos_abs

nonrec theorem cos_add : cos (x + y) = cos x * cos y - sin x * sin y :=
  ofReal_injective <| by simp [cos_add]
#align real.cos_add Real.cos_add

theorem sin_sub : sin (x - y) = sin x * cos y - cos x * sin y := by
  simp [sub_eq_add_neg, sin_add, sin_neg, cos_neg]
#align real.sin_sub Real.sin_sub

theorem cos_sub : cos (x - y) = cos x * cos y + sin x * sin y := by
  simp [sub_eq_add_neg, cos_add, sin_neg, cos_neg]
#align real.cos_sub Real.cos_sub

nonrec theorem sin_sub_sin : sin x - sin y = 2 * sin ((x - y) / 2) * cos ((x + y) / 2) :=
  ofReal_injective <| by simp [sin_sub_sin]
#align real.sin_sub_sin Real.sin_sub_sin

nonrec theorem cos_sub_cos : cos x - cos y = -2 * sin ((x + y) / 2) * sin ((x - y) / 2) :=
  ofReal_injective <| by simp [cos_sub_cos]
#align real.cos_sub_cos Real.cos_sub_cos

nonrec theorem cos_add_cos : cos x + cos y = 2 * cos ((x + y) / 2) * cos ((x - y) / 2) :=
  ofReal_injective <| by simp [cos_add_cos]
#align real.cos_add_cos Real.cos_add_cos

nonrec theorem tan_eq_sin_div_cos : tan x = sin x / cos x :=
  ofReal_injective <| by simp [tan_eq_sin_div_cos]
#align real.tan_eq_sin_div_cos Real.tan_eq_sin_div_cos

theorem tan_mul_cos {x : ℝ} (hx : cos x ≠ 0) : tan x * cos x = sin x := by
  rw [tan_eq_sin_div_cos, div_mul_cancel _ hx]
#align real.tan_mul_cos Real.tan_mul_cos

@[simp]
theorem tan_zero : tan 0 = 0 := by simp [tan]
#align real.tan_zero Real.tan_zero

@[simp]
theorem tan_neg : tan (-x) = -tan x := by simp [tan, neg_div]
#align real.tan_neg Real.tan_neg

@[simp]
nonrec theorem sin_sq_add_cos_sq : sin x ^ 2 + cos x ^ 2 = 1 :=
  ofReal_injective (by simp [sin_sq_add_cos_sq])
#align real.sin_sq_add_cos_sq Real.sin_sq_add_cos_sq

@[simp]
theorem cos_sq_add_sin_sq : cos x ^ 2 + sin x ^ 2 = 1 := by rw [add_comm, sin_sq_add_cos_sq]
#align real.cos_sq_add_sin_sq Real.cos_sq_add_sin_sq

theorem sin_sq_le_one : sin x ^ 2 ≤ 1 := by
  rw [← sin_sq_add_cos_sq x]; exact le_add_of_nonneg_right (sq_nonneg _)
#align real.sin_sq_le_one Real.sin_sq_le_one

theorem cos_sq_le_one : cos x ^ 2 ≤ 1 := by
  rw [← sin_sq_add_cos_sq x]; exact le_add_of_nonneg_left (sq_nonneg _)
#align real.cos_sq_le_one Real.cos_sq_le_one

theorem abs_sin_le_one : |sin x| ≤ 1 :=
  abs_le_one_iff_mul_self_le_one.2 <| by simp only [← sq, sin_sq_le_one]
#align real.abs_sin_le_one Real.abs_sin_le_one

theorem abs_cos_le_one : |cos x| ≤ 1 :=
  abs_le_one_iff_mul_self_le_one.2 <| by simp only [← sq, cos_sq_le_one]
#align real.abs_cos_le_one Real.abs_cos_le_one

theorem sin_le_one : sin x ≤ 1 :=
  (abs_le.1 (abs_sin_le_one _)).2
#align real.sin_le_one Real.sin_le_one

theorem cos_le_one : cos x ≤ 1 :=
  (abs_le.1 (abs_cos_le_one _)).2
#align real.cos_le_one Real.cos_le_one

theorem neg_one_le_sin : -1 ≤ sin x :=
  (abs_le.1 (abs_sin_le_one _)).1
#align real.neg_one_le_sin Real.neg_one_le_sin

theorem neg_one_le_cos : -1 ≤ cos x :=
  (abs_le.1 (abs_cos_le_one _)).1
#align real.neg_one_le_cos Real.neg_one_le_cos

nonrec theorem cos_two_mul : cos (2 * x) = 2 * cos x ^ 2 - 1 :=
  ofReal_injective <| by simp [cos_two_mul]
#align real.cos_two_mul Real.cos_two_mul

nonrec theorem cos_two_mul' : cos (2 * x) = cos x ^ 2 - sin x ^ 2 :=
  ofReal_injective <| by simp [cos_two_mul']
#align real.cos_two_mul' Real.cos_two_mul'

nonrec theorem sin_two_mul : sin (2 * x) = 2 * sin x * cos x :=
  ofReal_injective <| by simp [sin_two_mul]
#align real.sin_two_mul Real.sin_two_mul

nonrec theorem cos_sq : cos x ^ 2 = 1 / 2 + cos (2 * x) / 2 :=
  ofReal_injective <| by simp [cos_sq]
#align real.cos_sq Real.cos_sq

theorem cos_sq' : cos x ^ 2 = 1 - sin x ^ 2 := by rw [← sin_sq_add_cos_sq x, add_sub_cancel']
#align real.cos_sq' Real.cos_sq'

theorem sin_sq : sin x ^ 2 = 1 - cos x ^ 2 :=
  eq_sub_iff_add_eq.2 <| sin_sq_add_cos_sq _
#align real.sin_sq Real.sin_sq

lemma sin_sq_eq_half_sub : sin x ^ 2 = 1 / 2 - cos (2 * x) / 2 := by
  rw [sin_sq, cos_sq, ← sub_sub, sub_half]

theorem abs_sin_eq_sqrt_one_sub_cos_sq (x : ℝ) : |sin x| = sqrt (1 - cos x ^ 2) := by
  rw [← sin_sq, sqrt_sq_eq_abs]
#align real.abs_sin_eq_sqrt_one_sub_cos_sq Real.abs_sin_eq_sqrt_one_sub_cos_sq

theorem abs_cos_eq_sqrt_one_sub_sin_sq (x : ℝ) : |cos x| = sqrt (1 - sin x ^ 2) := by
  rw [← cos_sq', sqrt_sq_eq_abs]
#align real.abs_cos_eq_sqrt_one_sub_sin_sq Real.abs_cos_eq_sqrt_one_sub_sin_sq

theorem inv_one_add_tan_sq {x : ℝ} (hx : cos x ≠ 0) : (1 + tan x ^ 2)⁻¹ = cos x ^ 2 :=
  have : Complex.cos x ≠ 0 := mt (congr_arg re) hx
  ofReal_inj.1 <| by simpa using Complex.inv_one_add_tan_sq this
#align real.inv_one_add_tan_sq Real.inv_one_add_tan_sq

theorem tan_sq_div_one_add_tan_sq {x : ℝ} (hx : cos x ≠ 0) :
    tan x ^ 2 / (1 + tan x ^ 2) = sin x ^ 2 := by
  simp only [← tan_mul_cos hx, mul_pow, ← inv_one_add_tan_sq hx, div_eq_mul_inv, one_mul]
#align real.tan_sq_div_one_add_tan_sq Real.tan_sq_div_one_add_tan_sq

theorem inv_sqrt_one_add_tan_sq {x : ℝ} (hx : 0 < cos x) : (sqrt (1 + tan x ^ 2))⁻¹ = cos x := by
  rw [← sqrt_sq hx.le, ← sqrt_inv, inv_one_add_tan_sq hx.ne']
#align real.inv_sqrt_one_add_tan_sq Real.inv_sqrt_one_add_tan_sq

theorem tan_div_sqrt_one_add_tan_sq {x : ℝ} (hx : 0 < cos x) :
    tan x / sqrt (1 + tan x ^ 2) = sin x := by
  rw [← tan_mul_cos hx.ne', ← inv_sqrt_one_add_tan_sq hx, div_eq_mul_inv]
#align real.tan_div_sqrt_one_add_tan_sq Real.tan_div_sqrt_one_add_tan_sq

nonrec theorem cos_three_mul : cos (3 * x) = 4 * cos x ^ 3 - 3 * cos x := by
  rw [← ofReal_inj]; simp [cos_three_mul]
#align real.cos_three_mul Real.cos_three_mul

nonrec theorem sin_three_mul : sin (3 * x) = 3 * sin x - 4 * sin x ^ 3 := by
  rw [← ofReal_inj]; simp [sin_three_mul]
#align real.sin_three_mul Real.sin_three_mul

/-- The definition of `sinh` in terms of `exp`. -/
nonrec theorem sinh_eq (x : ℝ) : sinh x = (exp x - exp (-x)) / 2 :=
  ofReal_injective <| by simp [Complex.sinh]
#align real.sinh_eq Real.sinh_eq

@[simp]
theorem sinh_zero : sinh 0 = 0 := by simp [sinh]
#align real.sinh_zero Real.sinh_zero

@[simp]
theorem sinh_neg : sinh (-x) = -sinh x := by simp [sinh, exp_neg, (neg_div _ _).symm, add_mul]
#align real.sinh_neg Real.sinh_neg

nonrec theorem sinh_add : sinh (x + y) = sinh x * cosh y + cosh x * sinh y := by
  rw [← ofReal_inj]; simp [sinh_add]
#align real.sinh_add Real.sinh_add

/-- The definition of `cosh` in terms of `exp`. -/
theorem cosh_eq (x : ℝ) : cosh x = (exp x + exp (-x)) / 2 :=
  eq_div_of_mul_eq two_ne_zero <| by
    rw [cosh, exp, exp, Complex.ofReal_neg, Complex.cosh, mul_two, ← Complex.add_re, ← mul_two,
      div_mul_cancel _ (two_ne_zero' ℂ), Complex.add_re]
#align real.cosh_eq Real.cosh_eq

@[simp]
theorem cosh_zero : cosh 0 = 1 := by simp [cosh]
#align real.cosh_zero Real.cosh_zero

@[simp]
theorem cosh_neg : cosh (-x) = cosh x :=
  ofReal_inj.1 <| by simp
#align real.cosh_neg Real.cosh_neg

@[simp]
theorem cosh_abs : cosh |x| = cosh x := by
  cases le_total x 0 <;> simp [*, _root_.abs_of_nonneg, abs_of_nonpos]
#align real.cosh_abs Real.cosh_abs

nonrec theorem cosh_add : cosh (x + y) = cosh x * cosh y + sinh x * sinh y := by
  rw [← ofReal_inj]; simp [cosh_add]
#align real.cosh_add Real.cosh_add

theorem sinh_sub : sinh (x - y) = sinh x * cosh y - cosh x * sinh y := by
  simp [sub_eq_add_neg, sinh_add, sinh_neg, cosh_neg]
#align real.sinh_sub Real.sinh_sub

theorem cosh_sub : cosh (x - y) = cosh x * cosh y - sinh x * sinh y := by
  simp [sub_eq_add_neg, cosh_add, sinh_neg, cosh_neg]
#align real.cosh_sub Real.cosh_sub

nonrec theorem tanh_eq_sinh_div_cosh : tanh x = sinh x / cosh x :=
  ofReal_inj.1 <| by simp [tanh_eq_sinh_div_cosh]
#align real.tanh_eq_sinh_div_cosh Real.tanh_eq_sinh_div_cosh

@[simp]
theorem tanh_zero : tanh 0 = 0 := by simp [tanh]
#align real.tanh_zero Real.tanh_zero

@[simp]
theorem tanh_neg : tanh (-x) = -tanh x := by simp [tanh, neg_div]
#align real.tanh_neg Real.tanh_neg

@[simp]
theorem cosh_add_sinh : cosh x + sinh x = exp x := by rw [← ofReal_inj]; simp
#align real.cosh_add_sinh Real.cosh_add_sinh

@[simp]
theorem sinh_add_cosh : sinh x + cosh x = exp x := by rw [add_comm, cosh_add_sinh]
#align real.sinh_add_cosh Real.sinh_add_cosh

@[simp]
theorem exp_sub_cosh : exp x - cosh x = sinh x :=
  sub_eq_iff_eq_add.2 (sinh_add_cosh x).symm
#align real.exp_sub_cosh Real.exp_sub_cosh

@[simp]
theorem exp_sub_sinh : exp x - sinh x = cosh x :=
  sub_eq_iff_eq_add.2 (cosh_add_sinh x).symm
#align real.exp_sub_sinh Real.exp_sub_sinh

@[simp]
theorem cosh_sub_sinh : cosh x - sinh x = exp (-x) := by
  rw [← ofReal_inj]
  simp
#align real.cosh_sub_sinh Real.cosh_sub_sinh

@[simp]
theorem sinh_sub_cosh : sinh x - cosh x = -exp (-x) := by rw [← neg_sub, cosh_sub_sinh]
#align real.sinh_sub_cosh Real.sinh_sub_cosh

@[simp]
theorem cosh_sq_sub_sinh_sq (x : ℝ) : cosh x ^ 2 - sinh x ^ 2 = 1 := by rw [← ofReal_inj]; simp
#align real.cosh_sq_sub_sinh_sq Real.cosh_sq_sub_sinh_sq

nonrec theorem cosh_sq : cosh x ^ 2 = sinh x ^ 2 + 1 := by rw [← ofReal_inj]; simp [cosh_sq]
#align real.cosh_sq Real.cosh_sq

theorem cosh_sq' : cosh x ^ 2 = 1 + sinh x ^ 2 :=
  (cosh_sq x).trans (add_comm _ _)
#align real.cosh_sq' Real.cosh_sq'

nonrec theorem sinh_sq : sinh x ^ 2 = cosh x ^ 2 - 1 := by rw [← ofReal_inj]; simp [sinh_sq]
#align real.sinh_sq Real.sinh_sq

nonrec theorem cosh_two_mul : cosh (2 * x) = cosh x ^ 2 + sinh x ^ 2 := by
  rw [← ofReal_inj]; simp [cosh_two_mul]
#align real.cosh_two_mul Real.cosh_two_mul

nonrec theorem sinh_two_mul : sinh (2 * x) = 2 * sinh x * cosh x := by
  rw [← ofReal_inj]; simp [sinh_two_mul]
#align real.sinh_two_mul Real.sinh_two_mul

nonrec theorem cosh_three_mul : cosh (3 * x) = 4 * cosh x ^ 3 - 3 * cosh x := by
  rw [← ofReal_inj]; simp [cosh_three_mul]
#align real.cosh_three_mul Real.cosh_three_mul

nonrec theorem sinh_three_mul : sinh (3 * x) = 4 * sinh x ^ 3 + 3 * sinh x := by
  rw [← ofReal_inj]; simp [sinh_three_mul]
#align real.sinh_three_mul Real.sinh_three_mul

open IsAbsoluteValue Nat

theorem sum_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : ∑ i in range n, x ^ i / i ! ≤ exp x :=
  calc
    ∑ i in range n, x ^ i / i ! ≤ lim (⟨_, isCauSeq_re (exp' x)⟩ : CauSeq ℝ Abs.abs) := by
      refine' le_lim (CauSeq.le_of_exists ⟨n, fun j hj => _⟩)
      simp only [exp', const_apply, re_sum]
      norm_cast
      refine sum_le_sum_of_subset_of_nonneg (range_mono hj) fun _ _ _ ↦ ?_
      positivity
    _ = exp x := by rw [exp, Complex.exp, ← cauSeqRe, lim_re]
#align real.sum_le_exp_of_nonneg Real.sum_le_exp_of_nonneg

theorem quadratic_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 1 + x + x ^ 2 / 2 ≤ exp x :=
  calc
    1 + x + x ^ 2 / 2 = ∑ i in range 3, x ^ i / i ! := by
        simp only [sum_range_succ, range_one, sum_singleton, _root_.pow_zero, factorial, cast_one,
          ne_eq, one_ne_zero, not_false_eq_true, div_self, pow_one, mul_one, div_one, Nat.mul_one,
          cast_succ, add_right_inj]
        ring_nf
    _ ≤ exp x := sum_le_exp_of_nonneg hx 3
#align real.quadratic_le_exp_of_nonneg Real.quadratic_le_exp_of_nonneg

theorem add_one_lt_exp_of_pos {x : ℝ} (hx : 0 < x) : x + 1 < exp x :=
  (by nlinarith : x + 1 < 1 + x + x ^ 2 / 2).trans_le (quadratic_le_exp_of_nonneg hx.le)
#align real.add_one_lt_exp_of_pos Real.add_one_lt_exp_of_pos

/-- This is an intermediate result that is later replaced by `Real.add_one_le_exp`; use that lemma
instead. -/
theorem add_one_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : x + 1 ≤ exp x := by
  rcases eq_or_lt_of_le hx with (rfl | h)
  · simp
  exact (add_one_lt_exp_of_pos h).le
#align real.add_one_le_exp_of_nonneg Real.add_one_le_exp_of_nonneg

theorem one_le_exp {x : ℝ} (hx : 0 ≤ x) : 1 ≤ exp x := by linarith [add_one_le_exp_of_nonneg hx]
#align real.one_le_exp Real.one_le_exp

theorem exp_pos (x : ℝ) : 0 < exp x :=
  (le_total 0 x).elim (lt_of_lt_of_le zero_lt_one ∘ one_le_exp) fun h => by
    rw [← neg_neg x, Real.exp_neg]
    exact inv_pos.2 (lt_of_lt_of_le zero_lt_one (one_le_exp (neg_nonneg.2 h)))
#align real.exp_pos Real.exp_pos

@[simp]
theorem abs_exp (x : ℝ) : |exp x| = exp x :=
  abs_of_pos (exp_pos _)
#align real.abs_exp Real.abs_exp

@[mono]
theorem exp_strictMono : StrictMono exp := fun x y h => by
  rw [← sub_add_cancel y x, Real.exp_add]
  exact (lt_mul_iff_one_lt_left (exp_pos _)).2
      (lt_of_lt_of_le (by linarith) (add_one_le_exp_of_nonneg (by linarith)))
#align real.exp_strict_mono Real.exp_strictMono

@[gcongr]
theorem exp_lt_exp_of_lt {x y : ℝ} (h : x < y) : exp x < exp y := exp_strictMono h

@[mono]
theorem exp_monotone : Monotone exp :=
  exp_strictMono.monotone
#align real.exp_monotone Real.exp_monotone

@[gcongr]
theorem exp_le_exp_of_le {x y : ℝ} (h : x ≤ y) : exp x ≤ exp y := exp_monotone h

@[simp]
theorem exp_lt_exp {x y : ℝ} : exp x < exp y ↔ x < y :=
  exp_strictMono.lt_iff_lt
#align real.exp_lt_exp Real.exp_lt_exp

@[simp]
theorem exp_le_exp {x y : ℝ} : exp x ≤ exp y ↔ x ≤ y :=
  exp_strictMono.le_iff_le
#align real.exp_le_exp Real.exp_le_exp

theorem exp_injective : Function.Injective exp :=
  exp_strictMono.injective
#align real.exp_injective Real.exp_injective

@[simp]
theorem exp_eq_exp {x y : ℝ} : exp x = exp y ↔ x = y :=
  exp_injective.eq_iff
#align real.exp_eq_exp Real.exp_eq_exp

@[simp]
theorem exp_eq_one_iff : exp x = 1 ↔ x = 0 :=
  exp_injective.eq_iff' exp_zero
#align real.exp_eq_one_iff Real.exp_eq_one_iff

@[simp]
theorem one_lt_exp_iff {x : ℝ} : 1 < exp x ↔ 0 < x := by rw [← exp_zero, exp_lt_exp]
#align real.one_lt_exp_iff Real.one_lt_exp_iff

@[simp]
theorem exp_lt_one_iff {x : ℝ} : exp x < 1 ↔ x < 0 := by rw [← exp_zero, exp_lt_exp]
#align real.exp_lt_one_iff Real.exp_lt_one_iff

@[simp]
theorem exp_le_one_iff {x : ℝ} : exp x ≤ 1 ↔ x ≤ 0 :=
  exp_zero ▸ exp_le_exp
#align real.exp_le_one_iff Real.exp_le_one_iff

@[simp]
theorem one_le_exp_iff {x : ℝ} : 1 ≤ exp x ↔ 0 ≤ x :=
  exp_zero ▸ exp_le_exp
#align real.one_le_exp_iff Real.one_le_exp_iff

/-- `Real.cosh` is always positive -/
theorem cosh_pos (x : ℝ) : 0 < Real.cosh x :=
  (cosh_eq x).symm ▸ half_pos (add_pos (exp_pos x) (exp_pos (-x)))
#align real.cosh_pos Real.cosh_pos

theorem sinh_lt_cosh : sinh x < cosh x :=
  lt_of_pow_lt_pow 2 (cosh_pos _).le <| (cosh_sq x).symm ▸ lt_add_one _
#align real.sinh_lt_cosh Real.sinh_lt_cosh

end Real

namespace Complex

theorem sum_div_factorial_le {α : Type*} [LinearOrderedField α] (n j : ℕ) (hn : 0 < n) :
    (∑ m in filter (fun k => n ≤ k) (range j),
      (1 / m.factorial : α)) ≤ n.succ / (n.factorial * n) :=
  calc
    (∑ m in filter (fun k => n ≤ k) (range j), (1 / m.factorial : α)) =
        ∑ m in range (j - n), (1 / ((m + n).factorial : α)) :=
      sum_bij (fun m _ => m - n)
        (fun m hm =>
          mem_range.2 <|
            (tsub_lt_tsub_iff_right (by simp at hm; tauto)).2 (by simp at hm; tauto))
        (fun m hm => by rw [tsub_add_cancel_of_le]; simp at *; tauto)
        (fun a₁ a₂ ha₁ ha₂ h => by
          rwa [tsub_eq_iff_eq_add_of_le, tsub_add_eq_add_tsub, eq_comm, tsub_eq_iff_eq_add_of_le,
              add_left_inj, eq_comm] at h <;>
          simp at * <;> aesop)
        fun b hb =>
        ⟨b + n,
          mem_filter.2 ⟨mem_range.2 <| lt_tsub_iff_right.mp (mem_range.1 hb), Nat.le_add_left _ _⟩,
          by dsimp; rw [add_tsub_cancel_right]⟩
    _ ≤ ∑ m in range (j - n), ((n.factorial : α) * (n.succ : α) ^ m)⁻¹ := by
      simp_rw [one_div]
      gcongr
      · rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.cast_le, add_comm]
        exact Nat.factorial_mul_pow_le_factorial
    _ = (n.factorial : α)⁻¹ * ∑ m in range (j - n), (n.succ : α)⁻¹ ^ m := by
      simp [mul_inv, mul_sum.symm, sum_mul.symm, mul_comm, inv_pow]
    _ = ((n.succ : α) - n.succ * (n.succ : α)⁻¹ ^ (j - n)) / (n.factorial * n) := by
      have h₁ : (n.succ : α) ≠ 1 :=
        @Nat.cast_one α _ ▸ mt Nat.cast_inj.1 (mt Nat.succ.inj (pos_iff_ne_zero.1 hn))
      have h₂ : (n.succ : α) ≠ 0 := by positivity
      have h₃ : (n.factorial * n : α) ≠ 0 := by positivity
      have h₄ : (n.succ - 1 : α) = n := by simp
      rw [geom_sum_inv h₁ h₂, eq_div_iff_mul_eq h₃, mul_comm _ (n.factorial * n : α),
          ← mul_assoc (n.factorial⁻¹ : α), ← mul_inv_rev, h₄, ← mul_assoc (n.factorial * n : α),
          mul_comm (n : α) n.factorial, mul_inv_cancel h₃, one_mul, mul_comm]
    _ ≤ n.succ / (n.factorial * n : α) := by gcongr; apply sub_le_self; positivity
#align complex.sum_div_factorial_le Complex.sum_div_factorial_le

theorem exp_bound {x : ℂ} (hx : abs x ≤ 1) {n : ℕ} (hn : 0 < n) :
    abs (exp x - ∑ m in range n, x ^ m / m.factorial) ≤
      abs x ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) := by
  rw [← lim_const (abv := Complex.abs) (∑ m in range n, _), exp, sub_eq_add_neg,
    ← lim_neg, lim_add, ← lim_abs]
  refine' lim_le (CauSeq.le_of_exists ⟨n, fun j hj => _⟩)
  simp_rw [← sub_eq_add_neg]
  show
    abs ((∑ m in range j, x ^ m / m.factorial) - ∑ m in range n, x ^ m / m.factorial) ≤
      abs x ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹)
  rw [sum_range_sub_sum_range hj]
  calc
    abs (∑ m in (range j).filter fun k => n ≤ k, (x ^ m / m.factorial : ℂ)) =
      abs (∑ m in (range j).filter fun k => n ≤ k,
        (x ^ n * (x ^ (m - n) / m.factorial) : ℂ)) := by
      refine' congr_arg abs (sum_congr rfl fun m hm => _)
      rw [mem_filter, mem_range] at hm
      rw [← mul_div_assoc, ← pow_add, add_tsub_cancel_of_le hm.2]
    _ ≤ ∑ m in filter (fun k => n ≤ k) (range j), abs (x ^ n * (x ^ (m - n) / m.factorial)) :=
      (abv_sum_le_sum_abv (abv := Complex.abs) _ _)
    _ ≤ ∑ m in filter (fun k => n ≤ k) (range j), abs x ^ n * (1 / m.factorial) := by
      simp_rw [map_mul, map_pow, map_div₀, abs_natCast]
      gcongr
      · rw [abv_pow abs]
        exact pow_le_one _ (abs.nonneg _) hx
    _ = abs x ^ n * ∑ m in (range j).filter fun k => n ≤ k, (1 / m.factorial : ℝ) := by
      simp [abs_mul, abv_pow abs, abs_div, mul_sum.symm]
    _ ≤ abs x ^ n * (n.succ * (n.factorial * n : ℝ)⁻¹) := by
      gcongr
      exact sum_div_factorial_le _ _ hn
#align complex.exp_bound Complex.exp_bound

theorem exp_bound' {x : ℂ} {n : ℕ} (hx : abs x / n.succ ≤ 1 / 2) :
    abs (exp x - ∑ m in range n, x ^ m / m.factorial) ≤ abs x ^ n / n.factorial * 2 := by
  rw [← lim_const (abv := Complex.abs) (∑ m in range n, _),
    exp, sub_eq_add_neg, ← lim_neg, lim_add, ← lim_abs]
  refine' lim_le (CauSeq.le_of_exists ⟨n, fun j hj => _⟩)
  simp_rw [← sub_eq_add_neg]
  show abs ((∑ m in range j, x ^ m / m.factorial) - ∑ m in range n, x ^ m / m.factorial) ≤
    abs x ^ n / n.factorial * 2
  let k := j - n
  have hj : j = n + k := (add_tsub_cancel_of_le hj).symm
  rw [hj, sum_range_add_sub_sum_range]
  calc
    abs (∑ i : ℕ in range k, x ^ (n + i) / ((n + i).factorial : ℂ)) ≤
        ∑ i : ℕ in range k, abs (x ^ (n + i) / ((n + i).factorial : ℂ)) :=
      abv_sum_le_sum_abv _ _
    _ ≤ ∑ i : ℕ in range k, abs x ^ (n + i) / (n + i).factorial := by
      simp [Complex.abs_natCast, map_div₀, abv_pow abs]
    _ ≤ ∑ i : ℕ in range k, abs x ^ (n + i) / ((n.factorial : ℝ) * (n.succ : ℝ) ^ i) := ?_
    _ = ∑ i : ℕ in range k, abs x ^ n / n.factorial * (abs x ^ i / (n.succ : ℝ) ^ i) := ?_
    _ ≤ abs x ^ n / ↑n.factorial * 2 := ?_
  · gcongr
    · exact_mod_cast Nat.factorial_mul_pow_le_factorial
  · refine' Finset.sum_congr rfl fun _ _ => _
    simp only [pow_add, div_eq_inv_mul, mul_inv, mul_left_comm, mul_assoc]
  · rw [← mul_sum]
    gcongr
    · simp_rw [← div_pow]
      rw [geom_sum_eq, div_le_iff_of_neg]
      · trans (-1 : ℝ)
        · linarith
        · simp only [neg_le_sub_iff_le_add, div_pow, Nat.cast_succ, le_add_iff_nonneg_left]
          positivity
      · linarith
      · linarith
#align complex.exp_bound' Complex.exp_bound'

theorem abs_exp_sub_one_le {x : ℂ} (hx : abs x ≤ 1) : abs (exp x - 1) ≤ 2 * abs x :=
  calc
    abs (exp x - 1) = abs (exp x - ∑ m in range 1, x ^ m / m.factorial) := by simp [sum_range_succ]
    _ ≤ abs x ^ 1 * ((Nat.succ 1 : ℝ) * ((Nat.factorial 1) * (1 : ℕ) : ℝ)⁻¹) :=
      (exp_bound hx (by decide))
    _ = 2 * abs x := by simp [two_mul, mul_two, mul_add, mul_comm, add_mul, Nat.factorial]
#align complex.abs_exp_sub_one_le Complex.abs_exp_sub_one_le

theorem abs_exp_sub_one_sub_id_le {x : ℂ} (hx : abs x ≤ 1) : abs (exp x - 1 - x) ≤ abs x ^ 2 :=
  calc
    abs (exp x - 1 - x) = abs (exp x - ∑ m in range 2, x ^ m / m.factorial) := by
      simp [sub_eq_add_neg, sum_range_succ_comm, add_assoc, Nat.factorial]
    _ ≤ abs x ^ 2 * ((Nat.succ 2 : ℝ) * (Nat.factorial 2 * (2 : ℕ) : ℝ)⁻¹) :=
      (exp_bound hx (by decide))
    _ ≤ abs x ^ 2 * 1 := by gcongr; norm_num [Nat.factorial]
    _ = abs x ^ 2 := by rw [mul_one]
#align complex.abs_exp_sub_one_sub_id_le Complex.abs_exp_sub_one_sub_id_le

end Complex

namespace Real

open Complex Finset

nonrec theorem exp_bound {x : ℝ} (hx : |x| ≤ 1) {n : ℕ} (hn : 0 < n) :
    |exp x - ∑ m in range n, x ^ m / m.factorial| ≤ |x| ^ n * (n.succ / (n.factorial * n)) := by
  have hxc : Complex.abs x ≤ 1 := by exact_mod_cast hx
  convert exp_bound hxc hn using 2 <;>
  --Porting note: was `norm_cast`
  simp only [← abs_ofReal, ← ofReal_sub, ← ofReal_exp, ← ofReal_sum, ← ofReal_pow,
    ← ofReal_div, ← ofReal_nat_cast]
#align real.exp_bound Real.exp_bound

theorem exp_bound' {x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ 1) {n : ℕ} (hn : 0 < n) :
    Real.exp x ≤ (∑ m in Finset.range n, x ^ m / m.factorial) +
      x ^ n * (n + 1) / (n.factorial * n) := by
  have h3 : |x| = x := by simpa
  have h4 : |x| ≤ 1 := by rwa [h3]
  have h' := Real.exp_bound h4 hn
  rw [h3] at h'
  have h'' := (abs_sub_le_iff.1 h').1
  have t := sub_le_iff_le_add'.1 h''
  simpa [mul_div_assoc] using t
#align real.exp_bound' Real.exp_bound'

theorem abs_exp_sub_one_le {x : ℝ} (hx : |x| ≤ 1) : |exp x - 1| ≤ 2 * |x| := by
  have : abs' x ≤ 1 := by exact_mod_cast hx
  --Porting note: was
  --exact_mod_cast Complex.abs_exp_sub_one_le (x := x) this
  have := Complex.abs_exp_sub_one_le (x := x) (by simpa using this)
  rw [← ofReal_exp, ← ofReal_one, ← ofReal_sub, abs_ofReal, abs_ofReal] at this
  exact this
#align real.abs_exp_sub_one_le Real.abs_exp_sub_one_le

theorem abs_exp_sub_one_sub_id_le {x : ℝ} (hx : |x| ≤ 1) : |exp x - 1 - x| ≤ x ^ 2 := by
  rw [← _root_.sq_abs]
  --Porting note: was
  --exact_mod_cast Complex.abs_exp_sub_one_sub_id_le this
  have : Complex.abs x ≤ 1 := by exact_mod_cast hx
  have := Complex.abs_exp_sub_one_sub_id_le this
  rw [← ofReal_one, ← ofReal_exp, ← ofReal_sub, ← ofReal_sub, abs_ofReal, abs_ofReal] at this
  exact this
#align real.abs_exp_sub_one_sub_id_le Real.abs_exp_sub_one_sub_id_le

/-- A finite initial segment of the exponential series, followed by an arbitrary tail.
For fixed `n` this is just a linear map wrt `r`, and each map is a simple linear function
of the previous (see `expNear_succ`), with `expNear n x r ⟶ exp x` as `n ⟶ ∞`,
for any `r`. -/
noncomputable def expNear (n : ℕ) (x r : ℝ) : ℝ :=
  (∑ m in range n, x ^ m / m.factorial) + x ^ n / n.factorial * r
#align real.exp_near Real.expNear

@[simp]
theorem expNear_zero (x r) : expNear 0 x r = r := by simp [expNear]
#align real.exp_near_zero Real.expNear_zero

@[simp]
theorem expNear_succ (n x r) : expNear (n + 1) x r = expNear n x (1 + x / (n + 1) * r) := by
  simp [expNear, range_succ, mul_add, add_left_comm, add_assoc, pow_succ, div_eq_mul_inv,
      mul_inv, Nat.factorial]
  ac_rfl
#align real.exp_near_succ Real.expNear_succ

theorem expNear_sub (n x r₁ r₂) : expNear n x r₁ -
    expNear n x r₂ = x ^ n / n.factorial * (r₁ - r₂) := by
  simp [expNear, mul_sub]
#align real.exp_near_sub Real.expNear_sub

theorem exp_approx_end (n m : ℕ) (x : ℝ) (e₁ : n + 1 = m) (h : |x| ≤ 1) :
    |exp x - expNear m x 0| ≤ |x| ^ m / m.factorial * ((m + 1) / m) := by
  simp only [expNear, mul_zero, add_zero]
  convert exp_bound (n := m) h ?_ using 1
  field_simp [mul_comm]
  linarith
#align real.exp_approx_end Real.exp_approx_end

theorem exp_approx_succ {n} {x a₁ b₁ : ℝ} (m : ℕ) (e₁ : n + 1 = m) (a₂ b₂ : ℝ)
    (e : |1 + x / m * a₂ - a₁| ≤ b₁ - |x| / m * b₂)
    (h : |exp x - expNear m x a₂| ≤ |x| ^ m / m.factorial * b₂) :
    |exp x - expNear n x a₁| ≤ |x| ^ n / n.factorial * b₁ := by
  refine' (abs_sub_le _ _ _).trans ((add_le_add_right h _).trans _)
  subst e₁; rw [expNear_succ, expNear_sub, abs_mul]
  convert mul_le_mul_of_nonneg_left (a := abs' x ^ n / ↑(Nat.factorial n))
      (le_sub_iff_add_le'.1 e) ?_ using 1
  · simp [mul_add, pow_succ', div_eq_mul_inv, abs_mul, abs_inv, ← pow_abs, mul_inv, Nat.factorial]
    ac_rfl
  · simp [div_nonneg, abs_nonneg]
#align real.exp_approx_succ Real.exp_approx_succ

theorem exp_approx_end' {n} {x a b : ℝ} (m : ℕ) (e₁ : n + 1 = m) (rm : ℝ) (er : ↑m = rm)
    (h : |x| ≤ 1) (e : |1 - a| ≤ b - |x| / rm * ((rm + 1) / rm)) :
    |exp x - expNear n x a| ≤ |x| ^ n / n.factorial * b := by
  subst er
  exact exp_approx_succ _ e₁ _ _ (by simpa using e) (exp_approx_end _ _ _ e₁ h)
#align real.exp_approx_end' Real.exp_approx_end'

theorem exp_1_approx_succ_eq {n} {a₁ b₁ : ℝ} {m : ℕ} (en : n + 1 = m) {rm : ℝ} (er : ↑m = rm)
    (h : |exp 1 - expNear m 1 ((a₁ - 1) * rm)| ≤ |1| ^ m / m.factorial * (b₁ * rm)) :
    |exp 1 - expNear n 1 a₁| ≤ |1| ^ n / n.factorial * b₁ := by
  subst er
  refine' exp_approx_succ _ en _ _ _ h
  field_simp [show (m : ℝ) ≠ 0 by norm_cast; linarith]
#align real.exp_1_approx_succ_eq Real.exp_1_approx_succ_eq

theorem exp_approx_start (x a b : ℝ) (h : |exp x - expNear 0 x a| ≤ |x| ^ 0 / Nat.factorial 0 * b) :
    |exp x - a| ≤ b := by simpa using h
#align real.exp_approx_start Real.exp_approx_start

theorem cos_bound {x : ℝ} (hx : |x| ≤ 1) : |cos x - (1 - x ^ 2 / 2)| ≤ |x| ^ 4 * (5 / 96) :=
  calc
    |cos x - (1 - x ^ 2 / 2)| = Complex.abs (Complex.cos x - (1 - (x : ℂ) ^ 2 / 2)) := by
      rw [← abs_ofReal]; simp
    _ = Complex.abs ((Complex.exp (x * I) + Complex.exp (-x * I) - (2 - (x : ℂ) ^ 2)) / 2) := by
      simp [Complex.cos, sub_div, add_div, neg_div, div_self (two_ne_zero' ℂ)]
    _ = abs
          (((Complex.exp (x * I) - ∑ m in range 4, (x * I) ^ m / m.factorial) +
              (Complex.exp (-x * I) - ∑ m in range 4, (-x * I) ^ m / m.factorial)) / 2) :=
      (congr_arg Complex.abs
        (congr_arg (fun x : ℂ => x / 2)
          (by
            simp only [sum_range_succ, neg_mul, pow_succ, pow_zero, mul_one, range_zero, sum_empty,
              Nat.factorial, Nat.cast_one, ne_eq, one_ne_zero, not_false_eq_true, div_self,
              zero_add, div_one, Nat.mul_one, Nat.cast_succ, Nat.cast_mul, Nat.cast_ofNat, mul_neg,
              neg_neg]
            apply Complex.ext <;> simp [div_eq_mul_inv, normSq] <;> ring_nf
            )))
    _ ≤ abs ((Complex.exp (x * I) - ∑ m in range 4, (x * I) ^ m / m.factorial) / 2) +
          abs ((Complex.exp (-x * I) - ∑ m in range 4, (-x * I) ^ m / m.factorial) / 2) :=
      by rw [add_div]; exact Complex.abs.add_le _ _
    _ = abs (Complex.exp (x * I) - ∑ m in range 4, (x * I) ^ m / m.factorial) / 2 +
          abs (Complex.exp (-x * I) - ∑ m in range 4, (-x * I) ^ m / m.factorial) / 2 :=
      by simp [map_div₀]
    _ ≤ Complex.abs (x * I) ^ 4 * (Nat.succ 4 * ((Nat.factorial 4) * (4 : ℕ) : ℝ)⁻¹) / 2 +
          Complex.abs (-x * I) ^ 4 * (Nat.succ 4 * ((Nat.factorial 4) * (4 : ℕ) : ℝ)⁻¹) / 2 := by
      gcongr
      · exact Complex.exp_bound (by simpa) (by decide)
      · exact Complex.exp_bound (by simpa) (by decide)
    _ ≤ |x| ^ 4 * (5 / 96) := by norm_num [Nat.factorial]
#align real.cos_bound Real.cos_bound

theorem sin_bound {x : ℝ} (hx : |x| ≤ 1) : |sin x - (x - x ^ 3 / 6)| ≤ |x| ^ 4 * (5 / 96) :=
  calc
    |sin x - (x - x ^ 3 / 6)| = Complex.abs (Complex.sin x - (x - x ^ 3 / 6 : ℝ)) := by
      rw [← abs_ofReal]; simp
    _ = Complex.abs (((Complex.exp (-x * I) - Complex.exp (x * I)) * I -
          (2 * x - x ^ 3 / 3 : ℝ)) / 2) := by
      simp [Complex.sin, sub_div, add_div, neg_div, mul_div_cancel_left _ (two_ne_zero' ℂ), div_div,
        show (3 : ℂ) * 2 = 6 by norm_num]
    _ = Complex.abs (((Complex.exp (-x * I) - ∑ m in range 4, (-x * I) ^ m / m.factorial) -
                (Complex.exp (x * I) - ∑ m in range 4, (x * I) ^ m / m.factorial)) * I / 2) :=
      (congr_arg Complex.abs
        (congr_arg (fun x : ℂ => x / 2)
          (by
            simp only [sum_range_succ, neg_mul, pow_succ, pow_zero, mul_one, ofReal_sub, ofReal_mul,
              ofReal_ofNat, ofReal_div, range_zero, sum_empty, Nat.factorial, Nat.cast_one, ne_eq,
              one_ne_zero, not_false_eq_true, div_self, zero_add, div_one, mul_neg, neg_neg,
              Nat.mul_one, Nat.cast_succ, Nat.cast_mul, Nat.cast_ofNat]
            apply Complex.ext <;> simp [div_eq_mul_inv, normSq]; ring)))
    _ ≤ abs ((Complex.exp (-x * I) - ∑ m in range 4, (-x * I) ^ m / m.factorial) * I / 2) +
          abs (-((Complex.exp (x * I) - ∑ m in range 4, (x * I) ^ m / m.factorial) * I) / 2) :=
      by rw [sub_mul, sub_eq_add_neg, add_div]; exact Complex.abs.add_le _ _
    _ = abs (Complex.exp (x * I) - ∑ m in range 4, (x * I) ^ m / m.factorial) / 2 +
          abs (Complex.exp (-x * I) - ∑ m in range 4, (-x * I) ^ m / m.factorial) / 2 :=
      by simp [add_comm, map_div₀]
    _ ≤ Complex.abs (x * I) ^ 4 * (Nat.succ 4 * (Nat.factorial 4 * (4 : ℕ) : ℝ)⁻¹) / 2 +
          Complex.abs (-x * I) ^ 4 * (Nat.succ 4 * (Nat.factorial 4 * (4 : ℕ) : ℝ)⁻¹) / 2 := by
      gcongr
      · exact Complex.exp_bound (by simpa) (by decide)
      · exact Complex.exp_bound (by simpa) (by decide)
    _ ≤ |x| ^ 4 * (5 / 96) := by norm_num [Nat.factorial]
#align real.sin_bound Real.sin_bound

theorem cos_pos_of_le_one {x : ℝ} (hx : |x| ≤ 1) : 0 < cos x :=
  calc 0 < 1 - x ^ 2 / 2 - |x| ^ 4 * (5 / 96) :=
      sub_pos.2 <|
        lt_sub_iff_add_lt.2
          (calc
            |x| ^ 4 * (5 / 96) + x ^ 2 / 2 ≤ 1 * (5 / 96) + 1 / 2 := by
                  gcongr
                  · exact pow_le_one _ (abs_nonneg _) hx
                  · rw [sq, ← abs_mul_self, abs_mul]
                    exact mul_le_one hx (abs_nonneg _) hx
            _ < 1 := by norm_num)
    _ ≤ cos x := sub_le_comm.1 (abs_sub_le_iff.1 (cos_bound hx)).2
#align real.cos_pos_of_le_one Real.cos_pos_of_le_one

theorem sin_pos_of_pos_of_le_one {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1) : 0 < sin x :=
  calc 0 < x - x ^ 3 / 6 - |x| ^ 4 * (5 / 96) :=
      sub_pos.2 <| lt_sub_iff_add_lt.2
          (calc
            |x| ^ 4 * (5 / 96) + x ^ 3 / 6 ≤ x * (5 / 96) + x / 6 := by
                gcongr
                · calc
                    |x| ^ 4 ≤ |x| ^ 1 :=
                      pow_le_pow_of_le_one (abs_nonneg _)
                        (by rwa [_root_.abs_of_nonneg (le_of_lt hx0)]) (by decide)
                    _ = x := by simp [_root_.abs_of_nonneg (le_of_lt hx0)]
                · calc
                    x ^ 3 ≤ x ^ 1 := pow_le_pow_of_le_one (le_of_lt hx0) hx (by decide)
                    _ = x := pow_one _
            _ < x := by linarith)
    _ ≤ sin x :=
      sub_le_comm.1 (abs_sub_le_iff.1 (sin_bound (by rwa [_root_.abs_of_nonneg (le_of_lt hx0)]))).2
#align real.sin_pos_of_pos_of_le_one Real.sin_pos_of_pos_of_le_one

theorem sin_pos_of_pos_of_le_two {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 2) : 0 < sin x :=
  have : x / 2 ≤ 1 := (div_le_iff (by norm_num)).mpr (by simpa)
  calc
    0 < 2 * sin (x / 2) * cos (x / 2) :=
      mul_pos (mul_pos (by norm_num) (sin_pos_of_pos_of_le_one (half_pos hx0) this))
        (cos_pos_of_le_one (by rwa [_root_.abs_of_nonneg (le_of_lt (half_pos hx0))]))
    _ = sin x := by rw [← sin_two_mul, two_mul, add_halves]
#align real.sin_pos_of_pos_of_le_two Real.sin_pos_of_pos_of_le_two

theorem cos_one_le : cos 1 ≤ 2 / 3 :=
  calc
    cos 1 ≤ |(1 : ℝ)| ^ 4 * (5 / 96) + (1 - 1 ^ 2 / 2) :=
      sub_le_iff_le_add.1 (abs_sub_le_iff.1 (cos_bound (by simp))).1
    _ ≤ 2 / 3 := by norm_num
#align real.cos_one_le Real.cos_one_le

theorem cos_one_pos : 0 < cos 1 :=
  cos_pos_of_le_one (le_of_eq abs_one)
#align real.cos_one_pos Real.cos_one_pos

theorem cos_two_neg : cos 2 < 0 :=
  calc cos 2 = cos (2 * 1) := congr_arg cos (mul_one _).symm
    _ = _ := (Real.cos_two_mul 1)
    _ ≤ 2 * (2 / 3) ^ 2 - 1 := by
      gcongr
      · exact cos_one_pos.le
      · apply cos_one_le
    _ < 0 := by norm_num
#align real.cos_two_neg Real.cos_two_neg

theorem exp_bound_div_one_sub_of_interval' {x : ℝ} (h1 : 0 < x) (h2 : x < 1) :
    Real.exp x < 1 / (1 - x) := by
  have H : 0 < 1 - (1 + x + x ^ 2) * (1 - x)
  · calc
      0 < x ^ 3 := by positivity
      _ = 1 - (1 + x + x ^ 2) * (1 - x) := by ring
  calc
    exp x ≤ _ := exp_bound' h1.le h2.le zero_lt_three
    _ ≤ 1 + x + x ^ 2 := by
      -- Porting note: was `norm_num [Finset.sum] <;> nlinarith`
      -- This proof should be restored after the norm_num plugin for big operators is ported.
      -- (It may also need the positivity extensions in #3907.)
      repeat erw [Finset.sum_range_succ]
      norm_num [Nat.factorial]
      nlinarith
    _ < 1 / (1 - x) := by rw [lt_div_iff] <;> nlinarith
#align real.exp_bound_div_one_sub_of_interval' Real.exp_bound_div_one_sub_of_interval'

theorem exp_bound_div_one_sub_of_interval {x : ℝ} (h1 : 0 ≤ x) (h2 : x < 1) :
    Real.exp x ≤ 1 / (1 - x) := by
  rcases eq_or_lt_of_le h1 with (rfl | h1)
  · simp
  · exact (exp_bound_div_one_sub_of_interval' h1 h2).le
#align real.exp_bound_div_one_sub_of_interval Real.exp_bound_div_one_sub_of_interval

theorem one_sub_lt_exp_minus_of_pos {y : ℝ} (h : 0 < y) : 1 - y < Real.exp (-y) := by
  cases' le_or_lt 1 y with h' h'
  · linarith [(-y).exp_pos]
  rw [exp_neg, lt_inv _ y.exp_pos, inv_eq_one_div]
  · exact exp_bound_div_one_sub_of_interval' h h'
  · linarith
#align real.one_sub_le_exp_minus_of_pos Real.one_sub_lt_exp_minus_of_pos

theorem one_sub_le_exp_minus_of_nonneg {y : ℝ} (h : 0 ≤ y) : 1 - y ≤ Real.exp (-y) := by
  rcases eq_or_lt_of_le h with (rfl | h)
  · simp
  · exact (one_sub_lt_exp_minus_of_pos h).le
#align real.one_sub_le_exp_minus_of_nonneg Real.one_sub_le_exp_minus_of_nonneg

theorem add_one_lt_exp_of_neg {x : ℝ} (h : x < 0) : x + 1 < Real.exp x := by
  have h1 : 0 < -x := by linarith
  simpa [add_comm] using one_sub_lt_exp_minus_of_pos h1
#align real.add_one_lt_exp_of_neg Real.add_one_lt_exp_of_neg

theorem add_one_lt_exp_of_nonzero {x : ℝ} (hx : x ≠ 0) : x + 1 < Real.exp x := by
  cases' lt_or_gt_of_ne hx with h h
  · exact add_one_lt_exp_of_neg h
  exact add_one_lt_exp_of_pos h
#align real.add_one_lt_exp_of_nonzero Real.add_one_lt_exp_of_nonzero

theorem add_one_le_exp (x : ℝ) : x + 1 ≤ Real.exp x := by
  cases' le_or_lt 0 x with h h
  · exact Real.add_one_le_exp_of_nonneg h
  exact (add_one_lt_exp_of_neg h).le
#align real.add_one_le_exp Real.add_one_le_exp

theorem one_sub_div_pow_le_exp_neg {n : ℕ} {t : ℝ} (ht' : t ≤ n) : (1 - t / n) ^ n ≤ exp (-t) := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
    rwa [Nat.cast_zero] at ht'
  convert pow_le_pow_of_le_left ?_ (add_one_le_exp (-(t / n))) n using 2
  · abel
  · rw [← Real.exp_nat_mul]
    congr 1
    field_simp
    ring_nf
  · rwa [add_comm, ← sub_eq_add_neg, sub_nonneg, div_le_one]
    positivity
#align real.one_sub_div_pow_le_exp_neg Real.one_sub_div_pow_le_exp_neg

end Real

namespace Mathlib.Meta.Positivity
open Lean.Meta Qq

/-- Extension for the `positivity` tactic: `Real.exp` is always positive. -/
@[positivity Real.exp _]
def evalExp : PositivityExt where eval {_ _} _ _ e := do
  let (.app _ (a : Q(ℝ))) ← withReducible (whnf e) | throwError "not Real.exp"
  pure (.positive (q(Real.exp_pos $a) : Lean.Expr))

end Mathlib.Meta.Positivity

namespace Complex

@[simp]
theorem abs_cos_add_sin_mul_I (x : ℝ) : abs (cos x + sin x * I) = 1 := by
  have := Real.sin_sq_add_cos_sq x
  simp_all [add_comm, abs, normSq, sq, sin_ofReal_re, cos_ofReal_re, mul_re]
set_option linter.uppercaseLean3 false in
#align complex.abs_cos_add_sin_mul_I Complex.abs_cos_add_sin_mul_I

@[simp]
theorem abs_exp_ofReal (x : ℝ) : abs (exp x) = Real.exp x := by
  rw [← ofReal_exp]
  exact abs_of_nonneg (le_of_lt (Real.exp_pos _))
#align complex.abs_exp_of_real Complex.abs_exp_ofReal

@[simp]
theorem abs_exp_ofReal_mul_I (x : ℝ) : abs (exp (x * I)) = 1 := by
  rw [exp_mul_I, abs_cos_add_sin_mul_I]
set_option linter.uppercaseLean3 false in
#align complex.abs_exp_of_real_mul_I Complex.abs_exp_ofReal_mul_I

theorem abs_exp (z : ℂ) : abs (exp z) = Real.exp z.re := by
  rw [exp_eq_exp_re_mul_sin_add_cos, map_mul, abs_exp_ofReal, abs_cos_add_sin_mul_I, mul_one]
#align complex.abs_exp Complex.abs_exp

theorem abs_exp_eq_iff_re_eq {x y : ℂ} : abs (exp x) = abs (exp y) ↔ x.re = y.re := by
  rw [abs_exp, abs_exp, Real.exp_eq_exp]
#align complex.abs_exp_eq_iff_re_eq Complex.abs_exp_eq_iff_re_eq

end Complex
