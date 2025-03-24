/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.NumberTheory.SelbergSieve.Basic

/-!
# The Selberg Sieve

This file proves `selberg_bound_simple`, the fundamental theorem of the Selberg sieve.
-/

noncomputable section

open scoped BigOperators Classical SelbergSieve.Notation

open Finset Real Nat ArithmeticFunction

namespace SelbergSieve

variable [s : SelbergSieve]

@[simp]
def selbergBoundingSum : ℝ :=
  ∑ l ∈ divisors P, if l ^ 2 ≤ y then g l else 0

scoped [SelbergSieve.Notation] notation3 "S" => selbergBoundingSum

lemma selbergBoundingSum_def :
  S = ∑ l ∈ divisors P, if l ^ 2 ≤ y then g l else 0 := rfl

theorem selbergBoundingSum_pos :
    0 < S := by
  dsimp only [selbergBoundingSum]
  rw [← sum_filter]
  apply sum_pos;
  · intro l hl
    rw [mem_filter, mem_divisors] at hl
    · apply s.selbergTerms_pos _ (hl.1.1)
  · simp_rw [Finset.Nonempty, mem_filter]; use 1
    constructor
    · apply one_mem_divisors.mpr s.prodPrimes_ne_zero
    rw [cast_one, one_pow]
    exact s.one_le_level

theorem selbergBoundingSum_ne_zero : S ≠ 0 := by
  apply _root_.ne_of_gt
  exact s.selbergBoundingSum_pos

theorem selbergBoundingSum_nonneg : 0 ≤ S := _root_.le_of_lt s.selbergBoundingSum_pos

def selbergWeights : ℕ → ℝ := fun d =>
  if d ∣ P then
    (ν d)⁻¹ * g d * μ d * S⁻¹ *
      ∑ m ∈ divisors P, if (d * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
  else 0

-- This notation traditionally uses λ, which is unavailable in lean
scoped [SelbergSieve.Notation] notation3 "γ" => SelbergSieve.selbergWeights

theorem selbergWeights_eq_zero_of_not_dvd {d : ℕ} (hd : ¬ d ∣ P) :
    γ d = 0 := by
  rw [selbergWeights, if_neg hd]

theorem selbergWeights_eq_zero (d : ℕ) (hd : ¬d ^ 2 ≤ y) :
    γ d = 0 := by
  dsimp only [selbergWeights]
  split_ifs with h
  · rw [mul_eq_zero_of_right _]
    apply Finset.sum_eq_zero
    refine fun m hm => if_neg ?_
    intro hyp
    have : (d^2:ℝ) ≤ (d*m)^2 := by
      norm_cast;
      refine Nat.pow_le_pow_of_le_left ?h 2
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_mem_divisors hm)
    linarith [hyp.1]
  · rfl

theorem selbergWeights_mul_mu_nonneg (d : ℕ) (hdP : d ∣ P) :
    0 ≤ γ d * μ d := by
  dsimp only [selbergWeights]
  rw [if_pos hdP, mul_assoc]
  trans ((μ d :ℝ)^2 * (ν d)⁻¹ * g d * S⁻¹ * ∑ m ∈ divisors P,
          if (d * m) ^ 2 ≤ y ∧ Coprime m d then g m else 0)
  · apply mul_nonneg;
    · have := s.selbergBoundingSum_nonneg
      have := s.nu_pos_of_dvd_prodPrimes hdP
      have := s.selbergTerms_pos d hdP
      positivity
    apply sum_nonneg;
    intro m hm
    split_ifs with h
    · exact le_of_lt <| s.selbergTerms_pos m (dvd_of_mem_divisors hm)
    · rfl
  · apply le_of_eq; ring

omit s in
theorem divisors_image_mul (n d : ℕ) (hd : d ≠ 0) :
    n.divisors.image (d * ·) = (d*n).divisors.filter (fun k ↦ d ∣ k) := by
  ext r
  simp only [mem_image, mem_divisors, ne_eq, mem_filter, _root_.mul_eq_zero, not_or]
  constructor
  · rintro ⟨x, ⟨hx, hn⟩, rfl⟩
    refine ⟨⟨Nat.mul_dvd_mul_left d hx, hd, hn⟩, d.dvd_mul_right x⟩
  · rintro ⟨⟨hrdn, hd, hn⟩, hdr⟩
    exact ⟨r/d, ⟨(div_dvd_iff_dvd_mul hdr hd).mpr hrdn, hn⟩, Nat.mul_div_cancel' hdr⟩

omit s in
lemma sum_mul_subst (k n: ℕ) {f : ℕ → ℝ} (h : ∀ l, l ∣ n → ¬ k ∣ l → f l = 0) :
      ∑ l ∈ n.divisors, f l
    = ∑ m ∈ n.divisors, if k*m ∣ n then f (k*m) else 0 := by
  by_cases hn : n = 0
  · simp [hn]
  by_cases hk : k = 0
  · simp [hk, hn] at h ⊢
    apply sum_eq_zero
    simp +contextual [mem_divisors, ne_eq, and_imp, ne_zero_of_dvd_ne_zero hn, h]
  trans ∑ l ∈ image (fun x ↦ k * x) n.divisors, if l ∣ n then f l else 0
  · rw [divisors_image_mul _ _ hk, ← sum_filter, filter_comm, divisors_filter_dvd_of_dvd, eq_comm]
    · apply sum_subset
      · exact filter_subset (fun k_1 ↦ k ∣ k_1) n.divisors
      · simp only [mem_divisors, ne_eq, mem_filter, not_and, and_imp]
        intro l hl hn h'
        apply h l hl (h' hl hn)
    · positivity
    · exact Nat.dvd_mul_left n k
  · rw [sum_image]
    intro _ _ _ _ h;
    exact (Nat.mul_right_inj hk).mp h

theorem tmp (d : ℕ) (hd : d ∣ P) :
    ∑ l ∈ divisors P, (if d ∣ l ∧ ↑l ^ 2 ≤ y then g l else 0)
    = g d * ∑ m ∈ divisors P, if (↑d * ↑m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0 := by
  rw [sum_mul_subst d P (by simp +contextual)]
  simp_rw [← sum_filter, mul_sum]
  apply sum_congr _
  · intro m
    simp only [mem_filter, mem_divisors, ne_eq, and_imp]
    intro x _ _ h
    refine selbergTerms_mult.map_mul_of_coprime h.symm
  · ext m
    simp only [dvd_mul_right, cast_mul, true_and, mem_filter, mem_divisors, ne_eq, and_assoc,
      and_congr_right_iff]
    rw [and_comm, and_congr_right_iff]
    intro hmP hP _
    constructor
    · intro h
      apply Coprime.symm <| coprime_of_squarefree_mul _
      apply prodPrimes_squarefree.squarefree_of_dvd h
    · intro h
      refine Coprime.mul_dvd_of_dvd_of_dvd h.symm hd hmP

-- Important facts about the selberg weights
theorem selbergWeights_eq_dvds_sum (d : ℕ) :
    ν d * γ d =
      S⁻¹ * μ d *
        ∑ l ∈ divisors P, if d ∣ l ∧ l ^ 2 ≤ y then g l else 0 := by
  by_cases h_dvd : d ∣ P
  swap
  · dsimp only [selbergWeights]; rw [if_neg h_dvd]
    rw [sum_eq_zero]
    · ring
    intro l hl; rw [mem_divisors] at hl
    rw [if_neg]; push_neg; intro h
    exfalso; exact h_dvd (dvd_trans h hl.left)
  dsimp only [selbergWeights]
  rw [if_pos h_dvd]
  repeat rw [mul_sum]
  apply symm
  simp_rw [← mul_sum, tmp _ h_dvd, ← mul_assoc, ]
  rw [mul_inv_cancel₀ (nu_ne_zero h_dvd)]
  ring

omit s in
private theorem moebius_inv_dvd_lower_bound (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then μ d else 0) = if l = m then μ l else 0 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero <| Squarefree.ne_zero hm
  revert hm
  revert m
  apply (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on {n | Squarefree n}
    (fun _ _ => Squarefree.squarefree_of_dvd)).mpr
  intro m hm_pos hm
  rw [sum_divisorsAntidiagonal' (f:= fun r s => μ r • if l=s then μ l else 0)]
  by_cases hl : l ∣ m
  · rw [if_pos hl, sum_eq_single l]
    · have hmul : m / l * l = m := Nat.div_mul_cancel hl
      rw [if_pos rfl, smul_eq_mul, ←isMultiplicative_moebius.map_mul_of_coprime,
        hmul]
      apply coprime_of_squarefree_mul; rw [hmul]; exact hm
    · intro d _ hdl; rw[if_neg hdl.symm, smul_zero]
    · intro h; rw[mem_divisors] at h; exfalso; exact h ⟨hl, (Nat.ne_of_lt hm_pos).symm⟩
  · rw [if_neg hl, sum_eq_zero]; intro d hd
    rw [if_neg, smul_zero]
    by_contra h; rw [←h] at hd; exact hl (dvd_of_mem_divisors hd)

theorem selbergWeights_diagonalisation (l : ℕ) (hl : l ∈ divisors P) :
    (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) =
      if l ^ 2 ≤ y then g l * μ l * S⁻¹ else 0 := by
  calc
    (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) =
      ∑ k ∈ divisors P, if k ^ 2 ≤ y then
            (∑ d ∈ divisors P, if d ∣ k ∧ l ∣ d then (μ d:ℝ) else 0) * g k * S⁻¹
          else 0 := by
      simp_rw [selbergWeights_eq_dvds_sum, ← sum_filter, mul_sum, sum_mul, sum_filter, ite_sum_zero,
        ← ite_and]
      rw [sum_comm]
      congr with d
      simp_rw [← sum_filter]
      apply sum_congr
      · ext x; simp only [mem_filter, mem_divisors, ne_eq, and_congr_right_iff, and_imp]; tauto
      intros; ring
    _ = ∑ x ∈ divisors P, if x = l then if ↑l ^ 2 ≤ y then g l * ↑(μ l) * S⁻¹ else 0 else 0 := by
      apply sum_congr rfl; intro k hk
      norm_cast
      simp_rw [ite_and, ← sum_filter,
        Nat.divisors_filter_dvd_of_dvd prodPrimes_ne_zero (Nat.dvd_of_mem_divisors hk), sum_filter]
      rw [moebius_inv_dvd_lower_bound _ _ (squarefree_of_mem_divisors_prodPrimes hk)]
      push_cast
      rw [← ite_and, ite_zero_mul, ite_zero_mul, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · rw [and_comm, eq_comm]
        refine and_congr_right (fun heq ↦ ?_)
        rw [heq]
      intro h; rw[h.1]; ring
    _ = if l ^ 2 ≤ y then g l * μ l * S⁻¹ else 0 := by
      rw [sum_ite_eq_of_mem' _ _ _ hl]

def selbergMuPlus : ℕ → ℝ :=
  lambdaSquared γ

scoped [SelbergSieve.Notation] notation3 "μ⁺" => SelbergSieve.selbergMuPlus

theorem weight_one_of_selberg : γ 1 = 1 := by
  dsimp only [selbergWeights]
  rw [if_pos (one_dvd P), s.nu_mult.left, selbergTerms_mult.left]
  simp only [inv_one, mul_one, isUnit_one, IsUnit.squarefree, moebius_apply_of_squarefree,
    cardFactors_one, _root_.pow_zero, Int.cast_one, selbergBoundingSum, cast_pow, one_mul,
    coprime_one_right_eq_true, and_true, cast_one]
  rw [inv_mul_cancel₀]
  convert s.selbergBoundingSum_ne_zero

theorem selbergMuPlus_eq_zero (d : ℕ) (hd : ¬d ≤ y) : μ⁺ d = 0 :=
  by
  apply lambdaSquared_eq_zero_of_not_le_height _ y _ d hd
  apply selbergWeights_eq_zero

def upperMoebius_selbergMuPlus : UpperMoebius selbergMuPlus :=
  upperMoebius_lambdaSquared γ (s.weight_one_of_selberg)

theorem mainSum_eq_diag_quad_form :
    s.mainSum μ⁺ =
      ∑ l ∈ divisors P,
        1 / g l *
          (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) ^ 2 :=
  lambdaSquared_mainSum_eq_diag_quad_form ..

theorem selberg_bound_simple_mainSum :
    s.mainSum μ⁺ = S⁻¹ :=
  by
  trans (∑ l ∈ divisors P, (if l ^ 2 ≤ y then g l *  (S⁻¹) ^ 2 else 0))
  · rw [mainSum_eq_diag_quad_form]
    apply sum_congr rfl; intro l hl
    rw [s.selbergWeights_diagonalisation l hl, ite_pow, zero_pow, mul_ite_zero]
    · congr 1
      trans (1/g l * g l * g l * (μ l:ℝ)^2  * (S⁻¹) ^ 2)
      · ring
      rw_mod_cast [moebius_sq_eq_one_of_squarefree <| s.squarefree_of_mem_divisors_prodPrimes hl,
        one_div_mul_cancel <| _root_.ne_of_gt <| s.selbergTerms_pos l <| dvd_of_mem_divisors hl]
      ring
    linarith
  rw [← sum_filter, ← sum_mul, sum_filter, ←selbergBoundingSum_def, sq, ←mul_assoc,
    mul_inv_cancel₀ (_root_.ne_of_gt s.selbergBoundingSum_pos), one_mul]

omit s in
lemma eq_gcd_mul_of_dvd_of_coprime {k d m :ℕ} (hkd : k ∣ d) (hmd : Coprime m d) (hk : k ≠ 0) :
    k = d.gcd (k*m) := by
  cases' hkd with r hr
  have hrdvd : r ∣ d := by use k; rw [mul_comm]; exact hr
  apply symm; rw [hr, Nat.gcd_mul_left, mul_eq_left₀ hk, Nat.gcd_comm]
  apply Coprime.coprime_dvd_right hrdvd hmd

private lemma _helper {k m d :ℕ} (hkd : k ∣ d) (hk: k ∈ divisors P) (hm: m ∈ divisors P):
    k * m ∣ P ∧ k = Nat.gcd d (k * m) ∧ (k * m) ^ 2 ≤ y ↔
    (k * m) ^ 2 ≤ y ∧ Coprime m d := by
  constructor
  · intro h
    constructor
    · exact h.2.2
    · cases' hkd with r hr
      rw [hr, Nat.gcd_mul_left, eq_comm, mul_eq_left₀ (by rintro rfl; simp at hk ⊢)] at h
      rw [hr, coprime_comm]
      apply Coprime.mul
      · apply coprime_of_squarefree_mul <|
          Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree
      exact h.2.1
  · intro h
    constructor
    · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · rw [coprime_comm]
        exact Coprime.coprime_dvd_right hkd h.2
      · exact dvd_of_mem_divisors hk
      exact dvd_of_mem_divisors hm
    constructor
    · exact eq_gcd_mul_of_dvd_of_coprime hkd h.2 (by rintro rfl; simp at hk ⊢)
    · exact h.1

theorem selbergBoundingSum_ge {d : ℕ} (hdP : d ∣ P) :
    S ≥ γ d * ↑(μ d) * S := by
  calc
  _ = (∑ k ∈ divisors P, ∑ l ∈ divisors P, if k = d.gcd l ∧ l ^ 2 ≤ y then g l else 0) := by
    dsimp only [selbergBoundingSum]
    rw [sum_comm, sum_congr rfl]; intro l _
    simp_rw [ite_and]
    rw [sum_ite_eq_of_mem']
    · rw [mem_divisors]
      exact ⟨(Nat.gcd_dvd_left d l).trans (hdP), s.prodPrimes_ne_zero⟩
  _ = (∑ k ∈ divisors P,
          if k ∣ d then
            g k * ∑ m ∈ divisors P, if (k * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
          else 0) := by
    apply sum_congr rfl; intro k hk
    rw [mul_sum]
    split_ifs with hkd
    swap
    · rw [sum_eq_zero]; intro l _
      rw [if_neg]
      push_neg; intro h; exfalso
      rw [h] at hkd
      exact hkd <| Nat.gcd_dvd_left d l
    rw [sum_mul_subst k P, sum_congr rfl]
    · intro m hm
      rw [mul_ite_zero, ← ite_and]
      · apply if_ctx_congr _ _ fun _ => rfl
        · exact_mod_cast s._helper hkd hk hm
        · intro h;
          apply selbergTerms_mult.2
          rw [coprime_comm]; apply h.2.coprime_dvd_right hkd
    · intro l _ hkl; apply if_neg
      push_neg; intro h; exfalso
      rw [h] at hkl; exact hkl (Nat.gcd_dvd_right d l)
  _ ≥ (∑ k ∈ divisors P, if k ∣ d
          then g k * ∑ m ∈ divisors P, if (d * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
          else 0 ) := by
    apply sum_le_sum; intro k _
    split_ifs with hkd
    swap
    · rfl
    gcongr with m hm
    · exact (le_of_lt <| s.selbergTerms_pos k <| Trans.trans hkd hdP)
    · split_ifs with h h'
      · rfl
      · exfalso; apply h'
        refine ⟨le_trans ?_ h.1, h.2⟩
        gcongr
        refine Nat.le_of_dvd
          (Nat.pos_of_ne_zero <| ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hdP) hkd
      · refine le_of_lt <| s.selbergTerms_pos m <| dvd_of_mem_divisors hm
      · rfl
  _ = _ := by
    simp_rw [← ite_zero_mul, ←sum_mul, s.conv_selbergTerms_eq_selbergTerms_mul_nu hdP]
    trans (S * S⁻¹ * (μ d:ℝ)^2 * (ν d)⁻¹ * g d *
      (∑ m ∈ divisors P, if (d*m) ^ 2 ≤ y ∧ Coprime m d then g m else 0))
    · rw [mul_inv_cancel₀, ←Int.cast_pow, moebius_sq_eq_one_of_squarefree]
      · ring
      · exact Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
      · exact _root_.ne_of_gt <| s.selbergBoundingSum_pos
    dsimp only [selbergWeights]; rw [if_pos hdP]
    ring

theorem selberg_bound_weights (d : ℕ) : |γ d| ≤ 1 := by
  by_cases hdP : d ∣ P
  swap
  · rw [s.selbergWeights_eq_zero_of_not_dvd hdP]; simp only [zero_le_one, abs_zero]
  have : 1*S ≥ γ d * ↑(μ d) * S := by
    rw[one_mul]
    exact s.selbergBoundingSum_ge hdP
  replace this : γ d * μ d ≤ 1 := by
    apply le_of_mul_le_mul_of_pos_right this (s.selbergBoundingSum_pos)
  convert this using 1
  rw [← abs_of_nonneg <| s.selbergWeights_mul_mu_nonneg d hdP,
    abs_mul, ←Int.cast_abs, abs_moebius_eq_one_of_squarefree <|
    (s.prodPrimes_squarefree.squarefree_of_dvd hdP), Int.cast_one, mul_one]


theorem selberg_bound_muPlus (n : ℕ) (hn : n ∈ divisors P) :
    |μ⁺ n| ≤ (3:ℝ) ^ ω n := by
  let f : ℕ → ℕ → ℝ := fun x z : ℕ => if n = x.lcm z then 1 else 0
  dsimp only [selbergMuPlus, lambdaSquared]
  calc
    |∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, if n = d1.lcm d2 then γ d1 * γ d2 else 0| ≤
        ∑ d1 ∈ n.divisors, |∑ d2 ∈ n.divisors, if n = d1.lcm d2 then γ d1 * γ d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, |if n = d1.lcm d2 then γ d1 * γ d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, f d1 d2 := ?_
    _ = (n.divisors ×ˢ n.divisors).sum fun p => f p.fst p.snd := ?_
    _ = Finset.card ((n.divisors ×ˢ n.divisors).filter fun p : ℕ × ℕ => n = p.fst.lcm p.snd) := ?_
    _ = (3:ℕ) ^ ω n := ?_
    _ = (3:ℝ) ^ ω n := ?_
  · apply abs_sum_le_sum_abs
  · gcongr; apply abs_sum_le_sum_abs
  · gcongr with d1 _ d2
    rw [apply_ite abs, abs_zero, abs_mul]
    simp only [f]
    by_cases h : n = d1.lcm d2
    · rw [if_pos h, if_pos h]
      apply mul_le_one₀ (s.selberg_bound_weights d1) (abs_nonneg <| γ d2)
        (s.selberg_bound_weights d2)
    · rw [if_neg h, if_neg h]
  · rw [← Finset.sum_product']
  · dsimp only
    rw [← sum_filter, Finset.sum_const, smul_one_eq_cast]
  · norm_cast
    simp [← card_pair_lcm_eq (s.squarefree_of_mem_divisors_prodPrimes hn), eq_comm]
  norm_num

theorem selberg_bound_simple_errSum :
    s.errSum μ⁺ ≤
      ∑ d ∈ divisors P, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |R d| else 0 := by
  dsimp only [errSum]
  gcongr with d hd
  split_ifs with h
  · apply mul_le_mul _ le_rfl (abs_nonneg <| R d) (pow_nonneg _ <| ω d)
    · exact s.selberg_bound_muPlus d hd
    linarith
  · rw [s.selbergMuPlus_eq_zero d h, abs_zero, zero_mul]

omit s in
theorem selberg_bound (s : SelbergSieve) :
    s.siftedSum ≤
      X / S +
        ∑ d ∈ divisors P, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |R d| else 0 := by
  let mu_plus := selbergMuPlus
  calc
    s.siftedSum ≤ X * s.mainSum μ⁺ + s.errSum μ⁺ :=
      s.siftedSum_le_mainSum_errSum_of_upperMoebius mu_plus upperMoebius_selbergMuPlus
    _ ≤ _ := ?_
  gcongr
  · rw [s.selberg_bound_simple_mainSum, div_eq_mul_inv]
  · apply s.selberg_bound_simple_errSum

end SelbergSieve
