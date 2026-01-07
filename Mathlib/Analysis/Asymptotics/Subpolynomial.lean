/-
Copyright (c) 2025 Youheng Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Youheng Luo
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-!
# Subpolynomial Growth

This file defines the notion of subpolynomial growth for functions.

## Main definitions

* `Asymptotics.IsSubpolynomial`: A function `f` has subpolynomial growth with respect to `g`
  along filter `l` if `f = O(1 + ‖g‖^k)` for some natural `k`.

## Main results

* `IsSubpolynomial.add`: Subpolynomial functions are closed under addition.
* `IsSubpolynomial.mul`: Subpolynomial functions are closed under multiplication.
* `IsSubpolynomial.pow`: Subpolynomial functions are closed under powers.
* `isSubpolynomial_iff_one_add`: Equivalent characterization using `(1 + ‖g‖)^k`.
-/

open Filter Asymptotics
open scoped Topology

namespace Asymptotics

variable {α : Type*} {E : Type*} {F : Type*}
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

/-- A function `f` has subpolynomial growth with respect to `g` along filter `l`
if `f = O(1 + ‖g‖^k)` for some natural `k`. -/
public def IsSubpolynomial (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∃ k : ℕ, IsBigO l f (fun x => 1 + ‖g x‖ ^ k)

/-! ### Basic instances -/

/-- A constant function has subpolynomial growth. -/
public theorem IsSubpolynomial.const (l : Filter α) (c : E) (g : α → F) :
    IsSubpolynomial l (fun _ => c) g := by
  use 0
  simp only [pow_zero]
  exact isBigO_const_const c (by norm_num : (1 : ℝ) + 1 ≠ 0) l

/-- The function `g` has subpolynomial growth with respect to itself. -/
public theorem IsSubpolynomial.id (l : Filter α) (g : α → F) :
    IsSubpolynomial l (fun x => ‖g x‖) g := by
  use 1
  simp only [pow_one]
  apply IsBigO.of_bound 1
  filter_upwards with x
  simp only [Real.norm_eq_abs, one_mul]
  rw [abs_of_nonneg (norm_nonneg _)]
  rw [abs_of_pos (by linarith [norm_nonneg (g x)] : 0 < 1 + ‖g x‖)]
  linarith

/-! ### Closure properties -/

/-- Auxiliary: 1 + x^k ≤ 2 * (1 + x^m) when k ≤ m and x ≥ 0 -/
private lemma one_add_pow_le_two_mul {x : ℝ} (hx : 0 ≤ x) {k m : ℕ} (hkm : k ≤ m) :
    1 + x ^ k ≤ 2 * (1 + x ^ m) := by
  rcases le_or_gt 1 x with hx1 | hx1
  · -- Case x ≥ 1: then x^k ≤ x^m
    have h : x ^ k ≤ x ^ m := pow_le_pow_right₀ hx1 hkm
    linarith [pow_nonneg hx m]
  · -- Case x < 1: then x^k ≤ 1
    have h : x ^ k ≤ 1 := pow_le_one₀ hx (le_of_lt hx1)
    linarith [pow_nonneg hx m]

/-- Subpolynomial growth is preserved under addition. -/
public theorem IsSubpolynomial.add {l : Filter α} {f₁ f₂ : α → E} {g : α → F}
    (hf₁ : IsSubpolynomial l f₁ g) (hf₂ : IsSubpolynomial l f₂ g) :
    IsSubpolynomial l (f₁ + f₂) g := by
  obtain ⟨k₁, hk₁⟩ := hf₁
  obtain ⟨k₂, hk₂⟩ := hf₂
  use max k₁ k₂
  have h1 : IsBigO l (fun x => 1 + ‖g x‖ ^ k₁) (fun x => 1 + ‖g x‖ ^ (max k₁ k₂)) := by
    apply IsBigO.of_bound 2
    filter_upwards with x
    simp only [Real.norm_eq_abs]
    have pos1 : 0 < 1 + ‖g x‖ ^ k₁ := by linarith [pow_nonneg (norm_nonneg (g x)) k₁]
    have pos2 : 0 < 1 + ‖g x‖ ^ (max k₁ k₂) := by
      linarith [pow_nonneg (norm_nonneg (g x)) (max k₁ k₂)]
    rw [abs_of_pos pos1, abs_of_pos pos2]
    exact one_add_pow_le_two_mul (norm_nonneg _) (le_max_left k₁ k₂)
  have h2 : IsBigO l (fun x => 1 + ‖g x‖ ^ k₂) (fun x => 1 + ‖g x‖ ^ (max k₁ k₂)) := by
    apply IsBigO.of_bound 2
    filter_upwards with x
    simp only [Real.norm_eq_abs]
    have pos1 : 0 < 1 + ‖g x‖ ^ k₂ := by linarith [pow_nonneg (norm_nonneg (g x)) k₂]
    have pos2 : 0 < 1 + ‖g x‖ ^ (max k₁ k₂) := by
      linarith [pow_nonneg (norm_nonneg (g x)) (max k₁ k₂)]
    rw [abs_of_pos pos1, abs_of_pos pos2]
    exact one_add_pow_le_two_mul (norm_nonneg _) (le_max_right k₁ k₂)
  exact (hk₁.trans h1).add (hk₂.trans h2)

/-- Subpolynomial growth is preserved under negation. -/
public theorem IsSubpolynomial.neg {l : Filter α} {f : α → E} {g : α → F}
    (hf : IsSubpolynomial l f g) :
    IsSubpolynomial l (-f) g := by
  obtain ⟨k, hk⟩ := hf
  use k
  exact hk.neg_left

/-- Subpolynomial growth is preserved under subtraction. -/
public theorem IsSubpolynomial.sub {l : Filter α} {f₁ f₂ : α → E} {g : α → F}
    (hf₁ : IsSubpolynomial l f₁ g) (hf₂ : IsSubpolynomial l f₂ g) :
    IsSubpolynomial l (f₁ - f₂) g := by
  simpa only [sub_eq_add_neg] using hf₁.add hf₂.neg

variable {R : Type*} [NormedRing R]

/-- Auxiliary: (1 + x^k₁) * (1 + x^k₂) ≤ 4 * (1 + x^(k₁+k₂)) for x ≥ 0 -/
private lemma one_add_pow_mul_le {x : ℝ} (hx : 0 ≤ x) (k₁ k₂ : ℕ) :
    (1 + x ^ k₁) * (1 + x ^ k₂) ≤ 4 * (1 + x ^ (k₁ + k₂)) := by
  rcases le_or_gt 1 x with hx1 | hx1
  · -- Case x ≥ 1
    have h1 : (1 : ℝ) ≤ x ^ (k₁ + k₂) := by
      simpa using pow_le_pow_right₀ hx1 (Nat.zero_le _)
    have h2 : x ^ k₁ ≤ x ^ (k₁ + k₂) := by
      apply pow_le_pow_right₀ hx1
      omega
    have h3 : x ^ k₂ ≤ x ^ (k₁ + k₂) := by
      apply pow_le_pow_right₀ hx1
      omega
    calc (1 + x ^ k₁) * (1 + x ^ k₂)
        = 1 + x ^ k₁ + x ^ k₂ + x ^ k₁ * x ^ k₂ := by ring
      _ = 1 + x ^ k₁ + x ^ k₂ + x ^ (k₁ + k₂) := by rw [← pow_add]
      _ ≤ x ^ (k₁ + k₂) + x ^ (k₁ + k₂) + x ^ (k₁ + k₂) + x ^ (k₁ + k₂) := by linarith
      _ = 4 * x ^ (k₁ + k₂) := by ring
      _ ≤ 4 * (1 + x ^ (k₁ + k₂)) := by linarith [pow_nonneg hx (k₁ + k₂)]
  · -- Case x < 1
    have h1 : x ^ k₁ ≤ 1 := pow_le_one₀ hx (le_of_lt hx1)
    have h2 : x ^ k₂ ≤ 1 := pow_le_one₀ hx (le_of_lt hx1)
    have h3 : x ^ (k₁ + k₂) ≤ 1 := pow_le_one₀ hx (le_of_lt hx1)
    calc (1 + x ^ k₁) * (1 + x ^ k₂)
        ≤ (1 + 1) * (1 + 1) := by nlinarith [pow_nonneg hx k₁, pow_nonneg hx k₂]
      _ = 4 := by norm_num
      _ ≤ 4 * (1 + x ^ (k₁ + k₂)) := by linarith [pow_nonneg hx (k₁ + k₂)]

/-- Subpolynomial growth is preserved under multiplication. -/
public theorem IsSubpolynomial.mul {l : Filter α} {f₁ f₂ : α → R} {g : α → F}
    (hf₁ : IsSubpolynomial l f₁ g) (hf₂ : IsSubpolynomial l f₂ g) :
    IsSubpolynomial l (f₁ * f₂) g := by
  obtain ⟨k₁, hk₁⟩ := hf₁
  obtain ⟨k₂, hk₂⟩ := hf₂
  use k₁ + k₂
  have hmul := hk₁.mul hk₂
  have hbound : IsBigO l (fun x => (1 + ‖g x‖ ^ k₁) * (1 + ‖g x‖ ^ k₂))
      (fun x => 1 + ‖g x‖ ^ (k₁ + k₂)) := by
    apply IsBigO.of_bound 4
    filter_upwards with x
    simp only [Real.norm_eq_abs]
    have pos1 : 0 < (1 + ‖g x‖ ^ k₁) * (1 + ‖g x‖ ^ k₂) := by
      apply mul_pos <;> linarith [pow_nonneg (norm_nonneg (g x)) k₁,
        pow_nonneg (norm_nonneg (g x)) k₂]
    have pos2 : 0 < 1 + ‖g x‖ ^ (k₁ + k₂) := by
      linarith [pow_nonneg (norm_nonneg (g x)) (k₁ + k₂)]
    rw [abs_of_pos pos1, abs_of_pos pos2]
    exact one_add_pow_mul_le (norm_nonneg _) k₁ k₂
  exact hmul.trans hbound

/-- Subpolynomial growth is preserved under natural powers. -/
public theorem IsSubpolynomial.pow {l : Filter α} {f : α → R} {g : α → F}
    (hf : IsSubpolynomial l f g) (n : ℕ) :
    IsSubpolynomial l (f ^ n) g := by
  induction n with
  | zero => simp only [pow_zero]; exact IsSubpolynomial.const l 1 g
  | succ n ih => simp only [pow_succ]; exact ih.mul hf

/-! ### Equivalent characterizations -/

/-- Auxiliary: 1 + x^k ≤ 2 * (1 + x)^k for x ≥ 0 -/
private lemma one_add_pow_le_two_mul_add_one_pow {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    1 + x ^ k ≤ 2 * (1 + x) ^ k := by
  have h1x : 1 ≤ 1 + x := by linarith
  have h1 : 1 ≤ (1 + x) ^ k := by
    simpa using pow_le_pow_right₀ h1x (Nat.zero_le k)
  have h2 : x ^ k ≤ (1 + x) ^ k := by
    apply pow_le_pow_left₀ hx
    linarith
  linarith

/-- Auxiliary: (1 + x)^k ≤ 2^k * (1 + x^k) for x ≥ 0 -/
private lemma add_one_pow_le_two_pow_mul {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    (1 + x) ^ k ≤ 2 ^ k * (1 + x ^ k) := by
  rcases le_or_gt x 1 with hx1 | hx1
  · -- Case x ≤ 1: then 1 + x ≤ 2
    have h1 : 1 + x ≤ 2 := by linarith
    have h2 : (1 + x) ^ k ≤ 2 ^ k := by
      apply pow_le_pow_left₀ (by linarith) h1
    have h3 : (0 : ℝ) ≤ 2 ^ k := pow_nonneg (by norm_num) k
    have h4 : (0 : ℝ) ≤ x ^ k := pow_nonneg hx k
    calc (1 + x) ^ k
        ≤ 2 ^ k := h2
      _ = 2 ^ k * 1 := by ring
      _ ≤ 2 ^ k * (1 + x ^ k) := by nlinarith
  · -- Case x > 1: then 1 + x ≤ 2 * x
    have h1 : 1 + x ≤ 2 * x := by linarith
    have h2 : (1 + x) ^ k ≤ (2 * x) ^ k := by
      apply pow_le_pow_left₀ (by linarith) h1
    have h3 : (2 * x) ^ k = 2 ^ k * x ^ k := by ring
    calc (1 + x) ^ k
        ≤ 2 ^ k * x ^ k := by rw [← h3]; exact h2
      _ ≤ 2 ^ k * (1 + x ^ k) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k)
          linarith [pow_nonneg hx k]

/-- Equivalent characterization: using `(1 + ‖g‖)^k` instead of `1 + ‖g‖^k`. -/
public theorem isSubpolynomial_iff_one_add {l : Filter α} {f : α → E} {g : α → F} :
    IsSubpolynomial l f g ↔ ∃ k : ℕ, IsBigO l f (fun x => (1 + ‖g x‖) ^ k) := by
  constructor
  · intro ⟨k, hk⟩
    use k
    have hbound : IsBigO l (fun x => 1 + ‖g x‖ ^ k) (fun x => (1 + ‖g x‖) ^ k) := by
      apply IsBigO.of_bound 2
      filter_upwards with x
      simp only [Real.norm_eq_abs]
      have pos1 : 0 < 1 + ‖g x‖ ^ k := by linarith [pow_nonneg (norm_nonneg (g x)) k]
      have pos2 : 0 < (1 + ‖g x‖) ^ k := pow_pos (by linarith [norm_nonneg (g x)]) k
      rw [abs_of_pos pos1, abs_of_pos pos2]
      exact one_add_pow_le_two_mul_add_one_pow (norm_nonneg _) k
    exact hk.trans hbound
  · intro ⟨k, hk⟩
    use k
    have hbound : IsBigO l (fun x => (1 + ‖g x‖) ^ k) (fun x => 1 + ‖g x‖ ^ k) := by
      apply IsBigO.of_bound (2 ^ k)
      filter_upwards with x
      simp only [Real.norm_eq_abs]
      have pos1 : 0 < (1 + ‖g x‖) ^ k := pow_pos (by linarith [norm_nonneg (g x)]) k
      have pos2 : 0 < 1 + ‖g x‖ ^ k := by linarith [pow_nonneg (norm_nonneg (g x)) k]
      rw [abs_of_pos pos1, abs_of_pos pos2]
      exact add_one_pow_le_two_pow_mul (norm_nonneg _) k
    exact hk.trans hbound

/-! ### Uniformity -/

/-- For a finite set of subpolynomial functions, the constants can be chosen uniformly. -/
public theorem IsSubpolynomial.uniform {ι : Type*} {s : Finset ι} {l : Filter α}
    {f : ι → α → E} {g : α → F}
    (hf : ∀ i ∈ s, IsSubpolynomial l (f i) g) :
    ∃ k : ℕ, ∃ C : ℝ, ∀ i ∈ s, IsBigOWith C l (f i) (fun x => 1 + ‖g x‖ ^ k) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨0, 0, fun _ h => (Finset.notMem_empty _ h).elim⟩
  have hchoice : ∀ i ∈ s, ∃ k C, IsBigOWith C l (f i) (fun x => 1 + ‖g x‖ ^ k) := fun i hi => by
    obtain ⟨k, hk⟩ := hf i hi
    obtain ⟨c, hc⟩ := hk.isBigOWith
    exact ⟨k, c, hc⟩
  choose! k_fun C_fun hkC using hchoice
  let k := s.sup' hs k_fun
  use k
  use 2 * s.sup' hs (fun i => |C_fun i|)
  intro i hi
  have hkC_i := hkC i hi
  have hk_le : k_fun i ≤ k := Finset.le_sup' k_fun hi
  have hC_le : |C_fun i| ≤ s.sup' hs (fun j => |C_fun j|) := Finset.le_sup' (fun j => |C_fun j|) hi
  apply IsBigOWith.of_bound
  filter_upwards [hkC_i.bound] with x hx
  have hC_abs : C_fun i ≤ |C_fun i| := le_abs_self _
  calc ‖f i x‖
      ≤ C_fun i * ‖1 + ‖g x‖ ^ k_fun i‖ := hx
    _ ≤ |C_fun i| * ‖1 + ‖g x‖ ^ k_fun i‖ := by
        apply mul_le_mul_of_nonneg_right hC_abs (norm_nonneg _)
    _ ≤ |C_fun i| * (2 * ‖1 + ‖g x‖ ^ k‖) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        simp only [Real.norm_eq_abs]
        have pos1 : 0 < 1 + ‖g x‖ ^ k_fun i := by
          linarith [pow_nonneg (norm_nonneg (g x)) (k_fun i)]
        have pos2 : 0 < 1 + ‖g x‖ ^ k := by
          linarith [pow_nonneg (norm_nonneg (g x)) k]
        rw [abs_of_pos pos1, abs_of_pos pos2]
        exact one_add_pow_le_two_mul (norm_nonneg _) hk_le
    _ = 2 * |C_fun i| * ‖1 + ‖g x‖ ^ k‖ := by ring
    _ ≤ 2 * s.sup' hs (fun j => |C_fun j|) * ‖1 + ‖g x‖ ^ k‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        linarith
end Asymptotics
