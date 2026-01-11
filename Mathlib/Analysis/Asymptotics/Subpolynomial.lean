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
  along filter `l` if `f = O((1 + ‖g‖)^k)` for some natural `k`.

## Main results

* `IsSubpolynomial.const`: Constant functions are subpolynomial.
* `IsSubpolynomial.id`: The norm of the reference function is subpolynomial.
-/

open Filter Asymptotics
open scoped Topology

namespace Asymptotics

variable {α : Type*} {E : Type*} {F : Type*}
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

/-- A function `f` has subpolynomial growth with respect to `g` along filter `l`
if `f = O((1 + ‖g‖)^k)` for some natural `k`. -/
public def IsSubpolynomial (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∃ k : ℕ, IsBigO l f (fun x => (1 + ‖g x‖) ^ k)

/-- A constant function has subpolynomial growth. -/
public theorem IsSubpolynomial.const (l : Filter α) (c : E) (g : α → F) :
    IsSubpolynomial l (fun _ => c) g := by
  use 0
  simp only [pow_zero]
  exact isBigO_const_const c (by norm_num : (1 : ℝ) ≠ 0) l

/-- The function `x ↦ ‖g x‖` has subpolynomial growth with respect to `g`. -/
public theorem IsSubpolynomial.id (l : Filter α) (g : α → F) :
    IsSubpolynomial l (fun x => ‖g x‖) g := by
  use 1
  simp only [pow_one]
  apply IsBigO.of_bound 1
  filter_upwards with x
  simp only [Real.norm_eq_abs, one_mul]
  rw [abs_of_nonneg (norm_nonneg _)]
  rw [abs_of_pos (by linarith [norm_nonneg (g x)] : 0 < 1 + ‖g x‖)]
  linarith [norm_nonneg (g x)]

/-! ### Closure properties -/

/-- If `k ≤ m`, then `(1 + x)^k ≤ (1 + x)^m` for `x ≥ 0`.
This monotonicity is a key advantage of the new definition. -/
private lemma pow_mono_height {x : ℝ} (hx : 0 ≤ x) {k m : ℕ} (hkm : k ≤ m) :
    (1 + x) ^ k ≤ (1 + x) ^ m :=
  pow_le_pow_right₀ (by linarith) hkm

/-- Subpolynomial growth is closed under addition. -/
public theorem IsSubpolynomial.add {l : Filter α} {f₁ f₂ : α → E} {g : α → F}
    (hf₁ : IsSubpolynomial l f₁ g) (hf₂ : IsSubpolynomial l f₂ g) :
    IsSubpolynomial l (f₁ + f₂) g := by
  obtain ⟨k₁, hk₁⟩ := hf₁
  obtain ⟨k₂, hk₂⟩ := hf₂
  let k := max k₁ k₂
  use k
  have h1 : IsBigO l (fun x => (1 + ‖g x‖) ^ k₁) (fun x => (1 + ‖g x‖) ^ k) := by
    apply IsBigO.of_bound 1
    filter_upwards with x
    simp only [Real.norm_eq_abs, one_mul]
    rw [abs_of_pos (pow_pos (by linarith [norm_nonneg (g x)]) k₁)]
    rw [abs_of_pos (pow_pos (by linarith [norm_nonneg (g x)]) k)]
    exact pow_mono_height (norm_nonneg _) (le_max_left _ _)
  have h2 : IsBigO l (fun x => (1 + ‖g x‖) ^ k₂) (fun x => (1 + ‖g x‖) ^ k) := by
    apply IsBigO.of_bound 1
    filter_upwards with x
    simp only [Real.norm_eq_abs, one_mul]
    rw [abs_of_pos (pow_pos (by linarith [norm_nonneg (g x)]) k₂)]
    rw [abs_of_pos (pow_pos (by linarith [norm_nonneg (g x)]) k)]
    exact pow_mono_height (norm_nonneg _) (le_max_right _ _)
  exact (hk₁.trans h1).add (hk₂.trans h2)

/-- Subpolynomial growth is closed under negation. -/
public theorem IsSubpolynomial.neg {l : Filter α} {f : α → E} {g : α → F}
    (hf : IsSubpolynomial l f g) :
    IsSubpolynomial l (-f) g := by
  obtain ⟨k, hk⟩ := hf
  use k
  exact hk.neg_left

/-- Subpolynomial growth is closed under subtraction. -/
public theorem IsSubpolynomial.sub {l : Filter α} {f₁ f₂ : α → E} {g : α → F}
    (hf₁ : IsSubpolynomial l f₁ g) (hf₂ : IsSubpolynomial l f₂ g) :
    IsSubpolynomial l (f₁ - f₂) g := by
  simpa only [sub_eq_add_neg] using hf₁.add hf₂.neg

variable {R : Type*} [NormedRing R]

/-- Subpolynomial growth is closed under multiplication. -/
public theorem IsSubpolynomial.mul {l : Filter α} {f₁ f₂ : α → R} {g : α → F}
    (hf₁ : IsSubpolynomial l f₁ g) (hf₂ : IsSubpolynomial l f₂ g) :
    IsSubpolynomial l (f₁ * f₂) g := by
  obtain ⟨k₁, hk₁⟩ := hf₁
  obtain ⟨k₂, hk₂⟩ := hf₂
  use k₁ + k₂
  simp_rw [pow_add]
  exact hk₁.mul hk₂

/-- Subpolynomial growth is closed under natural powers. -/
public theorem IsSubpolynomial.pow {l : Filter α} {f : α → R} {g : α → F}
    (hf : IsSubpolynomial l f g) (n : ℕ) :
    IsSubpolynomial l (f ^ n) g := by
  induction n with
  | zero =>
    simp only [pow_zero]
    exact IsSubpolynomial.const l 1 g
  | succ n ih =>
    simp only [pow_succ]
    exact ih.mul hf

/-! ### Equivalence with the old definition -/

/-- Auxiliary lemma: `1 + x^k ≤ 2 * (1 + x)^k` for `x ≥ 0`. -/
private lemma one_add_pow_le_two_mul_add_one_pow {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    1 + x ^ k ≤ 2 * (1 + x) ^ k := by
  have h1 : 1 ≤ (1 + x) ^ k := one_le_pow₀ (by linarith)
  have h2 : x ^ k ≤ (1 + x) ^ k := pow_le_pow_left₀ hx (by linarith) k
  linarith

/-- Auxiliary lemma: `(1 + x)^k ≤ 2^k * (1 + x^k)` for `x ≥ 0`. -/
private lemma add_one_pow_le_two_pow_mul {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    (1 + x) ^ k ≤ 2 ^ k * (1 + x ^ k) := by
  rcases le_or_gt x 1 with hx1 | hx1
  · have h1 : (1 + x) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
    have h2 : 1 ≤ 1 + x ^ k := by
      have : 0 ≤ x ^ k := pow_nonneg hx k
      linarith
    calc (1 + x) ^ k ≤ 2 ^ k := h1
      _ = 2 ^ k * 1 := by rw [mul_one]
      _ ≤ 2 ^ k * (1 + x ^ k) := by
        apply mul_le_mul_of_nonneg_left h2 (pow_nonneg (by norm_num) k)
  · have h1 : 1 + x ≤ 2 * x := by linarith
    calc (1 + x) ^ k ≤ (2 * x) ^ k := pow_le_pow_left₀ (by linarith) h1 k
      _ = 2 ^ k * x ^ k := by rw [mul_pow]
      _ ≤ 2 ^ k * (1 + x ^ k) := by
        apply mul_le_mul_of_nonneg_left (by linarith [pow_nonneg hx k]) (pow_nonneg (by norm_num) k)

/-- Equivalence between `f = O((1 + ‖g‖)^k)` and `f = O(1 + ‖g‖^k)`. -/
public theorem isSubpolynomial_iff_one_add {l : Filter α} {f : α → E} {g : α → F} :
    IsSubpolynomial l f g ↔ ∃ k : ℕ, IsBigO l f (fun x => 1 + ‖g x‖ ^ k) := by
  constructor
  · intro ⟨k, hk⟩
    use k
    have hbound : IsBigO l (fun x => (1 + ‖g x‖) ^ k) (fun x => 1 + ‖g x‖ ^ k) := by
      apply IsBigO.of_bound (2 ^ k)
      filter_upwards with x
      simp only [Real.norm_eq_abs]
      rw [abs_of_pos (pow_pos (by linarith [norm_nonneg (g x)]) k)]
      rw [abs_of_pos (by linarith [pow_nonneg (norm_nonneg (g x)) k] : 0 < 1 + ‖g x‖ ^ k)]
      exact add_one_pow_le_two_pow_mul (norm_nonneg _) k
    exact hk.trans hbound
  · intro ⟨k, hk⟩
    use k
    have hbound : IsBigO l (fun x => 1 + ‖g x‖ ^ k) (fun x => (1 + ‖g x‖) ^ k) := by
      apply IsBigO.of_bound 2
      filter_upwards with x
      simp only [Real.norm_eq_abs]
      rw [abs_of_pos (by linarith [pow_nonneg (norm_nonneg (g x)) k] : 0 < 1 + ‖g x‖ ^ k)]
      rw [abs_of_pos (pow_pos (by linarith [norm_nonneg (g x)]) k)]
      exact one_add_pow_le_two_mul_add_one_pow (norm_nonneg _) k
    exact hk.trans hbound

/-- For a finite family of subpolynomial functions, one can choose a uniform degree and constant. -/
public theorem IsSubpolynomial.uniform {ι : Type*} {s : Finset ι} {l : Filter α}
    {f : ι → α → E} {g : α → F}
    (hf : ∀ i ∈ s, IsSubpolynomial l (f i) g) :
    ∃ k : ℕ, ∃ C : ℝ, ∀ i ∈ s, IsBigOWith C l (f i) (fun x => (1 + ‖g x‖) ^ k) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨0, 0, fun _ h => (Finset.notMem_empty _ h).elim⟩
  have hchoice : ∀ i ∈ s, ∃ k C, IsBigOWith C l (f i) (fun x => (1 + ‖g x‖) ^ k) := fun i hi => by
    obtain ⟨k, hk⟩ := hf i hi
    obtain ⟨c, hc⟩ := hk.isBigOWith
    exact ⟨k, c, hc⟩
  choose! k_fun C_fun hkC using hchoice
  let k := s.sup' hs k_fun
  let C := s.sup' hs (fun i => max 0 (C_fun i))
  use k, C
  intro i hi
  have hkC_i := hkC i hi
  have hk_le : k_fun i ≤ k := Finset.le_sup' k_fun hi
  have hC_le : C_fun i ≤ C :=
    (le_max_right 0 (C_fun i)).trans (Finset.le_sup' (fun j => max 0 (C_fun j)) hi)
  apply IsBigOWith.of_bound
  filter_upwards [hkC_i.bound] with x hx
  have h0C : 0 ≤ C := by
    let j := Classical.choose hs
    have hj : j ∈ s := Classical.choose_spec hs
    exact le_trans (le_max_left 0 (C_fun j)) (Finset.le_sup' (fun m => max 0 (C_fun m)) hj)
  calc ‖f i x‖
      ≤ C_fun i * ‖(1 + ‖g x‖) ^ k_fun i‖ := hx
    _ ≤ C * ‖(1 + ‖g x‖) ^ k_fun i‖ :=
        mul_le_mul_of_nonneg_right hC_le (norm_nonneg _)
    _ ≤ C * ‖(1 + ‖g x‖) ^ k‖ := by
        apply mul_le_mul_of_nonneg_left _ h0C
        simp only [Real.norm_eq_abs]
        rw [abs_of_pos (pow_pos (by linarith [norm_nonneg (g x)]) _)]
        rw [abs_of_pos (pow_pos (by linarith [norm_nonneg (g x)]) _)]
        exact pow_le_pow_right₀ (by linarith [norm_nonneg (g x)]) hk_le

end Asymptotics
