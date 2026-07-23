/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Subpolynomial Asymptotics

This file defines a predicate `Asymptotics.IsSubpolynomial l f g` for a function `f`
that is bounded by a polynomial in `g` asymptotically along a filter `l`.

## Main definition

* `IsSubpolynomial l f g` means there exists `k : ℕ` such that `f =O[l] fun x => 1 + ‖g x‖ ^ k`.

## Main statements

* `IsSubpolynomial.const`: Constant functions are subpolynomial.
* `IsSubpolynomial.add`: Sum of two subpolynomial functions is subpolynomial.
* `IsSubpolynomial.mul`: Product of two subpolynomial functions is subpolynomial.
* `IsSubpolynomial.pow`: A natural number power of a subpolynomial function is subpolynomial.
-/

@[expose] public section

namespace Asymptotics

variable {α : Type*} {E F : Type*}

section Defs
variable [Norm E] [Norm F]

/-- `f` is subpolynomial in `g` along `l` if there exists `k : ℕ` such that
  `f =O[l] fun x => 1 + ‖g x‖ ^ k`. -/
def IsSubpolynomial (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∃ (k : ℕ), f =O[l] fun x : α => (1 : ℝ) + ‖g x‖ ^ k

theorem IsSubpolynomial.def {l : Filter α} {f : α → E} {g : α → F}
    (h : IsSubpolynomial l f g) :
    ∃ (k : ℕ), f =O[l] fun x : α => (1 : ℝ) + ‖g x‖ ^ k :=
  h

theorem isSubpolynomial_iff {l : Filter α} {f : α → E} {g : α → F} :
    IsSubpolynomial l f g ↔ ∃ (k : ℕ), f =O[l] fun x : α => (1 : ℝ) + ‖g x‖ ^ k :=
  Iff.rfl

end Defs

section Basic
variable [Norm E] [Norm F]

/-- Constant functions are subpolynomial. -/
theorem IsSubpolynomial.const {l : Filter α} {g : α → F} (c : E) :
    IsSubpolynomial l (fun _ : α => c) g := by
  refine ⟨0, ?_⟩
  have h₁ : (fun (_ : α) => c) =O[l] fun (_ : α) => (2 : ℝ) := by
    exact isBigO_const_const c (show (2 : ℝ) ≠ 0 by norm_num) l
  convert h₁ using 1
  ext x
  norm_num

end Basic

section Helper
variable [SeminormedAddCommGroup F]

lemma one_plus_pow_le_two_mul_one_plus_pow (r : ℝ) (hr : 0 ≤ r) (k₁ k : ℕ) (h : k₁ ≤ k) :
    ‖((1 : ℝ) + r ^ k₁)‖ ≤ (2 : ℝ) * ‖((1 : ℝ) + r ^ k)‖ := by
  have h₃ : 0 ≤ (1 : ℝ) + r ^ k₁ := by positivity
  have h₄ : 0 ≤ (1 : ℝ) + r ^ k := by positivity
  have h₅ : ‖((1 : ℝ) + r ^ k₁)‖ = (1 : ℝ) + r ^ k₁ := by
    rw [Real.norm_eq_abs, abs_of_nonneg h₃]
  have h₆ : ‖((1 : ℝ) + r ^ k)‖ = (1 : ℝ) + r ^ k := by
    rw [Real.norm_eq_abs, abs_of_nonneg h₄]
  rw [h₅, h₆]
  by_cases h₁ : r ≤ 1
  · -- Case r ≤ 1
    have h₂ : r ^ k₁ ≤ 1 := by
      have h₃ : ∀ n : ℕ, r ^ n ≤ 1 := fun n => by
        induction n with
        | zero => norm_num
        | succ n ih =>
          calc
            r ^ (n + 1) = r ^ n * r := by ring
            _ ≤ 1 * r := by gcongr
            _ ≤ 1 * 1 := by gcongr
            _ = 1 := by ring
      exact h₃ k₁
    have h₃ : (1 : ℝ) + r ^ k₁ ≤ 2 := by linarith
    have h₄₁ : 0 ≤ (1 : ℝ) + r ^ k := h₄
    have h₄₂ : 2 ≤ 2 * ((1 : ℝ) + r ^ k) := by
      have h₅ : 0 ≤ r ^ k := by positivity
      nlinarith
    linarith
  · -- Case 1 < r
    have h₁' : 1 ≤ r := by linarith
    have h₂ : r ^ k₁ ≤ r ^ k := by
      gcongr
    have h₃ : (1 : ℝ) + r ^ k₁ ≤ (1 : ℝ) + r ^ k := by linarith
    have h₄₁ : 0 ≤ (1 : ℝ) + r ^ k := h₄
    have h₄₂ : (1 : ℝ) + r ^ k ≤ 2 * ((1 : ℝ) + r ^ k) := by
      nlinarith
    linarith

lemma product_one_plus_pow_le_four_mul_one_plus_pow_sum (r : ℝ) (hr : 0 ≤ r) (k₁ k₂ : ℕ) :
    ‖((1 : ℝ) + r ^ k₁) * ((1 : ℝ) + r ^ k₂)‖ ≤ (4 : ℝ) * ‖((1 : ℝ) + r ^ (k₁ + k₂))‖ := by
  have hbound_nonneg : 0 ≤ (1 : ℝ) + r ^ (k₁ + k₂) := by positivity
  have h₃ : 0 ≤ ((1 : ℝ) + r ^ k₁) * ((1 : ℝ) + r ^ k₂) := by positivity
  have h₅ : ‖((1 : ℝ) + r ^ k₁) * ((1 : ℝ) + r ^ k₂)‖ = ((1 : ℝ) + r ^ k₁) * ((1 : ℝ) + r ^ k₂) := by
    rw [Real.norm_eq_abs, abs_of_nonneg h₃]
  have h₆ : ‖((1 : ℝ) + r ^ (k₁ + k₂))‖ = (1 : ℝ) + r ^ (k₁ + k₂) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hbound_nonneg]
  rw [h₅, h₆]
  by_cases h₁ : r ≤ 1
  · -- Case r ≤ 1
    have h₂ : r ^ k₁ ≤ 1 := by
      have h₃ : ∀ n : ℕ, r ^ n ≤ 1 := fun n => by
        induction n with
        | zero => norm_num
        | succ n ih =>
          calc
            r ^ (n + 1) = r ^ n * r := by ring
            _ ≤ 1 * r := by gcongr
            _ ≤ 1 * 1 := by gcongr
            _ = 1 := by ring
      exact h₃ k₁
    have h₃ : r ^ k₂ ≤ 1 := by
      have h₄ : ∀ n : ℕ, r ^ n ≤ 1 := fun n => by
        induction n with
        | zero => norm_num
        | succ n ih =>
          calc
            r ^ (n + 1) = r ^ n * r := by ring
            _ ≤ 1 * r := by gcongr
            _ ≤ 1 * 1 := by gcongr
            _ = 1 := by ring
      exact h₄ k₂
    have h₄₁ : (1 : ℝ) + r ^ k₁ ≤ 2 := by linarith
    have h₄₂ : (1 : ℝ) + r ^ k₂ ≤ 2 := by linarith
    have h₄₃ : 0 ≤ (1 : ℝ) + r ^ k₁ := by positivity
    have h₄₄ : 0 ≤ (1 : ℝ) + r ^ k₂ := by positivity
    have h₄ : ((1 : ℝ) + r ^ k₁) * ((1 : ℝ) + r ^ k₂) ≤ 2 * 2 := by
      exact mul_le_mul h₄₁ h₄₂ h₄₄ (by norm_num : (0 : ℝ) ≤ 2)
    have h₅₁ : 0 ≤ (1 : ℝ) + r ^ (k₁ + k₂) := hbound_nonneg
    have h₅₂ : 2 * 2 ≤ 4 * ((1 : ℝ) + r ^ (k₁ + k₂)) := by
      have h₆ : 0 ≤ r ^ (k₁ + k₂) := by positivity
      nlinarith
    linarith
  · -- Case 1 < r
    have h₁' : 1 ≤ r := by linarith
    have h₂₁ : k₁ ≤ k₁ + k₂ := Nat.le_add_right k₁ k₂
    have h₂ : r ^ k₁ ≤ r ^ (k₁ + k₂) := by
      gcongr
    have h₃₁ : k₂ ≤ k₁ + k₂ := Nat.le_add_left k₂ k₁
    have h₃ : r ^ k₂ ≤ r ^ (k₁ + k₂) := by
      gcongr
    have h₄ : 1 ≤ r ^ (k₁ + k₂) := by
      have h₅ : 1 ≤ r := h₁'
      have h₆ : 1 ≤ r ^ (k₁ + k₂) := by
        have h₇ : 1 ≤ r := h₅
        have h₈ : 1 ^ (k₁ + k₂) ≤ r ^ (k₁ + k₂) := by
          gcongr
        simpa using h₈
      exact h₆
    have h₅ : ((1 : ℝ) + r ^ k₁) * ((1 : ℝ) + r ^ k₂) =
        1 + r ^ k₁ + r ^ k₂ + r ^ (k₁ + k₂) := by ring
    rw [h₅]
    have h₆ : 1 + r ^ k₁ + r ^ k₂ + r ^ (k₁ + k₂) ≤ 4 * r ^ (k₁ + k₂) := by
      linarith
    have h₇₁ : 0 ≤ r ^ (k₁ + k₂) := by positivity
    have h₇₂ : 4 * r ^ (k₁ + k₂) ≤ 4 * ((1 : ℝ) + r ^ (k₁ + k₂)) := by
      nlinarith [hbound_nonneg]
    linarith

end Helper

section Additive
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] {l : Filter α} {g : α → F}
variable {f₁ f₂ : α → E}

/-- Sum of two subpolynomial functions is subpolynomial. -/
theorem IsSubpolynomial.add (h₁ : IsSubpolynomial l f₁ g) (h₂ : IsSubpolynomial l f₂ g) :
    IsSubpolynomial l (f₁ + f₂) g := by
  rcases h₁ with ⟨k₁, hk₁⟩
  rcases h₂ with ⟨k₂, hk₂⟩
  let k := max k₁ k₂
  let bound : α → ℝ := fun x : α => (1 : ℝ) + ‖g x‖ ^ k
  have hk₁₁ : k₁ ≤ k := le_max_left k₁ k₂
  have hk₂₁ : k₂ ≤ k := le_max_right k₁ k₂
  have h₃ : (fun x : α => (1 : ℝ) + ‖g x‖ ^ k₁) =O[l] bound := by
    apply IsBigO.of_bound 2
    filter_upwards with x
    exact one_plus_pow_le_two_mul_one_plus_pow (‖g x‖) (norm_nonneg (g x)) k₁ k hk₁₁
  have h₄ : (fun x : α => (1 : ℝ) + ‖g x‖ ^ k₂) =O[l] bound := by
    apply IsBigO.of_bound 2
    filter_upwards with x
    exact one_plus_pow_le_two_mul_one_plus_pow (‖g x‖) (norm_nonneg (g x)) k₂ k hk₂₁
  have h₅ : f₁ =O[l] bound := hk₁.trans h₃
  have h₆ : f₂ =O[l] bound := hk₂.trans h₄
  have h₇ : (fun x : α => f₁ x + f₂ x) =O[l] bound := Asymptotics.IsBigO.add h₅ h₆
  simpa [Pi.add_apply] using ⟨k, h₇⟩

end Additive

section Multiplicative
variable [SeminormedRing E] [SeminormedAddCommGroup F] {l : Filter α} {g : α → F}
variable {f₁ f₂ : α → E}

/-- Product of two subpolynomial functions is subpolynomial. -/
theorem IsSubpolynomial.mul (h₁ : IsSubpolynomial l f₁ g) (h₂ : IsSubpolynomial l f₂ g) :
    IsSubpolynomial l (f₁ * f₂) g := by
  rcases h₁ with ⟨k₁, hk₁⟩
  rcases h₂ with ⟨k₂, hk₂⟩
  let k := k₁ + k₂
  let bound₁ : α → ℝ := fun x : α => (1 : ℝ) + ‖g x‖ ^ k₁
  let bound₂ : α → ℝ := fun x : α => (1 : ℝ) + ‖g x‖ ^ k₂
  let bound : α → ℝ := fun x : α => (1 : ℝ) + ‖g x‖ ^ k
  have h₃₁ : (fun x : α => ‖f₁ x‖) =O[l] bound₁ := hk₁.norm_left
  have h₃₂ : (fun x : α => ‖f₂ x‖) =O[l] bound₂ := hk₂.norm_left
  have h₃₃ : (fun x : α => ‖f₁ x‖ * ‖f₂ x‖) =O[l] (fun x : α => bound₁ x * bound₂ x) :=
    Asymptotics.IsBigO.mul h₃₁ h₃₂
  have h₃₄ : (fun x : α => bound₁ x * bound₂ x) =O[l] bound := by
    apply IsBigO.of_bound 4
    filter_upwards with x
    exact product_one_plus_pow_le_four_mul_one_plus_pow_sum (‖g x‖) (norm_nonneg (g x)) k₁ k₂
  have h₃₅ : (fun x : α => ‖f₁ x‖ * ‖f₂ x‖) =O[l] bound := h₃₃.trans h₃₄
  have h₃₆ : ∀ x, ‖f₁ x * f₂ x‖ ≤ ‖f₁ x‖ * ‖f₂ x‖ := fun x => norm_mul_le (f₁ x) (f₂ x)
  have h₃₇₁ : (fun x : α => f₁ x * f₂ x) =O[l] (fun x : α => ‖f₁ x‖ * ‖f₂ x‖) := by
    apply IsBigO.of_bound 1
    filter_upwards with x
    have h₃₈₁ : 0 ≤ ‖f₁ x‖ * ‖f₂ x‖ := by positivity
    have h₃₈₂ : ‖f₁ x * f₂ x‖ ≤ 1 * ‖‖f₁ x‖ * ‖f₂ x‖‖ := by
      have h₃₈₃ : ‖‖f₁ x‖ * ‖f₂ x‖‖ = ‖f₁ x‖ * ‖f₂ x‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg h₃₈₁]
      rw [h₃₈₃]
      simpa [one_mul] using h₃₆ x
    exact h₃₈₂
  have h₃₇ : (fun x : α => f₁ x * f₂ x) =O[l] bound := h₃₇₁.trans h₃₅
  simpa [Pi.mul_apply] using ⟨k, h₃₇⟩

/-- A natural number power of a subpolynomial function is subpolynomial. -/
theorem IsSubpolynomial.pow {f : α → E} (h : IsSubpolynomial l f g) (n : ℕ) :
    IsSubpolynomial l (f ^ n) g := by
  induction n with
  | zero =>
    simpa using IsSubpolynomial.const (l := l) (g := g) (c := (1 : E))
  | succ n ih =>
    simpa [pow_succ] using ih.mul h

end Multiplicative

end Asymptotics

end
