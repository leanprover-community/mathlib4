/-
Copyright (c) 2025 Youheng Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Youheng Luo
-/
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Bound

/-!
# Subpolynomial Growth

This file defines the notion of subpolynomial growth for functions.

## Main definitions

* `Asymptotics.IsSubpolynomial`: A function `f` has subpolynomial growth with respect to `g`
  along filter `l` if `f = O((1 + ‖g‖)^k)` for some natural `k`.

## Main results

* `IsSubpolynomial.add`: Subpolynomial functions are closed under addition.
* `IsSubpolynomial.neg`: Subpolynomial functions are closed under negation.
* `IsSubpolynomial.sub`: Subpolynomial functions are closed under subtraction.
* `IsSubpolynomial.mul`: Subpolynomial functions are closed under multiplication.
* `IsSubpolynomial.pow`: Subpolynomial functions are closed under natural powers.
* `IsSubpolynomial.norm_left`: Norm of left function preserves subpolynomiality.
* `IsSubpolynomial.norm_right`: Norm of right function preserves subpolynomiality.
* `IsSubpolynomial.uniform`: Uniform bounds for a finite set of subpolynomial functions.
* `isSubpolynomial_iff_eventually_isBigO`: Equivalence with eventually BigO behavior.
* `isSubpolynomial_iff_one_add`: Equivalence with the growth condition `O(1 + ‖g‖^k)`.
-/

section
open Filter Asymptotics
open scoped Topology

namespace Asymptotics

variable {α E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
variable {l : Filter α} {f : α → E} {g : α → F}

/-- A function `f` has subpolynomial growth with respect to `g` along filter `l`
if `f = O((1 + ‖g‖)^k)` for some natural `k`. -/
def IsSubpolynomial (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∃ k : ℕ, IsBigO l f (fun x => (1 + ‖g x‖) ^ k)

/-! ### Basic instances -/

/-- A constant function has subpolynomial growth. -/
theorem IsSubpolynomial.const (c : E) :
    IsSubpolynomial l (fun _ => c) g := by
  use 0
  simp only [pow_zero]
  exact isBigO_const_const c (by norm_num : (1 : ℝ) ≠ 0) l

/-- The function `g` has subpolynomial growth with respect to itself. -/
theorem IsSubpolynomial.self : IsSubpolynomial l g g := by
  use 1
  apply IsBigO.of_norm_le
  intro x
  simp [pow_one]

/-- Norm of the left function does not change subpolynomiality. -/
theorem IsSubpolynomial.norm_left : IsSubpolynomial l (fun x => ‖f x‖) g ↔ IsSubpolynomial l f g :=
  exists_congr fun _ => isBigO_norm_left

/-- Norm of the right function does not change subpolynomiality. -/
theorem IsSubpolynomial.norm_right : IsSubpolynomial l f (fun x => ‖g x‖) ↔ IsSubpolynomial l f g :=
  by simp only [IsSubpolynomial, norm_norm]

/-! ### Closure properties -/

theorem isSubpolynomial_iff_eventually_isBigO :
    IsSubpolynomial l f g ↔ ∀ᶠ k in atTop, IsBigO l f (fun x => (1 + ‖g x‖) ^ k) := by
  refine ⟨fun ⟨k, hk⟩ ↦ ?_, fun H ↦ H.exists⟩
  rw [eventually_atTop]
  use k
  intro n hkn
  refine hk.trans_le (fun x ↦ ?_)
  have h1 : 1 ≤ 1 + ‖g x‖ := le_add_of_nonneg_right (norm_nonneg _)
  simp (discharger := positivity) only [Real.norm_of_nonneg]
  bound

/-- Subpolynomial growth is preserved under addition. -/
theorem IsSubpolynomial.add {f₁ f₂ : α → E}
    (hf₁ : IsSubpolynomial l f₁ g) (hf₂ : IsSubpolynomial l f₂ g) :
    IsSubpolynomial l (f₁ + f₂) g := by
  rw [isSubpolynomial_iff_eventually_isBigO] at *
  filter_upwards [hf₁, hf₂] with k hkf₁ hkf₂ using hkf₁.add hkf₂

/-- Subpolynomial growth is preserved under negation. -/
theorem IsSubpolynomial.neg (hf : IsSubpolynomial l f g) :
    IsSubpolynomial l (-f) g := by
  obtain ⟨k, hk⟩ := hf
  use k
  exact hk.neg_left

/-- Subpolynomial growth is preserved under subtraction. -/
theorem IsSubpolynomial.sub {f₁ f₂ : α → E}
    (hf₁ : IsSubpolynomial l f₁ g) (hf₂ : IsSubpolynomial l f₂ g) :
    IsSubpolynomial l (f₁ - f₂) g := by
  simpa only [sub_eq_add_neg] using hf₁.add hf₂.neg

variable {R : Type*} [NormedRing R]

/-- Subpolynomial growth is preserved under multiplication. -/
theorem IsSubpolynomial.mul {f₁ f₂ : α → R}
    (hf₁ : IsSubpolynomial l f₁ g) (hf₂ : IsSubpolynomial l f₂ g) :
    IsSubpolynomial l (f₁ * f₂) g := by
  obtain ⟨k₁, hk₁⟩ := hf₁
  obtain ⟨k₂, hk₂⟩ := hf₂
  use k₁ + k₂
  simp_rw [pow_add]
  exact hk₁.mul hk₂

/-- Subpolynomial growth is preserved under natural powers. -/
theorem IsSubpolynomial.pow {f : α → R} (hf : IsSubpolynomial l f g) (n : ℕ) :
    IsSubpolynomial l (f ^ n) g := by
  induction n with
  | zero => simp only [pow_zero]; exact IsSubpolynomial.const 1
  | succ n ih => simp only [pow_succ]; exact ih.mul hf

/-! ### Equivalence with `O(1 + ‖g‖^k)` -/

/-- Auxiliary lemma: `1 + x^k ≤ 2 * (1 + x)^k` for `x ≥ 0`. -/
private lemma one_add_pow_le_two_mul_add_one_pow {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    1 + x ^ k ≤ 2 * (1 + x) ^ k := by
  have h1 : 1 ≤ (1 + x) ^ k := by bound
  have h2 : x ^ k ≤ (1 + x) ^ k := by bound
  bound

/-- Auxiliary lemma: `(1 + x)^k ≤ 2^k * (1 + x^k)` for `x ≥ 0`. -/
private lemma add_one_pow_le_two_pow_mul {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    (1 + x) ^ k ≤ 2 ^ k * (1 + x ^ k) := by
  rcases le_or_gt x 1 with hx1 | hx1
  · calc (1 + x) ^ k
        ≤ 2 ^ k := by bound
      _ ≤ 2 ^ k * (1 + x ^ k) := by bound
  · calc (1 + x) ^ k
        ≤ (2 * x) ^ k := by bound
      _ = 2 ^ k * x ^ k := by rw [mul_pow]
      _ ≤ 2 ^ k * (1 + x ^ k) := by bound

/-- Equivalence between `f = O((1 + ‖g‖)^k)` and `f = O(1 + ‖g‖^k)`. -/
theorem isSubpolynomial_iff_one_add :
    IsSubpolynomial l f g ↔ ∃ k : ℕ, IsBigO l f (fun x => 1 + ‖g x‖ ^ k) := by
  constructor
  · intro ⟨k, hk⟩
    use k
    have hbound : IsBigO l (fun x => (1 + ‖g x‖) ^ k) (fun x => 1 + ‖g x‖ ^ k) := by
      apply IsBigO.of_bound (2 ^ k)
      filter_upwards with x
      simp (discharger := positivity) only [Real.norm_of_nonneg]
      exact add_one_pow_le_two_pow_mul (norm_nonneg _) k
    exact hk.trans hbound
  · intro ⟨k, hk⟩
    use k
    have hbound : IsBigO l (fun x => 1 + ‖g x‖ ^ k) (fun x => (1 + ‖g x‖) ^ k) := by
      apply IsBigO.of_bound 2
      filter_upwards with x
      simp (discharger := positivity) only [Real.norm_of_nonneg]
      exact one_add_pow_le_two_mul_add_one_pow (norm_nonneg _) k
    exact hk.trans hbound

/-! ### Uniformity -/

/-- For a finite family of subpolynomial functions, one can choose a uniform degree and constant. -/
theorem IsSubpolynomial.uniform {ι : Type*} {s : Finset ι} {l : Filter α}
    {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)]
    {f : (i : ι) → α → E i} {g : α → F}
    (hf : ∀ i ∈ s, IsSubpolynomial l (f i) g) :
    ∃ k : ℕ, ∃ C ≥ 0, ∀ i ∈ s, IsBigOWith C l (f i) (fun x => (1 + ‖g x‖) ^ k) := by
  simp_rw [isSubpolynomial_iff_eventually_isBigO, isBigO_iff_eventually_isBigOWith,
    ← eventually_all_finset] at hf
  obtain ⟨k, hk⟩ := hf.exists
  obtain ⟨C, C_nonneg, hC⟩ := (eventually_ge_atTop 0).and hk |>.exists
  use k, C

end Asymptotics
