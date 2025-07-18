/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-!
# seminormFromBounded
In this file, we prove [BGR, Proposition 1.2.1/2][bosch-guntzer-remmert] : given a nonzero
additive group seminorm on a commutative ring `R` such that for some `c : ℝ` and every `x y : R`,
the inequality `f (x * y) ≤ c * f x * f y)` is satisfied, we create a ring seminorm on `R`.

In the file comments, we will use the expression `f is multiplicatively bounded` to indicate that
this condition holds.


## Main Definitions

* `seminormFromBounded'` : the real-valued function sending `x ∈ R` to the supremum of
  `f(x*y)/f(y)`, where `y` runs over the elements of `R`.
* `seminormFromBounded` : the function `seminormFromBounded'` as a `RingSeminorm` on `R`.
* `normFromBounded` :`seminormFromBounded' f` as a `RingNorm` on `R`, provided that `f` is
  nonnegative, multiplicatively bounded and subadditive, that it preserves `0` and negation, and
  that `f` has trivial kernel.


## Main Results

* `seminormFromBounded_isNonarchimedean` : if `f : R → ℝ` is a nonnegative, multiplicatively
  bounded, nonarchimedean function, then `seminormFromBounded' f` is nonarchimedean.
* `seminormFromBounded_of_mul_is_mul` : if `f : R → ℝ` is a nonnegative, multiplicatively bounded
  function and `x : R` is multiplicative for `f`, then `x` is multiplicative for
  `seminormFromBounded' f`.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

seminormFromBounded, RingSeminorm, Nonarchimedean
-/

noncomputable section

open scoped Topology NNReal

variable {R : Type _} [CommRing R] (f : R → ℝ) {c : ℝ}

section seminormFromBounded

/-- The real-valued function sending `x ∈ R` to the supremum of  `f(x*y)/f(y)`, where `y` runs over
the elements of `R`. -/
def seminormFromBounded' : R → ℝ := fun x ↦ iSup fun y : R ↦ f (x * y) / f y

variable {f}

/-- If `f : R → ℝ` is a nonzero, nonnegative, multiplicatively bounded function, then `f 1 ≠ 0`. -/
theorem map_one_ne_zero (f_ne_zero : f ≠ 0) (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) : f 1 ≠ 0 := by
  intro h1
  specialize f_mul 1
  simp_rw [h1, one_mul, mul_zero, zero_mul] at f_mul
  obtain ⟨z, hz⟩ := Function.ne_iff.mp f_ne_zero
  exact hz <| (f_mul z).antisymm (f_nonneg z)

/-- If `f : R → ℝ` is a nonnegative multiplicatively bounded function and `x : R` is a unit with
  `f x ≠ 0`, then for every `n : ℕ`, we have `f (x ^ n) ≠ 0`. -/
theorem map_pow_ne_zero (f_nonneg : 0 ≤ f) {x : R} (hx : IsUnit x) (hfx : f x ≠ 0) (n : ℕ)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) : f (x ^ n) ≠ 0 := by
  have h1 : f 1 ≠ 0 := map_one_ne_zero (Function.ne_iff.mpr ⟨x, hfx⟩) f_nonneg f_mul
  intro hxn
  have : f 1 ≤ 0 := by simpa [← mul_pow, hxn] using f_mul (x ^ n) (hx.unit⁻¹ ^ n)
  exact h1 <| this.antisymm (f_nonneg 1)

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then given `x y : R` with
  `f x = 0`, we have `f (x * y) = 0`. -/
theorem map_mul_zero_of_map_zero (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) {x : R} (hx : f x = 0)
    (y : R) : f (x * y) = 0 := by
  replace f_mul : f (x * y) ≤ 0 := by simpa [hx] using f_mul x y
  exact le_antisymm f_mul (f_nonneg _)

/-- `seminormFromBounded' f` preserves `0`. -/
theorem seminormFromBounded_zero (f_zero : f 0 = 0) : seminormFromBounded' f (0 : R) = 0 := by
  simp_rw [seminormFromBounded', zero_mul, f_zero, zero_div, ciSup_const]

theorem seminormFromBounded_aux (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) (x : R) : 0 ≤ c * f x := by
  rcases (f_nonneg x).eq_or_lt' with hx | hx
  · simp [hx]
  · change 0 < f x at hx
    have hc : 0 ≤ c := by
      specialize f_mul x 1
      rw [mul_one, show c * f x * f 1 = c * f 1 * f x by ring, le_mul_iff_one_le_left hx] at f_mul
      replace f_nonneg : 0 ≤ f 1 := f_nonneg 1
      rcases f_nonneg.eq_or_lt' with h1 | h1
      · linarith [show (1 : ℝ) ≤ 0 by simpa [h1] using f_mul]
      · rw [← div_le_iff₀ h1] at f_mul
        linarith [one_div_pos.mpr h1]
    positivity

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then for every `x : R`,
  the image of `y ↦ f (x * y) / f y` is bounded above. -/
theorem seminormFromBounded_bddAbove_range (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) (x : R) :
    BddAbove (Set.range fun y ↦ f (x * y) / f y) := by
  use c * f x
  rintro r ⟨y, rfl⟩
  rcases (f_nonneg y).eq_or_lt' with hy0 | hy0
  · simpa [hy0] using seminormFromBounded_aux f_nonneg f_mul x
  · simpa [div_le_iff₀ hy0] using f_mul x y

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then for every `x : R`,
  `seminormFromBounded' f x` is bounded above by some multiple of `f x`. -/
theorem seminormFromBounded_le (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) (x : R) :
    seminormFromBounded' f x ≤ c * f x := by
  refine ciSup_le (fun y ↦ ?_)
  rcases (f_nonneg y).eq_or_lt' with hy | hy
  · simpa [hy] using seminormFromBounded_aux f_nonneg f_mul x
  · rw [div_le_iff₀ hy]
    apply f_mul

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then for every `x : R`,
  `f x ≤ f 1 * seminormFromBounded' f x`. -/
theorem seminormFromBounded_ge (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) (x : R) :
    f x ≤ f 1 * seminormFromBounded' f x := by
  by_cases h1 : f 1 = 0
  · specialize f_mul x 1
    rw [mul_one, h1, mul_zero] at f_mul
    have hx0 : f x = 0 := f_mul.antisymm (f_nonneg _)
    rw [hx0, h1, zero_mul]
  · rw [mul_comm, ← div_le_iff₀ (lt_of_le_of_ne' (f_nonneg _) h1)]
    conv_lhs => rw [← mul_one x]
    exact le_ciSup (seminormFromBounded_bddAbove_range f_nonneg f_mul x) (1 : R)

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then
  `seminormFromBounded' f` is nonnegative. -/
theorem seminormFromBounded_nonneg (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y)  :
    0 ≤ seminormFromBounded' f := fun x ↦
  le_csSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul x) ⟨1, rfl⟩
    (div_nonneg (f_nonneg _) (f_nonneg _))

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then
  `seminormFromBounded' f x = 0` if and only if `f x = 0`. -/
theorem seminormFromBounded_eq_zero_iff (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) (x : R) :
    seminormFromBounded' f x = 0 ↔ f x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hf := seminormFromBounded_ge f_nonneg f_mul x
    rw [h, mul_zero] at hf
    exact hf.antisymm (f_nonneg _)
  · have hf : seminormFromBounded' f x ≤ c * f x :=
      seminormFromBounded_le f_nonneg f_mul x
    rw [h, mul_zero] at hf
    exact hf.antisymm (seminormFromBounded_nonneg f_nonneg f_mul x)

/-- If `f` is invariant under negation of `x`, then so is `seminormFromBounded'`. -/
theorem seminormFromBounded_neg (f_neg : ∀ x : R, f (-x) = f x) (x : R) :
    seminormFromBounded' f (-x) = seminormFromBounded' f x := by
  suffices ⨆ y, f (-x * y) / f y = ⨆ y, f (x * y) / f y by simpa only [seminormFromBounded']
  congr
  ext y
  rw [neg_mul, f_neg]

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then
  `seminormFromBounded' f` is submultiplicative. -/
theorem seminormFromBounded_mul (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) (x y : R) :
    seminormFromBounded' f (x * y) ≤ seminormFromBounded' f x * seminormFromBounded' f y := by
  apply ciSup_le
  by_cases hy : seminormFromBounded' f y = 0
  · rw [seminormFromBounded_eq_zero_iff f_nonneg f_mul] at hy
    intro z
    rw [mul_comm x y, mul_assoc, map_mul_zero_of_map_zero f_nonneg f_mul hy (x * z), zero_div]
    exact mul_nonneg (seminormFromBounded_nonneg f_nonneg f_mul x)
      (seminormFromBounded_nonneg f_nonneg f_mul y)
  · intro z
    rw [← div_le_iff₀ (lt_of_le_of_ne' (seminormFromBounded_nonneg f_nonneg f_mul _) hy)]
    apply le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul x) z
    rw [div_le_iff₀ (lt_of_le_of_ne' (seminormFromBounded_nonneg f_nonneg f_mul _) hy),
      div_mul_eq_mul_div]
    by_cases hz : f z = 0
    · have hxyz : f (z * (x * y)) = 0 := map_mul_zero_of_map_zero f_nonneg f_mul hz _
      simp_rw [mul_comm, hxyz, zero_div]
      exact div_nonneg (mul_nonneg (seminormFromBounded_nonneg f_nonneg f_mul y) (f_nonneg _))
        (f_nonneg _)
    · rw [div_le_div_iff_of_pos_right (lt_of_le_of_ne' (f_nonneg _) hz), mul_comm (f (x * z))]
      by_cases hxz : f (x * z) = 0
      · rw [mul_comm x y, mul_assoc, mul_comm y, map_mul_zero_of_map_zero f_nonneg f_mul hxz y]
        exact mul_nonneg (seminormFromBounded_nonneg f_nonneg f_mul y) (f_nonneg _)
      · rw [← div_le_iff₀ (lt_of_le_of_ne' (f_nonneg _) hxz)]
        apply le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul y) (x * z)
        rw [div_le_div_iff_of_pos_right (lt_of_le_of_ne' (f_nonneg _) hxz), mul_comm x y, mul_assoc]

/-- If `f : R → ℝ` is a nonzero, nonnegative, multiplicatively bounded function, then
  `seminormFromBounded' f 1 = 1`. -/
theorem seminormFromBounded_one (f_ne_zero : f ≠ 0) (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) :
    seminormFromBounded' f 1 = 1 := by
  simp_rw [seminormFromBounded', one_mul]
  apply le_antisymm
  · refine ciSup_le (fun x ↦ ?_)
    by_cases hx : f x = 0
    · rw [hx, div_zero]; exact zero_le_one
    · rw [div_self hx]
  · rw [← div_self (map_one_ne_zero f_ne_zero f_nonneg f_mul)]
    have h_bdd : BddAbove (Set.range fun y ↦ f y / f y) := by
      use (1 : ℝ)
      rintro r ⟨y, rfl⟩
      by_cases hy : f y = 0
      · simp only [hy, div_zero, zero_le_one]
      · simp only [div_self hy, le_refl]
    exact le_ciSup h_bdd (1 : R)

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then
  `seminormFromBounded' f 1 ≤ 1`. -/
theorem seminormFromBounded_one_le (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) :
    seminormFromBounded' f 1 ≤ 1 := by
  by_cases f_ne_zero : f ≠ 0
  · exact le_of_eq (seminormFromBounded_one f_ne_zero f_nonneg f_mul)
  · simp_rw [seminormFromBounded', one_mul]
    refine ciSup_le (fun _ ↦ ?_)
    push_neg at f_ne_zero
    simp only [f_ne_zero, Pi.zero_apply, div_zero, zero_le_one]

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded, subadditive function, then
  `seminormFromBounded' f` is subadditive. -/
theorem seminormFromBounded_add (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y)
    (f_add : ∀ a b, f (a + b) ≤ f a + f b) (x y : R) :
    seminormFromBounded' f (x + y) ≤ seminormFromBounded' f x + seminormFromBounded' f y := by
  refine ciSup_le (fun z ↦ ?_)
  suffices hf : f ((x + y) * z) / f z ≤ f (x * z) / f z + f (y * z) / f z by
    exact le_trans hf (add_le_add
      (le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul x) z (le_refl _))
      (le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul y) z (le_refl _)))
  by_cases hz : f z = 0
  · simp only [hz, div_zero, zero_add, le_refl]
  · rw [div_add_div_same, div_le_div_iff_of_pos_right (lt_of_le_of_ne' (f_nonneg _) hz), add_mul]
    exact f_add _ _

/-- `seminormFromBounded'` is a ring seminorm on `R`. -/
def seminormFromBounded (f_zero : f 0 = 0) (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y)
    (f_add : ∀ a b, f (a + b) ≤ f a + f b) (f_neg : ∀ x : R, f (-x) = f x) : RingSeminorm R where
  toFun     := seminormFromBounded' f
  map_zero' := seminormFromBounded_zero f_zero
  add_le'   := seminormFromBounded_add f_nonneg f_mul f_add
  mul_le'   := seminormFromBounded_mul f_nonneg f_mul
  neg'      := seminormFromBounded_neg f_neg

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded, nonarchimedean function, then
  `seminormFromBounded' f` is nonarchimedean. -/
theorem seminormFromBounded_isNonarchimedean (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y)
    (hna : IsNonarchimedean f) : IsNonarchimedean (seminormFromBounded' f) := by
  refine fun x y ↦ ciSup_le (fun z ↦ ?_)
  rw [le_max_iff]
  suffices hf : f ((x + y) * z) / f z ≤ f (x * z) / f z ∨ f ((x + y) * z) / f z ≤ f (y * z) / f z by
    rcases hf with hfx | hfy
    · exact Or.inl <| le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul x) z hfx
    · exact Or.inr <| le_ciSup_of_le (seminormFromBounded_bddAbove_range f_nonneg f_mul y) z hfy
  by_cases hz : f z = 0
  · simp only [hz, div_zero, le_refl, or_self_iff]
  · rw [div_le_div_iff_of_pos_right (lt_of_le_of_ne' (f_nonneg _) hz),
      div_le_div_iff_of_pos_right (lt_of_le_of_ne' (f_nonneg _) hz), add_mul, ← le_max_iff]
    exact hna _ _

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function and `x : R` is
  multiplicative for `f`, then `seminormFromBounded' f x = f x`. -/
theorem seminormFromBounded_of_mul_apply (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) {x : R}
    (hx : ∀ y : R, f (x * y) = f x * f y) : seminormFromBounded' f x = f x := by
  simp_rw [seminormFromBounded', hx, ← mul_div_assoc']
  apply le_antisymm
  · refine ciSup_le (fun x ↦ ?_)
    by_cases hx : f x = 0
    · rw [hx, div_zero, mul_zero]; exact f_nonneg _
    · rw [div_self hx, mul_one]
  · by_cases f_ne_zero : f ≠ 0
    · conv_lhs => rw [← mul_one (f x)]
      rw [← div_self (map_one_ne_zero f_ne_zero f_nonneg f_mul)]
      have h_bdd : BddAbove (Set.range fun y ↦ f x * (f y / f y)) := by
        use f x
        rintro r ⟨y, rfl⟩
        by_cases hy0 : f y = 0
        · simp only [hy0, div_zero, mul_zero]; exact f_nonneg _
        · simp only [div_self hy0, mul_one, le_refl]
      exact le_ciSup h_bdd (1 : R)
    · push_neg at f_ne_zero
      simp_rw [f_ne_zero, Pi.zero_apply, zero_div, zero_mul, ciSup_const]; rfl

/-- If `f : R → ℝ` is a nonnegative function and `x : R` is submultiplicative for `f`, then
  `seminormFromBounded' f x = f x`. -/
theorem seminormFromBounded_of_mul_le (f_nonneg : 0 ≤ f) {x : R}
    (hx : ∀ y : R, f (x * y) ≤ f x * f y) (h_one : f 1 ≤ 1) : seminormFromBounded' f x = f x := by
  simp_rw [seminormFromBounded']
  apply le_antisymm
  · refine ciSup_le (fun y ↦ ?_)
    by_cases hy : f y = 0
    · rw [hy, div_zero]; exact f_nonneg _
    · rw [div_le_iff₀ (lt_of_le_of_ne' (f_nonneg _) hy)]; exact hx _
  · have h_bdd : BddAbove (Set.range fun y ↦ f (x * y) / f y) := by
      use f x
      rintro r ⟨y, rfl⟩
      by_cases hy0 : f y = 0
      · simp only [hy0, div_zero]
        exact f_nonneg _
      · rw [← mul_one (f x), ← div_self hy0, ← mul_div_assoc,
          div_le_iff₀ (lt_of_le_of_ne' (f_nonneg _) hy0), mul_div_assoc, div_self hy0, mul_one]
        exact hx y
    convert le_ciSup h_bdd (1 : R)
    by_cases h0 : f x = 0
    · rw [mul_one, h0, zero_div]
    · have heq : f 1 = 1 := by
        apply h_one.antisymm
        specialize hx 1
        rw [mul_one, le_mul_iff_one_le_right (lt_of_le_of_ne (f_nonneg _) (Ne.symm h0))] at hx
        exact hx
      rw [heq, mul_one, div_one]

/-- If `f : R → ℝ` is a nonzero, nonnegative, multiplicatively bounded function, then
  `seminormFromBounded' f` is nonzero. -/
theorem seminormFromBounded_nonzero (f_ne_zero : f ≠ 0) (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) :
    seminormFromBounded' f ≠ 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp f_ne_zero
  rw [Function.ne_iff]
  use x
  rw [ne_eq, Pi.zero_apply, seminormFromBounded_eq_zero_iff f_nonneg f_mul x]
  exact hx

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then the kernel of
  `seminormFromBounded' f` equals the kernel of `f`. -/
theorem seminormFromBounded_ker (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) :
    seminormFromBounded' f ⁻¹' {0} = f ⁻¹' {0} := by
  ext x
  exact seminormFromBounded_eq_zero_iff f_nonneg f_mul x

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded, subadditive function that preserves
  zero and negation, then `seminormFromBounded' f` is a norm if and only if `f⁻¹' {0} = {0}`. -/
theorem seminormFromBounded_is_norm_iff (f_zero : f 0 = 0) (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y)
    (f_add : ∀ a b, f (a + b) ≤ f a + f b) (f_neg : ∀ x : R, f (-x) = f x) :
    (∀ x : R, (seminormFromBounded f_zero f_nonneg f_mul f_add f_neg).toFun x = 0 → x = 0) ↔
      f ⁻¹' {0} = {0} := by
  refine ⟨fun h0 ↦ ?_, fun h_ker x hx ↦ ?_⟩
  · rw [← seminormFromBounded_ker f_nonneg f_mul]
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h ↦ h0 x h, fun h ↦ by rw [h]; exact seminormFromBounded_zero f_zero⟩
  · rw [← Set.mem_singleton_iff, ← h_ker, Set.mem_preimage, Set.mem_singleton_iff,
      ← seminormFromBounded_eq_zero_iff f_nonneg f_mul x]
    exact hx

/-- `seminormFromBounded' f` as a `RingNorm` on `R`, provided that `f` is nonnegative,
  multiplicatively bounded and subadditive, that it preserves `0` and negation, and that `f` has
  trivial kernel. -/
def normFromBounded (f_zero : f 0 = 0) (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y)
    (f_add : ∀ a b, f (a + b) ≤ f a + f b) (f_neg : ∀ x : R, f (-x) = f x)
    (f_ker : f ⁻¹' {0} = {0}) : RingNorm R :=
  { seminormFromBounded f_zero f_nonneg f_mul f_add f_neg with
    eq_zero_of_map_eq_zero' :=
      (seminormFromBounded_is_norm_iff f_zero f_nonneg f_mul f_add f_neg).mpr f_ker }

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function and `x : R` is
  multiplicative for `f`, then `x` is multiplicative for `seminormFromBounded' f`. -/
theorem seminormFromBounded_of_mul_is_mul (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) {x : R}
    (hx : ∀ y : R, f (x * y) = f x * f y) (y : R) :
    seminormFromBounded' f (x * y) = seminormFromBounded' f x * seminormFromBounded' f y := by
  rw [seminormFromBounded_of_mul_apply f_nonneg f_mul hx]
  simp only [seminormFromBounded', mul_assoc, hx, mul_div_assoc,
    Real.mul_iSup_of_nonneg (f_nonneg _)]

end seminormFromBounded
