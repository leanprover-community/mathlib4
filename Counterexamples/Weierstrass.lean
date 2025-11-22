/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Weierstrass function: a function that is continuous everywhere but differentiable nowhere

This file defines the real-valued Weierstrass function as

$$f(x) = \sum_{n=0}^\infty a^n \cos (b^n\pi x)$$

and prove that it is continuous everywhere but differentiable nowhere for $a \mem (0, 1)$, and
positive odd integer $b$ such that

$$1 + \frac{3}{2}\pi < ab$

which is the original bound given by Karl Weierstrass. There is a better bound $1 \le ab$ given by
G. H. Hardy, but it is not implemented here.

## References

* [Weierstrass, Karl, *Über continuirliche Functionen eines reellen Arguments, die für keinen Werth
des letzeren einen bestimmten Differentialquotienten besitzen*][weierstrass1895]

-/

theorem abs_sub_abs_le_abs_add
    {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] (a b : G) :
    |a| - |b| ≤ |a + b| := by
  convert abs_sub_abs_le_abs_sub a (-b) using 2 <;> simp

theorem abs_sub_abs_le_abs_add'
    {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] (a b : G) :
    |a| - |b| ≤ |b + a| := by
  rw [add_comm]
  apply abs_sub_abs_le_abs_add

theorem Real.cos_int_mul_pi (n : ℤ) :
    cos (n * Real.pi) = (-1) ^ n := by
  convert Real.cos_add_int_mul_pi 0 n using 2 <;> simp

theorem Real.abs_cos_sub_cos_le (x y : ℝ) :
    |cos x - cos y| ≤ |x - y| := by
  wlog h : y ≤ x
  · convert this y x (le_of_lt (not_le.mp h)) using 1 <;> apply abs_sub_comm
  suffices ‖cos x - cos y‖ ≤ 1 * (x - y) by
    convert this using 1
    simpa using h
  have hx : x ∈ Set.Icc y x := by simpa using h
  have hsin : ∀ z ∈ Set.Ico y x, ‖-sin z‖ ≤ 1 := by
    intro z _
    simpa using Real.abs_sin_le_one z
  refine norm_image_sub_le_of_norm_deriv_le_segment' (fun x _ ↦ ?_) hsin _ hx
  apply HasDerivAt.hasDerivWithinAt
  simpa using HasDerivAt.cos (hasDerivAt_id' x)

theorem abs_zpow {α : Type*} [Field α] [LinearOrder α] [IsOrderedRing α]
    (a : α) (n : ℤ) : |a ^ n| = |a| ^ n := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [zero_zpow_eq, abs_ite]
  have ha' : |a| ≠ 0 := by
    simpa using ha
  induction n with
  | zero => simp
  | succ n ih =>
    simp_rw [zpow_add_one₀ ha, zpow_add_one₀ ha', abs_mul, ih]
  | pred n ih =>
    simp_rw [zpow_sub_one₀ ha, zpow_sub_one₀ ha', abs_mul, abs_inv, ih]

theorem abs_neg_one_zpow {α : Type*} [Field α] [LinearOrder α] [IsOrderedRing α]
    (n : ℤ) : |(-1 : α) ^ n| = 1:= by
  simp [abs_zpow]

open Real Topology

/-- For real parameter $a$ and $b$, define the Weierstrass function as
$$f(x) = \sum_{n=0}^\infty a^n \cos (b^n\pi x)$$ -/
noncomputable
def weierstrass (a b x : ℝ) := ∑' n, a ^ n * cos (b ^ n * π * x)

theorem hasSumUniformlyOn_weierstrass {a : ℝ} (ha : a ∈ Set.Ioo 0 1) (b : ℝ) :
    HasSumUniformlyOn (fun n x ↦ a ^ n * cos (b ^ n * π * x)) (weierstrass a b) {Set.univ} := by
  have habs : |(|a|)| < 1 := by grind [abs_abs, abs_lt]
  unfold weierstrass
  apply HasSumUniformlyOn.of_norm_le_summable (summable_geometric_of_abs_lt_one habs)
  intro n x _
  suffices |a| ^ n * |cos (b ^ n * π * x)| ≤ |a| ^ n * 1 by simpa
  gcongr
  exact abs_cos_le_one _

theorem tendstoUniformly_weierstrass {a : ℝ} (ha : a ∈ Set.Ioo 0 1) (b : ℝ) :
    TendstoUniformly (fun s x ↦ ∑ n ∈ s, a ^ n * cos (b ^ n * π * x))
    (weierstrass a b) Filter.atTop := by
  rw [← tendstoUniformlyOn_univ]
  exact (hasSumUniformlyOn_iff_tendstoUniformlyOn).mp
    (hasSumUniformlyOn_weierstrass ha b) _ (by simp)

theorem summable_weierstrass {a : ℝ} (ha : a ∈ Set.Ioo 0 1) (b x : ℝ) :
    Summable fun n ↦ a ^ n * cos (b ^ n * π * x) := by
  exact (hasSumUniformlyOn_weierstrass ha b).summableUniformlyOn.summable
    (Set.mem_singleton _) (Set.mem_univ _)

theorem continuous_weierstrass {a : ℝ} (ha : a ∈ Set.Ioo 0 1) (b : ℝ) :
    Continuous (weierstrass a b) := by
  have htendsto (x : ℝ) (_ : x ∈ Set.univ) := (summable_weierstrass ha b x).tendsto_sum_tsum_nat
  apply TendstoUniformly.continuous (tendstoUniformly_weierstrass ha b)
  apply Filter.Eventually.of_forall
  intro
  fun_prop

/-- Define a sequence to approximate $x$, for wich we will show the slope doesn't converge. -/
noncomputable
def xm (b x : ℝ) (m : ℕ) := ⌊b ^ m * x + 3 / 2⌋ / b ^ m

theorem lt_xm {b : ℝ} (hb : 0 < b) (x : ℝ) (m : ℕ) : x < xm b x m := by
  unfold xm
  grw [← Int.sub_one_lt_floor]
  field_simp
  grind

theorem le_xm {b : ℝ} (hb : 0 < b) (x : ℝ) : (fun _ ↦ x) ≤ xm b x :=
  fun m ↦ (lt_xm hb x m).le

theorem xm_le {b : ℝ} (hb : 0 < b) (x : ℝ) :
    xm b x ≤ fun m ↦ x + (3 / 2) * b⁻¹ ^ m := by
  rw [Pi.le_def]
  intro m
  have hb0' : b ^ m ≠ 0 := by simp [hb.ne.symm]
  unfold xm
  grw [Int.floor_le]
  apply le_of_eq
  rw [add_div]
  rw [mul_div_cancel_left_of_imp (by simp [hb0'])]
  rw [inv_pow, div_eq_mul_inv]

theorem tendsto_xm {b : ℝ} (hb : 1 < b) (x : ℝ) :
    Filter.Tendsto (xm b x ·) Filter.atTop (𝓝 x) := by
  unfold xm
  have hb0 : 0 < b := lt_trans (by norm_num) hb
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ ?_ (le_xm hb0 x) (xm_le hb0 x)
  · exact tendsto_const_nhds_iff.mpr rfl
  rw [show nhds x = nhds (x + (3 / 2) * 0) by simp]
  refine tendsto_const_nhds.add (Filter.Tendsto.const_mul _ ?_)
  refine tendsto_pow_atTop_nhds_zero_of_lt_one (by simpa using hb0.le) ?_
  exact (inv_lt_one₀ hb0).mpr hb

theorem tendsto_inv_xm_sub_x {b : ℝ} (hb : 1 < b) (x : ℝ) :
    Filter.Tendsto (fun m ↦ (xm b x m - x)⁻¹) Filter.atTop Filter.atTop := by
  have hb0 : 0 < b := lt_trans (by norm_num) hb
  apply Filter.Tendsto.inv_tendsto_nhdsGT_zero
  suffices Filter.Tendsto (fun m ↦ xm b x m - x) Filter.atTop (𝓝 0) by
    refine tendsto_nhdsWithin_iff.mpr ⟨this, Filter.Eventually.of_forall fun m ↦ ?_⟩
    simpa using lt_xm hb0 x m
  rw [tendsto_sub_nhds_zero_iff]
  exact tendsto_xm hb x

theorem weiestrass_slope {a : ℝ} (ha : a ∈ Set.Ioo 0 1) {b : ℕ} (hb : Odd b) (hab : 1 < a * b)
    (x : ℝ) (m : ℕ) :
    (2 / 3 - π / (a * b - 1)) * (a * b) ^ m * |xm b x m - x| ≤
    |weierstrass a b (xm b x m) - weierstrass a b x| := by
  obtain ⟨ha0, ha1⟩ : 0 < a ∧ a < 1 := by simpa using ha
  have hb0 : b ≠ 0 := by
    contrapose! hb with rfl
    simp
  have hb0' : (0 : ℝ) < b := by simpa using Nat.pos_of_ne_zero hb0
  simp_rw [weierstrass]
  obtain hsxm := (summable_weierstrass ha b (xm b x m))
  obtain hsx := (summable_weierstrass ha b x)
  obtain hsum := hsxm.sub hsx
  rw [← hsxm.tsum_sub hsx]
  simp_rw [← mul_sub] at ⊢ hsum
  rw [← hsum.sum_add_tsum_nat_add m]
  obtain hsum_shift := (summable_nat_add_iff m).mpr hsum
  refine le_trans ?_ (abs_sub_abs_le_abs_add' _ _)
  rw [sub_mul (2 / 3), sub_mul (2 / 3 * (a * b) ^ m)]
  apply sub_le_sub
  · trans a ^ m * (1 + cos ((b ^ m * x - ⌊b ^ m * x + 2⁻¹⌋) * π))
    · suffices a ^ m * (2 / 3 * b ^ m * |xm b x m - x|) ≤
          a ^ m * (1 + cos ((b ^ m * x - ⌊b ^ m * x + 2⁻¹⌋) * π)) by
        convert this using 1
        ring
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg ha0.le _)
      trans 1
      · rw [abs_eq_self.mpr (by simpa using (lt_xm hb0' _ _).le), xm]
        grw [Int.floor_le]
        have : b ^ m ≠ (0 : ℝ) := by simp [hb0]
        field_simp
        ring_nf
        rfl
      · rw [le_add_iff_nonneg_right]
        apply Real.cos_nonneg_of_mem_Icc
        rw [Set.mem_Icc]
        constructor
        · grw [Int.floor_le]
          grind
        · grw [← Int.sub_one_lt_floor]
          ring_nf
          rfl
    have h1 (n : ℕ) : cos (b ^ (n + m) * π * xm b x m) =
        - (-1) ^ (⌊b ^ m * x + 2⁻¹⌋) :=
      calc
        cos (b ^ (n + m) * π * xm b x m) =
            cos (b ^ n * ⌊b ^ m * x + 2⁻¹ + 1⌋ * π / b ^ m * b ^ m) := by
          rw [xm]
          ring_nf
        _ = cos (b ^ n * (⌊b ^ m * x + 2⁻¹⌋ + 1) * π) := by
          simp [hb0]
        _ = cos ((b ^ n * (⌊b ^ m * x + 2⁻¹⌋ + 1) : ℤ) * π) := by norm_num
        _ = (-1) ^ (b ^ n * (⌊b ^ m * x + 2⁻¹⌋ + 1)) := by rw [Real.cos_int_mul_pi]
        _ = ((-1) ^ b ^ n) ^ (⌊b ^ m * x + 2⁻¹⌋) * (-1) ^ b ^ n := by
          rw [mul_add_one, zpow_add₀ (by simp), zpow_mul]
          norm_cast
        _ = - (-1) ^ (⌊b ^ m * x + 2⁻¹⌋) := by
          simp [Odd.neg_one_pow (show Odd (b ^ n) from hb.pow)]
    have h2 (n : ℕ) : cos (b ^ (n + m) * π * x) = (-1) ^ (⌊b ^ m * x + 2⁻¹⌋) *
            cos (b ^ n * (b ^ m * x - ⌊b ^ m * x + 2⁻¹⌋) * π) :=
      calc
        cos (b ^ (n + m) * π * x) = cos (b ^ n * (b ^ m * x - ⌊b ^ m * x + 2⁻¹⌋) * π +
            (b ^ n * (⌊b ^ m * x + 2⁻¹⌋) : ℤ) * π) := by
          norm_num
          ring_nf
        _ = ((-1) ^ b ^ n) ^ (⌊b ^ m * x + 2⁻¹⌋) *
            cos (b ^ n * (b ^ m * x - ⌊b ^ m * x + 2⁻¹⌋) * π) := by
          rw [Real.cos_add_int_mul_pi, zpow_mul]
          norm_cast
        _ = (-1) ^ (⌊b ^ m * x + 2⁻¹⌋) *
            cos (b ^ n * (b ^ m * x - ⌊b ^ m * x + 2⁻¹⌋) * π) := by
          simp [Odd.neg_one_pow (show Odd (b ^ n) from hb.pow)]
    have h3 (n : ℕ) : a ^ (n + m) *
          (cos (b ^ (n + m) * π * xm b x m) - cos (b ^ (n + m) * π * x))
        = - (-1) ^ (⌊b ^ m * x + 2⁻¹⌋) *
          (a ^ (n + m) * (1 + cos (b ^ n * (b ^ m * x - ⌊b ^ m * x + 2⁻¹⌋) * π))) := by
      rw [h1, h2]
      ring
    simp_rw [h3, tsum_mul_left] at ⊢ hsum_shift
    rw [summable_mul_left_iff (by grind [zpow_ne_zero])] at hsum_shift
    rw [abs_mul, abs_neg, abs_neg_one_zpow, one_mul]
    have hnnonneg (n : ℕ) :
        0 ≤ a ^ (n + m) * (1 + cos (b ^ n * (b ^ m * x - ⌊b ^ m * x + 2⁻¹⌋) * π)) := by
      apply mul_nonneg (by positivity)
      rw [← neg_le_iff_add_nonneg']
      apply Real.neg_one_le_cos
    rw [abs_eq_self.mpr (tsum_nonneg hnnonneg)]
    rw [Summable.tsum_eq_zero_add hsum_shift]
    simpa using tsum_nonneg (fun n ↦ hnnonneg (n + 1))
  · grw [Finset.abs_sum_le_sum_abs]
    simp_rw [abs_mul, abs_pow, abs_eq_self.mpr ha0.le]
    apply le_trans <| Finset.sum_le_sum fun n _ ↦
      mul_le_mul_of_nonneg_left (Real.abs_cos_sub_cos_le _ _) (pow_nonneg ha0.le _)
    have (n : ℕ) : a ^ n * |b ^ n * π * xm b x m - b ^ n * π * x| =
        (a * b) ^ n * (π * |xm b x m - x|) := by
      simp_rw [← mul_sub, abs_mul, abs_pow, mul_pow]
      rw [abs_eq_self.mpr Real.pi_pos.le]
      rw [abs_eq_self.mpr (show (0 : ℝ) ≤ b by simp)]
      ring
    simp_rw [this, ← Finset.sum_mul]
    rw [geom_sum_eq hab.ne.symm]
    field_simp
    refine div_le_div_of_nonneg_right ?_ (sub_nonneg.mpr hab.le)
    rw [sub_one_mul]
    simp

/-- Weierstrass function is nowhere differentiable for some suitable $a$ and $b$. -/
theorem not_differentiableAt_weierstrass
    {a : ℝ} (ha : a ∈ Set.Ioo 0 1) {b : ℕ} (hb : Odd b) (hab : 3 / 2 * π + 1 < a * b) (x : ℝ) :
    ¬ DifferentiableAt ℝ (weierstrass a b) x := by
  have hb0 : b ≠ 0 := by
    contrapose! hb with rfl
    simp
  have hb0' : (0 : ℝ) < b := by simpa using Nat.pos_of_ne_zero hb0
  have hb1 : (1 : ℝ) < b := by
    contrapose! hab with hb1
    trans 1
    · apply mul_le_one₀ (ha.2.le) hb0'.le hb1
    simp [pi_nonneg]
  have hab' : 1 < a * b := lt_trans (lt_add_of_pos_left _ (mul_pos (by norm_num) pi_pos)) hab
  by_contra! h
  obtain ⟨f', h⟩ := h
  have h : Filter.Tendsto
      (fun m ↦ (xm b x m - x)⁻¹ * (weierstrass a b (xm b x m) - weierstrass a b x))
      Filter.atTop (nhds (f' 1)) := by
    convert (h.lim_real 1).comp (tendsto_inv_xm_sub_x hb1 x)
    simp
  obtain h := (continuous_abs.tendsto _).comp h
  contrapose! h
  apply not_tendsto_nhds_of_tendsto_atTop
  suffices Filter.Tendsto (fun m ↦ (2 / 3 - π / (a * b - 1)) * (a * b) ^ m)
      Filter.atTop Filter.atTop by
    rw [Filter.tendsto_atTop_atTop] at ⊢ this
    intro r
    obtain ⟨n, h⟩ := this r
    use n
    intro m hm
    rw [Function.comp_apply, abs_mul, abs_inv]
    rw [le_inv_mul_iff₀ (lt_of_le_of_ne (by simp) (by
      symm
      simpa [sub_eq_zero] using (lt_xm hb0' x _).ne.symm))]
    rw [mul_comm] -- le_inv_mul_iff₀' is broken
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)) (weiestrass_slope ha hb hab' x m)
    exact h m hm
  have hpos : 0 < 2 / 3 - π / (a * b - 1) := by
    rw [sub_pos, div_lt_iff₀ (by simpa using hab'), ← div_lt_iff₀' (by norm_num), lt_sub_iff_add_lt]
    convert hab using 1
    grind
  exact (tendsto_const_nhds_iff.mpr rfl).pos_mul_atTop hpos (tendsto_pow_atTop_atTop_of_one_lt hab')

/-- A concrete example of $a$ and $b$ to show that the condition is not vacuous. -/
theorem not_differentiableAt_weierstrass_seven (x : ℝ) :
    ¬ DifferentiableAt ℝ (weierstrass 0.9 7) x := by
  apply not_differentiableAt_weierstrass (by norm_num) (by decide)
  grw [Real.pi_lt_d2]
  norm_num

theorem exists_continuous_and_not_differentiableAt :
    ∃ f : ℝ → ℝ, Continuous f ∧ ∀ x, ¬ DifferentiableAt ℝ f x :=
  ⟨(weierstrass 0.9 7), continuous_weierstrass (by norm_num) _,
    not_differentiableAt_weierstrass_seven⟩
