/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Floris van Doorn
-/
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Analysis.SpecialFunctions.Gaussian

/-!
A loose port of https://isabelle.in.tum.de/library/HOL/HOL-Analysis/Ball_Volume.html
-/

open Classical Real NNReal ENNReal BigOperators Finset Function MeasureTheory
set_option autoImplicit true

-- move to Data.Finset.Basic
theorem Finset.constant_of_eq_insert {α β : Type _} (f : Finset α → β)
    (H : ∀ {s : Finset α}, ∀ {i}, i ∉ s → f (insert i s) = f s) (s t : Finset α) :
    f s = f t := by
  have h1 : ∀ {s : Finset α}, ∀ {i}, f (insert i s) = f s := by
    intros s i
    by_cases hi : i ∈ s <;> simp [*]
  have h2 : ∀ s t, f (s ∪ t) = f s := by
    intro s t
    induction' t using Finset.induction with i t _ ih
    · simp
    · calc f (s ∪ insert i t) = f (insert i (s ∪ t)) := by rw [Finset.union_insert]
        _ = f (s ∪ t) := h1
        _ = f s := by rw [ih]
  calc f s = f (s ∪ t) := by rw [h2]
      _ = f (t ∪ s) := by rw [union_comm]
      _ = f t := by rw [h2]

noncomputable section

@[simp, norm_cast]
theorem Nat.cast_le_zero [OrderedSemiring R] [CharZero R] {n : ℕ} :
    (n : R) ≤ 0 ↔ n = 0 := by rw [← cast_zero, cast_le, le_zero_iff]

-- protect NNReal.inv_lt_one_iff and ENNReal.one_lt_two (also write linter for this)

-- unused
@[simp]
theorem Nat.floor_half [LinearOrderedField α] [FloorRing α] :
    ⌊(2⁻¹ : α)⌋₊ = 0 := by
  simp [floor_eq_zero, _root_.inv_lt_one_iff, _root_.one_lt_two]

attribute [simp] Real.Gamma_one_half_eq

@[simp]
theorem Real.Gamma_two_inv : Real.Gamma 2⁻¹ = sqrt π := by
  simp [← Real.Gamma_one_half_eq]

@[simp]
theorem Real.Gamma_three_div_two : Real.Gamma (3 / 2) = sqrt π / 2 := by
  calc Gamma (3 / 2) =
        Gamma (2⁻¹ + 1) := by norm_num
    _ = sqrt π / 2 := by simp [Gamma_add_one, div_eq_inv_mul]

/-- The beta function on `ℝ`, defined as `Β(a,b) := Γ(a)Γ(b)/Γ(a + b)`. -/
def Real.Beta (a b : ℝ) : ℝ := Gamma a * Gamma b / Gamma (a + b)

@[simp]
lemma Real.Beta_add_one {a b : ℝ} (hb : b ≠ 0) (hab : a + b ≠ 0) :
    a.Beta (b + 1) = b / (a + b) * a.Beta b := by
  simp [Beta, ← add_assoc, Gamma_add_one, hab, hb]
  field_simp
  ring

lemma Real.Beta_nonneg {a b : ℝ} (hb : 0 ≤ a) (hab : 0 ≤ b) : 0 ≤ Beta a b := by
  have : 0 ≤ a + b := by positivity
  apply div_nonneg; apply mul_nonneg
  all_goals
    apply Gamma_nonneg_of_nonneg; assumption

/-- The gamma function on the nonnegative reals `ℝ≥0`. -/
def NNReal.Gamma (x : ℝ≥0) : ℝ≥0 := ⟨Real.Gamma x, Real.Gamma_nonneg_of_nonneg x.property⟩

@[simp]
theorem NNReal.coe_Gamma {x : ℝ≥0} : (NNReal.Gamma x : ℝ) = Real.Gamma x := rfl

theorem NNReal.Gamma_pos_of_pos {x : ℝ≥0} (hx : 0 < x) : 0 < NNReal.Gamma x := by
  rw [← NNReal.coe_lt_coe]
  simp
  exact Real.Gamma_pos_of_pos hx

theorem NNReal.Gamma_half : NNReal.Gamma (1 / 2) = sqrt NNReal.pi := by
  ext
  simp

@[simp]
theorem NNReal.Gamma_three_div_two : NNReal.Gamma (3 / 2) = sqrt NNReal.pi / 2 := by
  ext
  simp

@[simp]
theorem NNReal.Gamma_one : NNReal.Gamma 1 = 1 := Subtype.ext Real.Gamma_one

/-- The beta function on the nonnegative reals `ℝ≥0`. -/
def NNReal.Beta (a b : ℝ≥0) : ℝ≥0 := Gamma a * Gamma b / Gamma (a + b)

@[simp]
lemma NNReal.coe_Beta (a b : ℝ≥0) : (a.Beta b : ℝ) = (a : ℝ).Beta b := rfl

@[simp]
lemma NNReal.Beta_add_one {a b : ℝ≥0} (hb : 0 < b) :
    a.Beta (b + 1) = b / (a + b) * a.Beta b := by
  ext
  have h1 : 0 < (b : ℝ) := hb
  have h2 : 0 < (a + b : ℝ) := h1.trans_le <| le_add_of_nonneg_left <| coe_nonneg a
  simp [Real.Beta_add_one h1.ne' h2.ne']

@[simp]
theorem integral_cos_pow_eq_beta : (n : ℕ) →
    ∫ θ in (-(π / 2))..(π / 2), cos θ ^ n = Real.Beta (1 / 2) ((n + 1) / 2)
  | 0 => by
    simp [Real.Beta, neg_div]
    norm_num
    simp [Real.Gamma_one, ← pow_two]
    rw [Real.sq_sqrt]
    positivity
  | 1 => by
    simp [Real.Beta, Real.Gamma_one]
    norm_num
    simp [div_div_eq_mul_div]
    rw [mul_comm]
    rw [mul_div_assoc]
    simp
    rw [div_self]
    positivity
  | (n + 2) => by
    simp [integral_cos_pow, integral_cos_pow_eq_beta n]
    simp_rw [add_right_comm (n : ℝ) 2 1, div_add_same <| two_ne_zero (α := ℝ)]
    simp (discharger := positivity) [Real.Beta_add_one]
    field_simp
    ring_nf
    simp

theorem integral_cos_pow_eq_beta' (n : ℕ) :
    ∫ θ in (-(π / 2))..(π / 2), cos θ ^ (n + 1) = Real.Beta (1 / 2) (n / 2 + 1) := by
  norm_num
  congr
  rw [add_assoc, add_div]
  simp

-- unused
theorem lintegral_cos_pow_eq_beta (n : ℕ) :
    ∫⁻ θ in Set.Icc (-(π / 2) : ℝ) (π / 2 : ℝ), .ofReal (cos θ ^ n) =
    NNReal.Beta (1 / 2) ((n + 1) / 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le, integral_cos_pow_eq_beta, ← ofReal_coe_nnreal]
  · rfl
  · simp [neg_le_self_iff]; positivity
  · exact Continuous.integrableOn_Icc <| continuous_cos.pow _
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    apply Filter.eventually_of_forall
    intro x hx
    simp
    apply pow_nonneg <| cos_nonneg_of_mem_Icc hx

-- unused
theorem lintegral_cos_pow_eq_beta' (n : ℕ) :
    ∫⁻ θ in Set.Icc (-(π / 2) : ℝ) (π / 2 : ℝ), .ofReal (cos θ ^ (n + 1)) =
    NNReal.Beta (1 / 2) (n / 2 + 1) := by
  rw [lintegral_cos_pow_eq_beta]
  norm_num
  congr
  rw [add_assoc, add_div]
  norm_num

/-- Auxiliary function, defined as `t ^ (n / 2)` for `t ≥ 0`. -/
def I (n : ℕ) (t : ℝ) : ℝ≥0 := if ht : 0 ≤ t then (⟨t, ht⟩ ^ ((n:ℝ) / 2)) else 0

@[simp] theorem I_zero (t : ℝ) : I 0 t = if 0 ≤ t then 1 else 0 := by
  simp [I]

@[simp] theorem indicator_I : (Set.Ici (0 : ℝ)).indicator (I n ·) = I n := by
  ext; simp (config := {contextual := true}) [not_le_of_lt, I]

theorem I_apply_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : I n t = (⟨t, ht⟩ ^ ((n:ℝ) / 2)) := by
  rw [I, dif_pos]

theorem I_apply_nnreal (n : ℕ) (t : ℝ≥0) : I n t = t ^ ((n:ℝ)/2) := by
  rw [I_apply_nonneg]
  rfl

@[simp] theorem I_apply_sq_nnreal (n : ℕ) (t : ℝ≥0) : I n ((t:ℝ) ^ 2) = t ^ n := by
  ext
  simp [I]
  rw [← Real.rpow_two, ← Real.rpow_mul]
  · simp [mul_div_cancel']
  · exact NNReal.zero_le_coe

@[measurability]
theorem measurable_I {n : ℕ} : Measurable (I n) := by
  have hf : Measurable (fun x : ℝ≥0 ↦ x ^ ((n:ℝ) / 2)) := measurable_id.pow_const _
  exact hf.dite measurable_const measurableSet_Ici

/-- The expected volume of the unit ball, as a function of dimension. -/
def B (n : ℕ) : ℝ≥0 := NNReal.pi ^ ((n:ℝ) / 2) / NNReal.Gamma (n / 2 + 1)

@[simp] theorem B_zero : B 0 = 1 := by simp [B]

-- some automation broken here, track it down
theorem B_succ (n : ℕ) : B (n + 1) = B n * NNReal.Beta (1 / 2) (n / 2 + 1) := by
  dsimp only [B, NNReal.Beta]
  push_cast
  simp only [add_div]
  ring_nf
  have h₁ : 0 < NNReal.Gamma (1 + n / 2) := NNReal.Gamma_pos_of_pos (by positivity)
  have h₂ : 0 < NNReal.Gamma (1 + n / 2 + 1 / 2) := NNReal.Gamma_pos_of_pos (by positivity)
  set X := NNReal.Gamma (1 + n / 2)
  set Y := NNReal.Gamma (1 + n / 2 + 1 / 2)
  clear_value X Y
  field_simp [h₁.ne', h₂.ne', NNReal.Gamma_half]
  rw [add_div, NNReal.rpow_add, NNReal.sqrt_eq_rpow]
  · ring
  · apply Subtype.ne_of_val_ne
    dsimp
    exact Real.pi_ne_zero

lemma integral_sub_sq_sqrt_pow {R : ℝ} (hR : 0 ≤ R) :
    ∫ x in (-R)..R, (Real.sqrt (R ^ 2 - x ^ 2)) ^ n =
    ∫ θ in (-(π / 2))..π / 2, cos θ ^ (n + 1) * R ^ (n + 1) := by
  let a := -(π / 2)
  let b := π / 2
  have h1 : ∀ x ∈ Set.uIcc a b, HasDerivAt (R * sin ·) (R * cos x) x :=
    fun x _ ↦ hasDerivAt_sin x |>.const_mul R
  have h2 : ContinuousOn (R * cos ·) (Set.uIcc a b) :=
    continuous_const.mul continuous_cos |>.continuousOn
  have h3 : Continuous <| fun x ↦ (Real.sqrt (R ^ 2 - x ^ 2)) ^ n :=
    continuous_const.sub (continuous_id.pow 2) |>.sqrt.pow n
  have h4 : ∀ a b : ℝ, a - a * b = a * (1 - b) := by intros; ring
  calc ∫ x in (-R)..R, (Real.sqrt (R ^ 2 - x ^ 2)) ^ n
      = ∫ x in (R * sin a)..(R * sin b), (Real.sqrt (R ^ 2 - x ^ 2)) ^ n := by
        simp
    _ = ∫ θ in a..b, (Real.sqrt (R ^ 2 - (R * sin θ) ^ 2)) ^ n * (R * cos θ) :=
        intervalIntegral.integral_comp_mul_deriv h1 h2 h3 |>.symm
    _ = ∫ θ in a..b, cos θ ^ (n + 1) * R ^ (n + 1) := by
        simp_rw [mul_pow, h4, Real.sqrt_mul <| sq_nonneg _, sqrt_sq hR]
        apply intervalIntegral.integral_congr
        intros x hx
        dsimp
        rw [mul_pow]
        rw [Set.uIcc_of_le] at hx
        · rw [← cos_eq_sqrt_one_sub_sin_sq hx.1 hx.2] -- lemma: wrong = order, wrong hyp statement
          ring
        simp [neg_le_self_iff]; positivity

/-- auxiliary one-variable integral -/
theorem lintegral_I_sub_sq_nnreal (n : ℕ) (R : ℝ≥0) :
    ∫⁻ x : ℝ, I n (R ^ 2 - x ^ 2) = NNReal.Beta (1 / 2) (n / 2 + 1) * (R:ℝ≥0∞) ^ (n + 1) := by
  calc ∫⁻ x : ℝ, I n (R ^ 2 - x ^ 2)
      = ∫⁻ x in Set.Icc (-R : ℝ) (R : ℝ), .ofReal ((Real.sqrt (R ^ 2 - x ^ 2)) ^ n) := by
        rw [← lintegral_indicator _ measurableSet_Icc]
        congr with x
        simp [Set.indicator, I, sq_le_sq, abs_le]
        split_ifs with h; swap; rfl
        rw [← ofReal_coe_nnreal]
        congr
        simp
        rw [rpow_div_two_eq_sqrt]
        · simp
        · simp [sq_le_sq, abs_le, h]
    _ = .ofReal (∫ x in (-R)..R, (Real.sqrt ((R : ℝ) ^ 2 - x ^ 2)) ^ n) := by
        rw [← ofReal_integral_eq_lintegral_ofReal, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le]
        · simp [neg_le_self_iff]
        · apply Continuous.integrableOn_Icc
          exact continuous_const.sub (continuous_id.pow 2) |>.sqrt.pow n
        · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
          exact Filter.eventually_of_forall fun _ _ ↦ pow_nonneg (sqrt_nonneg _) _
        -- x = R * sin θ
    _ = .ofReal (∫ θ in (-(π / 2))..π / 2, cos θ ^ (n + 1) * R ^ (n + 1)) := by
        simp_rw [integral_sub_sq_sqrt_pow R.coe_nonneg]
    _ = .ofReal ((∫ θ in (-(π / 2))..π / 2, cos θ ^ (n + 1)) * R ^ (n + 1)) := by
        rw [intervalIntegral.integral_mul_const]
    _ = NNReal.Beta (1 / 2) (n / 2 + 1) * (R:ℝ≥0∞) ^ (n + 1) := by
        rw [integral_cos_pow_eq_beta', ← ofReal_coe_nnreal]
        rw [NNReal.coe_Beta, ofReal_mul]
        simp
        rw [ENNReal.ofReal_pow]
        simp
        positivity
        apply Real.Beta_nonneg (by positivity) (by positivity)

-- some automation broken here, track it down
set_option linter.unreachableTactic false in
theorem lintegral_I_sub_sq (n : ℕ) (c : ℝ) :
    ∫⁻ x : ℝ, I n (c - x ^ 2) = NNReal.Beta (1 / 2) (n / 2 + 1) * I (n + 1) c := by
  by_cases h : (0:ℝ) ≤ c
  · let r : ℝ≥0 := ⟨sqrt c, sqrt_nonneg _⟩
    have hr : r ^ 2 = c := Real.sq_sqrt h
    clear_value r
    rw [← hr, lintegral_I_sub_sq_nnreal, ← NNReal.coe_pow, I_apply_nnreal]
    norm_cast
    push_cast
    have : (r ^ 2) ^ ((((n : ℝ) + 1) / 2)) = r ^ n * r := by
      rw [← NNReal.rpow_two, ← NNReal.rpow_mul]
      simp (discharger := positivity) [mul_div_cancel', NNReal.rpow_add']
    rw [this]
    ring
  · have h₁ : (fun t ↦ ↑(I n (c - t ^ 2))) = (fun _ ↦ 0 : ℝ → ℝ≥0∞) := by
      ext1 t
      dsimp
      rw [I, dif_neg]
      · simp
      · have : (0:ℝ) ≤ t ^ 2 := by positivity
        linarith
    have h₂ : I (n + 1) c = 0 := by
      rw [I, dif_neg h]
    simp [h₁, h₂, -compl_insert, -mul_eq_zero, -zero_eq_mul]

variable [Fintype ι]

/-- The function that we will integrate in below. -/
def A (R : ℝ) (s : Finset ι) (x : ι → ℝ) : ℝ≥0∞ :=
  B s.card * I s.card (R ^ 2 - ∑ j in sᶜ, x j ^ 2)

theorem measurable_A (R : ℝ) (s : Finset ι) : Measurable (A R s) := by
  refine measurable_const.mul <| measurable_coe_nnreal_ennreal.comp ?_
  refine measurable_I.comp <| measurable_const.sub ?_
  exact measurable_sum _ (fun i _ ↦ Measurable.pow_const (measurable_pi_apply _) _)

theorem marginal_A_eq_marginal_A_insert {R : ℝ} {s : Finset ι} {i : ι} (hi : i ∉ s) :
    (∫⋯∫⁻_(insert i s)ᶜ, A R (insert i s)) = (∫⋯∫⁻_sᶜ, A R s) := by
  symm
  have hi' : i ∉ (insert i s)ᶜ := not_mem_compl.mpr <| mem_insert_self i s
  simp_rw [← insert_compl_insert hi, lmarginal_insert' _ (measurable_A ..) hi']
  congr! 2 with _ x
  calc ∫⁻ t, B s.card * I s.card (R ^ 2 - ∑ j in sᶜ, update x i t j ^ 2)
      = ∫⁻ (t : ℝ), B s.card * I s.card ((R ^ 2 - ∑ j in (insert i s)ᶜ, x j ^ 2) - t ^ 2) := by
          congr! 2 with t
          have H : ∀ j ∈ (insert i s)ᶜ, update x i t j ^ 2 = x j ^ 2 := by
            intro j hj
            have hij : j ≠ i := by aesop
            rw [update_noteq hij]
          simp only [← insert_compl_insert hi, sum_insert hi', update_same, sum_congr rfl H]
          ring_nf
    _ = B (insert i s).card * I (insert i s).card (R ^ 2 - ∑ j in (insert i s)ᶜ, x j ^ 2) := by
          rw [lintegral_const_mul, card_insert_of_not_mem hi, lintegral_I_sub_sq, B_succ]
          · norm_cast
            ring
          · refine measurable_coe_nnreal_ennreal.comp <| measurable_I.comp ?_
            exact measurable_const.sub <| measurable_id.pow_const _

theorem marginal_A_emptyset_eq_marginal_A_univ (R : ℝ) :
    (∫⋯∫⁻_∅ᶜ, A R ∅) = ∫⋯∫⁻_(univ : Finset ι)ᶜ, A R univ := by
  refine constant_of_eq_insert (fun s : Finset ι ↦ ∫⋯∫⁻_sᶜ, A R s) ?_ ∅ univ
  apply marginal_A_eq_marginal_A_insert

/-- The volume of a Euclidean ball of radius `R` in the space `ι → ℝ`, equipped with the product
measure, is `B (Fintype.card ι) * R ^ Fintype.card ι`. -/
theorem volume_ball (R : ℝ≥0) :
    volume {x : ι → ℝ | ∑ j, x j ^ 2 ≤ (R : ℝ) ^ 2} = B (Fintype.card ι) * R ^ Fintype.card ι := by
  calc volume {x : ι → ℝ | ∑ j, x j ^ 2 ≤ (R : ℝ) ^ 2}
      = ∫⁻ x : ι → ℝ, Set.indicator {y : ι → ℝ | (0 : ℝ) ≤ R ^ 2 - ∑ i : ι, y i ^ 2} 1 x := by
          convert (lintegral_indicator_const _ 1).symm
          · simp
          · refine measurableSet_le measurable_const <| measurable_const.sub ?_
            exact measurable_sum _ (fun i _ ↦ Measurable.pow_const (measurable_pi_apply _) _)
    _ = ∫⁻ x : ι → ℝ, I 0 (R ^ 2 - ∑ i : ι, x i ^ 2) := by simp [apply_ite, Set.indicator_apply]
    _ = B (Fintype.card ι) * R ^ Fintype.card ι := by
          simpa [A, lmarginal_univ, lmarginal_empty, card_univ, -I_zero] using
            congr_fun (marginal_A_emptyset_eq_marginal_A_univ R) (0 : ι → ℝ)
