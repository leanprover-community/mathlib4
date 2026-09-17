/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Analysis.SpecialFunctions.ArithmeticGeometricMean
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# An integral related to the arithmetic-geometric mean

For $a,b>0$ consider the improper integral
$$I(a,b) = \int_0^\infty \frac{dx}{\sqrt{(x^2+a^2)(x^2+b^2)}}.$$
Then making the substitution $x = t+\sqrt{t^2+ab}$ yields, after rearranging,
$$I(a,b) = \int_{-\infty}^\infty \frac{dx}{2\sqrt{(x^2+ab)(x^2+((a+b)/2)^2)}}
= I(\sqrt{ab},(a+b)/2).$$
As shown in `Mathlib/Analysis/SpecialFunctions/AGM/Basic.lean`, iterating this transformation drives
both arguments towards the arithmetic-geometric mean (AGM) of $a$ and $b$, so we have
$$I(a,b)=I(\operatorname{agm}(a,b),\operatorname{agm}(a,b))=\frac{\pi/2}{\operatorname{agm}(a,b)}$$
where the second equality follows from an elementary integral.
This establishes an important link between the AGM and complete elliptic integrals.
-/

@[expose] public section

open MeasureTheory Real

/-- The elliptic integral related to the arithmetic-geometric mean. -/
noncomputable def agmIntegral (a b : ℝ) : ℝ :=
  ∫ x in Set.Ioi 0, (√((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)))⁻¹

variable {a b : ℝ}

lemma integrableOn_agmIntegrand_Ioi_of_pos (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun x ↦ (√((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)))⁻¹) (Set.Ioi 0) := by
  apply Integrable.mono' (g := fun x ↦ (x ^ 2 + min a b ^ 2)⁻¹)
  · have mnz : min a b ≠ 0 := by positivity
    conv =>
      enter [1, x]
      rw [← mul_div_cancel₀ x mnz, mul_pow, ← mul_add_one, mul_inv, add_comm]
    exact ((integrable_inv_one_add_sq.comp_div mnz).const_mul _).restrict
  · exact (AEMeasurable.aestronglyMeasurable (by fun_prop)).restrict
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    rw [norm_of_nonneg (by positivity), inv_le_inv₀ (by positivity) (by positivity),
      ← sqrt_mul_self (show 0 ≤ x ^ 2 + min a b ^ 2 by positivity)]
    gcongr <;> grind

lemma agmIntegral_comm : agmIntegral a b = agmIntegral b a := by
  simp [agmIntegral, mul_comm]

/-- The integral diverges (and thus takes the junk value of 0 in Lean) when `a = 0`. -/
@[simp]
lemma agmIntegral_zero_left : agmIntegral 0 b = 0 := by
  have cong (x) (mx : x ∈ Set.Ioi 0) :
      (√((x ^ 2 + 0 ^ 2) * (x ^ 2 + b ^ 2)))⁻¹ = (x * √(x ^ 2 + b ^ 2))⁻¹ := by
    rw [sq 0, mul_zero, add_zero, sqrt_mul (sq_nonneg _), sqrt_sq mx.le]
  rw [agmIntegral, setIntegral_congr_fun measurableSet_Ioi cong]
  apply integral_undef (?_ : ¬IntegrableOn _ _ _)
  by_contra! h
  replace h := h.mono_set (Set.Ioc_subset_Ioi_self (a := 1))
  replace h : IntegrableOn (fun a ↦ a⁻¹ * (√(1 + b ^ 2))⁻¹) (Set.Ioc 0 1) := by
    apply h.mono' (measurable_inv.aestronglyMeasurable.restrict.mul_const _)
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun x ⟨hx₁, hx₂⟩ ↦ ?_
    rw [← mul_inv, norm_inv, norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
    bound
  replace h : IntegrableOn _ _ _ := h.mul_const √(1 + b ^ 2)
  conv at h =>
    enter [1, x]
    rw [inv_mul_cancel_right₀ (by positivity)]
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
  simp at h

/-- The integral diverges (and thus takes the junk value of 0 in Lean) when `b = 0`. -/
@[simp]
lemma agmIntegral_zero_right : agmIntegral a 0 = 0 := by
  rw [agmIntegral_comm, agmIntegral_zero_left]

/-- The limiting, special case of `agmIntegral`. -/
theorem agmIntegral_self (ha : 0 ≤ a) : agmIntegral a a = π / 2 / a := by
  rcases ha.eq_or_lt with rfl | ha; · simp
  unfold agmIntegral
  conv_lhs =>
    enter [2, x]
    rw [← sq, sqrt_sq (by positivity)]
  have l₁ (x) (hx : x ∈ Set.Ioi 0) : HasDerivWithinAt (a * ·) a (Set.Ioi 0) x :=
    (hasDerivAt_const_mul a).hasDerivWithinAt
  have l₂ : MonotoneOn (a * ·) (Set.Ioi 0) :=
    (monotone_mul_left_of_nonneg ha.le).monotoneOn _
  rw [← Set.image_const_mul_Ioi_zero ha,
    integral_image_eq_integral_deriv_smul_of_monotoneOn measurableSet_Ioi l₁ l₂]
  conv_lhs =>
    enter [2, x]
    rw [mul_pow, ← mul_add_one, mul_inv, smul_eq_mul, ← mul_assoc, ← div_eq_mul_inv a, sq,
      div_self_mul_self', add_comm]
  rw [integral_const_mul, integral_Ioi_inv_one_add_sq, arctan_zero]
  ring

/-- **Landen's transformation** for `agmIntegral`. -/
theorem agmIntegral_eq_agmIntegral_gm_am (ha : 0 ≤ a) (hb : 0 ≤ b) :
    agmIntegral a b = agmIntegral √(a * b) ((a + b) / 2) := by
  -- Handle degenerate cases
  rcases ha.eq_or_lt with rfl | ha; · simp
  rcases hb.eq_or_lt with rfl | hb; · simp
  -- Define prerequisites for the substitution
  let f (t : ℝ) := t + √(t ^ 2 + a * b)
  let f' (t : ℝ) := f t / √(t ^ 2 + a * b)
  let g (x : ℝ) := (√((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)))⁻¹
  have pf (t) : 0 < f t := by
    rcases le_or_gt 0 t with ht | ht; · positivity
    rw [← neg_lt_iff_pos_add']
    nth_rw 1 [← abs_of_nonpos ht.le, ← sqrt_sq_eq_abs, ← add_zero (t ^ 2)]
    gcongr
    positivity
  have df (t) : HasDerivAt f (f' t) t := by
    unfold f'
    rw [← div_add_one (by positivity), add_comm]
    apply (hasDerivAt_id' _).fun_add
    rw [← mul_div_mul_left _ _ two_ne_zero]
    refine ((HasDerivAt.add_const _) ?_).sqrt (by positivity)
    convert hasDerivAt_pow 2 t using 1
    ring
  have mf : StrictMono f := strictMono_of_hasDerivAt_pos df fun t ↦ by positivity [pf t]
  have rf : f '' Set.univ = Set.Ioi 0 := by
    ext x
    rw [Set.image_univ, Set.mem_range, Set.mem_Ioi]
    refine ⟨fun ⟨t, ht⟩ ↦ ht.symm ▸ (pf _), fun hx ↦ ?_⟩
    use (x ^ 2 - a * b) / (2 * x)
    unfold f
    rw [div_pow, div_add' _ (a * b) _ (by positivity),
      show ((x ^ 2 - a * b) ^ 2 + a * b * (2 * x) ^ 2) = (x ^ 2 + a * b) ^ 2 by ring, ← div_pow,
      sqrt_sq (by positivity), ← add_div, sub_add_add_cancel, ← two_mul,
      mul_div_mul_left _ _ two_ne_zero, sq, mul_self_div_self]
  -- Make the substitution, whose LHS is simply `agmIntegral a b`
  change ∫ x in Set.Ioi 0, g x = _
  rw [← rf, integral_image_eq_integral_deriv_smul_of_monotoneOn MeasurableSet.univ
    (fun t _ ↦ hasDerivWithinAt_univ.mpr (df t)) (monotoneOn_univ.mpr mf.monotone) g]
  -- Simplify the post-substitution integral
  have rearr₁ (t) : (f t * (t - √(t ^ 2 + a * b))) ^ 2 = (a * b) ^ 2 := by
    rw [← sq_sub_sq, sq_sqrt (by positivity)]
    ring
  have rearr₂ (t) : f t ^ 2 + (t - √(t ^ 2 + a * b)) ^ 2 = 4 * t ^ 2 + 2 * a * b := by
    rw [add_sq, sub_sq, sq_sqrt (by positivity)]
    ring
  have rearr₃ (t) :
      (f t ^ 2 + a ^ 2) * (f t ^ 2 + b ^ 2) = (2 * f t) ^ 2 * (t ^ 2 + ((a + b) / 2) ^ 2) := by
    rw [show (f t ^ 2 + a ^ 2) * (f t ^ 2 + b ^ 2) =
      f t ^ 2 * (f t ^ 2 + a ^ 2 + b ^ 2) + (a * b) ^ 2 by ring, ← rearr₁ t, mul_pow, ← mul_add,
      add_right_comm, add_right_comm (f t ^ 2), rearr₂]
    ring
  unfold f' g
  conv_lhs =>
    enter [2, t]
    rw [rearr₃, sqrt_mul (sq_nonneg _), sqrt_sq (by positivity [pf t]), smul_eq_mul, mul_inv,
      div_eq_mul_inv, mul_mul_mul_comm, ← mul_inv, ← sqrt_mul (by positivity),
      ← div_eq_mul_inv (f t), ← div_div, div_div_cancel_left' (pf t).ne']
  rw [integral_const_mul, inv_mul_eq_div, div_eq_iff two_ne_zero, Measure.restrict_univ]
  -- The current LHS integral is an even integrand over all ℝ,
  -- so it is twice the integral over (0, ∞), i.e. the RHS integral
  rw [mul_comm _ 2, agmIntegral, ← integral_comp_abs]
  congr! 4 with _ t
  rw [sq_abs, sq_sqrt (by positivity)]

lemma continuousOn_agmIntegral :
    ContinuousOn (fun p ↦ agmIntegral p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioi 0) := by
  rintro ⟨a, b⟩ ⟨ha : 0 < a, hb : 0 < b⟩
  apply continuousWithinAt_of_dominated (bound := fun x ↦ (x ^ 2 + (min a b / 2) ^ 2)⁻¹)
  · exact eventually_nhdsWithin_of_forall fun _ _ ↦
      (AEMeasurable.aestronglyMeasurable (by fun_prop)).restrict
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨min a b / 2, by positivity,
      fun (a', b') dp mp ↦ ae_restrict_of_forall_mem measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_⟩
    simp_rw [Prod.dist_eq, max_lt_iff, dist_eq] at dp
    rw [norm_of_nonneg (by positivity), inv_le_inv₀ (by positivity) (by positivity),
      ← sqrt_mul_self (show 0 ≤ t ^ 2 + (min a b / 2) ^ 2 by positivity)]
    gcongr <;> grind
  · have mnz : min a b / 2 ≠ 0 := by positivity
    conv =>
      enter [1, x]
      rw [← mul_div_cancel₀ x mnz, mul_pow, ← mul_add_one, mul_inv, add_comm]
    exact ((integrable_inv_one_add_sq.comp_div mnz).const_mul _).restrict
  · exact Filter.Eventually.of_forall fun _ ↦ ContinuousWithinAt.inv₀ (by fun_prop) (by positivity)

lemma strictAntiOn_agmIntegral :
    StrictAntiOn (fun p ↦ agmIntegral p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioi 0) := by
  rintro ⟨a₁, b₁⟩ ⟨ha₁ : 0 < a₁, hb₁ : 0 < b₁⟩ ⟨a₂, b₂⟩ ⟨ha₂ : 0 < a₂, hb₂ : 0 < b₂⟩ l
  simp only [Prod.lt_iff, agmIntegral] at l ⊢
  have int₁ := integrableOn_agmIntegrand_Ioi_of_pos ha₁ hb₁
  have int₂ := integrableOn_agmIntegrand_Ioi_of_pos ha₂ hb₂
  rw [← sub_pos, ← integral_sub int₁ int₂]
  refine (integral_pos_iff_support_of_nonneg (fun x ↦ ?_) (int₁.sub int₂)).mpr ?_
  · simp only [Pi.zero_apply, Pi.sub_apply, sub_nonneg]
    gcongr <;> grind
  · rw [Measure.restrict_apply' measurableSet_Ioi, Pi.sub_def]
    suffices Set.Ioi 0 ⊆ Function.support fun x ↦
        (√((x ^ 2 + a₁ ^ 2) * (x ^ 2 + b₁ ^ 2)))⁻¹ - (√((x ^ 2 + a₂ ^ 2) * (x ^ 2 + b₂ ^ 2)))⁻¹ by
      simp [Set.inter_eq_right.mpr this]
    intro x (hx : 0 < x)
    rw [Function.mem_support]
    apply ne_of_gt
    rw [sub_pos]
    gcongr (√(?_))⁻¹
    obtain ⟨o₁, o₂⟩ | ⟨o₁, o₂⟩ := l
    · calc
        _ < (x ^ 2 + a₂ ^ 2) * (x ^ 2 + b₁ ^ 2) := by gcongr
        _ ≤ _ := by gcongr
    · calc
        _ ≤ (x ^ 2 + a₂ ^ 2) * (x ^ 2 + b₁ ^ 2) := by gcongr
        _ < _ := by gcongr

open NNReal

variable {a b : ℝ≥0}

lemma agmIntegral_eq_agmIntegral_agmSequences {n : ℕ} :
    agmIntegral a b = agmIntegral (agmSequences a b n).1 (agmSequences a b n).2 := by
  induction n with
  | zero =>
    rw [agmIntegral_eq_agmIntegral_gm_am (coe_nonneg a) (coe_nonneg b)]
    simp [agmSequences_zero]
  | succ n ih =>
    rw [ih, agmIntegral_eq_agmIntegral_gm_am (coe_nonneg _) (coe_nonneg _),
      agmSequences_succ', coe_sqrt, NNReal.coe_mul]
    rfl

open Filter Topology in
/-- The fundamental relation between `agmIntegral` and `agm`. -/
theorem agmIntegral_eq_pi_div_two_div_agm : agmIntegral a b = π / 2 / agm a b := by
  by_cases h : a = 0 ∨ b = 0
  · obtain rfl | rfl := h <;> simp
  rw [not_or, ← Ne, ← pos_iff_ne_zero, ← Ne, ← pos_iff_ne_zero] at h
  let f (n : ℕ) : ℝ × ℝ := ((agmSequences a b n).1, (agmSequences a b n).2)
  let g (p : ℝ × ℝ) : ℝ := agmIntegral p.1 p.2
  suffices Tendsto (g ∘ f) atTop (𝓝 (agmIntegral (agm a b) (agm a b))) by
    rw [← agmIntegral_self (coe_nonneg _)]
    refine tendsto_nhds_unique ?_ this
    change Tendsto (fun n ↦ agmIntegral (agmSequences a b n).1 (agmSequences a b n).2) _ _
    simp [← agmIntegral_eq_agmIntegral_agmSequences]
  have tt : Tendsto f atTop (𝓝 (agm a b, agm a b)) :=
    (Prod.tendsto_iff _ _).mpr
      ⟨tendsto_coe.mpr tendsto_agmSequences_fst_agm, tendsto_coe.mpr tendsto_agmSequences_snd_agm⟩
  refine (continuousOn_agmIntegral.continuousAt ?_).tendsto.comp tt
  exact prod_mem_nhds (Ioi_mem_nhds (agm_pos h.1 h.2)) (Ioi_mem_nhds (agm_pos h.1 h.2))

theorem agm_eq_pi_div_two_div_agmIntegral : agm a b = π / 2 / agmIntegral a b := by
  by_cases h : a = 0 ∨ b = 0
  · obtain rfl | rfl := h <;> simp
  rw [not_or, ← Ne, ← pos_iff_ne_zero, ← Ne, ← pos_iff_ne_zero] at h
  have e := @agmIntegral_eq_pi_div_two_div_agm a b
  have agmp : (0 : ℝ) < agm a b := agm_pos h.1 h.2
  have aip : 0 < agmIntegral a b := by
    rw [e]
    positivity
  rwa [eq_div_iff aip.ne', mul_comm, ← eq_div_iff agmp.ne']

theorem strictMonoOn_agm : StrictMonoOn (fun p ↦ agm p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioi 0) := by
  rintro ⟨a₁, b₁⟩ ⟨ha₁ : 0 < a₁, hb₁ : 0 < b₁⟩ ⟨a₂, b₂⟩ ⟨ha₂ : 0 < a₂, hb₂ : 0 < b₂⟩ l
  simp_rw [← coe_lt_coe, agm_eq_pi_div_two_div_agmIntegral]
  apply div_lt_div_of_pos_left (by bound) ?_ ?_
  · rw [agmIntegral_eq_pi_div_two_div_agm]
    have agmp := agm_pos ha₂ hb₂
    positivity
  · have h₁ : (a₁.toReal, b₁.toReal) ∈ Set.Ioi 0 ×ˢ Set.Ioi 0 := by simp [ha₁, hb₁]
    have h₂ : (a₂.toReal, b₂.toReal) ∈ Set.Ioi 0 ×ˢ Set.Ioi 0 := by simp [ha₂, hb₂]
    exact strictAntiOn_agmIntegral h₁ h₂ l

/-- The AGM is monotone in both arguments. -/
theorem monotone_agm : Monotone fun (p : ℝ≥0 × ℝ≥0) ↦ agm p.1 p.2 := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨l₁, l₂⟩
  dsimp only at l₁ l₂ ⊢
  by_cases h₁ : a₁ = 0 ∨ b₁ = 0
  · obtain rfl | rfl := h₁ <;> simp
  rw [not_or, ← Ne, ← pos_iff_ne_zero, ← Ne, ← pos_iff_ne_zero] at h₁
  have h₂ : 0 < a₂ ∧ 0 < b₂ := ⟨h₁.1.trans_le l₁, h₁.2.trans_le l₂⟩
  have m₁ : (a₁, b₁) ∈ Set.Ioi 0 ×ˢ Set.Ioi 0 := by simp [h₁.1, h₁.2]
  have m₂ : (a₂, b₂) ∈ Set.Ioi 0 ×ˢ Set.Ioi 0 := by simp [h₂.1, h₂.2]
  apply strictMonoOn_agm.monotoneOn m₁ m₂ ⟨l₁, l₂⟩

lemma strictMono_agm_fst (hb : 0 < b) : StrictMono (agm · b) := fun a a' l ↦ by
  dsimp only
  rcases eq_zero_or_pos a with rfl | ha
  · simp [agm_pos l hb]
  · have h : (a, b) ∈ Set.Ioi 0 ×ˢ Set.Ioi 0 := by simp [ha, hb]
    have h' : (a', b) ∈ Set.Ioi 0 ×ˢ Set.Ioi 0 := by simp [ha.trans l, hb]
    apply strictMonoOn_agm h h' (Prod.mk_lt_mk_iff_left.mpr l)

lemma strictMono_agm_snd (ha : 0 < a) : StrictMono (agm a ·) := by
  conv =>
    enter [1, b]
    rw [agm_comm]
  exact strictMono_agm_fst ha
