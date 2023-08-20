import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
A loose port of https://isabelle.in.tum.de/library/HOL/HOL-Analysis/Ball_Volume.html
-/

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220


open Classical Real NNReal ENNReal BigOperators Finset Function MeasureTheory

-- move to Data.Finset.Basic
theorem Finset.constant_of_eq_insert {α β : Type _} (f : Finset α → β)
    (H : ∀ s : Finset α, ∀ {i} (hi : i ∉ s), f s = f (insert i s)) (s t : Finset α) :
    f s = f t := by
  suffices H : ∀ u v, u ∩ v = ∅ → f u = f (u ∪ v)
  · calc f s = f ((s ∩ t) ∪ (s \ t)) := by
            congr
            ext
            simp only [mem_union, mem_inter, mem_sdiff]
            tauto
      _ = f (s ∩ t) := by rw [← H]; aesop
      _ = f (t ∩ s) := by rw [inter_comm]
      _ = f ((t ∩ s) ∪ (t \ s)) := by rw [← H]; aesop
      _ = f t := by
            congr
            ext
            simp only [mem_union, mem_inter, mem_sdiff]
            tauto
  intro s t hst
  induction' t using Finset.induction with i t hit ih
  · simp
  · have his : i ∉ s := by aesop
    have hst' : s ∩ t = ∅ := by aesop
    calc f s = f (s ∪ t) := ih hst'
      _ = f (insert i (s ∪ t)) := H _ (by aesop)
      _ = f (s ∪ (insert i t)) := by rw [Finset.union_insert]

noncomputable section

theorem Real.Gamma_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.Gamma x := by
    obtain rfl | hx := eq_or_lt_of_le hx
    · simp [Gamma_zero]
    · exact (Gamma_pos_of_pos hx).le

@[simp]
theorem Real.Gamma_half : Real.Gamma (1 / 2) = sqrt π := sorry

def NNReal.Gamma (x : ℝ≥0) : ℝ≥0 := ⟨Real.Gamma x, Real.Gamma_nonneg_of_nonneg x.property⟩

theorem NNReal.Gamma_pos_of_pos {x : ℝ≥0} (h : 0 < x) : 0 < Real.Gamma x := sorry -- algebra

@[simp]
theorem NNReal.Gamma_half : NNReal.Gamma (1 / 2) = sqrt NNReal.pi := sorry -- algebra

@[simp]
theorem NNReal.Gamma_one : NNReal.Gamma 1 = 1 := Subtype.ext Real.Gamma_one

def NNReal.Beta (a b : ℝ≥0) : ℝ≥0 := Gamma a * Gamma b / Gamma (a + b)

def I (n : ℕ) (t : ℝ) : ℝ≥0 := if ht : 0 ≤ t then (⟨t, ht⟩ ^ ((n:ℝ) / 2)) else 0

@[simp] theorem I_zero (t : ℝ) : I 0 t = if 0 ≤ t then 1 else 0 := sorry

theorem I_apply_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : I n t = (⟨t, ht⟩ ^ ((n:ℝ) / 2)) := by
  rw [I, dif_pos]

theorem I_apply_nnreal (n : ℕ) (t : ℝ≥0) : I n t = t ^ ((n:ℝ)/2) := by
  rw [I_apply_nonneg]
  rfl

@[simp] theorem I_apply_sq_nnreal (n : ℕ) (t : ℝ≥0) : I n ((t:ℝ) ^ 2) = t ^ n := sorry

@[measurability]
theorem measurable_I {n : ℕ} : Measurable (I n) := by
  have hf : Measurable (fun x : ℝ≥0 ↦ x ^ ((n:ℝ) / 2)) := measurable_id.pow_const _
  exact hf.dite measurable_const measurableSet_Ici

/-- The expected volume of the unit ball, as a function of dimension. -/
def B (n : ℕ) : ℝ≥0 := NNReal.pi ^ ((n:ℝ) / 2) / NNReal.Gamma (n / 2 + 1)

@[simp] theorem B_zero : B 0 = 1 := by simp [B]

-- some automation broken here, track it down
theorem B_succ (n : ℕ) : B (n + 1) = B n * Beta (1 / 2) (n / 2 + 1) := by
  dsimp only [B, Beta]
  push_cast
  simp only [add_div]
  ring_nf
  simp only
  have h₁ : 0 < NNReal.Gamma (1 + n / 2) := NNReal.Gamma_pos_of_pos (by positivity)
  have h₂ : 0 < NNReal.Gamma (1 + n / 2 + 1 / 2) := NNReal.Gamma_pos_of_pos (by positivity)
  set X := NNReal.Gamma (1 + n / 2)
  set Y := NNReal.Gamma (1 + n / 2 + 1 / 2)
  clear_value X Y
  field_simp [h₁.ne', h₂.ne']
  rw [add_div, NNReal.rpow_add, NNReal.sqrt_eq_rpow]
  · ring
  · apply Subtype.ne_of_val_ne
    dsimp
    exact Real.pi_ne_zero

/-- auxiliary one-variable integral -/
theorem lintegral_I_sub_sq_nnreal (n : ℕ) (R : ℝ≥0) :
    ∫⁻ x : ℝ, I n (R ^ 2 - x ^ 2) = Beta (1 / 2) (n / 2 + 1) * (R:ℝ≥0∞) ^ (n + 1) :=
  sorry

-- some automation broken here, track it down
theorem lintegral_I_sub_sq (n : ℕ) (c : ℝ) :
    ∫⁻ x : ℝ, I n (c - x ^ 2) = Beta (1 / 2) (n / 2 + 1) * I (n + 1) c := by
  by_cases h : (0:ℝ) ≤ c
  · let r : ℝ≥0 := ⟨sqrt c, sqrt_nonneg _⟩
    have hr : r ^ 2 = c := Real.sq_sqrt h
    clear_value r
    rw [← hr, lintegral_I_sub_sq_nnreal, I_apply_nnreal]
    norm_cast
    push_cast
    have : (r ^ 2) ^ ((((n : ℝ) + 1) / 2)) = r ^ n * r
    · sorry -- algebra
    rw [this]
    ring
  · have h₁ : (fun t ↦ ↑(I n (c - t ^ 2))) = (fun _ ↦ 0 : ℝ → ℝ≥0∞)
    · ext1 t
      dsimp
      rw [I, dif_neg]
      · simp
      · have : (0:ℝ) ≤ t ^ 2 := by positivity
        linarith
    have h₂ : I n c = 0
    · rw [I, dif_neg h]
    have h₃ : I (n + 1) c = 0
    · rw [I, dif_neg h]
    simp [h₁, h₂, h₃, -compl_insert, -mul_eq_zero, -zero_eq_mul]

variable [Fintype ι]

def A (R : ℝ) (s : Finset ι) (x : ι → ℝ) : ℝ≥0∞ :=
  B s.card * I s.card (R ^ 2 - ∑ j in sᶜ, x j ^ 2)

theorem measurable_A (R : ℝ) (s : Finset ι) : Measurable (A R s) := by
  refine measurable_const.mul <| measurable_coe_nnreal_ennreal.comp ?_
  refine measurable_I.comp <| measurable_const.sub ?_
  exact Finset.measurable_sum _ (fun i _ ↦ Measurable.pow_const (measurable_pi_apply _) _)

theorem sphere_aux_le_sphere_aux_insert {R : ℝ} (s : Finset ι) {i : ι} (hi : i ∉ s) :
    (∫⋯∫_sᶜ, A R s) = ∫⋯∫_(insert i s)ᶜ, A R (insert i s) := by
  have hi' : i ∉ (insert i s)ᶜ := not_mem_compl.mpr <| mem_insert_self i s
  simp_rw [← insert_compl_insert hi, marginal_insert' _ (measurable_A ..) hi']
  congr! 2 with _ x
  calc ∫⁻ t, B s.card * I s.card (R ^ 2 - ∑ j in sᶜ, update x i t j ^ 2)
      = ∫⁻ (t : ℝ), B s.card * I s.card ((R ^ 2 - ∑ j in (insert i s)ᶜ, x j ^ 2) - t ^ 2) := by
          congr! 2 with t
          have H : ∀ j ∈ (insert i s)ᶜ, update x i t j ^ 2 = x j ^ 2
          · intro j hj
            rw [update_noteq (by aesop)]
          simp only [← insert_compl_insert hi, sum_insert hi', update_same, sum_congr rfl H]
          ring_nf
    _ = B (insert i s).card * I (insert i s).card (R ^ 2 - ∑ j in (insert i s)ᶜ, x j ^ 2) := by
          rw [lintegral_const_mul, card_insert_of_not_mem hi, lintegral_I_sub_sq, B_succ]
          · norm_cast
            ring
          · refine measurable_coe_nnreal_ennreal.comp <| measurable_I.comp ?_
            exact measurable_const.sub <| measurable_id.pow_const _

theorem sphere_aux_emptyset_eq_sphere_aux_univ (R : ℝ) :
    (∫⋯∫_∅ᶜ, A R ∅) = ∫⋯∫_(univ : Finset ι)ᶜ, A R univ := by
  refine Finset.constant_of_eq_insert (fun s : Finset ι ↦ ∫⋯∫_sᶜ, A R s) ?_ ∅ univ
  apply sphere_aux_le_sphere_aux_insert

/-- The volume of a Euclidean ball of radius `R` in the space `ι → ℝ`, equipped with the product
measure, is `B (Fintype.card ι) * R ^ Fintype.card ι`. -/
theorem volume_ball (R : ℝ≥0) :
    volume {x : ι → ℝ | 0 ≤ R ^ 2 - ∑ j, x j ^ 2} = B (Fintype.card ι) * R ^ Fintype.card ι := by
  calc volume {x : ι → ℝ | 0 ≤ R ^ 2 - ∑ j, x j ^ 2}
      = ∫⁻ x : ι → ℝ, Set.indicator {y : ι → ℝ | (0:ℝ) ≤ R ^ 2 - ∑ i : ι, y i ^ 2} 1 x := by
          convert (lintegral_indicator_const _ 1).symm
          · simp
          · refine measurableSet_le measurable_const <| measurable_const.sub ?_
            exact Finset.measurable_sum _ (fun i _ ↦ Measurable.pow_const (measurable_pi_apply _) _)
    _ = ∫⁻ x : ι → ℝ, I 0 (R ^ 2 - ∑ i : ι, x i ^ 2) := by simp [apply_ite, Set.indicator_apply]
    _ = B (Fintype.card ι) * R ^ Fintype.card ι := by
          simpa [A, marginal_univ, marginal_empty, Finset.card_univ, -I_zero] using
            congr_fun (sphere_aux_emptyset_eq_sphere_aux_univ R) (0 : ι → ℝ)
