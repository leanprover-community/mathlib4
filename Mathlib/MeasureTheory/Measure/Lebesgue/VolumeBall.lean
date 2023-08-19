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
  suffices : ∀ u v, u ∩ v = ∅ → f u = f (u ∪ v)
  · calc f s = f ((s ∩ t) ∪ (s \ t)) := by congr; sorry
      _ = f (s ∩ t) := by rw [← this]; aesop
      _ = f (t ∩ s) := by rw [inter_comm]
      _ = f ((t ∩ s) ∪ (t \ s)) := by rw [← this]; aesop
      _ = f t := by congr; sorry
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
theorem lintegral_I_sub_sq (n : ℕ) (R : ℝ≥0) :
    ∫⁻ x : ℝ, I n (R ^ 2 - x ^ 2) = Beta (1 / 2) (n / 2 + 1) * (R:ℝ≥0∞) ^ (n + 1) :=
  sorry

variable [Fintype ι]

def A (R : ℝ) (s : Finset ι) (x : ι → ℝ) : ℝ≥0∞ :=
  B s.card * I s.card (R ^ 2 - ∑ j in sᶜ, x j ^ 2)

theorem sphere_aux_le_sphere_aux_insert {R : ℝ} (hR : 0 ≤ R) (s : Finset ι) {i : ι} (hi : i ∉ s) :
    (∫⋯∫_sᶜ, A R s) = ∫⋯∫_(insert i s)ᶜ, A R (insert i s) := by
  have hi' : i ∉ (insert i s)ᶜ := not_mem_compl.mpr <| mem_insert_self i s
  calc (∫⋯∫_sᶜ, A R s)
      = ∫⋯∫_(insert i (insert i s)ᶜ), A R s := by simp_rw [← insert_compl_insert hi]
    _ = ∫⋯∫_(insert i s)ᶜ, (fun x ↦ ∫⁻ t, A R s (update x i t)) := by
          rw [marginal_insert' _ _ hi']
          sorry -- measurability
    _ = _ := ?_
  congr! 1
  ext x
  calc ∫⁻ t, B s.card * I s.card (R ^ 2 - ∑ j in sᶜ, update x i t j ^ 2)
      = ∫⁻ t, B s.card * I s.card (R ^ 2 - ∑ j in insert i (insert i s)ᶜ, update x i t j ^ 2) := by
          simp_rw [← insert_compl_insert hi]
    _ = ∫⁻ (t : ℝ), B s.card * I s.card ((R ^ 2 - ∑ j in (insert i s)ᶜ, x j ^ 2) - t ^ 2) := by
          congr
          ext t
          have H : ∀ j ∈ (insert i s)ᶜ, update x i t j ^ 2 = x j ^ 2
          · intro j hj
            rw [update_noteq (by aesop)]
          simp only [sum_insert hi', update_same, sum_congr rfl H]
          ring_nf
    _ = B s.card * ∫⁻ (t : ℝ), I s.card ((R ^ 2 - ∑ j in (insert i s)ᶜ, x j ^ 2) - t ^ 2) := by
          rw [lintegral_const_mul]
          sorry -- measurability
    _ = B (s.card + 1) * I (s.card + 1) (R ^ 2 - ∑ j in (insert i s)ᶜ, x j ^ 2) := ?_
    _ = B (insert i s).card * I (insert i s).card (R ^ 2 - ∑ j in (insert i s)ᶜ, x j ^ 2) := by
          rw [card_insert_of_not_mem hi]
  by_cases h : (0:ℝ) ≤ R ^ 2 - ∑ j in (insert i s)ᶜ, x j ^ 2
  · let r : ℝ≥0 := ⟨sqrt (R ^ 2 - ∑ j in (insert i s)ᶜ, x j ^ 2), sqrt_nonneg _⟩
    have hr : r ^ 2 = R ^ 2 - ∑ j in (insert i s)ᶜ, x j ^ 2 := Real.sq_sqrt h
    clear_value r
    rw [← hr, lintegral_I_sub_sq, I_apply_nnreal, B_succ]
    norm_cast
    push_cast -- some automation broken here, track it down
    have : (r ^ 2) ^ ((((s.card : ℝ) + 1) / 2)) = r ^ s.card * r
    · sorry -- algebra
    rw [this]
    ring
  · have h₁ : (fun t ↦ ↑(I s.card (R ^ 2 - ∑ j in (insert i s)ᶜ, x j ^ 2 - t ^ 2)))
      = (fun _ ↦ 0 : ℝ → ℝ≥0∞)
    · ext1 t
      dsimp
      rw [I, dif_neg]
      · simp
      · have : (0:ℝ) ≤ t ^ 2 := by positivity
        linarith
    have h₂ : I (s.card + 1) (R ^ 2 - ∑ j in (insert i s)ᶜ, x j ^ 2) = 0
    · rw [I, dif_neg h]
    simp [h₁, h₂, -compl_insert, -mul_eq_zero]

theorem sphere_aux_emptyset_eq_sphere_aux_univ {R : ℝ} (hR : 0 ≤ R) :
    (∫⋯∫_∅ᶜ, A R ∅) = ∫⋯∫_(univ : Finset ι)ᶜ, A R univ := by
  refine Finset.constant_of_eq_insert (fun s : Finset ι ↦ ∫⋯∫_sᶜ, A R s) ?_ ∅ univ
  apply sphere_aux_le_sphere_aux_insert hR

theorem volume_ball (R : ℝ≥0) :
    volume {x : ι → ℝ | 0 ≤ R ^ 2 - ∑ j, x j ^ 2} = B (Fintype.card ι) * R ^ Fintype.card ι := by
  calc volume {x : ι → ℝ | 0 ≤ R ^ 2 - ∑ j, x j ^ 2}
      = ∫⁻ x : ι → ℝ, Set.indicator {y : ι → ℝ | 0 ≤ R ^ 2 - ∑ i : ι, y i ^ 2} 1 x := ?_
    _ = ∫⁻ x : ι → ℝ, I 0 (R ^ 2 - ∑ i : ι, x i ^ 2) := ?_
    _ = B (Fintype.card ι) * I (Fintype.card ι) (R ^ 2) := ?_
    _ = _ := ?_
  · convert (lintegral_indicator_const _ 1).symm
    · simp
    · sorry -- measurability
  · congr! 3 with x
    rw [I_zero]
    simp [Set.indicator]
    split <;> simp
  · have H := congr_fun (sphere_aux_emptyset_eq_sphere_aux_univ R.property) (0 : ι → ℝ)
    simpa [A, marginal_univ, marginal_empty, Finset.card_univ, -I_zero] using H
  · congr
    simp [I]
    show (R ^ 2) ^ ((Fintype.card ι : ℝ) / 2) = _
    sorry -- algebra
