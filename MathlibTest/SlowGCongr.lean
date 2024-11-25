import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Set Real Classical

class GromovHyperbolicSpace (X : Type*) [MetricSpace X] where
  deltaG : ℝ

noncomputable def gromovProductAt {X : Type*} [MetricSpace X] (e x y : X) : ℝ :=
  (dist e x + dist e y - dist x y) / 2

variable {X : Type*} [MetricSpace X] [GromovHyperbolicSpace X]
variable {δ : ℝ}

/- We give their values to the parameters `L`, `D` and `α` that we will use in the proof. -/
local notation "α" => 12 / 100
local notation "L" => 18 * δ
local notation "D" => 55 * δ


-- #time
set_option profiler true in
set_option profiler.threshold 10 in
-- set_option trace.profiler true in
lemma Morse_Gromov_theorem_aux0
    {f p : ℝ → X} {um uM Λ C z dm dM ym yM closestm closestM: ℝ}
    (h_um_uM : um ≤ uM)
    (hz : z ∈ Icc um uM)
    (hC : 0 ≤ C)
    (hu : 0 ≤ uM - um)
    (hΛ : 1 ≤ Λ)
    (hΛ' : 1 ≤ Λ ^ 2)
    (hδ₀ : 0 < δ)
    (pz : p z = f z)
    (hdM : 0 ≤ dM)
    (hdm : dm ≤ D + 4 * C)
    (hdM : dM ≤ D + 4 * C)
    (hδ : δ > GromovHyperbolicSpace.deltaG X) :
    /- We define two constants `K` and `Kmult` that appear in the precise formulation of the
    bounds. Their values have no precise meaning, they are just the outcome of the computation. -/
    let K : ℝ := α * log 2 / (5 * (4 + (L + 2 * δ)/D) * δ * Λ)
    let Kmult : ℝ := ((L + 4 * δ)/(L - 13 * δ)) * ((4 * exp (1/2 * log 2)) * Λ * exp (- ((1 - α) * D * log 2 / (5 * δ))) / K)
    gromovProductAt (f z) (f um) (f uM)
      ≤ Λ^2 * (D + (3/2) * L + δ + 11/2 * C) - 2 * δ + Kmult * (1 - exp (- K * (uM - um))) := by

  set G := gromovProductAt (f z) (f um) (f uM)
  have h_fz_pum_G : G ≤ dist (f z) (p um) := by sorry
  have hym_dist : L - 4 * δ ≤ dist (p um) (p ym) ∧ ∀ x ∈ Icc um ym, G ≤ dist (f z) (p x) + L := by
    sorry
  have h_fz_puM_G : G ≤ dist (f z) (p uM) := by sorry
  have hyM_dist : L - 4 * δ ≤ dist (p uM) (p yM) ∧ ∀ x ∈ Icc yM uM, G ≤ dist (f z) (p x) + L := by
    sorry

  intro K Kmult
  have : 0 < K := sorry
  have : Kmult > 0 := sorry

  /- First slow `gcongr` -/
  have : Λ^2 * (24 * δ + 3 * C) - Λ^2 * 12 * δ
      ≤ Λ^2 * ((2 * D + L + 2 * δ) + 11 * C) - 1 * 12 * δ := by
    gcongr -- Λ^2 * (?_ + ?_) - ?_ * 12 * δ
    . sorry
    · sorry

  /- Second slow `gcongr` -/
  have : Λ * (Λ * (dm + (L + C + 2 * δ) + dM)) + 1 * 2 * C
      ≤ Λ * (Λ * ((D + 4 * C) + (L + C + 2 * δ) + (D + 4 * C))) + Λ^2 * 2 * C := by
    gcongr -- Λ * (Λ * (?_ + _ + ?_)) + ?_ * _ * _

  /- Third slow `gcongr` -/
  have : Λ ^ 2 * dist (f closestm) (f closestM) + Λ ^ 2 * C + 1 * 2 * C
      ≤ Λ ^ 2 * (12 * δ) + Λ ^ 2 * C + Λ ^ 2 * 2 * C:= by
    have h_closest : dist (f closestm) (f closestM) ≤ 12 * δ := sorry
    gcongr -- _ * ?_ + _ + ?_ * _ * _

  /- Fourth slow `gcongr` -/
  have :
    gromovProductAt (f z) (f closestm) (f closestM) + 1 * L + 4 * δ + 0 * (1 - exp (- K * (uM - um)))
      ≤ (Λ^2 * (D + L / 2 + δ + 11/2 * C) - 6 * δ) + Λ^2 * L + 4 * δ + Kmult * (1 - exp (- K * (uM - um))) := by
    have I : gromovProductAt (f z) (f closestm) (f closestM) ≤ Λ^2 * (D + L / 2 + δ + 11/2 * C) - 6 * δ := by
      sorry
    gcongr -- ?_ + ?_ * _ + _ + ?_ *  _
    sorry

  sorry
