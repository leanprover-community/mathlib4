import Mathlib.Probability.ProbabilityMassFunction.Basic

theorem PMF.summable_toReal_abs {α : Type*} (p : PMF α) :
    Summable fun i => |(p i).toReal| := by
  simp only [abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.summable_toReal p.tsum_coe_ne_top

theorem PMF.dist_summable {α : Type*} (X Y : PMF α) :
    Summable fun i => dist (X i).toReal (Y i).toReal := by
  apply Summable.of_nonneg_of_le (f := fun i ↦ |(X i).toReal| + |(Y i).toReal|)
    (fun i ↦ abs_nonneg _) _
  · apply Summable.add
    · apply PMF.summable_toReal_abs
    · apply PMF.summable_toReal_abs
  · exact fun b ↦ abs_sub (X b).toReal (Y b).toReal

noncomputable instance StatisticalDistance {α} : MetricSpace (PMF α) where
  dist X Y := (1 / 2) * ∑' i, dist ((X i).toReal) ((Y i).toReal)
  dist_self X := by
    simp
  dist_comm X Y := by
    congr
    ext i
    exact PseudoMetricSpace.dist_comm (X i).toReal (Y i).toReal
  dist_triangle X Y Z := by
    rw [<-mul_add]
    rw [<-Summable.tsum_add (PMF.dist_summable X Y) (PMF.dist_summable Y Z)]
    simp only [one_div, inv_pos, Nat.ofNat_pos, mul_le_mul_iff_right₀]
    exact
      Summable.tsum_mono (PMF.dist_summable X Z)
        (Summable.add (PMF.dist_summable X Y) (PMF.dist_summable Y Z))
        fun i ↦ PseudoMetricSpace.dist_triangle (X i).toReal (Y i).toReal (Z i).toReal
  eq_of_dist_eq_zero {x} {y} := by
    simp only [one_div, mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or]
    intro h
    replace h : HasSum (fun i => dist (x i).toReal (y i).toReal) 0 := by
      sorry
    rw [hasSum_zero_iff_of_nonneg (f := fun i => dist (x i).toReal (y i).toReal)] at h
    ·
      simp only [funext_iff, Pi.zero_apply, dist_eq_zero] at h
      ext i
      specialize h i
      -- This sure would be easier if the PMF return type was a Real or something with injective casts.

      sorry
    · intro i
      simp
