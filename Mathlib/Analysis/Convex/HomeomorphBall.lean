import Mathlib.Analysis.NormedSpace.ScaleToNorm
import Mathlib.Analysis.Convex.Gauge

/-!
-/

open Metric Set Function Topology Filter
open scoped Pointwise

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {x : E}

/-- Scale a vector `x` to norm `gauge s x`. -/
noncomputable def scaleToGauge (s : Set E) (x : E) : E :=
  scaleToNorm ⟨gauge s x, gauge_nonneg _⟩ x

lemma scaleToGauge_def (s : Set E) (x : E) : scaleToGauge s x = (gauge s x / ‖x‖) • x := rfl

@[simp] theorem scaleToGauge_zero : scaleToGauge s 0 = 0 := scaleToNorm_zero_right _

theorem norm_scaleToGauge_le_gauge (s : Set E) (x : E) : ‖scaleToGauge s x‖ ≤ gauge s x :=
  norm_scaleToNorm_le _ _

theorem norm_scaleToGauge_eq (h : x ≠ 0) : ‖scaleToGauge s x‖ = gauge s x :=
  norm_scaleToNorm_eq _ h

theorem norm_scaleToGauge_le (h : x ∈ s) : ‖scaleToGauge s x‖ ≤ 1 :=
  (norm_scaleToGauge_le_gauge _ _).trans (gauge_le_one_of_mem h)

theorem mapsTo_scaleToGauge : MapsTo (scaleToGauge s) s (closedBall (0 : E) 1) := fun _ h ↦
  mem_closedBall_zero_iff.2 <| norm_scaleToGauge_le h

theorem mapsTo_scaleToGauge_interior : MapsTo (scaleToGauge s) (interior s) (ball 0 1) := fun _ h ↦
  mem_ball_zero_iff.2 <| (norm_scaleToGauge_le_gauge _ _).trans_lt <|
    interior_subset_gauge_lt_one _ h

theorem IsOpen.mapsTo_scaleToGauge (h : IsOpen s) : MapsTo (scaleToGauge s) s (ball 0 1) := by
  simpa only [h.interior_eq] using mapsTo_scaleToGauge_interior (s := s)

theorem continuous_scaleToGauge (hc : Convex ℝ s) (h₀ : s ∈ 𝓝 0) : Continuous (scaleToGauge s) := by
  refine ((hc.continuous_gauge h₀).subtype_mk _).scaleToNorm continuous_id fun x hx ↦ ?_
  rw [← NNReal.coe_eq_zero, NNReal.coe_mk, hx, gauge_zero]
  
noncomputable def scaleFromGauge (s : Set E) (x : E) : E :=
  (‖x‖ / gauge s x) • x

@[simp] theorem scaleFromGauge_zero (s : Set E) : scaleFromGauge s 0 = 0 := smul_zero _

theorem gauge_scaleFromGauge (hs : Absorbent ℝ s) (hb : Bounded s) :
    gauge s (scaleFromGauge s x) = ‖x‖ := by
  rw [scaleFromGauge, gauge_smul_of_nonneg (div_nonneg (norm_nonneg _) (gauge_nonneg _)),
    smul_eq_mul, div_mul_cancel_of_imp]
  exact not_imp_not.1 fun hx ↦ (gauge_pos hs hb (norm_ne_zero_iff.1 hx)).ne'

theorem norm_scaleFromGauge : ‖scaleFromGauge s x‖ = ‖x‖ ^ 2 / gauge s x := by
  field_simp [scaleFromGauge, norm_smul, abs_of_nonneg (gauge_nonneg _), sq]

theorem norm_scaleFromGauge_le (hs : Absorbent ℝ s) (hR : 0 ≤ R) (hsub : s ⊆ closedBall 0 R) :
    ‖scaleFromGauge s x‖ ≤ R * ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx; · simp
  rcases hR.eq_or_lt with rfl | hR
  · rw [closedBall_zero] at hsub
    rw [norm_scaleFromGauge, gauge_of_subset_zero hsub, Pi.zero_apply, div_zero, zero_mul]
  calc
    ‖scaleFromGauge s x‖ = ‖x‖ ^ 2 / gauge s x := norm_scaleFromGauge
    _ ≤ ‖x‖ ^ 2 / (‖x‖ / R) := by
      gcongr
      -- TODO: `positivity` fails to prove `0 < ‖x‖`, see #5265
      exacts [div_pos (norm_pos_iff.2 hx) hR, le_gauge_of_subset_closedBall hs hR.le hsub]
    _ = R * ‖x‖ := by field_simp [norm_ne_zero_iff.2 hx, sq]; ac_rfl

theorem continuous_scaleFromGauge (hc : Convex ℝ s) (h₀ : s ∈ 𝓝 0) (hb : Bounded s) :
    Continuous (scaleFromGauge s) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  rcases ne_or_eq x 0 with hx | rfl
  · refine (continuousAt_id.norm.div (hc.continuous_gauge h₀).continuousAt ?_).smul continuousAt_id
    exact (gauge_pos (absorbent_nhds_zero h₀) hb hx).ne'
  · rw [ContinuousAt, scaleFromGauge_zero]
    rcases hb.subset_ball_lt 0 0 with ⟨R, hR₀, hsub⟩
    apply squeeze_zero_norm (fun x ↦ norm_scaleFromGauge_le (absorbent_nhds_zero h₀) hR₀.le hsub)
    exact Continuous.tendsto' (by continuity) _ _ (by simp)

lemma scaleToGauge_scaleFromGauge (hs : Absorbent ℝ s) (hb : Bounded s) (x : E) :
    scaleToGauge s (scaleFromGauge s x) = x := by
  rcases eq_or_ne x 0 with rfl | hx; · simp
  have hg : 0 < gauge s x := gauge_pos hs hb hx
  have hc : 0 < ‖x‖ / gauge s x := div_pos (norm_pos_iff.2 hx) hg
  rw [scaleToGauge, scaleFromGauge, scaleToNorm_smul _ hc, scaleToNorm_eq_self]
  rw [NNReal.coe_mk, gauge_smul_of_nonneg hc.le, smul_eq_mul, div_mul_cancel _ hg.ne']

lemma scaleFromGauge_scaleToGauge (hs : Absorbent ℝ s) (hb : Bounded s) (x : E) :
    scaleFromGauge s (scaleToGauge s x) = x := by
  rcases eq_or_ne x 0 with rfl | hx; · simp
  simp only [scaleToGauge_def, scaleFromGauge, smul_smul]
  convert one_smul ℝ x
  have hg : 0 < gauge s x := gauge_pos hs hb hx
  field_simp [norm_smul, gauge_smul_of_nonneg (div_nonneg hg.le (norm_nonneg x)) x,
    abs_of_nonneg hg.le, hg.ne', norm_ne_zero_iff.2 hx]
  ac_rfl

theorem image_scaleToGauge_of_open (hc : Convex ℝ s) (h₀ : 0 ∈ s) (ho : IsOpen s) (hb : Bounded s) :
    scaleToGauge s '' s = ball 0 1 := by
  have ha : Absorbent ℝ s := absorbent_nhds_zero (ho.mem_nhds h₀)
  refine ho.mapsTo_scaleToGauge.image_subset.antisymm fun x hx ↦ ?_
  refine ⟨scaleFromGauge s x, ?_, scaleToGauge_scaleFromGauge ha hb _⟩
  apply gauge_lt_one_subset_self hc h₀ ha
  rwa [mem_setOf_eq, gauge_scaleFromGauge ha hb, ← mem_ball_zero_iff]
  
/-- If `s` is a bounded convex neighbourhood of zero, then `scaleToGaugeHomeomorph s _ _ _` is
a homeomorphism of the ambient space to itself that preserves rays from the origin and sends the
interior of `s` to the unit ball. -/
@[simps]
noncomputable def scaleToGaugeHomeomorph (s : Set E) (hc : Convex ℝ s) (hs : s ∈ 𝓝 0)
    (hb : Bounded s) : E ≃ₜ E where
  toFun := scaleToGauge s
  invFun := scaleFromGauge s
  left_inv := scaleFromGauge_scaleToGauge (absorbent_nhds_zero hs) hb
  right_inv := scaleToGauge_scaleFromGauge (absorbent_nhds_zero hs) hb
  continuous_toFun := continuous_scaleToGauge hc hs
  continuous_invFun := continuous_scaleFromGauge hc hs hb

theorem IsOpen.exists_homeomorph_unit_ball {s : Set E} (ho : IsOpen s) (hc : Convex ℝ s)
    (hb : Bounded s) (hne : s.Nonempty) :
    ∃ h : E ≃ₜ E, h '' s = ball 0 1 := by
  wlog h₀ : 0 ∈ s generalizing s
  · rcases hne with ⟨x, hx⟩
    have hb : Bounded (-x +ᵥ s)
    have := this (ho.vadd (-x)) (hc.vadd _)
    
