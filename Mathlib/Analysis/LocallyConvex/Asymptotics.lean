/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.Asymptotics.TVS
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Asymptotics for locally convex topological vector spaces

We provide a characterization of the Landau symbols,

-/

@[expose] public section

open scoped NNReal
open Filter

variable {ι κ α 𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]
variable {f f₁ f₂ : α → E} {g g₁ g₂ : α → F} {l : Filter α}
namespace PolynormableSpace

variable [PolynormableSpace 𝕜 E] [PolynormableSpace 𝕜 F]

theorem isBigOTVS_iff_le :
    f =O[𝕜; l] g ↔ ∀ p : Seminorm 𝕜 E, Continuous p → ∃ q : Seminorm 𝕜 F,
      Continuous q ∧ p ∘ f ≤ᶠ[l] q ∘ g := by
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  rw [(PolynormableSpace.hasBasis_zero_ball 𝕜 E).isBigOTVS_iff
      (PolynormableSpace.hasBasis_zero_ball 𝕜 F)]
  constructor <;>
  intro H p p_cont <;>
  obtain ⟨q, q_cont, hq⟩ := H p p_cont <;>
  refine ⟨‖c‖₊ • q, q_cont.const_smul _, hq.mono fun x hx ↦ ?_⟩
  · suffices (p (f x)).toNNReal ≤ ‖c‖ₑ * (q (g x)).toNNReal by
      simpa (discharger := positivity) [NNReal.smul_def, ← Real.toNNReal_le_toNNReal_iff,
        ← ENNReal.coe_le_coe, Real.toNNReal_mul]
    calc  ↑(p (f x)).toNNReal
      _ ≤ egauge 𝕜 (p.ball 0 1) (f x) := p.le_egauge_ball_one _
      _ ≤ egauge 𝕜 (q.ball 0 1) (g x) := hx
      _ ≤ ‖c‖ₑ * (q (g x)).toNNReal := q.egauge_ball_one_le_of_one_lt_norm hc _
  · calc  egauge 𝕜 (p.ball 0 1) (f x)
      _ ≤ ‖c‖ₑ * (p (f x)).toNNReal := p.egauge_ball_one_le_of_one_lt_norm hc _
      _ ≤ ‖c‖ₑ * (q (g x)).toNNReal := by gcongr; exact hx
      _ = ((‖c‖₊ • q) (g x)).toNNReal := by
            simp [NNReal.smul_def, Real.toNNReal_mul, enorm_eq_nnnorm]
      _ ≤ egauge 𝕜 ((‖c‖₊ • q).ball 0 1) (g x) := (‖c‖₊ • q).le_egauge_ball_one _

theorem isBigOTVS_iff :
    f =O[𝕜; l] g ↔ ∀ p : Seminorm 𝕜 E, Continuous p → ∃ q : Seminorm 𝕜 F,
      Continuous q ∧ (p ∘ f) =O[l] (q ∘ g) := by
  simp_rw [isBigOTVS_iff_le, Filter.EventuallyLE]
  congrm ∀ p p_cont, ?_
  constructor <;> rintro ⟨q, q_cont, hq⟩
  · exact ⟨q, q_cont, .of_bound' <| by simpa (discharger := positivity) [abs_of_nonneg]⟩
  · rw [Asymptotics.isBigO_iff'] at hq
    rcases hq with ⟨C, C_pos, hC⟩
    simp (discharger := positivity) only [Function.comp_apply, Real.norm_of_nonneg] at hC
    refine ⟨C.toNNReal • q, q_cont.const_smul _, ?_⟩
    simpa [NNReal.smul_def, C_pos.le]

theorem isLittleOTVS_iff_le :
    f =o[𝕜; l] g ↔ ∀ p : Seminorm 𝕜 E, Continuous p → ∃ q : Seminorm 𝕜 F,
      Continuous q ∧ ∀ ε : ℝ≥0, ε ≠ 0 → p ∘ f ≤ᶠ[l] (ε • q) ∘ g := by
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  rw [(PolynormableSpace.hasBasis_zero_ball 𝕜 E).isLittleOTVS_iff
      (PolynormableSpace.hasBasis_zero_ball 𝕜 F)]
  constructor <;>
  intro H p p_cont <;>
  obtain ⟨q, q_cont, hq⟩ := H p p_cont <;>
  refine ⟨‖c‖₊ • q, q_cont.const_smul _, fun ε hε ↦ (hq ε hε).mono fun x hx ↦ ?_⟩
  · suffices (p (f x)).toNNReal ≤ ε * ‖c‖ₑ * (q (g x)).toNNReal by
      simpa (discharger := positivity) [NNReal.smul_def, ← Real.toNNReal_le_toNNReal_iff,
        ← ENNReal.coe_le_coe, Real.toNNReal_mul, mul_assoc]
    calc  ↑(p (f x)).toNNReal
      _ ≤ egauge 𝕜 (p.ball 0 1) (f x) := p.le_egauge_ball_one _
      _ ≤ ε * egauge 𝕜 (q.ball 0 1) (g x) := hx
      _ ≤ ε * ‖c‖ₑ * (q (g x)).toNNReal := by
            grw [mul_assoc, q.egauge_ball_one_le_of_one_lt_norm hc _]
  · calc  egauge 𝕜 (p.ball 0 1) (f x)
      _ ≤ ‖c‖ₑ * (p (f x)).toNNReal := p.egauge_ball_one_le_of_one_lt_norm hc _
      _ ≤ ‖c‖ₑ * ((ε • q) (g x)).toNNReal := by gcongr; exact hx
      _ = ε * ((‖c‖₊ • q) (g x)).toNNReal := by
            simp [NNReal.smul_def, Real.toNNReal_mul, enorm_eq_nnnorm, ← mul_assoc, mul_comm]
      _ ≤ ε * egauge 𝕜 ((‖c‖₊ • q).ball 0 1) (g x) := by
            grw [(‖c‖₊ • q).le_egauge_ball_one _]

theorem isLittleOTVS_iff :
    f =o[𝕜; l] g ↔ ∀ p : Seminorm 𝕜 E, Continuous p → ∃ q : Seminorm 𝕜 F,
      Continuous q ∧ (p ∘ f) =o[l] (q ∘ g) := by
  simp_rw [isLittleOTVS_iff_le, Filter.EventuallyLE, Asymptotics.isLittleO_iff]
  congrm ∀ p p_cont, ∃ q, _ ∧ ?_
  constructor <;> intro H ε hε
  · have : NNReal.mk ε hε.le ≠ 0 := by simpa [← NNReal.coe_ne_zero] using hε.ne'
    simpa (discharger := positivity) [abs_of_nonneg, NNReal.smul_def] using
      H (NNReal.mk ε hε.le) this
  · simp (discharger := positivity) only [Function.comp_apply, Real.norm_of_nonneg] at H
    exact H (by positivity)

end PolynormableSpace

namespace WithSeminorms

variable {p : SeminormFamily 𝕜 E ι} {q : SeminormFamily 𝕜 F κ}

theorem isBigOTVS_iff_le_continuous (hp : WithSeminorms p) [PolynormableSpace 𝕜 F] :
    f =O[𝕜; l] g ↔ ∀ i : ι, ∃ q : Seminorm 𝕜 F, Continuous q ∧ p i ∘ f ≤ᶠ[l] (q ∘ g) := by
  have := hp.toPolynormableSpace
  rw [PolynormableSpace.isBigOTVS_iff_le]
  constructor <;> intro H
  · exact fun i ↦ H (p i) (hp.continuous_seminorm i)
  · intro r r_cont
    refine Seminorm.induction_add_of_continuous hp ?_ ?_ ?_ ?_ ?_ r_cont
    · assumption
    · exact ⟨0, continuous_zero, .rfl⟩
    · intro r₁ r₂ ⟨q₁, q₁_cont, hq₁⟩ ⟨q₂, q₂_cont, hq₂⟩
      use q₁ + q₂, q₁_cont.add q₂_cont
      filter_upwards [hq₁, hq₂] with x using add_le_add
    · intro r₁ r₂ h ⟨q, q_cont, hq⟩
      exact ⟨q, q_cont, hq.mono fun x hx ↦ (h _).trans hx⟩
    · intro r C ⟨q, q_cont, hq⟩
      exact ⟨C • q, q_cont.const_smul _, hq.mono fun x hx ↦ (smul_le_smul_of_nonneg_left hx C.2)⟩

theorem isBigOTVS_iff_le (hp : WithSeminorms p) (hq : WithSeminorms q) :
    f =O[𝕜; l] g ↔ ∀ i : ι, ∃ s : Finset κ, ∃ C : ℝ≥0, p i ∘ f ≤ᶠ[l] ((C • s.sup q) ∘ g) := by
  have := hq.toPolynormableSpace
  rw [hp.isBigOTVS_iff_le_continuous]
  congrm ∀ i, ?_
  constructor
  · intro ⟨r, r_cont, hr⟩
    obtain ⟨s, C, C_ne, hC⟩ := Seminorm.bound_of_continuous hq r r_cont
    exact ⟨s, C, hr.mono fun x hx ↦ hx.trans (hC _)⟩
  · intro ⟨s, C, hC⟩
    use C • s.sup q
    have := hq.topologicalAddGroup
    use (Seminorm.continuous_finsetSup fun i _ ↦ hq.continuous_seminorm i).const_smul _

theorem isBigOTVS_iff (hp : WithSeminorms p) (hq : WithSeminorms q) :
    f =O[𝕜; l] g ↔ ∀ i : ι, ∃ s : Finset κ, (p i ∘ f) =O[l] (↑(s.sup q) ∘ g) := by
  simp_rw [hp.isBigOTVS_iff_le hq, Filter.EventuallyLE]
  congrm ∀ i, ∃ s, ?_
  constructor
  · intro ⟨C, hC⟩
    exact .of_bound C <| by simpa (discharger := positivity) [abs_of_nonneg]
  · rw [Asymptotics.isBigO_iff']
    intro ⟨C, C_pos, hC⟩
    refine ⟨C.toNNReal, ?_⟩
    convert hC using 2
    simp (discharger := positivity) [abs_of_nonneg, NNReal.smul_def]

theorem isLittleOTVS_iff_le_continuous (hp : WithSeminorms p) [PolynormableSpace 𝕜 F] :
    f =o[𝕜; l] g ↔
      ∀ i : ι, ∃ q : Seminorm 𝕜 F, Continuous q ∧
        ∀ ε : ℝ≥0, ε ≠ 0 → p i ∘ f ≤ᶠ[l] ((ε • q) ∘ g) := by
  have := hp.toPolynormableSpace
  rw [PolynormableSpace.isLittleOTVS_iff_le]
  constructor <;> intro H
  · exact fun i ↦ H (p i) (hp.continuous_seminorm i)
  · intro r r_cont
    refine Seminorm.induction_add_of_continuous hp ?_ ?_ ?_ ?_ ?_ r_cont
    · assumption
    · exact ⟨0, continuous_zero, fun _ _ ↦ by simpa using .rfl⟩
    · intro r₁ r₂ ⟨q₁, q₁_cont, hq₁⟩ ⟨q₂, q₂_cont, hq₂⟩
      refine ⟨q₁ + q₂, q₁_cont.add q₂_cont, fun ε ε_ne ↦ ?_⟩
      filter_upwards [hq₁ ε ε_ne, hq₂ ε ε_ne] with x hx₁ hx₂
      simpa using add_le_add hx₁ hx₂
    · intro r₁ r₂ h ⟨q, q_cont, hq⟩
      exact ⟨q, q_cont, (hq · · |>.mono fun x hx ↦ h _ |>.trans hx)⟩
    · intro r C ⟨q, q_cont, hq⟩
      refine ⟨C • q, q_cont.const_smul _, fun ε ε_ne ↦ hq ε ε_ne |>.mono fun x hx ↦ ?_⟩
      rw [smul_comm]
      exact smul_le_smul_of_nonneg_left hx C.2

theorem isLittleOTVS_iff_le (hp : WithSeminorms p) (hq : WithSeminorms q) :
    f =o[𝕜; l] g ↔
      ∀ i : ι, ∃ s : Finset κ, ∀ ε : ℝ≥0, ε ≠ 0 → p i ∘ f ≤ᶠ[l] ((ε • s.sup q) ∘ g) := by
  have := hq.toPolynormableSpace
  rw [hp.isLittleOTVS_iff_le_continuous]
  congrm ∀ i, ?_
  constructor
  · intro ⟨r, r_cont, hr⟩
    obtain ⟨s, C, C_ne, hC⟩ := Seminorm.bound_of_continuous hq r r_cont
    refine ⟨s, fun ε ε_ne ↦ (hr (ε/C) (by positivity)).mono fun x hx ↦ ?_⟩
    simp only [Function.comp_apply, Seminorm.le_def, smul_apply] at hx hC ⊢
    grw [hx, hC _, ← mul_smul, div_mul_cancel₀ _ C_ne]
  · intro ⟨s, hs⟩
    have := hq.topologicalAddGroup
    use s.sup q, Seminorm.continuous_finsetSup fun i _ ↦ hq.continuous_seminorm i

theorem isLittleOTVS_iff (hp : WithSeminorms p) (hq : WithSeminorms q) :
    f =o[𝕜; l] g ↔ ∀ i : ι, ∃ s : Finset κ, (p i ∘ f) =o[l] ((s.sup q : Seminorm 𝕜 F) ∘ g) := by
  simp_rw [hp.isLittleOTVS_iff_le hq, Filter.EventuallyLE, Asymptotics.isLittleO_iff]
  congrm ∀ i, ∃ s, ?_
  constructor <;> intro H ε hε
  · have : NNReal.mk ε hε.le ≠ 0 := by simpa [← NNReal.coe_ne_zero] using hε.ne'
    simpa [abs_of_nonneg, NNReal.smul_def] using H _ this
  · simp (discharger := positivity) only [Function.comp_apply, Real.norm_of_nonneg] at H
    exact H (by positivity)

end WithSeminorms

end
