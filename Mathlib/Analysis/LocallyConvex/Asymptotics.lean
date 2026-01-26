/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.Asymptotics.TVS
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# TODO
-/

@[expose] public section

open scoped NNReal

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

theorem isLittleOTVS_iff_le :
    f =o[𝕜; l] g ↔ ∀ p : Seminorm 𝕜 E, Continuous p → ∃ q : Seminorm 𝕜 F,
      Continuous q ∧ ∀ ε : ℝ≥0, ε ≠ 0 → p ∘ f ≤ᶠ[l] ε • (q ∘ g) := by
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
      _ ≤ ‖c‖ₑ * (ε • q (g x)).toNNReal := by gcongr; exact hx
      _ = ε * ((‖c‖₊ • q) (g x)).toNNReal := by
            simp [NNReal.smul_def, Real.toNNReal_mul, enorm_eq_nnnorm, ← mul_assoc, mul_comm]
      _ ≤ ε * egauge 𝕜 ((‖c‖₊ • q).ball 0 1) (g x) := by
            grw [(‖c‖₊ • q).le_egauge_ball_one _]

end PolynormableSpace

namespace WithSeminorms

variable {p : SeminormFamily 𝕜 E ι} {q : SeminormFamily 𝕜 F κ}

theorem isBigOTVS_iff (hp : WithSeminorms p) (hq : WithSeminorms q) :
    f =O[𝕜; l] g ↔ ∀ i : ι, ∃ s : Finset κ, (p i ∘ f) =O[l] ((s.sup q : Seminorm 𝕜 F) ∘ g) := by
  have := hp.toPolynormableSpace
  have := hq.toPolynormableSpace
  rw [PolynormableSpace.isBigOTVS_iff_le]
  constructor <;> intro H
  · intro i
    obtain ⟨r, r_cont, hr⟩ := H (p i) (hp.continuous_seminorm i)
    obtain ⟨s, C, C_ne, hC⟩ := Seminorm.bound_of_continuous hq r r_cont
    refine ⟨s, .of_bound C <| hr.mono fun x hx ↦ ?_⟩
    simp (discharger := positivity) only [Function.comp_apply, Real.norm_of_nonneg]
    exact hx.trans (hC _)
  · intro r r_cont
    refine Seminorm.induction_of_continuous hp ?_ ?_ ?_ ?_ ?_ r_cont
    · intro i
      obtain ⟨s, hs⟩ := H i
      obtain ⟨C, C_pos, hC⟩ := Asymptotics.isBigO_iff'.mp hs
      simp (discharger := positivity) only [Function.comp_apply, Real.norm_of_nonneg] at hC
      use C.toNNReal • s.sup q
      use (Seminorm.continuous_finset_sup fun i _ ↦ hq.continuous_seminorm i).const_smul _
      filter_upwards [hC] with x hx
      simpa [NNReal.smul_def, C_pos.le]
    · exact ⟨0, continuous_zero, .rfl⟩
    · rintro r₁ r₂ ⟨s₁, s₁_cont, h₁⟩ ⟨s₂, s₂_cont, h₂⟩
      use s₁ ⊔ s₂, by fun_prop
      filter_upwards [h₁, h₂] with x h₁ h₂ using sup_le_sup h₁ h₂
    · rintro r₁ r₂ h ⟨s, s_cont, hs⟩
      exact ⟨s, s_cont, hs.mono fun x ↦ (h _).trans⟩
    · rintro r C ⟨s, s_cont, hs⟩
      refine ⟨C • s, s_cont.const_smul _, hs.mono fun x hx ↦ ?_⟩
      apply smul_le_smul le_rfl hx <;> simp

theorem isLittleOTVS_iff (hp : WithSeminorms p) (hq : WithSeminorms q) :
    f =o[𝕜; l] g ↔ ∀ i : ι, ∃ s : Finset κ, (p i ∘ f) =o[l] ((s.sup q : Seminorm 𝕜 F) ∘ g) := by
  sorry

end WithSeminorms

end
