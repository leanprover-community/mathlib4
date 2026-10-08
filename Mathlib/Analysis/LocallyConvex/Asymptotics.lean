/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Moritz Doll
-/
module

public import Mathlib.Analysis.Asymptotics.TVS
public import Mathlib.Analysis.Asymptotics.Basic
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Asymptotics for locally convex topological vector spaces

We provide a characterization of `IsBigOTVS` and `IsLittleOTVS` in terms of continuous seminorms
and families of seminorms.

## Main results:

* `PolynormableSpace.isBigOTVS_iff`
* `PolynormableSpace.isLittleOTVS_iff`
* `WithSeminorms.isBigOTVS_iff`
* `WithSeminorms.isLittleOTVS_iff`

-/

@[expose] public section

open scoped NNReal
open Filter

variable {ι κ α 𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F]
variable {f f₁ f₂ : α → E} {g g₁ g₂ : α → F} {l : Filter α}

namespace Seminorm

theorem isBigO_comp_iff {p : Seminorm 𝕜 E} {q : Seminorm 𝕜 F} :
    (p ∘ f) =O[l] (q ∘ g) ↔ ∃ C : ℝ≥0, p ∘ f ≤ᶠ[l] (C • q) ∘ g := by
  simp [Asymptotics.isBigO_iff_nnnorm, EventuallyLE, NNReal.smul_def, ← NNReal.coe_le_coe]

theorem isLittleO_comp_iff {p : Seminorm 𝕜 E} {q : Seminorm 𝕜 F} :
    (p ∘ f) =o[l] (q ∘ g) ↔ ∀ ε : ℝ≥0, ε ≠ 0 → p ∘ f ≤ᶠ[l] (ε • q) ∘ g := by
  simp [Asymptotics.isLittleO_iff_nnnorm, EventuallyLE, NNReal.smul_def, ← NNReal.coe_le_coe]

end Seminorm

variable [TopologicalSpace E] [TopologicalSpace F]

namespace PolynormableSpace

variable [PolynormableSpace 𝕜 E] [PolynormableSpace 𝕜 F]

theorem isBigOTVS_iff_le :
    f =O[𝕜; l] g ↔ ∀ p : Seminorm 𝕜 E, Continuous p → ∃ q : Seminorm 𝕜 F,
      Continuous q ∧ p ∘ f ≤ᶠ[l] q ∘ g := by
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  rw [(PolynormableSpace.hasBasis_zero_ball 𝕜 E).isBigOTVS_iff
      (PolynormableSpace.hasBasis_zero_ball 𝕜 F)]
  congrm ∀ p, _ → ?_
  constructor <;> rintro ⟨q, q_cont, hq⟩ <;>
  refine ⟨‖c‖₊ • q, q_cont.const_smul _, hq.mono fun x hx ↦ ?_⟩
  · simpa using Seminorm.le_smul_of_le_egauge_unitBall_le_mul 1 hc (by simpa using hx)
  · simpa using Seminorm.egauge_unitBall_le_mul_of_le_smul 1 hc (by simpa using hx)

theorem isBigOTVS_iff :
    f =O[𝕜; l] g ↔ ∀ p : Seminorm 𝕜 E, Continuous p → ∃ q : Seminorm 𝕜 F,
      Continuous q ∧ (p ∘ f) =O[l] (q ∘ g) := by
  simp_rw [isBigOTVS_iff_le, Seminorm.isBigO_comp_iff]
  congrm ∀ p p_cont, ?_
  exact ⟨fun ⟨q, q_cont, hq⟩ ↦ ⟨q, q_cont, 1, by simpa⟩,
    fun ⟨q, q_cont, C, hC⟩ ↦ ⟨C • q, q_cont.const_smul _, hC⟩⟩

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
  · exact Seminorm.le_smul_of_le_egauge_unitBall_le_mul ε hc hx
  · exact Seminorm.egauge_unitBall_le_mul_of_le_smul ε hc hx

theorem isLittleOTVS_iff :
    f =o[𝕜; l] g ↔ ∀ p : Seminorm 𝕜 E, Continuous p → ∃ q : Seminorm 𝕜 F,
      Continuous q ∧ (p ∘ f) =o[l] (q ∘ g) := by
  simp_rw [isLittleOTVS_iff_le, Seminorm.isLittleO_comp_iff]

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
    refine hp.induction_add_of_continuous H ?_ ?_ ?_ ?_ r_cont
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
  · exact fun ⟨s, C, hC⟩ ↦ ⟨C • s.sup q, (hq.continuous_finsetSup_seminorm s).const_smul _, hC⟩

theorem isBigOTVS_iff (hp : WithSeminorms p) (hq : WithSeminorms q) :
    f =O[𝕜; l] g ↔ ∀ i : ι, ∃ s : Finset κ, (p i ∘ f) =O[l] (↑(s.sup q) ∘ g) := by
  simp_rw [hp.isBigOTVS_iff_le hq, Seminorm.isBigO_comp_iff]

theorem isLittleOTVS_iff_le_continuous (hp : WithSeminorms p) [PolynormableSpace 𝕜 F] :
    f =o[𝕜; l] g ↔
      ∀ i : ι, ∃ q : Seminorm 𝕜 F, Continuous q ∧
        ∀ ε : ℝ≥0, ε ≠ 0 → p i ∘ f ≤ᶠ[l] ((ε • q) ∘ g) := by
  have := hp.toPolynormableSpace
  rw [PolynormableSpace.isLittleOTVS_iff_le]
  constructor <;> intro H
  · exact fun i ↦ H (p i) (hp.continuous_seminorm i)
  · intro r r_cont
    refine hp.induction_add_of_continuous H ?_ ?_ ?_ ?_ r_cont
    · exact ⟨0, continuous_zero, by simp [Filter.EventuallyLE.refl]⟩
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
    refine ⟨s, fun ε ε_ne ↦ (hr (ε / C) (by positivity)).mono fun x hx ↦ ?_⟩
    simp only [Function.comp_apply, Seminorm.le_def, smul_apply] at hx hC ⊢
    grw [hx, hC _, ← mul_smul, div_mul_cancel₀ _ C_ne]
  · intro ⟨s, hs⟩
    use s.sup q, hq.continuous_finsetSup_seminorm s

theorem isLittleOTVS_iff (hp : WithSeminorms p) (hq : WithSeminorms q) :
    f =o[𝕜; l] g ↔ ∀ i : ι, ∃ s : Finset κ, (p i ∘ f) =o[l] ((s.sup q : Seminorm 𝕜 F) ∘ g) := by
  simp_rw [hp.isLittleOTVS_iff_le hq, Seminorm.isLittleO_comp_iff]

end WithSeminorms

end
