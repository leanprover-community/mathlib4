module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Module.Dual

public section

section HahnBanach.lean

open RCLike Module ContinuousLinearEquiv Submodule

variable (𝕜 : Type*) [RCLike 𝕜] {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem exists_dual_vector_of_seminormed (x : E) : ∃ g : StrongDual 𝕜 E, ‖g‖ ≤ 1 ∧ g x = ‖x‖ := by
  by_cases hx : 0 < ‖x‖
  · have hnz : x ≠ 0 := by aesop
    have hhom := LinearEquiv.toSpanNonzeroSingleton_homothety 𝕜 x hnz
    let coord := (ofHomothety _ _ hx hhom).symm.toContinuousLinearMap
    obtain ⟨g, hg⟩ := exists_extension_norm_eq (𝕜 ∙ x) ((‖x‖ : 𝕜) • coord)
    refine ⟨g, ?_, ?_⟩
    · grw [hg.2, algebraMap_smul, norm_smul, norm_norm, coord.opNorm_le_bound (by positivity)
        (fun x ↦ (homothety_inverse _ hx _ hhom x).le), mul_inv_cancel₀ hx.ne']
    · have hgx : g x = g (⟨x, by simp⟩ : 𝕜 ∙ x) := by rw [Submodule.coe_mk]
      have hc : coord ⟨x, by simp⟩ = 1 := LinearEquiv.coord_self 𝕜 E x hnz
      simp [-algebraMap_smul, hgx, ↓hg.1, hc]
  · exact ⟨0, by simp, by simp [le_antisymm (not_lt.mp hx) (norm_nonneg x)]⟩

variable (𝕜 : Type*) [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem exists_dual_vector_new (x : E) (h : x ≠ 0) : ∃ g : StrongDual 𝕜 E, ‖g‖ = 1 ∧ g x = ‖x‖ := by
  obtain ⟨g, hg⟩ := exists_dual_vector_of_seminormed 𝕜 x
  refine ⟨g,  g.opNorm_eq_of_bounds (by simp) (g.le_of_opNorm_le hg.1) (fun _ _ hx =>
    one_le_of_le_mul_right₀ (norm_pos_iff.mpr h) (by simpa [hg.2] using hx x)), hg.2⟩

end HahnBanach.lean


section Dual.lean

noncomputable section

open Topology Bornology

universe u v

namespace NormedSpace

section BidualIsometry

variable (𝕜 : Type*) [RCLike 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The inclusion of a normed space in its double strong dual is an isometry onto its image. -/
def inclusionInDoubleDualLi_seminormed : E →ₗᵢ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
  { inclusionInDoubleDual 𝕜 E with
    norm_map' x := by
      apply le_antisymm (double_dual_bound 𝕜 E x)
      obtain ⟨g, hg⟩ := exists_dual_vector_of_seminormed 𝕜 x
      have := (inclusionInDoubleDual 𝕜 E x).le_opNorm g
      grw [hg.1, mul_one] at this
      simpa [hg.2] }

theorem norm_le_dual_bound_seminormed (x : E) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ f : StrongDual 𝕜 E, ‖f x‖ ≤ M * ‖f‖) : ‖x‖ ≤ M := by
  rw [← (inclusionInDoubleDualLi_seminormed 𝕜).norm_map x]
  exact ContinuousLinearMap.opNorm_le_bound _ hMp hM

end BidualIsometry

end NormedSpace

end

end Dual.lean
