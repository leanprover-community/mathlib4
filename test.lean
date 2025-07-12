import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RCLike

-- Lemma 1.2.9
theorem biInter_halfSpaces_eq {𝕜 E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    {s : Set E} [RCLike 𝕜] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [LocallyConvexSpace ℝ E] (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) (hs₃ : s.Nonempty) :
    ⋂ l ∈ {l : E →L[𝕜] 𝕜 | BddAbove (re ∘ l '' s)},
      {x | re (l x) ≤ ⨆ y : s, re (l y)} = s := by
  ext1 x
  simp only [Set.mem_setOf_eq, Set.mem_iInter]
  refine ⟨fun h ↦ ?_, fun hxs ↦ ?_⟩
  · by_contra hxs
    obtain ⟨l, r, hlA, hl⟩ := geometric_hahn_banach_closed_point (𝕜 := 𝕜) hs₁ hs₂ hxs
    refine ((hl.trans_le (h l ⟨r, ?_⟩)).trans_le ?_).false
    · rintro _ ⟨y, hys, rfl⟩
      exact (hlA y hys).le
    · have : Nonempty s := hs₃.to_subtype
      apply ciSup_le fun ⟨y, hys⟩ ↦ (hlA y hys).le
  · intro l hbdd
    exact le_ciSup_set hbdd hxs

end RCLike
