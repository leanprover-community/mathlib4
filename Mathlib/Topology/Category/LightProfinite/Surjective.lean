import Mathlib.Topology.Category.LightProfinite.Maps
import Mathlib.Topology.Category.Profinite.CofilteredLimit

open CategoryTheory Limits

namespace LightProfinite

variable (M : ℕᵒᵖ ⥤ LightProfinite)
  (hM : ∀ (n : ℕ), Function.Surjective (M.map ⟨homOfLE (Nat.le_succ n)⟩))
  (c : Cone M) (hc : IsLimit c)

lemma sequentialLimit_of_surjections_surjective :
    Function.Surjective (c.π.app ⟨0⟩) := by
  rw [eq_homMk (c.π.app ⟨0⟩)]
  apply homMk_surjective
  intro a n
  let hc' : IsLimit (lightToProfinite.mapCone c) := sorry
  obtain ⟨⟨m⟩, g, h⟩ := Profinite.exists_locallyConstant (lightToProfinite.mapCone c) hc'
    (locallyConstant_of_hom (c.π.app ⟨0⟩) n)
  sorry
