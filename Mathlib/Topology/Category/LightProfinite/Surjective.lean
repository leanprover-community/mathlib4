import Mathlib.Topology.Category.LightProfinite.Maps
import Mathlib.Topology.Category.Profinite.CofilteredLimit

open CategoryTheory Limits

namespace LightProfinite

variable (M : ℕᵒᵖ ⥤ LightProfinite)
  (hM : ∀ (n : ℕ), Function.Surjective (M.map ⟨homOfLE (Nat.le_succ n)⟩))
  (c : Cone M) (hc : IsLimit c)

lemma exists_locallyConstant (hc : IsLimit c) {X : Type*} (f : LocallyConstant c.pt X) :
    ∃ (n : ℕ) (g : LocallyConstant (M.obj ⟨n⟩) X), f = g.comap (c.π.app ⟨n⟩) := sorry

lemma sequentialLimit_of_surjections_surjective :
    Function.Surjective (c.π.app ⟨0⟩) := by
  rw [eq_homMk (c.π.app ⟨0⟩)]
  apply homMk_surjective
  intro a n
  obtain ⟨m, g, h⟩ := exists_locallyConstant M c hc (locallyConstant_of_hom (c.π.app ⟨0⟩) n)
  change ∃ b, (locallyConstant_of_hom (c.π.app ⟨0⟩) n) b = proj (M.obj ⟨0⟩) n a
  rw [h]
  sorry
  -- rw [LocallyConstant.coe_comap _ _ (c.π.app ⟨m⟩).continuous]
