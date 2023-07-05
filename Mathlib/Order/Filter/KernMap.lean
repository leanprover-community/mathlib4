/-
Copyright (c) 2023 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Order.Filter.Basic

open Set

namespace Filter

variable {α β : Type _} (m : α → β)

def kernMap (f : Filter α) : Filter β where
  sets := (kernImage m) '' f.sets
  univ_sets := ⟨univ, f.univ_sets, by simp [kernImage_eq_compl]⟩
  sets_of_superset := by
    rintro _ t ⟨s, hs, rfl⟩ hst
    refine ⟨m ⁻¹' t, mem_of_superset hs ?_, ?_⟩
    refine GaloisConnection.preimage
    exact ⟨f.sets_of_superset hm (subset_union_left s _), kern_image_upward_closed m hi⟩
  inter_sets := by
    rintro _ _ ⟨s₁, h₁, rfl⟩ ⟨s₂, h₂, rfl⟩
    use [s₁ ∩ s₂, f.inter_sets h₁ h₂]
    simp only [kern_image_eq_compl, compl_inter, image_union, compl_union]

end Filter
