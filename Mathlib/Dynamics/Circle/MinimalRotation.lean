import Mathlib.Topology.Instances.AddCircle
import Mathlib.Topology.Instances.Irrational
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
-/

open Set
open scoped Pointwise

#check AddSubgroup.dense_or_cyclic

namespace AddCircle

theorem dense_zmultiples_tfae (a p : ℝ) :
    List.TFAE [
      Dense (AddSubmonoid.multiples (a : AddCircle p) : Set (AddCircle p)),
      Dense (AddSubgroup.zmultiples (a : AddCircle p) : Set (AddCircle p)),
      Dense (AddSubgroup.closure {a, p} : Set ℝ),
      Irrational (a / p)
    ] := by
  tfae_have 1 → 2
  · refine fun h ↦ h.mono <| range_subset_iff.2 fun k ↦ ?_
    exact ⟨k, mod_cast rfl⟩
  tfae_have 2 ↔ 3
  · rw [← QuotientAddGroup.coe_mk', ← AddMonoidHom.map_zmultiples, AddSubgroup.coe_map,
      QuotientAddGroup.coe_mk', QuotientAddGroup.dense_image_mk,
      insert_eq, AddSubgroup.closure_union, AddSubgroup.zmultiples_eq_closure,
      AddSubgroup.zmultiples_eq_closure, AddSubgroup.add_normal]
  tfae_have 3 → 4
  · rintro h ⟨q, hq⟩
    rcases eq_or_ne p 0 with rfl | hp
    · rcases eq_or_ne a 0 with rfl | ha
      · specialize h 1
        simp [AddSubgroup.closure_singleton_zero] at h
      · 


end AddCircle
