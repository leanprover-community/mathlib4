/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Cocompact subgroups

A subgroup `H` of a topological group `G` is cocompact if the quotient `G ⧸ H` is compact.

## Main statements

* `Subgroup.isCocompact_iff_exists_isCompact_mul_eq_univ`: in a weakly locally compact group,
  `H` is cocompact if and only if `C * H = G` for some compact set `C`.
-/

@[expose] public section

open scoped Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace Subgroup

/-- A subgroup `H` of a topological group `G` is cocompact if the quotient `G ⧸ H` is compact. -/
@[to_additive /-- A subgroup `H` of an additive topological group `G` is cocompact if the quotient
`G ⧸ H` is compact. -/]
abbrev IsCocompact (H : Subgroup G) : Prop := CompactSpace (G ⧸ H)

variable (H : Subgroup G)

/-- If `C * H = G` for some compact set `C`, then `H` is cocompact. -/
@[to_additive /-- If `C + H = G` for some compact set `C`, then `H` is cocompact. -/]
theorem IsCocompact.of_isCompact_mul_eq_univ {C : Set G} (hC : IsCompact C)
    (h : C * (H : Set G) = Set.univ) : H.IsCocompact where
  isCompact_univ := by
    refine (Set.eq_univ_of_forall fun x ↦ ?_) ▸ hC.image QuotientGroup.continuous_mk
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨c, hc, h, hh, rfl⟩ := h ▸ Set.mem_univ g
    exact ⟨c, hc, (QuotientGroup.mk_mul_of_mem c hh).symm⟩

/-- In a weakly locally compact group, a cocompact subgroup `H` satisfies `C * H = G` for some
compact set `C`. -/
@[to_additive /-- In a weakly locally compact additive group, a cocompact subgroup `H` satisfies
`C + H = G` for some compact set `C`. -/]
theorem exists_isCompact_mul_eq_univ_of_isCocompact [SeparatelyContinuousMul G]
    [WeaklyLocallyCompactSpace G] [H.IsCocompact] :
    ∃ C : Set G, IsCompact C ∧ C * (H : Set G) = Set.univ := by
  obtain ⟨C, hC, hCH⟩ :=
    (QuotientGroup.isOpenQuotientMap_mk (N := H)).exists_isCompact_subset_image isCompact_univ
  refine ⟨C, hC, Set.eq_univ_of_forall fun g ↦ ?_⟩
  obtain ⟨c, hc, hcg⟩ := hCH (Set.mem_univ (g : G ⧸ H))
  exact ⟨c, hc, c⁻¹ * g, QuotientGroup.eq.mp hcg, mul_inv_cancel_left c g⟩

@[to_additive]
theorem isCocompact_iff_exists_isCompact_mul_eq_univ [SeparatelyContinuousMul G]
    [WeaklyLocallyCompactSpace G] :
    H.IsCocompact ↔ ∃ C : Set G, IsCompact C ∧ C * (H : Set G) = Set.univ :=
  ⟨fun _ ↦ H.exists_isCompact_mul_eq_univ_of_isCocompact,
    fun ⟨_, hC, h⟩ ↦ IsCocompact.of_isCompact_mul_eq_univ H hC h⟩

end Subgroup

namespace AddSubgroup

variable {G X : Type*} [AddGroup G] [TopologicalSpace G] [TopologicalSpace X] {H : AddSubgroup G}

/-- A continuous function that is periodic with respect to every element of a cocompact subgroup
has compact range. -/
theorem IsCocompact.isCompact_range_of_periodic [H.IsCocompact] {f : G → X} (hf : Continuous f)
  (hper : ∀ h ∈ H, f.Periodic h) : IsCompact (Set.range f) := by
  refine Set.range_quotient_lift (s := QuotientAddGroup.leftRel H) _ ▸
    isCompact_range (hf.quotient_lift fun a b hab ↦ ?_)
  simpa using (hper _ (QuotientAddGroup.leftRel_apply.mp hab) a).symm

end AddSubgroup
