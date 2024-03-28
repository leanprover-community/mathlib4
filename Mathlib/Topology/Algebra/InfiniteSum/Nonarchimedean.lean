/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Infinite sums in nonarchimedean abelian groups

Let `G` be a complete nonarchimedean abelian group and let `f : α → G` be a function. We prove that
`f` is unconditionally summable if and only if `f a` tends to zero on the cofinite filter on `α`.
-/

open Filter Topology

namespace NonarchimedeanAddGroup

open scoped Pointwise

/-- Let `G` be a nonarchimedean abelian group, and let `f : α → G` be a function that tends to
zero on the filter of cofinite sets. For each finite subset of `α`, consider the partial sum of `f`
on that subset. These partial sums form a Cauchy filter. -/
theorem cauchy_partial_sums_of_tendsto_cofinite_zero {α G : Type*} [AddCommGroup G] [UniformSpace G]
    [UniformAddGroup G] [NonarchimedeanAddGroup G] [DecidableEq α] {f : α → G}
    (hf : Tendsto f cofinite (𝓝 0)) : Cauchy (map (fun S ↦ Finset.sum S f) atTop) := by
  constructor
  · exact map_neBot
  · /- Let `U` be an entourage of `G`. We wish to show that if we take the partial sum of `f` on two
    finite subsets `S₁, S₂` of `α`, the two results (taken together as an element of `G × G`)
    eventually lie in `U`. -/
    intro U hU

    /- Since `G` is nonarchimedean, there exists an open subgroup `H` of `G` such that
    `U` contains every pair of elements whose difference is in `H`. -/
    rcases uniformity_eq_comap_nhds_zero G ▸ hU with ⟨T, hT, hT'⟩
    rcases is_nonarchimedean T hT with ⟨H, hH⟩

    -- By our assumption `hf`, we have `f a ∈ H` for all `a` outside of some finite set `S`.
    let S : Finset α :=
        (mem_cofinite.mp <| mem_map.mp <| hf <| IsOpen.mem_nhds H.isOpen' H.zero_mem').toFinset
    have hS : ∀ a ∉ S, f a ∈ H := by simp [S]

    -- Let `V` be the coset of `H` that contains the sum of `f` over the set `S`.
    let V : Set G := Finset.sum S f +ᵥ (H : Set G)

    -- The partial sum of `f` on a subset eventually lies in `V`.
    have hV : V ∈ map (fun s ↦ Finset.sum s f) atTop := by
      /- We will, in fact, show that for all finite supersets `S'` of `S`, the partial sum of `f` on
      `S'` is in `V`. -/
      apply mem_of_superset <| mem_atTop S
      intro S' hS'

      /- Break the partial sum of `f` on `S'` into a sum on `S` and on `S' \ S`. The latter is a sum
      of elements of `H`, so it is in `H`. Therefore, the sum of `f` on `S'` is in the coset `V`,
      as desired. -/
      use Finset.sum (S' \ S) f
      constructor
      · apply AddSubgroup.sum_mem
        intro a ha
        exact hS a (Finset.mem_sdiff.mp ha).right
      · dsimp only [vadd_eq_add]
        rw [add_comm]
        exact Finset.sum_sdiff hS'

    -- By the above, it remains to show that `V ×ˢ V` is a subset of `U`.
    apply mem_prod_iff.mpr
    use V, hV, V, hV

    -- This follows from the fact that the difference of two elements of `V` lies in `H`.
    rintro ⟨_, _⟩ ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩
    apply hT'
    apply hH
    simpa using (AddSubgroup.sub_mem _ hy hx)

/-- Let `G` be a complete nonarchimedean abelian group, and let `f : α → G` be a function that tends
to zero on the filter of cofinite sets. Then `f` is unconditionally summable. -/
theorem summable_of_tendsto_cofinite_zero {α G : Type*} [AddCommGroup G] [UniformSpace G]
    [UniformAddGroup G] [CompleteSpace G] [NonarchimedeanAddGroup G] [DecidableEq α] {f : α → G}
    (hf : Tendsto f cofinite (𝓝 0)) : Summable f :=
  CompleteSpace.complete (cauchy_partial_sums_of_tendsto_cofinite_zero hf)

/-- Let `G` be a complete nonarchimedean abelian group. Then a function `f : α → G` is
unconditionally summable if and only if it tends to zero on the filter of cofinite sets. -/
theorem summable_iff_tendsto_cofinite_zero {α G : Type*} [AddCommGroup G] [UniformSpace G]
    [UniformAddGroup G] [CompleteSpace G] [NonarchimedeanAddGroup G] [DecidableEq α]
    (f : α → G) : Summable f ↔ Tendsto f cofinite (𝓝 0) :=
  ⟨Summable.tendsto_cofinite_zero, summable_of_tendsto_cofinite_zero⟩

end NonarchimedeanAddGroup
