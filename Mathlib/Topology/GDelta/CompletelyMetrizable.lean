/-
Copyright (c) 2026 Justin Palumbo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Palumbo
-/
module


public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.Topology.Separation.GDelta

/-!
# Completely metrizable subspaces of a T6 are 'Gδ'.

## Main results
This file provides a proof that all completely metrizable subspaces of
a T6 space are Gδ. In particular, all completely metrizable subspaces of
a metric space are Gδ. This result is commonly credited to Alexandrov,
where it is usually framed in terms of Polish spaces - Polish subspaces of
a Polish space are Gδ.
-/

public section

open Set Metric Topology TopologicalSpace Filter
open scoped ENNReal

namespace TopologicalSpace.IsCompletelyMetrizableSpace

variable {X : Type*} [TopologicalSpace X] [T6Space X]

/-- **Alexandrov's theorem**: a subspace of a T6 space which is completely
metrizable for the subspace topology is a `Gδ` set. -/
theorem isGδ {s : Set X} (hs : IsCompletelyMetrizableSpace s) : IsGδ s := by
  let := upgradeIsCompletelyMetrizable s
  let U : ℕ → Set X := fun n : ℕ ↦ ⋃₀
      {V : Set X | IsOpen V ∧ (ediam ((↑) ⁻¹' V : Set s) ≤ (n : ℝ≥0∞)⁻¹)}
  have hopen : ∀ n, IsOpen (U n) := fun n ↦ isOpen_sUnion (fun t hht ↦ hht.1)
  -- `closure s` is Gδ because all closed sets are Gδ in perfectly normal spaces,
  -- and every `U n` is Gδ by virtue of being open
  -- so it's sufficient to prove `s` is their intersection
  suffices s = closure s ∩ (⋂ n, U n) by
    rw [this]
    apply (isClosed_closure (s := s)).isGδ.inter
    apply IsGδ.iInter
    exact fun n ↦ (hopen n).isGδ
  ext x
  constructor
  · intro hx
    refine ⟨subset_closure hx, ?_⟩
    rw [mem_iInter]
    intro n
    -- take the ball of radius `(n : ℝ≥0∞)⁻¹ / 2` around `x` in `s`'s metric,
    -- the ball is induced by some open set `V` of `X`, whose s diameter is no larger
    set c : ↥s := ⟨x, hx⟩
    have hr0 : 0 < (n : ℝ≥0∞)⁻¹ / 2 := ENNReal.div_pos (by simp) (by simp)
    obtain ⟨V, hVopen, hVeq⟩ :=
        (IsInducing.subtypeVal (t := s)).isOpen_iff.1
          (isOpen_eball (x := c) (r := (n : ℝ≥0∞)⁻¹ / 2))
    refine ⟨V, ⟨hVopen, ?_⟩, hVeq.symm.subset (mem_eball_self hr0)⟩
    rw [hVeq]
    refine ediam_le fun a ha b hb ↦ ?_
    calc edist a b ≤ edist a c + edist c b := edist_triangle a c b
      _ ≤ (n : ℝ≥0∞)⁻¹ / 2 + (n : ℝ≥0∞)⁻¹ / 2 :=
            add_le_add (mem_eball.1 ha).le (mem_eball'.1 hb).le
      _ = (n : ℝ≥0∞)⁻¹ := ENNReal.add_halves _
  · rintro ⟨hx, hxU⟩
    -- The hypotheses on x allow us to build a Cauchy sequence (filter)
    -- around x within s. The completeness of s gives us a limit within s,
    -- which is also a limit in the larger space, and so it coincides with x.
    let F : Filter ↥s := comap ((↑) : ↥s → X) (𝓝 x)
    have hfnebot : F.NeBot :=
      comap_neBot_iff.mpr (mem_closure_iff_nhds'.1 hx)
    have hFc : Cauchy F := by
      refine EMetric.cauchy_iff.2 ⟨hfnebot.ne', fun ε hε ↦ ?_⟩
      -- pick `n` with `(n : ℝ≥0∞)⁻¹ < ε`; the corresponding `V` from `x ∈ U n`
      -- traces out a set of `F` of diameter under `ε`
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hε.ne'
      obtain ⟨V, ⟨hVopen, hVdiam⟩, hxV⟩ := mem_iInter.1 hxU n
      refine ⟨(↑) ⁻¹' V, preimage_mem_comap (hVopen.mem_nhds hxV),
        fun a ha b hb ↦ ?_⟩
      exact ((edist_le_ediam_of_mem ha hb).trans hVdiam).trans_lt hn
    obtain ⟨y, hy⟩ := CompleteSpace.complete hFc
    have hxy : x = ↑y :=
      tendsto_nhds_unique map_comap_le
        (continuous_subtype_val.continuousAt.mono_left hy)
    rw [hxy]
    exact Subtype.coe_prop y

end TopologicalSpace.IsCompletelyMetrizableSpace
