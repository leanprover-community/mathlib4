/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Sébastien Gouëzel

! This file was ported from Lean 3 source module topology.metric_space.cau_seq_filter
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Completeness in terms of `Cauchy` filters vs `isCauSeq` sequences

In this file we apply `Metric.complete_of_cauchySeq_tendsto` to prove that a `NormedRing`
is complete in terms of `Cauchy` filter if and only if it is complete in terms
of `CauSeq` Cauchy sequences.
-/


universe u v

open Set Filter

open Topology Classical

variable {β : Type v}

theorem CauSeq.tendsto_limit [NormedRing β] [hn : IsAbsoluteValue (norm : β → ℝ)]
    (f : CauSeq β norm) [CauSeq.IsComplete β norm] : Tendsto f atTop (𝓝 f.lim) :=
  tendsto_nhds.mpr
    (by
      intro s os lfs
      suffices ∃ a : ℕ, ∀ b : ℕ, b ≥ a → f b ∈ s by simpa using this
      rcases Metric.isOpen_iff.1 os _ lfs with ⟨ε, ⟨hε, hεs⟩⟩
      cases' Setoid.symm (CauSeq.equiv_lim f) _ hε with N hN
      exists N
      intro b hb
      apply hεs
      dsimp [Metric.ball]
      rw [dist_comm, dist_eq_norm]
      solve_by_elim)
#align cau_seq.tendsto_limit CauSeq.tendsto_limit

variable [NormedField β]

/-
 This section shows that if we have a uniform space generated by an absolute value, topological
 completeness and Cauchy sequence completeness coincide. The problem is that there isn't
 a good notion of "uniform space generated by an absolute value", so right now this is
 specific to norm. Furthermore, norm only instantiates IsAbsoluteValue on NormedDivisionRing.
 This needs to be fixed, since it prevents showing that ℤ_[hp] is complete.
-/
open Metric

theorem CauchySeq.isCauSeq {f : ℕ → β} (hf : CauchySeq f) : IsCauSeq norm f := by
  cases' cauchy_iff.1 hf with hf1 hf2
  intro ε hε
  rcases hf2 { x | dist x.1 x.2 < ε } (dist_mem_uniformity hε) with ⟨t, ⟨ht, htsub⟩⟩
  simp at ht; cases' ht with N hN
  exists N
  intro j hj
  rw [← dist_eq_norm]
  apply @htsub (f j, f N)
  apply Set.mk_mem_prod <;> solve_by_elim [le_refl]
#align cauchy_seq.is_cau_seq CauchySeq.isCauSeq

theorem CauSeq.cauchySeq (f : CauSeq β norm) : CauchySeq f := by
  refine' cauchy_iff.2 ⟨by infer_instance, fun s hs => _⟩
  rcases mem_uniformity_dist.1 hs with ⟨ε, ⟨hε, hεs⟩⟩
  cases' CauSeq.cauchy₂ f hε with N hN
  exists { n | n ≥ N }.image f
  simp only [exists_prop, mem_atTop_sets, mem_map, mem_image, ge_iff_le, mem_setOf_eq]
  constructor
  · exists N
    intro b hb
    exists b
  · rintro ⟨a, b⟩ ⟨⟨a', ⟨ha'1, ha'2⟩⟩, ⟨b', ⟨hb'1, hb'2⟩⟩⟩
    dsimp at ha'1 ha'2 hb'1 hb'2
    rw [← ha'2, ← hb'2]
    apply hεs
    rw [dist_eq_norm]
    apply hN <;> assumption
#align cau_seq.cauchy_seq CauSeq.cauchySeq

/-- In a normed field, `CauSeq` coincides with the usual notion of Cauchy sequences. -/
theorem cau_seq_iff_cauchySeq {α : Type u} [NormedField α] {u : ℕ → α} :
    IsCauSeq norm u ↔ CauchySeq u :=
  ⟨fun h => CauSeq.cauchySeq ⟨u, h⟩, fun h => h.isCauSeq⟩
#align cau_seq_iff_cauchy_seq cau_seq_iff_cauchySeq

-- see Note [lower instance priority]
/-- A complete normed field is complete as a metric space, as Cauchy sequences converge by
assumption and this suffices to characterize completeness. -/
instance (priority := 100) completeSpace_of_cau_seq_complete [CauSeq.IsComplete β norm] :
    CompleteSpace β := by
  apply complete_of_cauchySeq_tendsto
  intro u hu
  have C : IsCauSeq norm u := cau_seq_iff_cauchySeq.2 hu
  exists CauSeq.lim ⟨u, C⟩
  rw [Metric.tendsto_atTop]
  intro ε εpos
  cases' (CauSeq.equiv_lim ⟨u, C⟩) _ εpos with N hN
  exists N
  simpa [dist_eq_norm] using hN
#align complete_space_of_cau_seq_complete completeSpace_of_cau_seq_complete
