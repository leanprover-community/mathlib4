/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.UrysohnsLemma

/-!
# Perfectly normal topological spaces.

This file proves some properties of a perfectly normal space.

## TODO

Prove that the product of a perfectly normal space and a metric space is perfectly normal.

-/

@[expose] public section

open Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A topological space is perfectly normal iff every closed set is the zero set of a continuous
function taking values in the unit interval. -/
theorem perfectlyNormalSpace_iff_forall_isClosed_preimage_zero :
    PerfectlyNormalSpace X ↔ ∀ s, IsClosed s → ∃ f : C(X, ℝ), s = f ⁻¹' {0} ∧
      range f ⊆ Icc 0 1 where
  mp h s hs := by
    -- write `s` as the intersection of a sequence of open sets `U n`
    obtain ⟨U, ho, hu⟩ := isGδ_iff_eq_iInter_nat.1 hs.isGδ
    have (n : ℕ) : Disjoint s (U n)ᶜ := by
      apply HasSubset.Subset.disjoint_compl_right
      grw [hu, iInter_subset]
    -- for each `n`, construct a continuous function `f n` that separates `s` from `(U n)ᶜ`
    choose f hfs hfu hfr using fun n =>
      exists_continuous_zero_one_of_isClosed hs (ho n).isClosed_compl (this n)
    have hsb (x : X) (n : ℕ) : ‖(f n) x * (1 / 2 / 2 ^ n)‖ ≤ 1 / 2 / 2 ^ n := by
      simp [abs_of_nonneg (hfr n x).1, (hfr n x).2]
    have hsx (x : X) : Summable fun n => f n x * (1 / 2 / 2 ^ n) :=
      (summable_geometric_two' 1).of_norm_bounded fun n => hsb x n
    -- consider the infinite sum of `f n x * (1 / 2 / 2 ^ n)`, which is uniformly convergent and
    -- thus continuous because it is dominated by a geometric series
    let h : C(X, ℝ) :=
      { toFun x := ∑' n, f n x * (1 / 2 / 2 ^ n)
        continuous_toFun :=
          continuous_tsum (fun n => by fun_prop) (summable_geometric_two' 1) fun n x => hsb x n }
    refine ⟨h, ?_, fun r ⟨x, hx⟩ => ⟨?_, ?_⟩⟩
    · ext x
      refine ⟨fun hp => ?_, fun hp => ?_⟩
      · suffices ∀ n, f n x = 0 from by simp [h, this]
        exact fun n => hfs n hp
      · contrapose h
        simp only [preimage, notMem_setOf_iff, ContinuousMap.coe_mk, mem_singleton_iff]
        apply ne_of_gt
        obtain ⟨i, hi⟩ := mem_iUnion.1 <| compl_iInter _ ▸ mem_compl (hu ▸ h)
        calc
        _ < 1 / 2 / 2 ^ i := by positivity
        _ = f i x * (1 / 2 / 2 ^ i) := by simp [hfu i hi]
        _ ≤ _ := (hsx x).le_tsum i fun j hj => by positivity [(hfr j x).1]
    · exact hx ▸ tsum_nonneg fun n => by simp [(hfr n x).1]
    · calc
      _ = ∑' n, f n x * (1 / 2 / 2 ^ n) := by simp [← hx, h]
      _ ≤ ∑' n, 1 / 2 / 2 ^ n :=
        (hsx x).tsum_le_tsum (fun n => by simp [(hfr n x).2]) (summable_geometric_two' 1)
      _ = _ := tsum_geometric_two' 1
  mpr h :=
    { normal s t hs ht hst := by
        -- pick `f, g` such that `s = f ⁻¹' {0}` and `t = g ⁻¹' {0}`, and then the function
        -- `f / (f  + g)` separates `s` and `t`.
        obtain ⟨f, hf, hfr⟩ := h s hs
        obtain ⟨g, hg, hgr⟩ := h t ht
        have hsn : SeparatedNhds {(0 : ℝ)} {1} :=
          SeparatedNhds.of_finite (finite_singleton _) (finite_singleton _)
          (disjoint_singleton.2 zero_ne_one)
        have hfg (x : X) : f x + g x ≠ 0 := by
          simp_all only [preimage, mem_singleton_iff]
          by_cases! hfx : f x = 0
          · simpa [hfx] using hst.notMem_of_mem_left hfx
          · simp only [range, Icc, setOf_subset_setOf, forall_exists_index,
              forall_apply_eq_imp_iff] at hfr hgr
            positivity [(hgr x).1, (hfr x).1]
        have hp : s = (fun a => f a / (f a + g a)) ⁻¹' {0} := by simp_all [preimage]
        have : t = (fun a => f a / (f a + g a)) ⁻¹' {1} := by simp_all [preimage, div_eq_one_iff_eq]
        rw [hp, this]
        exact hsn.preimage (f.continuous.div₀ (f.continuous.add g.continuous) hfg)
      closed_gdelta s hs := by
        by_cases! hse : s = ∅
        · simp_all
        -- pick `f` such that `s = f ⁻¹' {0} = ⋂ n, f ⁻¹' {(-1, 1 / (n + 1))}`
        obtain ⟨f, hf, hfr⟩ := h s hs
        refine isGδ_iff_eq_iInter_nat.2 ⟨fun n => f ⁻¹' (Ioo (-1 : ℝ) (1 / (n + 1))),
          fun n => ?_, ?_⟩
        · exact f.continuous.isOpen_preimage _ isOpen_Ioo
        · simp only [hf, ← preimage_iInter,
            ← preimage_range_inter (s := ⋂ (n : ℕ), Ioo (-1 : ℝ) (1 / (n + 1))), inter_iInter]
          congr
          rw [eq_comm, eq_singleton_iff_unique_mem]
          refine ⟨mem_iInter_of_mem fun n => ?_, fun x h => ?_⟩
          · exact ⟨(hf ▸ hse : (f ⁻¹' {0}).Nonempty), by norm_num, by positivity⟩
          · apply le_antisymm
            · simp only [mem_iInter, mem_inter_iff, mem_Ioo] at h
              exact ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat (fun n => (h n).2.2.le)
            · exact (hfr (mem_iInter.1 h 0).1).1 }

theorem Topology.IsEmbedding.perfectlyNormalSpace {e : X → Y} (he : IsEmbedding e)
    [PerfectlyNormalSpace Y] : PerfectlyNormalSpace X := by
  rw [perfectlyNormalSpace_iff_forall_isClosed_preimage_zero]
  intro t ht
  obtain ⟨c, hc⟩ : ∃ c, IsClosed c ∧ e '' t = c ∩ range e := he.image_eq_isClosed_inter_range ht
  obtain ⟨f, rfl, hf⟩ :=
    perfectlyNormalSpace_iff_forall_isClosed_preimage_zero.1 inferInstance c hc.1
  refine ⟨⟨f ∘ e, f.continuous.comp he.continuous⟩, ?_, (range_comp_subset_range e f).trans hf⟩
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have hx' : e x ∈ e '' t := mem_image_of_mem e hx
    simp_all
  · have hx' : e x ∈ e '' t := by simp_all
    exact he.injective.mem_set_image.1 hx'

instance {s : Set X} [PerfectlyNormalSpace X] : PerfectlyNormalSpace s :=
  IsEmbedding.subtypeVal.perfectlyNormalSpace
