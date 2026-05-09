/-
Copyright (c) 2026 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Semicontinuity.TVSandMetric
public import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Continuous
import Mathlib.Topology.Separation.AlexandrovDiscrete
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Michael's selection theorem

This file proves Michael's selection theorem, that a lower hemicontinuous function with
convex closed nonempty values admits a continuous selection.

## Main results

- `HasOpenLowerSections.exists_continuous_selection`: A correspondence with open lower sections and
  convex, nonempty values admits a continuous selection. A key ingredient to the proof of Michael's
  selection theorem. This holds in any topological vector space over ℝ.
- `LowerHemicontinuous.exists_continuous_selection`: Michael's selection theorem that a lower
  hemicontinous function from a paracompact space to a Banach space which takes convex, closed,
  nonempty values admits a continuous selection.
-/

public section

open Set Metric
open scoped Pointwise Topology

variable {α β : Type*} {f : α → Set β} {g : α → β}
  [TopologicalSpace α] [NormalSpace α] [ParacompactSpace α]

section approximate

variable [AddCommGroup β] [Module ℝ β] [TopologicalSpace β] [ContinuousAdd β]
  [ContinuousSMul ℝ β] {f : α → Set β}

/-- **Michael's selection theorem (approximate):** A correspondence with open lower sections and
convex, nonempty values admits a continuous selection. This holds in any topological vector space
over ℝ. -/
lemma HasOpenLowerSections.exists_continuous_selection (hf : HasOpenLowerSections f)
    (hf_nonempty : ∀ x, (f x).Nonempty) (hf_convex : ∀ x, Convex ℝ (f x)) :
    ∃ h : α → β, Continuous h ∧ ∀ x, h x ∈ f x := by
  choose F hF using hf_nonempty
  obtain ⟨φ, hφ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    _ (fun x' ↦ hf.isOpen (F x')) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hF x⟩)
  exact ⟨fun y ↦ ∑ᶠ x', (φ x' y) • F x',
    φ.continuous_finsum_smul (fun _ _ _ ↦ continuousAt_const), fun y ↦
    (hf_convex y).finsum_mem (fun i ↦ φ.nonneg i y) (φ.sum_eq_one (mem_univ y)) fun x' hx' ↦
      hφ x' (subset_tsupport _ hx')⟩

end approximate

section michael

variable [AddCommGroup β] [Module ℝ β] [UniformSpace β] [IsUniformAddGroup β]
    [ContinuousSMul ℝ β] [LocallyConvexSpace ℝ β] [FirstCountableTopology β] [CompleteSpace β]

/-- **Michael's selection theorem**: A lower hemicontinuous function from a paracompact Hausdorff
space (which is necessarily normal) to a Banach space with nonempty convex closed values
admits a continuous selection -/
theorem LowerHemicontinuous.exists_continuous_selection (hf : LowerHemicontinuous f)
    (hf_nonempty : ∀ x, (f x).Nonempty) (hf_convex : ∀ x, Convex ℝ (f x))
    (hf_isClosed : ∀ x, IsClosed (f x)) : ∃ g : α → β, Continuous g ∧ ∀ x, g x ∈ f x := by
  obtain ⟨V, hV⟩ := LocallyConvexSpace.convex_open_symm_add_closure_subset_hasAntitoneBasis_zero ℝ β
  -- Produce a sequence of continuous approximations to a selection
  obtain ⟨g, hg_cont, hg_mem⟩ :=
    hf.hasOpenCGraph_add_isOpen (V := V 0) (hV.1 0).2.1
      |>.hasOpenLowerSections.exists_continuous_selection
      (by simp only [add_nonempty, hf_nonempty, true_and]; intro _; use 0; exact (hV.1 0).1)
      (fun x ↦ (hf_convex x).add (hV.1 0).2.2.1)
  obtain ⟨h, hh_cont, hh_mem, hh_mem_ball⟩ : ∃ h : ℕ → α → β, (∀ n, Continuous (h n)) ∧
      (∀ n x, h n x ∈ f x + (V n)) ∧
      (∀ n x, h (n + 1) x - h n x ∈ V n) := by
    let P (n : ℕ) (h : α → β) := Continuous h ∧ ∀ x, h x ∈ f x + (V n)
    have step : ∀ n hn, P n hn →
        ∃ h', P (n + 1) h' ∧ ∀ x, (h' x) - (hn x) ∈ V n := by
      intro n hn hn_prop
      have : HasOpenLowerSections (fun x ↦ ((f x + V (n + 1)) ∩ ({hn x} + V n))) := by
        apply HasOpenLowerSections.inter
        · exact hf.hasOpenCGraph_add_isOpen (hV.1 (n + 1)).2.1 |>.hasOpenLowerSections
        · exact hn_prop.1.lowerHemicontinuous.hasOpenCGraph_add_isOpen (hV.1 n).2.1
            |>.hasOpenLowerSections
      obtain ⟨h', hh'_cont, hh'_mem⟩ := this.exists_continuous_selection (by
          intro x
          obtain ⟨a, ha, v, hv, hav⟩ := (hn_prop.2 x)
          exact ⟨hn x + (-v), ⟨a, ha, 0, (hV.1 (n + 1)).1, by simp [← hav]⟩,
              by simp [(hV.1 n).2.2.2.1 v hv]⟩)
        fun x ↦ ((hf_convex x).add (hV.1 (n + 1)).2.2.1).inter
            ((convex_singleton _).add (hV.1 n).2.2.1)
      use h'
      refine ⟨⟨hh'_cont, fun x ↦ (hh'_mem x).1⟩, fun x ↦ ?_⟩
      obtain ⟨_, rfl, v, hv, hv'⟩ := (hh'_mem x).2
      simp [← hv', hv]
    choose! F hF using step
    use Nat.rec g F
    rw [← forall_and, ← forall_and]
    intro n
    induction n with
    | zero => simp [hg_cont, hg_mem, hF, P]
    | succ n ih => simp [ih, P, hF]
  -- Prove the sequence is uniformly cauchy. The (necessarily continuous) limit is a selection
  have hUnif : UniformCauchySeqOn h Filter.atTop univ := by
    intro U hU
    obtain ⟨n, -, hn⟩ := hV.2.uniformity_of_nhds_zero.mem_iff.mp hU
    have key : ∀ m k j x, k + 1 ≤ j → h (j + m) x - h j x ∈ V k := fun m ↦ by
      induction m with
      | zero => intro k j x _; simp only [Nat.add_zero, sub_self]; exact (hV.1 k).1
      | succ m ih =>
        intro k j x hj
        have h1 : h (j + 1) x - h j x ∈ V (k + 1) := hV.2.antitone hj (hh_mem_ball j x)
        have h2 : h (j + 1 + m) x - h (j + 1) x ∈ V (k + 1) := ih (k + 1) (j + 1) x (by omega)
        convert (hV.1 k).2.2.2.2.1 (Set.add_mem_add h1 h2) using 1; abel_nf
    filter_upwards [(Filter.eventually_ge_atTop (n + 1)).prod_mk
        (Filter.eventually_ge_atTop (n + 1))]
    intro ⟨i, j⟩ ⟨hi, hj⟩ x _
    apply hn
    obtain h_lt | h_le := Nat.lt_or_ge j i
    · simpa [Nat.add_sub_cancel' h_lt.le, neg_sub] using (hV.1 n).2.2.2.1 _ (key (i - j) n j x hj)
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h_le
      exact key m n i x hi
  choose H hH using fun x ↦ cauchySeq_tendsto_of_complete (hUnif.cauchySeq (mem_univ x))
  use H
  constructor
  · rw [← continuousOn_univ]
    apply (hUnif.tendstoUniformlyOn_of_tendsto (fun x hx ↦ hH x)).continuousOn
    exact Filter.Frequently.of_forall (by simp [hh_cont])
  intro x
  have key : ⋂ n, closure (f x + V n) ⊆ f x := by
    calc ⋂ n, closure (f x + V n)
        ⊆ ⋂ n, closure (f x + V (n + 1)) :=
          fun y hy ↦ mem_iInter.mpr fun n ↦ mem_iInter.mp hy (n + 1)
      _ ⊆ ⋂ n, f x + V n :=
          iInter_mono fun n ↦ closure_add_subset_add_u (hV.1 (n + 1)).2.1 (hV.1 (n + 1)).1
            (hV.1 (n + 1)).2.2.2.1 (hV.1 n).2.2.2.2.1
      _ ⊆ f x := by
          intro y hy
          rw [← (hf_isClosed x).closure_eq, mem_closure_iff_nhds]
          intro U hU
          obtain ⟨n, hn⟩ := hV.2.mem_iff.mp <|
            (continuous_const_add y).continuousAt (x := 0) |>.preimage_mem_nhds (by simpa)
          obtain ⟨a, ha_f, v, hv, rfl⟩ := mem_iInter.mp hy n
          exact ⟨a, by simpa using hn ((hV.1 n).2.2.2.1 v hv), ha_f⟩
  exact key (Set.mem_iInter.mpr fun n ↦ mem_closure_of_tendsto (hH x) <|
    (Filter.eventually_ge_atTop n).mono fun i hi ↦ by
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp (hh_mem i x)
      exact hab ▸ Set.add_mem_add ha (hV.2.antitone hi hb))

end michael

end
