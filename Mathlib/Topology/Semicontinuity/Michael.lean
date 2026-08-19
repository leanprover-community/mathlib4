/-
Copyright (c) 2026 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.PartitionOfUnity
import Mathlib.Analysis.LocallyConvex.AbsConvex
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Semicontinuity.Hemicontinuity

/-!
# Michael's selection theorem

This file proves Michael's selection theorem, that a lower hemicontinuous function with
convex closed nonempty values admits a continuous selection.

## Main results

- `HasOpenLowerSections.exists_continuous_selection`: A correspondence with open lower sections and
  convex, nonempty values admits a continuous selection. A key ingredient to the proof of Michael's
  selection theorem. This holds in any topological vector space over ℝ.
- `LowerHemicontinuous.exists_continuous_selection`: Michael's selection theorem that a lower
  hemicontinuous function from a paracompact space to a Fréchet space which takes convex, closed,
  nonempty values admits a continuous selection.
-/

public section

open Set Metric
open scoped Pointwise Topology

variable {α β : Type*} {f : α → Set β} [TopologicalSpace α]

section tvs

lemma LowerHemicontinuous.hasOpenCGraph_of_add_hasOpenCGraph [TopologicalSpace β] [AddGroup β]
    [IsTopologicalAddGroup β] {g : α → Set β} (hf : LowerHemicontinuous f) (hg : HasOpenCGraph g) :
    HasOpenCGraph (f + g) := by
  rw [HasOpenCGraph, isOpen_prod_iff]
  rintro a b ⟨y, hy, z, hz, rfl⟩
  obtain ⟨W, O_z, hW, hO_z, ha_W, hz_Oz, hWO_z⟩ := isOpen_prod_iff.mp hg a z hz
  obtain ⟨U_y, U_b, hU_y, hU_b, hy_Uy, hb_Ub, hU⟩ :=
    isOpen_prod_iff.mp (hO_z.preimage <| continuous_fst.neg.add continuous_snd) y (y + z)
      (by simpa using hz_Oz)
  have hopen_a : IsOpen {a' | (f a' ∩ U_y).Nonempty} :=
    lowerHemicontinuous_iff_isOpen_inter_nonempty.mp hf U_y hU_y
  refine ⟨{a' | (f a' ∩ U_y).Nonempty} ∩ W, U_b, hopen_a.inter hW, hU_b,
    ⟨⟨y, hy, hy_Uy⟩, ha_W⟩, hb_Ub, ?_⟩
  intro ⟨a', b'⟩ ⟨⟨⟨y', hy'_fa, hy'_Uy⟩, ha'_W⟩, hb'_Ub⟩
  exact ⟨y', hy'_fa, -y' + b',
    hWO_z (Set.mk_mem_prod ha'_W (hU (Set.mk_mem_prod hy'_Uy hb'_Ub))), by simp⟩

end tvs

variable {g : α → β} [NormalSpace α] [ParacompactSpace α] [AddCommGroup β] [Module ℝ β]

section approximate

variable [TopologicalSpace β] [ContinuousSMul ℝ β]

/-- **Michael's selection theorem (approximate):** A correspondence with open lower sections and
convex, nonempty values admits a continuous selection. This holds in any topological vector space
over `ℝ`. -/
lemma HasOpenLowerSections.exists_continuous_selection [ContinuousAdd β]
    (hf : HasOpenLowerSections f) (hf_nonempty : ∀ x, (f x).Nonempty)
    (hf_convex : ∀ x, Convex ℝ (f x)) : ∃ h : α → β, Continuous h ∧ ∀ x, h x ∈ f x := by
  choose F hF using hf_nonempty
  obtain ⟨φ, hφ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    _ (fun x' ↦ hf.isOpen (F x')) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hF x⟩)
  exact ⟨fun y ↦ ∑ᶠ x', (φ x' y) • F x', by fun_prop, fun y ↦
    (hf_convex y).finsum_mem (fun i ↦ φ.nonneg i y) (φ.sum_eq_one (mem_univ y)) fun x' hx' ↦
      hφ x' (subset_tsupport _ hx')⟩

/-- **Michael's selection theorem (iteration):** An approximate continuous selection `g` to a
correspondence `f` with open lower sections and convex values can be refined to an approximate
continuous selection `h` whose values `h x` are both closer to `f x` and are close to `g x`. -/
private lemma LowerHemicontinuous.exists_continuous_selection_refine [IsTopologicalAddGroup β]
    (hf : LowerHemicontinuous f) (hf_convex : ∀ x, Convex ℝ (f x))
    {g : α → β} (hg : Continuous g) {W V : Set β} (hW_open : IsOpen W) (hW_convex : Convex ℝ W)
    (hV_open : IsOpen V) (hV_convex : Convex ℝ V) (hW_zero : 0 ∈ W) (hV_symm : V = -V)
    (hgV : ∀ x, g x ∈ f x + V) :
      ∃ h : α → β, Continuous h ∧ (∀ x, h x ∈ f x + W) ∧ (∀ x, h x ∈ {g x} + V) := by
  have h₁ : HasOpenLowerSections fun x ↦ (f x + W) ∩ ({g x} + V) := by
    apply hf.hasOpenCGraph_of_add_hasOpenCGraph (.const hW_open) |>.hasOpenLowerSections.inter
    exact hg.lowerHemicontinuous.hasOpenCGraph_of_add_hasOpenCGraph (.const hV_open)
      |>.hasOpenLowerSections
  have h₂ (x : α) : ((f x + W) ∩ ({g x} + V)).Nonempty := by
    obtain ⟨a, ha, b, hb, hab⟩ := hgV x
    refine ⟨g x + (-b), ?_, ?_⟩
    · refine ⟨a, ha, 0, by grind⟩
    · refine ⟨g x, rfl, -b, by rw [hV_symm]; simpa, by simp⟩
  have h₃ (x : α) : Convex ℝ ((f x + W) ∩ ({g x} + V)) := by
    apply_rules [Convex.add, Convex.inter, convex_singleton]
  grind [h₁.exists_continuous_selection h₂ h₃]

end approximate

section michael

variable [UniformSpace β] [IsUniformAddGroup β] [ContinuousSMul ℝ β]
  [LocallyConvexSpace ℝ β] [FirstCountableTopology β] [CompleteSpace β]

/-- **Michael's selection theorem**: A lower hemicontinuous function from a paracompact normal
space to a Fréchet space with nonempty convex closed values admits a continuous selection -/
theorem LowerHemicontinuous.exists_continuous_selection (hf : LowerHemicontinuous f)
    (hf_nonempty : ∀ x, (f x).Nonempty) (hf_convex : ∀ x, Convex ℝ (f x))
    (hf_isClosed : ∀ x, IsClosed (f x)) : ∃ g : α → β, Continuous g ∧ ∀ x, g x ∈ f x := by
  obtain ⟨V, hV_anti, hV_open, hV_conv, hV_add, hV_closure⟩ := by
    simpa only [forall_and] using exists_nhds_hasAntitoneBasis_absConvex_open_add_closure_subset ℝ β
  -- Produce a sequence of continuous approximations to a selection
  obtain ⟨g, hg_cont, hg_mem⟩ :=
    hf.hasOpenCGraph_of_add_hasOpenCGraph (.const <| hV_open 0)
      |>.hasOpenLowerSections.exists_continuous_selection
      (fun x ↦ (hf_nonempty x).add ⟨0, mem_of_mem_nhds (hV_anti.mem 0)⟩)
      (fun x ↦ (hf_convex x).add (hV_conv 0).2)
  obtain ⟨h, hh_cont, hh_mem, hh_mem_ball⟩ : ∃ h : ℕ → α → β, (∀ n, Continuous (h n)) ∧
      (∀ n x, h n x ∈ f x + (V n)) ∧
      (∀ n x, h (n + 1) x ∈ {h n x} + V n) := by
    let P (n : ℕ) (h : α → β) := Continuous h ∧ ∀ x, h x ∈ f x + (V n)
    choose! F hF using fun n hn (hn_prop : P n hn) =>
      hf.exists_continuous_selection_refine hf_convex hn_prop.1
        (hV_open (n + 1)) (hV_conv (n + 1)).2 (hV_open n) (hV_conv n).2
        (mem_of_mem_nhds (hV_anti.mem (n + 1))) (hV_conv n).1.neg_eq.symm hn_prop.2
    use Nat.rec g F
    rw [← forall_and, ← forall_and]
    intro n
    induction n with
    | zero => exact ⟨by fun_prop, hg_mem, (hF 0 g ⟨hg_cont, hg_mem⟩).2.2⟩
    | succ n ih => simp [ih, P, hF, -singleton_add]
  -- Prove the sequence is uniformly cauchy. The (necessarily continuous) limit is a selection
  have hUnif : UniformCauchySeqOn h Filter.atTop univ := by
    intro U hU
    obtain ⟨n, -, hn⟩ := hV_anti.toHasBasis.uniformity_of_nhds_zero.mem_iff.mp hU
    have key : ∀ m k j x, k + 1 ≤ j → h (j + m) x - h j x ∈ V k := fun m ↦ by
      induction m with
      | zero =>
        intro k j x _; simpa using mem_of_mem_nhds (hV_anti.mem k)
      | succ m ih =>
        intro k j x hj
        obtain ⟨_, rfl, v, hv, hv'⟩ := hh_mem_ball j x
        have h1 : h (j + 1) x - h j x ∈ V (k + 1) := by
          simpa [← hv'] using hV_anti.antitone hj hv
        have h2 : h (j + 1 + m) x - h (j + 1) x ∈ V (k + 1) := ih (k + 1) (j + 1) x (by lia)
        convert (hV_add k) (Set.add_mem_add h1 h2) using 1
        abel_nf
    filter_upwards [(Filter.eventually_ge_atTop (n + 1)).prod_mk
        (Filter.eventually_ge_atTop (n + 1))] with ⟨i, j⟩ ⟨hi, hj⟩ x _
    apply hn
    obtain h_le | h_le := le_total i j <;> obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h_le
    · exact key m n i x hi
    · simpa using (hV_conv n).1.neg_mem_iff.mpr (key m n j x hj)
  choose H hH using fun x ↦ cauchySeq_tendsto_of_complete (hUnif.cauchySeq (mem_univ x))
  refine ⟨H, ?_, fun x ↦ ?_⟩
  · simpa using (hUnif.tendstoUniformlyOn_of_tendsto fun x _ ↦ hH x).continuousOn
      (.of_forall fun n ↦ (hh_cont n).continuousOn)
  rw [← (hf_isClosed x).iInter_closure_add_right_eq hV_anti.toHasBasis]
  refine Set.mem_iInter₂.mpr fun n _ ↦ mem_closure_of_tendsto (hH x) ?_
  filter_upwards [Filter.eventually_ge_atTop n] with m hm
  exact Set.add_subset_add_left (hV_anti.antitone hm) (hh_mem m x)

end michael

end
