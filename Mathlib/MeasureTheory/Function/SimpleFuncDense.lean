/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Heather Macbeth
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFunc
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Density of simple functions

Show that each Borel measurable function can be approximated pointwise
by a sequence of simple functions.

## Main definitions

* `MeasureTheory.SimpleFunc.nearestPt (e : ℕ → α) (N : ℕ) : α →ₛ ℕ`: the `SimpleFunc` sending
  each `x : α` to the point `e k` which is the nearest to `x` among `e 0`, ..., `e N`.
* `MeasureTheory.SimpleFunc.approxOn (f : β → α) (hf : Measurable f) (s : Set α) (y₀ : α)
  (h₀ : y₀ ∈ s) [SeparableSpace s] (n : ℕ) : β →ₛ α` : a simple function that takes values in `s`
  and approximates `f`.

## Main results

* `tendsto_approxOn` (pointwise convergence): If `f x ∈ s`, then the sequence of simple
  approximations `MeasureTheory.SimpleFunc.approxOn f hf s y₀ h₀ n`, evaluated at `x`,
  tends to `f x` as `n` tends to `∞`.

## Notation

* `α →ₛ β` (local notation): the type of simple functions `α → β`.
-/

@[expose] public section

open Set Function Filter TopologicalSpace Metric MeasureTheory
open scoped Topology ENNReal

variable {α β : Type*}

noncomputable section

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

namespace SimpleFunc

/-! ### Pointwise approximation by simple functions -/


variable [MeasurableSpace α] [PseudoEMetricSpace α] [OpensMeasurableSpace α]

/-- `nearestPtInd e N x` is the index `k` such that `e k` is the nearest point to `x` among the
points `e 0`, ..., `e N`. If more than one point are at the same distance from `x`, then
`nearestPtInd e N x` returns the least of their indices. -/
noncomputable def nearestPtInd (e : ℕ → α) : ℕ → α →ₛ ℕ
  | 0 => const α 0
  | N + 1 =>
    piecewise (⋂ k ≤ N, { x | edist (e (N + 1)) x < edist (e k) x })
      (MeasurableSet.iInter fun _ =>
        MeasurableSet.iInter fun _ =>
          measurableSet_lt measurable_edist_right measurable_edist_right)
      (const α <| N + 1) (nearestPtInd e N)

/-- `nearestPt e N x` is the nearest point to `x` among the points `e 0`, ..., `e N`. If more than
one point are at the same distance from `x`, then `nearestPt e N x` returns the point with the
least possible index. -/
noncomputable def nearestPt (e : ℕ → α) (N : ℕ) : α →ₛ α :=
  (nearestPtInd e N).map e

@[simp]
theorem nearestPtInd_zero (e : ℕ → α) : nearestPtInd e 0 = const α 0 :=
  rfl

@[simp]
theorem nearestPt_zero (e : ℕ → α) : nearestPt e 0 = const α (e 0) :=
  rfl

theorem nearestPtInd_succ (e : ℕ → α) (N : ℕ) (x : α) :
    nearestPtInd e (N + 1) x =
      if ∀ k ≤ N, edist (e (N + 1)) x < edist (e k) x then N + 1 else nearestPtInd e N x := by
  simp only [nearestPtInd, coe_piecewise, Set.piecewise]
  congr
  simp

theorem nearestPtInd_le (e : ℕ → α) (N : ℕ) (x : α) : nearestPtInd e N x ≤ N := by
  induction N with
  | zero => simp
  | succ N ihN =>
    simp only [nearestPtInd_succ]
    split_ifs
    exacts [le_rfl, ihN.trans N.le_succ]

theorem edist_nearestPt_le (e : ℕ → α) (x : α) {k N : ℕ} (hk : k ≤ N) :
    edist (nearestPt e N x) x ≤ edist (e k) x := by
  induction N generalizing k with
  | zero => simp [nonpos_iff_eq_zero.1 hk]
  | succ N ihN =>
    simp only [nearestPt, nearestPtInd_succ, map_apply]
    split_ifs with h
    · rcases hk.eq_or_lt with (rfl | hk)
      exacts [le_rfl, (h k (Nat.lt_succ_iff.1 hk)).le]
    · push Not at h
      rcases h with ⟨l, hlN, hxl⟩
      rcases hk.eq_or_lt with (rfl | hk)
      exacts [(ihN hlN).trans hxl, ihN (Nat.lt_succ_iff.1 hk)]

theorem tendsto_nearestPt {e : ℕ → α} {x : α} (hx : x ∈ closure (range e)) :
    Tendsto (fun N => nearestPt e N x) atTop (𝓝 x) := by
  refine (atTop_basis.tendsto_iff nhds_basis_eball).2 fun ε hε => ?_
  rcases EMetric.mem_closure_iff.1 hx ε hε with ⟨_, ⟨N, rfl⟩, hN⟩
  rw [edist_comm] at hN
  exact ⟨N, trivial, fun n hn => (edist_nearestPt_le e x hn).trans_lt hN⟩

variable [MeasurableSpace β] {f : β → α}

/-- Approximate a measurable function by a sequence of simple functions `F n` such that
`F n x ∈ s`. -/
noncomputable def approxOn (f : β → α) (hf : Measurable f) (s : Set α) (y₀ : α) (h₀ : y₀ ∈ s)
    [SeparableSpace s] (n : ℕ) : β →ₛ α :=
  haveI : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  comp (nearestPt (fun k => Nat.casesOn k y₀ ((↑) ∘ denseSeq s) : ℕ → α) n) f hf

@[simp]
theorem approxOn_zero {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] (x : β) : approxOn f hf s y₀ h₀ 0 x = y₀ :=
  rfl

theorem approxOn_mem {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] (n : ℕ) (x : β) : approxOn f hf s y₀ h₀ n x ∈ s := by
  haveI : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  suffices ∀ n, (Nat.casesOn n y₀ ((↑) ∘ denseSeq s) : α) ∈ s by apply this
  rintro (_ | n)
  exacts [h₀, Subtype.mem _]

lemma approxOn_range_nonneg [Zero α] [Preorder α] {f : β → α}
    (hf : 0 ≤ f) {hfm : Measurable f} [SeparableSpace (range f ∪ {0} : Set α)] (n : ℕ) :
    0 ≤ approxOn f hfm (range f ∪ {0}) 0 (by simp) n := by
  have : range f ∪ {0} ⊆ Set.Ici 0 := by
    simp only [Set.union_singleton, Set.insert_subset_iff, Set.mem_Ici, le_refl, true_and]
    rintro - ⟨x, rfl⟩
    exact hf x
  exact fun _ ↦ this <| approxOn_mem ..

@[simp]
theorem approxOn_comp {γ : Type*} [MeasurableSpace γ] {f : β → α} (hf : Measurable f) {g : γ → β}
    (hg : Measurable g) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s) [SeparableSpace s] (n : ℕ) :
    approxOn (f ∘ g) (hf.comp hg) s y₀ h₀ n = (approxOn f hf s y₀ h₀ n).comp g hg :=
  rfl

theorem tendsto_approxOn {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] {x : β} (hx : f x ∈ closure s) :
    Tendsto (fun n => approxOn f hf s y₀ h₀ n x) atTop (𝓝 <| f x) := by
  haveI : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  rw [← @Subtype.range_coe _ s, ← image_univ, ← (denseRange_denseSeq s).closure_eq] at hx
  simp -iota only [approxOn, coe_comp]
  refine tendsto_nearestPt (closure_minimal ?_ isClosed_closure hx)
  simp -iota only [Nat.range_casesOn, closure_union, range_comp]
  exact
    Subset.trans (image_closure_subset_closure_image continuous_subtype_val)
      subset_union_right

theorem edist_approxOn_mono {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] (x : β) {m n : ℕ} (h : m ≤ n) :
    edist (approxOn f hf s y₀ h₀ n x) (f x) ≤ edist (approxOn f hf s y₀ h₀ m x) (f x) := by
  dsimp only [approxOn, coe_comp, Function.comp_def]
  exact edist_nearestPt_le _ _ ((nearestPtInd_le _ _ _).trans h)

theorem edist_approxOn_le {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] (x : β) (n : ℕ) : edist (approxOn f hf s y₀ h₀ n x) (f x) ≤ edist y₀ (f x) :=
  edist_approxOn_mono hf h₀ x (zero_le n)

theorem edist_approxOn_y0_le {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] (x : β) (n : ℕ) :
    edist y₀ (approxOn f hf s y₀ h₀ n x) ≤ edist y₀ (f x) + edist y₀ (f x) :=
  calc
    edist y₀ (approxOn f hf s y₀ h₀ n x) ≤
        edist y₀ (f x) + edist (approxOn f hf s y₀ h₀ n x) (f x) :=
      edist_triangle_right _ _ _
    _ ≤ edist y₀ (f x) + edist y₀ (f x) := by grw [edist_approxOn_le hf h₀ x n]

end SimpleFunc

end MeasureTheory

section CompactSupport

variable {X Y α : Type*} [Zero α]
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]

/-- A continuous function with compact support on a product space can be uniformly approximated by
simple functions. The subtlety is that we do not assume that the spaces are separable, so the
product of the Borel sigma algebras might not contain all open sets, but still it contains enough
of them to approximate compactly supported continuous functions. -/
lemma HasCompactSupport.exists_simpleFunc_approx_of_prod [PseudoMetricSpace α]
    {f : X × Y → α} (hf : Continuous f) (h'f : HasCompactSupport f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : SimpleFunc (X × Y) α), ∀ x, dist (f x) (g x) < ε := by
  have M : ∀ (K : Set (X × Y)), IsCompact K →
      ∃ (g : SimpleFunc (X × Y) α), ∃ (s : Set (X × Y)), MeasurableSet s ∧ K ⊆ s ∧
      ∀ x ∈ s, dist (f x) (g x) < ε := by
    intro K hK
    apply IsCompact.induction_on
      (p := fun t ↦ ∃ (g : SimpleFunc (X × Y) α), ∃ (s : Set (X × Y)), MeasurableSet s ∧ t ⊆ s ∧
        ∀ x ∈ s, dist (f x) (g x) < ε) hK
    · exact ⟨0, ∅, by simp⟩
    · intro t t' htt' ⟨g, s, s_meas, ts, hg⟩
      exact ⟨g, s, s_meas, htt'.trans ts, hg⟩
    · intro t t' ⟨g, s, s_meas, ts, hg⟩ ⟨g', s', s'_meas, t's', hg'⟩
      refine ⟨g.piecewise s s_meas g', s ∪ s', s_meas.union s'_meas,
        union_subset_union ts t's', fun p hp ↦ ?_⟩
      by_cases H : p ∈ s
      · simpa [H, SimpleFunc.piecewise_apply] using hg p H
      · simp only [SimpleFunc.piecewise_apply, H, ite_false]
        apply hg'
        simpa [H] using (mem_union _ _ _).1 hp
    · rintro ⟨x, y⟩ -
      obtain ⟨u, v, hu, xu, hv, yv, huv⟩ : ∃ u v, IsOpen u ∧ x ∈ u ∧ IsOpen v ∧ y ∈ v ∧
        u ×ˢ v ⊆ {z | dist (f z) (f (x, y)) < ε} :=
          mem_nhds_prod_iff'.1 <| Metric.continuousAt_iff'.1 hf.continuousAt ε hε
      refine ⟨u ×ˢ v, nhdsWithin_le_nhds <| (hu.prod hv).mem_nhds (mk_mem_prod xu yv), ?_⟩
      exact ⟨SimpleFunc.const _ (f (x, y)), u ×ˢ v, hu.measurableSet.prod hv.measurableSet,
        Subset.rfl, fun z hz ↦ huv hz⟩
  obtain ⟨g, s, s_meas, fs, hg⟩ : ∃ (g : SimpleFunc (X × Y) α) (s : Set (X × Y)),
    MeasurableSet s ∧ tsupport f ⊆ s ∧ ∀ (x : X × Y), x ∈ s → dist (f x) (g x) < ε := M _ h'f
  refine ⟨g.piecewise s s_meas 0, fun p ↦ ?_⟩
  by_cases H : p ∈ s
  · simpa [H, SimpleFunc.piecewise_apply] using hg p H
  · have : f p = 0 := by
      contrapose! H
      rw [← Function.mem_support] at H
      exact fs (subset_tsupport _ H)
    simp [SimpleFunc.piecewise_apply, H, this, hε]

/-- A continuous function with compact support on a product space is measurable for the product
sigma-algebra. The subtlety is that we do not assume that the spaces are separable, so the
product of the Borel sigma algebras might not contain all open sets, but still it contains enough
of them to approximate compactly supported continuous functions. -/
lemma HasCompactSupport.measurable_of_prod
    [TopologicalSpace α] [PseudoMetrizableSpace α] [MeasurableSpace α] [BorelSpace α]
    {f : X × Y → α} (hf : Continuous f) (h'f : HasCompactSupport f) :
    Measurable f := by
  letI : PseudoMetricSpace α := TopologicalSpace.pseudoMetrizableSpacePseudoMetric α
  obtain ⟨u, -, u_pos, u_lim⟩ : ∃ u, StrictAnti u ∧ (∀ (n : ℕ), 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  have : ∀ n, ∃ (g : SimpleFunc (X × Y) α), ∀ x, dist (f x) (g x) < u n :=
    fun n ↦ h'f.exists_simpleFunc_approx_of_prod hf (u_pos n)
  choose g hg using this
  have A : ∀ x, Tendsto (fun n ↦ g n x) atTop (𝓝 (f x)) := by
    intro x
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ ?_) u_lim
    rw [dist_comm]
    exact (hg n x).le
  apply measurable_of_tendsto_metrizable (fun n ↦ (g n).measurable) (tendsto_pi_nhds.2 A)

end CompactSupport
