/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Topology.CoveringDimension.Basic
import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Topology.ShrinkingLemma
public import Mathlib.Topology.UrysohnsLemma

/-! # Partitions between closed sets and covering dimension -/

public section

open Set TopologicalSpace

universe u

/-- An order-bounded open refinement of a compact metrizable
space can be represented by finitely many indexed opens together with a closure-controlled
shrinking and explicit parents in the original cover. -/
lemma existsFiniteIndexedShrinkingRefinement
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] {n : ℕ}
    (h : HasCoveringDimensionLE X n) {α : Type*} (A : α → Opens X)
    (hA : IsOpenCover A) :
    ∃ (ι : Type u) (_ : Finite ι) (B C : ι → Opens X) (p : ι → α),
      IsOpenCover B ∧ IsOpenCover C ∧
        (Set.range (fun i ↦ (B i : Set X))).HasOrderLE (n + 1) ∧
        Function.Injective (fun i ↦ (B i : Set X)) ∧
        (∀ i, B i ≤ A (p i)) ∧
        ∀ i, closure (C i : Set X) ⊆ B i := by
  classical
  -- Apply the finite shrinking construction to an order-bounded refinement.
  obtain ⟨κ, V, hVcover, hVrefines, hVorder⟩ := h.exists_refinement A hA
  obtain ⟨ι, hι, B, C, hBcover, hCcover, hBinjective, hBmem, hCclosure⟩ :=
    hVcover.exists_finite_shrinking
  -- Choose an original-cover parent for each retained refinement member.
  have hparent (i : ι) : ∃ a, B i ≤ A a := by
    obtain ⟨_, ⟨a, rfl⟩, hBA⟩ := hVrefines (hBmem i)
    exact ⟨a, hBA⟩
  choose p hp using hparent
  refine ⟨ι, hι, B, C, p, hBcover, hCcover, hVorder.of_subset ?_,
    hBinjective, hp, hCclosure⟩
  rintro _ ⟨i, rfl⟩
  obtain ⟨j, hj⟩ := hBmem i
  exact ⟨j, congrArg (fun U : Opens X ↦ (U : Set X)) hj⟩

/-- A real-valued map has a buffered fine zero cover of order
`q` when one finite open family has order at most `q` throughout a neighborhood of its zero
fiber and all of its members have diameter less than `δ`. -/
def HasBufferedFineZeroCover {X : Type*} [PseudoMetricSpace X]
    (f : C(X, ℝ)) (q : ℕ) (δ : ℝ) : Prop :=
  ∃ ε > 0, ∃ 𝒰 : Set (Set X),
    𝒰.Finite ∧
      (∀ U ∈ 𝒰, IsOpen U) ∧
      (∀ x, |f x| < ε → x ∈ ⋃₀ 𝒰) ∧
      (∀ x, |f x| < ε → Set.encard {U ∈ 𝒰 | x ∈ U} ≤ q) ∧
      ∀ U ∈ 𝒰, ∀ x ∈ U, ∀ y ∈ U, dist x y < δ

/-- Buffered fine zero covers persist under sufficiently small
uniform perturbations of the real-valued map. -/
lemma isOpen_setOf_hasBufferedFineZeroCover
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X] (q : ℕ) (δ : ℝ) :
    IsOpen {f : C(X, ℝ) | HasBufferedFineZeroCover f q δ} := by
  rw [isOpen_iff_mem_nhds]
  intro f hf
  obtain ⟨ε, hε, 𝒰, h𝒰finite, h𝒰open, h𝒰cover, h𝒰order, h𝒰diameter⟩ := hf
  apply Filter.mem_of_superset (Metric.ball_mem_nhds f (half_pos hε))
  intro g hg
  have hsmall (x : X) (hx : |g x| < ε / 2) : |f x| < ε := by
    have hdist : dist (g x) (f x) < ε / 2 :=
      lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist x) (Metric.mem_ball.mp hg)
    rw [Real.dist_eq] at hdist
    grind [abs_lt]
  exact ⟨ε / 2, half_pos hε, 𝒰, h𝒰finite, h𝒰open,
    fun x hx ↦ h𝒰cover x (hsmall x hx), fun x hx ↦ h𝒰order x (hsmall x hx), h𝒰diameter⟩

/-- A sufficiently small weighted sum of nonzero real vertices has
an active vertex of each sign. -/
lemma exists_active_vertices_of_bothSigns
    {ι : Type*} [Fintype ι] (w z : ι → ℝ) {ε : ℝ}
    (hw_nonnegative : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (hε : 0 < ε) (hz : ∀ i, ε ≤ |z i|)
    (hsmall : |∑ i, w i * z i| < ε) :
    (∃ i, 0 < z i ∧ w i ≠ 0) ∧ (∃ i, z i < 0 ∧ w i ≠ 0) := by
  have hpos (z : ι → ℝ) (hz : ∀ i, ε ≤ |z i|) (hsum : -ε < ∑ i, w i * z i) :
      ∃ i, 0 < z i ∧ w i ≠ 0 := by
    have hsum' : ∑ i, w i * (-ε) < ∑ i, w i * z i := by
      rwa [← Finset.sum_mul, hw_sum, one_mul]
    obtain ⟨i, _, hi⟩ := Finset.exists_lt_of_sum_lt hsum'
    have hzi := lt_of_mul_lt_mul_left hi (hw_nonnegative i)
    refine ⟨i, hε.trans_le ((le_abs.mp (hz i)).resolve_right (by linarith)), ?_⟩
    intro hwi
    simp only [hwi, zero_mul, lt_self_iff_false] at hi
  refine ⟨hpos z hz (abs_lt.mp hsmall).1, ?_⟩
  simpa only [Pi.neg_apply, neg_pos] using hpos (-z)
    (by simpa only [Pi.neg_apply, abs_neg] using hz)
    (by simpa only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_lt_neg_iff]
      using (abs_lt.mp hsmall).2)

/-- Maps with a buffered fine zero cover of order `n` are dense
when the compact metric domain has covering dimension at most `n`. -/
lemma dense_setOf_hasBufferedFineZeroCover
    {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X] {n : ℕ}
    (h : HasCoveringDimensionLE X n) {δ : ℝ} (hδ : 0 < δ) :
    Dense {f : C(X, ℝ) | HasBufferedFineZeroCover f n δ} := by
  rw [Metric.dense_iff]
  intro f r hr
  classical
  let neighborhood : X → Opens X := fun x ↦
    ⟨Metric.ball x (δ / 2) ∩ f ⁻¹' Metric.ball (f x) (r / 4),
      Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage f.continuous)⟩
  have hcover : IsOpenCover neighborhood := by
    apply IsOpenCover.of_sets
    apply Set.eq_univ_of_forall
    intro x
    apply Set.mem_iUnion.mpr
    refine ⟨x, ?_⟩
    have hrquarter : 0 < r / 4 := by positivity
    exact ⟨Metric.mem_ball_self (half_pos hδ), Metric.mem_ball_self hrquarter⟩
  obtain ⟨ι, hιfinite, B, _, c, hBcover, _, hBorder, hBinjective, hBp, _⟩ :=
    existsFiniteIndexedShrinkingRefinement h neighborhood hcover
  let _ : Finite ι := hιfinite
  let _ : Fintype ι := Fintype.ofFinite ι
  have hιnonempty : Nonempty ι := by
    obtain ⟨i, _⟩ := hBcover.exists_mem (Classical.arbitrary X)
    exact ⟨i⟩
  let i₀ : ι := Classical.choice hιnonempty
  let z : ι → ℝ := fun i ↦ if f (c i) = 0 then r / 4 else f (c i)
  have hznonzero : ∀ i, z i ≠ 0 := by grind
  have hzcenter : ∀ i, dist (z i) (f (c i)) < r / 2 := by
    intro i
    dsimp [z]
    split_ifs with hi <;> simp [hi, abs_of_pos hr] <;> linarith
  have hBcoverSet : (Set.univ : Set X) ⊆ ⋃ i, (B i : Set X) := by
    rw [hBcover.iSup_set_eq_univ]
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun i ↦ (B i : Set X)) (fun i ↦ (B i).2) hBcoverSet
  let g : C(X, ℝ) :=
    ⟨fun x ↦ ∑ i, ρ i x * z i,
      continuous_finsetSum _ fun i _ ↦ (ρ i).continuous.mul continuous_const⟩
  have hg_apply : ∀ x, g x = ∑ i, ρ i x * z i := fun _ ↦ rfl
  have hzpoint : ∀ i x, ρ i x ≠ 0 → dist (z i) (f x) < r := by
    intro i x hix
    have hxB : x ∈ B i := hρ i (subset_tsupport (ρ i) hix)
    have hxparent : x ∈ neighborhood (c i) := hBp i hxB
    have hcxf : dist (f (c i)) (f x) < r / 4 := by
      rw [dist_comm]
      exact Metric.mem_ball.mp hxparent.2
    have hsum : dist (z i) (f (c i)) + dist (f (c i)) (f x) < r := by
      linarith [hzcenter i]
    exact lt_of_le_of_lt (dist_triangle (z i) (f (c i)) (f x)) hsum
  have hgclose : dist g f < r := by
    apply ContinuousMap.dist_lt_of_nonempty
    intro x
    rw [hg_apply]
    simpa only [finsum_eq_sum_of_fintype, Metric.mem_ball, smul_eq_mul] using
      ρ.finsum_smul_mem_convex (g := fun i _ ↦ z i) (Set.mem_univ x)
        (fun i hi ↦ Metric.mem_ball.mpr (hzpoint i x hi))
        (convex_ball (f x) r)
  let ε : ℝ := Finset.univ.inf' ⟨i₀, Finset.mem_univ i₀⟩ fun i ↦ |z i|
  have hεpositive : 0 < ε := by
    exact (Finset.lt_inf'_iff _).2 fun i _ ↦ abs_pos.mpr (hznonzero i)
  have hεle : ∀ i, ε ≤ |z i| := by
    intro i
    exact Finset.inf'_le (fun j ↦ |z j|) (Finset.mem_univ i)
  let P : Set ι := {i | 0 < z i}
  let 𝒰 : Set (Set X) := (fun i ↦ (B i : Set X)) '' P
  have h𝒰finite : 𝒰.Finite := (Set.toFinite P).image _
  have h𝒰open : ∀ U ∈ 𝒰, IsOpen U := by
    rintro U ⟨i, _, rfl⟩
    exact (B i).2
  have hsigns : ∀ x, |g x| < ε →
      (∃ i, 0 < z i ∧ ρ i x ≠ 0) ∧ (∃ i, z i < 0 ∧ ρ i x ≠ 0) := by
    intro x hx
    rw [hg_apply] at hx
    apply exists_active_vertices_of_bothSigns (fun i ↦ ρ i x) z
    · exact fun i ↦ ρ.nonneg i x
    · simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ x)
    · exact hεpositive
    · exact hεle
    · exact hx
  have h𝒰cover : ∀ x, |g x| < ε → x ∈ ⋃₀ 𝒰 := by
    intro x hx
    obtain ⟨i, hiz, hiρ⟩ := (hsigns x hx).1
    exact Set.mem_sUnion.mpr ⟨(B i : Set X), ⟨i, hiz, rfl⟩,
      hρ i (subset_tsupport (ρ i) hiρ)⟩
  have h𝒰order : ∀ x, |g x| < ε → Set.encard {U ∈ 𝒰 | x ∈ U} ≤ n := by
    intro x hx
    obtain ⟨j, hjz, hjρ⟩ := (hsigns x hx).2
    let S : Set (Set X) := {U ∈ 𝒰 | x ∈ U}
    let T : Set (Set X) := {U ∈ Set.range (fun i ↦ (B i : Set X)) | x ∈ U}
    have hST : S ⊆ T := by
      rintro U ⟨⟨i, _, rfl⟩, hxi⟩
      exact ⟨⟨i, rfl⟩, hxi⟩
    have hjT : (B j : Set X) ∈ T :=
      ⟨⟨j, rfl⟩, hρ j (subset_tsupport (ρ j) hjρ)⟩
    have hjS : (B j : Set X) ∉ S := by
      rintro ⟨⟨i, hiz, hBi⟩, _⟩
      grind [hBinjective hBi]
    have hproper : S ⊂ T := (Set.ssubset_iff_of_subset hST).mpr ⟨B j, hjT, hjS⟩
    have hlt : Set.encard S < Set.encard T :=
      (h𝒰finite.subset fun U hU ↦ hU.1).encard_lt_encard hproper
    simpa only [Nat.cast_add, Nat.cast_one, ENat.lt_add_one_iff (ENat.natCast_ne_top n)]
      using hlt.trans_le (Set.hasOrderLE_iff.mp hBorder x)
  have h𝒰diameter : ∀ U ∈ 𝒰, ∀ x ∈ U, ∀ y ∈ U, dist x y < δ := by
    rintro U ⟨i, _, rfl⟩ x hx y hy
    exact Metric.ball_half_subset (c i) (Metric.mem_ball_comm.mp (hBp i hy).1) (hBp i hx).1
  exact ⟨g, Metric.mem_ball.mpr hgclose,
    ε, hεpositive, 𝒰, h𝒰finite, h𝒰open, h𝒰cover, h𝒰order, h𝒰diameter⟩

/-- Buffered fine zero covers at every metric scale give the
corresponding covering-dimension bound on every closed subset of the zero fiber. -/
lemma hasCoveringDimensionLE_closedSubset_zeroFiber
    {X : Type u} [MetricSpace X] [CompactSpace X] {f : C(X, ℝ)} {L : Set X} {q : ℕ}
    (hLclosed : IsClosed L) (hLzero : L ⊆ {x | f x = 0})
    (hfine : ∀ k : ℕ,
      HasBufferedFineZeroCover f (q + 1) (1 / (k + 1 : ℝ))) :
    HasCoveringDimensionLE L q := by
  intro ι A hA
  classical
  let _ : CompactSpace L := isCompact_iff_compactSpace.mp hLclosed.isCompact
  obtain ⟨δ, hδ, hLebesgue⟩ := lebesgue_number_lemma_of_metric
    isCompact_univ (fun i ↦ (A i).isOpen) (by simp [hA.iSup_set_eq_univ])
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  obtain ⟨ε, hε, 𝒰, _, h𝒰open, h𝒰cover, h𝒰order, h𝒰diameter⟩ := hfine k
  have hsmall (z : L) : |f z.1| < ε := by rwa [hLzero z.2, abs_zero]
  let ℬ : Set (Set L) :=
    {V | V.Nonempty ∧ ∃ U ∈ 𝒰, V = (Subtype.val : L → X) ⁻¹' U}
  have hℬopen (V : ℬ) : IsOpen V.1 := by
    obtain ⟨_, U, hU𝒰, hVU⟩ := V.2
    rw [hVU]
    exact (h𝒰open U hU𝒰).preimage continuous_subtype_val
  let B : ℬ → Opens L := fun V ↦ ⟨V.1, hℬopen V⟩
  refine ⟨ℬ, B, ?_, ?_, ?_⟩
  · apply IsOpenCover.of_sets
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨U, hU𝒰, hzU⟩ := Set.mem_sUnion.mp (h𝒰cover z.1 (hsmall z))
    exact Set.mem_iUnion.mpr
      ⟨⟨(Subtype.val : L → X) ⁻¹' U, ⟨z, hzU⟩, U, hU𝒰, rfl⟩, hzU⟩
  · rintro _ ⟨⟨V, ⟨z, hzV⟩, U, hU𝒰, rfl⟩, rfl⟩
    obtain ⟨i, hi⟩ := hLebesgue z (Set.mem_univ z)
    refine ⟨A i, Set.mem_range_self i, ?_⟩
    intro y hy
    apply hi
    apply Metric.mem_ball.mpr
    simpa only [Subtype.dist_eq, dist_comm] using
      (h𝒰diameter U hU𝒰 z.1 hzV y.1 hy).trans hk
  · change (Set.range (Subtype.val : ℬ → Set L)).HasOrderLE (q + 1)
    rw [Subtype.range_val, Set.hasOrderLE_iff]
    intro z
    let pullback : Set X → Set L := fun U ↦ (Subtype.val : L → X) ⁻¹' U
    have hincident : {V ∈ ℬ | z ∈ V} ⊆
        pullback '' {U ∈ 𝒰 | z.1 ∈ U} := by
      rintro V ⟨⟨_, U, hU𝒰, rfl⟩, hzV⟩
      exact ⟨U, ⟨hU𝒰, hzV⟩, rfl⟩
    calc
      Set.encard {V ∈ ℬ | z ∈ V}
          ≤ Set.encard (pullback '' {U ∈ 𝒰 | z.1 ∈ U}) := Set.encard_mono hincident
      _ ≤ Set.encard {U ∈ 𝒰 | z.1 ∈ U} := Set.encard_image_le pullback _
      _ ≤ q + 1 := h𝒰order z.1 (hsmall z)

/-- A compact metric space of covering dimension at most `n`
admits a real separator whose zero fiber has buffered fine covers of order `n` at every scale. -/
lemma exists_zeroFiberSeparator_with_fineCovers
    {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X] {n : ℕ}
    (h : HasCoveringDimensionLE X n) {K F : Set X}
    (hK : IsClosed K) (hF : IsClosed F) (hKF : Disjoint K F) :
    ∃ f : C(X, ℝ),
      (∀ x ∈ K, f x < 0) ∧ (∀ x ∈ F, 0 < f x) ∧
        ∀ k : ℕ, HasBufferedFineZeroCover f n (1 / (k + 1 : ℝ)) := by
  have hopen : ∀ k : ℕ,
      IsOpen {f : C(X, ℝ) | HasBufferedFineZeroCover f n (1 / (k + 1 : ℝ))} :=
    fun k ↦ isOpen_setOf_hasBufferedFineZeroCover n (1 / (k + 1 : ℝ))
  have hdense : ∀ k : ℕ,
      Dense {f : C(X, ℝ) | HasBufferedFineZeroCover f n (1 / (k + 1 : ℝ))} := by
    intro k
    have hscale : 0 < 1 / (k + 1 : ℝ) := by positivity
    exact dense_setOf_hasBufferedFineZeroCover h hscale
  have hgeneric : Dense (⋂ k : ℕ,
      {f : C(X, ℝ) | HasBufferedFineZeroCover f n (1 / (k + 1 : ℝ))}) :=
    BaireSpace.baire_property _ hopen hdense
  obtain ⟨u, huK, huF, _⟩ := exists_continuous_zero_one_of_isClosed hK hF hKF
  let f₀ : C(X, ℝ) := (ContinuousMap.const X 2) * u - ContinuousMap.const X 1
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hballNonempty : (Metric.ball f₀ (1 / 2 : ℝ)).Nonempty :=
    ⟨f₀, Metric.mem_ball_self hhalf⟩
  obtain ⟨f, hfine, hfclose⟩ :=
    hgeneric.exists_mem_open Metric.isOpen_ball hballNonempty
  refine ⟨f, ?_, ?_, Set.mem_iInter.mp hfine⟩
  · intro x hxK
    have hpoint : dist (f x) (f₀ x) < (1 / 2 : ℝ) :=
      lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist x) (Metric.mem_ball.mp hfclose)
    have hux : u x = 0 := huK hxK
    have hf₀ : f₀ x = -1 := by norm_num [f₀, hux]
    rw [hf₀, Real.dist_eq] at hpoint
    have := (abs_lt.mp hpoint).2
    linarith
  · intro x hxF
    have hpoint : dist (f x) (f₀ x) < (1 / 2 : ℝ) :=
      lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist x) (Metric.mem_ball.mp hfclose)
    have hux : u x = 1 := huF hxF
    have hf₀ : f₀ x = 1 := by norm_num [f₀, hux]
    rw [hf₀, Real.dist_eq] at hpoint
    have := (abs_lt.mp hpoint).1
    linarith

/-- A covering-dimension bound gives a controlled open partition
between two disjoint closed subsets of a compact metrizable space. -/
lemma existsOpenPartition_of_hasCoveringDimensionLE
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X] {n : ℕ}
    (h : HasCoveringDimensionLE X n) {K F : Set X} (hK : IsClosed K) (hF : IsClosed F)
    (hKF : Disjoint K F) :
    ∃ V : Set X,
      IsOpen V ∧ K ⊆ V ∧ closure V ⊆ Fᶜ ∧
        HasCoveringDimensionLT ↥(frontier V) n := by
  classical
  cases isEmpty_or_nonempty X with
  | inl hX =>
      let _ : IsEmpty X := hX
      refine ⟨∅, isOpen_empty, ?_, by simp, ?_⟩
      · intro x _
        exact isEmptyElim x
      · cases n with
        | zero =>
            exact Set.isEmpty_coe_sort.mpr frontier_empty
        | succ q =>
            exact hasCoveringDimensionLE_of_isEmpty
              (Set.isEmpty_coe_sort.mpr frontier_empty) q
  | inr hX =>
      let _ : Nonempty X := hX
      let _ : MetricSpace X := metrizableSpaceMetric X
      obtain ⟨f, hfK, hfF, hfine⟩ :=
        exists_zeroFiberSeparator_with_fineCovers h hK hF hKF
      let V : Set X := {x | f x < 0}
      have hVopen : IsOpen V := isOpen_lt f.continuous continuous_const
      have hKV : K ⊆ V := fun x hx ↦ hfK x hx
      have hVclosure : closure V ⊆ Fᶜ := by
        have hclosed : IsClosed {x | f x ≤ 0} :=
          isClosed_le f.continuous continuous_const
        have hsubset : V ⊆ {x | f x ≤ 0} := by
          intro x hx
          change f x < 0 at hx
          exact hx.le
        intro x hxclosure hxF
        have hfx : f x ≤ 0 := closure_minimal hsubset hclosed hxclosure
        exact (not_lt_of_ge hfx) (hfF x hxF)
      have hfrontierZero : frontier V ⊆ {x | f x = 0} := by
        exact frontier_lt_subset_eq f.continuous continuous_const
      refine ⟨V, hVopen, hKV, hVclosure, ?_⟩
      cases n with
      | zero =>
          constructor
          rintro ⟨x, hxfrontier⟩
          obtain ⟨ε, hε, 𝒰, _, _, h𝒰cover, h𝒰order, _⟩ := hfine 0
          have hxsmall : |f x| < ε := by
            rw [hfrontierZero hxfrontier]
            simpa using hε
          obtain ⟨U, hU𝒰, hxU⟩ := Set.mem_sUnion.mp (h𝒰cover x hxsmall)
          have hone : (1 : ℕ∞) ≤ Set.encard {W ∈ 𝒰 | x ∈ W} :=
            Set.one_le_encard_iff_nonempty.mpr ⟨U, hU𝒰, hxU⟩
          have hzero : Set.encard {W ∈ 𝒰 | x ∈ W} ≤ (0 : ℕ) :=
            h𝒰order x hxsmall
          have hnotOneZero : ¬ (1 : ℕ∞) ≤ 0 := by norm_num
          exact hnotOneZero (hone.trans hzero)
      | succ q =>
          exact hasCoveringDimensionLE_closedSubset_zeroFiber isClosed_frontier
            hfrontierZero hfine
