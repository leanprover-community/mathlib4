/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Topology.CoveringDimension.ClosedUnion
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.ShrinkingLemma

/-! # Covering dimension of compact Euclidean subspaces and manifolds -/

public section

open scoped CoveringDimension

open Set TopologicalSpace

universe u

/-- The fractional translation used for one phase of the
Euclidean grid. -/
private noncomputable def euclideanCoverPhaseShift (N : ℕ) (c : Fin (N + 1)) : ℝ :=
  (c : ℝ) / (N + 1)

/-- An open box in one translated Euclidean grid. -/
private def shiftedEuclideanBox (N : ℕ) (a : ℝ) (c : Fin (N + 1))
    (p : Fin N → ℤ) : Set (EuclideanSpace ℝ (Fin N)) :=
  (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)) ⁻¹' Set.pi Set.univ
    (fun i ↦ Ioo
      (a * ((p i : ℝ) + euclideanCoverPhaseShift N c))
      (a * ((p i : ℝ) + 1 + euclideanCoverPhaseShift N c)))

/-- The family of all boxes in one translated grid. -/
private def shiftedEuclideanBoxFamily (N : ℕ) (a : ℝ) (c : Fin (N + 1)) :
    Set (Set (EuclideanSpace ℝ (Fin N))) :=
  Set.range (shiftedEuclideanBox N a c)

/-- Membership in a shifted Euclidean box is coordinatewise
membership in its defining intervals. -/
private lemma mem_shiftedEuclideanBox_iff {N : ℕ} {a : ℝ} {c : Fin (N + 1)}
    {p : Fin N → ℤ} {x : EuclideanSpace ℝ (Fin N)} :
    x ∈ shiftedEuclideanBox N a c p ↔
      ∀ i, x i ∈ Ioo
        (a * ((p i : ℝ) + euclideanCoverPhaseShift N c))
        (a * ((p i : ℝ) + 1 + euclideanCoverPhaseShift N c)) := by
  -- Unfold the box once, exposing the stable coordinatewise interface used below.
  simp only [shiftedEuclideanBox, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
  rfl

/-- A real coordinate lies on the boundary grid of at most
one of the `N + 1` phases. -/
private lemma euclideanGridBoundary_phase_unique {N : ℕ} {a x : ℝ} (ha : 0 < a)
    {c d : Fin (N + 1)}
    (hc : ∃ n : ℤ, x = a * ((n : ℝ) + euclideanCoverPhaseShift N c))
    (hd : ∃ n : ℤ, x = a * ((n : ℝ) + euclideanCoverPhaseShift N d)) :
    c = d := by
  -- Clear the common denominator and recover the phase as the residue modulo `N + 1`.
  obtain ⟨n, hn⟩ := hc
  obtain ⟨m, hm⟩ := hd
  have hscaled : (n : ℝ) + euclideanCoverPhaseShift N c =
      (m : ℝ) + euclideanCoverPhaseShift N d := mul_left_cancel₀ ha.ne' (hn.symm.trans hm)
  have heq : n * (N + 1 : ℤ) + c.val = m * (N + 1 : ℤ) + d.val := by
    dsimp [euclideanCoverPhaseShift] at hscaled
    field_simp at hscaled
    exact_mod_cast (by nlinarith only [hscaled] :
      (n : ℝ) * (N + 1) + (c : ℝ) = (m : ℝ) * (N + 1) + (d : ℝ))
  have hmod := congrArg (fun k : ℤ ↦ k % (N + 1)) heq
  have hcmod : (c.val : ℤ) % (N + 1) = c.val :=
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast c.isLt)
  have hdmod : (d.val : ℤ) % (N + 1) = d.val :=
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast d.isLt)
  simp only [Int.mul_add_emod_self_right, hcmod, hdmod] at hmod
  exact Fin.ext (by exact_mod_cast hmod)

/-- Among `N + 1` translated grids, one phase avoids the
boundary grid in all `N` coordinates. -/
private lemma exists_phase_avoiding_euclideanGridBoundaries {N : ℕ} {a : ℝ}
    (ha : 0 < a) (x : EuclideanSpace ℝ (Fin N)) :
    ∃ c : Fin (N + 1), ∀ i : Fin N,
      ¬ ∃ n : ℤ, x i = a * ((n : ℝ) + euclideanCoverPhaseShift N c) := by
  -- Each coordinate forbids at most one phase, so their union cannot exhaust `N + 1` phases.
  classical
  let bad : Fin N → Set (Fin (N + 1)) := fun i ↦
    {c | ∃ n : ℤ, x i = a * ((n : ℝ) + euclideanCoverPhaseShift N c)}
  have hbad (i : Fin N) : Set.encard (bad i) ≤ 1 := by
    rw [Set.encard_le_one_iff]
    intro c d hc hd
    exact euclideanGridBoundary_phase_unique ha hc hd
  by_contra hnone
  have hall : (Set.univ : Set (Fin (N + 1))) ⊆ ⋃ i, bad i := by
    simpa [Set.subset_def, bad] using not_exists.mp hnone
  have hcard : ((N + 1 : ℕ) : ℕ∞) ≤ N := by
    calc
      ((N + 1 : ℕ) : ℕ∞) = Set.encard (Set.univ : Set (Fin (N + 1))) := by simp
      _ ≤ Set.encard (⋃ i, bad i) := Set.encard_le_encard hall
      _ ≤ ∑ i, Set.encard (bad i) := Set.encard_iUnion_le_of_fintype bad
      _ ≤ ∑ _i : Fin N, (1 : ℕ∞) := Finset.sum_le_sum fun i _ ↦ hbad i
      _ = N := by simp
  have hcardNat : N + 1 ≤ N := by
    exact_mod_cast hcard
  omega

/-- Avoiding every coordinate boundary selects a containing
shifted Euclidean box. -/
private lemma mem_shiftedEuclideanBox_of_phaseAvoidance {N : ℕ} {a : ℝ}
    (ha : 0 < a) (x : EuclideanSpace ℝ (Fin N)) (c : Fin (N + 1))
    (havoid : ∀ i : Fin N,
      ¬ ∃ n : ℤ, x i = a * ((n : ℝ) + euclideanCoverPhaseShift N c)) :
    x ∈ shiftedEuclideanBox N a c
      (fun i ↦ ⌊x i / a - euclideanCoverPhaseShift N c⌋) := by
  -- Floor bounds locate every coordinate strictly between consecutive grid hyperplanes.
  rw [mem_shiftedEuclideanBox_iff]
  intro i
  have hfloor := Int.floor_le (x i / a - euclideanCoverPhaseShift N c)
  have hstrict : (⌊x i / a - euclideanCoverPhaseShift N c⌋ : ℝ) <
      x i / a - euclideanCoverPhaseShift N c := by
    apply lt_of_le_of_ne hfloor
    intro heq
    apply havoid i
    refine ⟨⌊x i / a - euclideanCoverPhaseShift N c⌋, ?_⟩
    field_simp [ha.ne'] at heq ⊢
    nlinarith
  have hupp := Int.lt_floor_add_one (x i / a - euclideanCoverPhaseShift N c)
  constructor <;> field_simp [ha.ne'] at hstrict hupp ⊢ <;> nlinarith

/-- Boxes in one translated grid are pointwise unique. -/
private lemma shiftedEuclideanBoxFamily_pointwiseUnique {N : ℕ} {a : ℝ} (ha : 0 < a)
    (c : Fin (N + 1)) (x : EuclideanSpace ℝ (Fin N))
    {V W : Set (EuclideanSpace ℝ (Fin N))}
    (hV : V ∈ shiftedEuclideanBoxFamily N a c)
    (hW : W ∈ shiftedEuclideanBoxFamily N a c)
    (hxV : x ∈ V) (hxW : x ∈ W) : V = W := by
  -- Each grid index is the floor of its translated, rescaled coordinate.
  obtain ⟨p, rfl⟩ := hV
  obtain ⟨q, rfl⟩ := hW
  rw [mem_shiftedEuclideanBox_iff] at hxV hxW
  have hfloor (i : Fin N) (k : ℤ)
      (hk : x i ∈ Ioo (a * (k + euclideanCoverPhaseShift N c))
        (a * (k + 1 + euclideanCoverPhaseShift N c))) :
      ⌊x i / a - euclideanCoverPhaseShift N c⌋ = k := by
    rw [Int.floor_eq_iff, le_sub_iff_add_le, le_div_iff₀ ha,
      sub_lt_iff_lt_add, div_lt_iff₀ ha]
    constructor <;> nlinarith [hk.1, hk.2]
  exact congrArg (shiftedEuclideanBox N a c)
    (funext fun i ↦ (hfloor i (p i) (hxV i)).symm.trans (hfloor i (q i) (hxW i)))

/-- The distance between two points of one shifted box is at
most `Real.sqrt N * a`. -/
private lemma shiftedEuclideanBox_dist_le {N : ℕ} {a : ℝ} (ha : 0 < a)
    (c : Fin (N + 1)) (p : Fin N → ℤ)
    {x y : EuclideanSpace ℝ (Fin N)}
    (hx : x ∈ shiftedEuclideanBox N a c p)
    (hy : y ∈ shiftedEuclideanBox N a c p) :
    dist x y ≤ Real.sqrt N * a := by
  -- Bound each squared coordinate distance by `a²`, then sum over the `N` coordinates.
  rw [mem_shiftedEuclideanBox_iff] at hx hy
  have hcoord (i : Fin N) : dist (x i) (y i) < a := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> nlinarith [(hx i).1, (hx i).2, (hy i).1, (hy i).2]
  have hsum : ∑ i, dist (x i) (y i) ^ 2 ≤ (N : ℝ) * a ^ 2 := by
    calc
      ∑ i, dist (x i) (y i) ^ 2 ≤ ∑ _i : Fin N, a ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith [dist_nonneg (x := x i) (y := y i), hcoord i]
      _ = (N : ℝ) * a ^ 2 := by simp
  simpa only [EuclideanSpace.dist_eq, Real.sqrt_mul (Nat.cast_nonneg N),
    Real.sqrt_sq_eq_abs, abs_of_pos ha] using Real.sqrt_le_sqrt hsum

/-- There is a uniformly fine open cover of `N`-dimensional
Euclidean space with pointwise order at most `N + 1`. -/
private lemma exists_euclideanOpenCover_order {N : ℕ} (ε : ℝ) (hε : 0 < ε) :
    ∃ 𝒸 : Set (Set (EuclideanSpace ℝ (Fin N))),
      (∀ V ∈ 𝒸, IsOpen V) ∧ ⋃₀ 𝒸 = Set.univ ∧ 𝒸.HasOrderLE (N + 1) ∧
        ∀ V ∈ 𝒸, Bornology.IsBounded V ∧ Metric.diam V < ε := by
  -- Use `N + 1` translated grids with mesh small enough for the Euclidean diameter bound.
  classical
  let a : ℝ := ε / (Real.sqrt N + 1)
  have hsqrt : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hdenom : 0 < Real.sqrt (N : ℝ) + 1 := by linarith
  have ha : 0 < a := by
    exact div_pos hε hdenom
  have haε : Real.sqrt N * a < ε := by
    dsimp [a]
    rw [← mul_div_assoc, div_lt_iff₀ hdenom]
    nlinarith
  let 𝒸 : Set (Set (EuclideanSpace ℝ (Fin N))) :=
    ⋃ c : Fin (N + 1), shiftedEuclideanBoxFamily N a c
  refine ⟨𝒸, ?_, ?_, ?_, ?_⟩
  · -- Every cover member is an open box from one phase.
    intro V hV
    obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hV
    obtain ⟨p, rfl⟩ := hc
    exact (isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo).preimage
      (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℝ)).continuous
  · -- Phase avoidance and coordinatewise floors place every point in a cover member.
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨c, hc⟩ := exists_phase_avoiding_euclideanGridBoundaries ha x
    let p : Fin N → ℤ := fun i ↦ ⌊x i / a - euclideanCoverPhaseShift N c⌋
    have hxp : x ∈ shiftedEuclideanBox N a c p :=
      mem_shiftedEuclideanBox_of_phaseAvoidance ha x c hc
    rw [Set.mem_sUnion]
    exact ⟨shiftedEuclideanBox N a c p,
      Set.mem_iUnion.2 ⟨c, ⟨p, rfl⟩⟩, hxp⟩
  · -- Split the members through a point by phase; each phase contributes at most one box.
    rw [Set.hasOrderLE_iff]
    intro x
    let throughPhase : Fin (N + 1) → Set (Set (EuclideanSpace ℝ (Fin N))) :=
      fun c ↦ {V ∈ shiftedEuclideanBoxFamily N a c | x ∈ V}
    have hsub : {V ∈ 𝒸 | x ∈ V} ⊆ ⋃ c, throughPhase c := by
      change (⋃ c, shiftedEuclideanBoxFamily N a c) ∩ {V | x ∈ V} ⊆ _
      rw [Set.iUnion_inter]
      rfl
    have hphase (c : Fin (N + 1)) : Set.encard (throughPhase c) ≤ 1 := by
      rw [Set.encard_le_one_iff]
      intro V W hV hW
      exact shiftedEuclideanBoxFamily_pointwiseUnique ha c x hV.1 hW.1 hV.2 hW.2
    calc
      Set.encard {V ∈ 𝒸 | x ∈ V}
          ≤ Set.encard (⋃ c, throughPhase c) := Set.encard_le_encard hsub
      _ ≤ ∑ c, Set.encard (throughPhase c) :=
        Set.encard_iUnion_le_of_fintype throughPhase
      _ ≤ ∑ _c : Fin (N + 1), (1 : ℕ∞) :=
        Finset.sum_le_sum fun c _ ↦ hphase c
      _ = N + 1 := by simp
  · -- The chosen mesh turns the box diameter estimate into strict `ε`-smallness.
    intro V hV
    obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hV
    obtain ⟨p, rfl⟩ := hc
    have hdist := fun x hx y hy ↦ shiftedEuclideanBox_dist_le ha c p (x := x) (y := y) hx hy
    exact ⟨Metric.isBounded_iff.mpr ⟨_, hdist⟩,
      (Metric.diam_le_of_forall_dist_le (mul_nonneg hsqrt ha.le) hdist).trans_lt haε⟩

/-- Restricting a uniformly fine Euclidean cover to a
subtype gives a nonempty uniformly fine cover of the same order. -/
lemma exists_subtypeEuclideanCover_order {N : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin N))) (ε : ℝ) (hε : 0 < ε) :
    ∃ ℬ : Set (Set X),
      (∀ B ∈ ℬ, IsOpen B) ∧ ⋃₀ ℬ = Set.univ ∧ ℬ.HasOrderLE (N + 1) ∧
        ∀ B ∈ ℬ, B.Nonempty ∧ Bornology.IsBounded B ∧ Metric.diam B < ε := by
  -- Pull the ambient cover back along the subtype inclusion and discard empty members.
  obtain ⟨𝒸, h𝒸open, h𝒸cover, h𝒸order, h𝒸small⟩ :=
    exists_euclideanOpenCover_order ε hε
  let pullback : Set (Set X) :=
    ((fun V : Set (EuclideanSpace ℝ (Fin N)) ↦
      ((↑) : X → EuclideanSpace ℝ (Fin N)) ⁻¹' V) '' 𝒸)
  let ℬ : Set (Set X) := {B ∈ pullback | B.Nonempty}
  refine ⟨ℬ, ?_, ?_, ?_, ?_⟩
  · -- Openness is preserved by the continuous subtype inclusion.
    intro B hB
    obtain ⟨V, hV𝒸, rfl⟩ := hB.1
    exact (h𝒸open V hV𝒸).preimage continuous_subtype_val
  · -- Ambient coverage supplies a nonempty pullback member through each subtype point.
    apply Set.eq_univ_of_forall
    intro x
    rw [Set.mem_sUnion]
    have hx : (x : EuclideanSpace ℝ (Fin N)) ∈ ⋃₀ 𝒸 := by
      rw [h𝒸cover]
      exact Set.mem_univ _
    rw [Set.mem_sUnion] at hx
    obtain ⟨V, hV𝒸, hxV⟩ := hx
    let B : Set X := ((↑) : X → EuclideanSpace ℝ (Fin N)) ⁻¹' V
    have hxB : x ∈ B := hxV
    have hBpullback : B ∈ pullback := ⟨V, hV𝒸, rfl⟩
    exact ⟨B, ⟨hBpullback, ⟨x, hxB⟩⟩, hxB⟩
  · -- Filtering out empty members cannot increase point multiplicity.
    exact (h𝒸order.preimage ((↑) : X → EuclideanSpace ℝ (Fin N))).of_subset
      fun _ hB ↦ hB.1
  · -- The subtype inclusion is an isometry, so boundedness and diameter bounds descend.
    rintro B ⟨⟨V, hV, rfl⟩, hB⟩
    obtain ⟨hVbounded, hVdiam⟩ := h𝒸small V hV
    refine ⟨hB, isometry_subtype_coe.antilipschitzWith.isBounded_preimage hVbounded, ?_⟩
    rw [← isometry_subtype_coe.diam_image]
    exact (Metric.diam_mono (Set.image_preimage_subset _ _) hVbounded).trans_lt hVdiam

/-- Every compact subspace of `EuclideanSpace ℝ (Fin N)` has covering-dimension
bound `N`. -/
theorem compactSubset_euclideanSpace_hasCoveringDimensionLE {N : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin N))) (hX : IsCompact X) :
    HasCoveringDimensionLE X N := by
  -- Choose a Lebesgue number, then refine by the uniformly fine order-`N + 1` cover.
  intro ι A hA
  let _ : CompactSpace X := isCompact_iff_compactSpace.mp hX
  obtain ⟨δ, hδ, hLebesgue⟩ := CompactSpace.lebesgue_number_lemma
    (fun i ↦ (A i : Set X)) (fun i ↦ (A i).isOpen) hA.iSup_set_eq_univ
  obtain ⟨ℬ, hℬopen, hℬcover, hℬorder, hℬsmall⟩ :=
    exists_subtypeEuclideanCover_order X δ hδ
  let B : ℬ → Opens X := fun U ↦ ⟨U.1, hℬopen U.1 U.2⟩
  refine ⟨ℬ, B, IsOpenCover.of_sets _
    (by simpa only [← Set.sUnion_eq_iUnion] using hℬcover), ?_, ?_⟩
  · rintro _ ⟨U, rfl⟩
    obtain ⟨i, hi⟩ := hLebesgue U.1 (hℬsmall U.1 U.2).1 (hℬsmall U.1 U.2).2.2.le
    exact ⟨A i, Set.mem_range_self i, hi⟩
  · change (Set.range (Subtype.val : ℬ → Set X)).HasOrderLE (N + 1)
    simpa only [Subtype.range_val] using hℬorder

/-- Every compact subspace of `EuclideanSpace ℝ (Fin N)` has
covering dimension at most `N`. -/
theorem compactSubset_euclideanSpace_coveringDimension_le {N : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin N))) (hX : IsCompact X) :
    dim X ≤ N := by
  -- Translate the proved cover-refinement bound into the numerical dimension inequality.
  rw [coveringDimension_le_iff]
  exact compactSubset_euclideanSpace_hasCoveringDimensionLE X hX

/-- Every compact subset of the plane has covering dimension at most two. -/
theorem compactSubset_euclideanPlane_coveringDimension_le_two
    (X : Set (ℝ × ℝ)) (hX : IsCompact X) :
    dim X ≤ 2 := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ :=
    (PiLp.homeomorph 2 (fun _ : Fin 2 ↦ ℝ)).trans Homeomorph.finTwoArrow
  let Y : Set (EuclideanSpace ℝ (Fin 2)) := e ⁻¹' X
  have hY : IsCompact Y := e.isCompact_preimage.mpr hX
  have hImage : e '' Y = X := by
    simp [Y]
  let eY : Y ≃ₜ X :=
    (Homeomorph.image e Y).trans (Homeomorph.setCongr hImage)
  rw [← eY.coveringDimension_congr]
  exact compactSubset_euclideanSpace_coveringDimension_le Y hY

/-! ## Compact manifolds -/

/-- The covering dimension of a compact Hausdorff `m`-manifold is at most `m`. -/
theorem compactManifold_coveringDimension_le {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [T2Space M] [CompactSpace M] :
    HasCoveringDimensionLE M m := by
  classical
  -- Choose finitely many charts and shrink their sources while retaining a cover.
  let e := chartAt (EuclideanSpace ℝ (Fin m)) (M := M)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M ↦ (e x).source) (fun x ↦ (e x).open_source)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, mem_chart_source _ x⟩)
  let U : t → Set M := fun i ↦ (e i.1).source
  have hUcover : ⋃ i, U i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨V, hVcover, _, hVclosure⟩ := exists_iUnion_eq_closure_subset
    (fun i : t ↦ (e i.1).open_source) (fun _ ↦ Set.toFinite _) hUcover
  apply HasCoveringDimensionLE.finite_iUnion_closed (fun i ↦ closure (V i))
    (fun _ ↦ isClosed_closure)
    (by rw [← closure_iUnion_of_finite, hVcover, closure_univ])
  intro i
  -- Each closed shrinking is compact and homeomorphic to its image in one Euclidean chart.
  let K := closure (V i)
  have hK : IsCompact K := isClosed_closure.isCompact
  have hsource : K ⊆ (e i.1).source := hVclosure i
  exact ((e i.1).homeomorphOfImageSubsetSource hsource rfl).symm.hasCoveringDimensionLE_of
    (compactSubset_euclideanSpace_hasCoveringDimensionLE _
      (hK.image_of_continuousOn ((e i.1).continuousOn.mono hsource)))
