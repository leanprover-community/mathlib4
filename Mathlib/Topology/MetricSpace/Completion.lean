/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.UniformSpace.Completion

/-!
# The completion of a metric space

Completion of uniform spaces are already defined in `Topology.UniformSpace.Completion`. We show
here that the uniform space completion of a metric space inherits a metric space structure,
by extending the distance to the completion and checking that it is indeed a distance, and that
it defines the same uniformity as the already defined uniform structure on the completion
-/


open Set Filter UniformSpace Metric

open Filter Topology Uniformity

noncomputable section

universe u v

variable {α : Type u} {β : Type v} [PseudoMetricSpace α]

namespace UniformSpace.Completion

/-- The distance on the completion is obtained by extending the distance on the original space,
by uniform continuity. -/
instance : Dist (Completion α) :=
  ⟨Completion.extension₂ dist⟩

/-- The new distance is uniformly continuous. -/
protected theorem uniformContinuous_dist :
    UniformContinuous fun p : Completion α × Completion α ↦ dist p.1 p.2 :=
  uniformContinuous_extension₂ dist

/-- The new distance is continuous. -/
protected theorem continuous_dist [TopologicalSpace β] {f g : β → Completion α} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x ↦ dist (f x) (g x) :=
  Completion.uniformContinuous_dist.continuous.comp (hf.prodMk hg :)

/-- The new distance is an extension of the original distance. -/
@[simp]
protected theorem dist_eq (x y : α) : dist (x : Completion α) y = dist x y :=
  Completion.extension₂_coe_coe uniformContinuous_dist _ _

/- Let us check that the new distance satisfies the axioms of a distance, by starting from the
properties on α and extending them to `Completion α` by continuity. -/
protected theorem dist_self (x : Completion α) : dist x x = 0 := by
  refine induction_on x ?_ ?_
  · refine isClosed_eq ?_ continuous_const
    exact Completion.continuous_dist continuous_id continuous_id
  · intro a
    rw [Completion.dist_eq, dist_self]

protected theorem dist_comm (x y : Completion α) : dist x y = dist y x := by
  refine induction_on₂ x y ?_ ?_
  · exact isClosed_eq (Completion.continuous_dist continuous_fst continuous_snd)
        (Completion.continuous_dist continuous_snd continuous_fst)
  · intro a b
    rw [Completion.dist_eq, Completion.dist_eq, dist_comm]

protected theorem dist_triangle (x y z : Completion α) : dist x z ≤ dist x y + dist y z := by
  refine induction_on₃ x y z ?_ ?_
  · refine isClosed_le ?_ (Continuous.add ?_ ?_) <;>
      apply_rules [Completion.continuous_dist, Continuous.fst, Continuous.snd, continuous_id]
  · intro a b c
    rw [Completion.dist_eq, Completion.dist_eq, Completion.dist_eq]
    exact dist_triangle a b c

/-- Elements of the uniformity (defined generally for completions) can be characterized in terms
of the distance. -/
protected theorem mem_uniformity_dist (s : Set (Completion α × Completion α)) :
    s ∈ 𝓤 (Completion α) ↔ ∃ ε > 0, ∀ {a b}, dist a b < ε → (a, b) ∈ s := by
  constructor
  · /- Start from an entourage `s`. It contains a closed entourage `t`. Its pullback in `α` is an
      entourage, so it contains an `ε`-neighborhood of the diagonal by definition of the entourages
      in metric spaces. Then `t` contains an `ε`-neighborhood of the diagonal in `Completion α`, as
      closed properties pass to the completion. -/
    intro hs
    rcases mem_uniformity_isClosed hs with ⟨t, ht, ⟨tclosed, ts⟩⟩
    have A : { x : α × α | (↑x.1, ↑x.2) ∈ t } ∈ uniformity α :=
      uniformContinuous_def.1 (uniformContinuous_coe α) t ht
    rcases mem_uniformity_dist.1 A with ⟨ε, εpos, hε⟩
    refine ⟨ε, εpos, @fun x y hxy ↦ ?_⟩
    have : ε ≤ dist x y ∨ (x, y) ∈ t := by
      refine induction_on₂ x y ?_ ?_
      · have : { x : Completion α × Completion α | ε ≤ dist x.fst x.snd ∨ (x.fst, x.snd) ∈ t } =
               { p : Completion α × Completion α | ε ≤ dist p.1 p.2 } ∪ t := by ext; simp
        rw [this]
        apply IsClosed.union _ tclosed
        exact isClosed_le continuous_const Completion.uniformContinuous_dist.continuous
      · intro x y
        rw [Completion.dist_eq]
        by_cases h : ε ≤ dist x y
        · exact Or.inl h
        · have Z := hε (not_le.1 h)
          simp only [Set.mem_setOf_eq] at Z
          exact Or.inr Z
    simp only [not_le.mpr hxy, false_or] at this
    exact ts this
  · /- Start from a set `s` containing an ε-neighborhood of the diagonal in `Completion α`. To show
        that it is an entourage, we use the fact that `dist` is uniformly continuous on
        `Completion α × Completion α` (this is a general property of the extension of uniformly
        continuous functions). Therefore, the preimage of the ε-neighborhood of the diagonal in ℝ
        is an entourage in `Completion α × Completion α`. Massaging this property, it follows that
        the ε-neighborhood of the diagonal is an entourage in `Completion α`, and therefore this is
        also the case of `s`. -/
    rintro ⟨ε, εpos, hε⟩
    let r : Set (ℝ × ℝ) := { p | dist p.1 p.2 < ε }
    have : r ∈ uniformity ℝ := Metric.dist_mem_uniformity εpos
    have T := uniformContinuous_def.1 (@Completion.uniformContinuous_dist α _) r this
    simp only [uniformity_prod_eq_prod, mem_prod_iff, Filter.mem_map] at T
    rcases T with ⟨t1, ht1, t2, ht2, ht⟩
    refine mem_of_superset ht1 ?_
    have A : ∀ a b : Completion α, (a, b) ∈ t1 → dist a b < ε := by
      intro a b hab
      have : ((a, b), (a, a)) ∈ t1 ×ˢ t2 := ⟨hab, refl_mem_uniformity ht2⟩
      exact lt_of_le_of_lt (le_abs_self _)
        (by simpa [r, Completion.dist_self, Real.dist_eq, Completion.dist_comm] using ht this)
    grind

/-- Reformulate `Completion.mem_uniformity_dist` in terms that are suitable for the definition
of the metric space structure. -/
protected theorem uniformity_dist' :
    𝓤 (Completion α) = ⨅ ε : { ε : ℝ // 0 < ε }, 𝓟 { p | dist p.1 p.2 < ε.val } := by
  ext s; rw [mem_iInf_of_directed]
  · simp [Completion.mem_uniformity_dist, subset_def]
  · rintro ⟨r, hr⟩ ⟨p, hp⟩
    use ⟨min r p, lt_min hr hp⟩
    simp +contextual

protected theorem uniformity_dist : 𝓤 (Completion α) = ⨅ ε > 0, 𝓟 { p | dist p.1 p.2 < ε } := by
  simpa [iInf_subtype] using @Completion.uniformity_dist' α _

/-- Metric space structure on the completion of a pseudo_metric space. -/
instance instMetricSpace : MetricSpace (Completion α) :=
  @MetricSpace.ofT0PseudoMetricSpace _
    { dist_self := Completion.dist_self
      dist_comm := Completion.dist_comm
      dist_triangle := Completion.dist_triangle
      dist := dist
      toUniformSpace := inferInstance
      uniformity_dist := Completion.uniformity_dist } _

/-- The embedding of a metric space in its completion is an isometry. -/
theorem coe_isometry : Isometry ((↑) : α → Completion α) :=
  Isometry.of_dist_eq Completion.dist_eq

@[simp]
protected theorem edist_eq (x y : α) : edist (x : Completion α) y = edist x y :=
  coe_isometry x y

instance {M} [Zero M] [Zero α] [SMul M α] [PseudoMetricSpace M] [IsBoundedSMul M α] :
    IsBoundedSMul M (Completion α) where
  dist_smul_pair' c x₁ x₂ := by
    induction x₁, x₂ using induction_on₂ with
    | hp =>
      exact isClosed_le
        ((continuous_fst.const_smul _).dist (continuous_snd.const_smul _))
        (continuous_const.mul (continuous_fst.dist continuous_snd))
    | ih x₁ x₂ =>
      rw [← coe_smul, ← coe_smul, Completion.dist_eq, Completion.dist_eq]
      exact dist_smul_pair c x₁ x₂
  dist_pair_smul' c₁ c₂ x := by
    induction x using induction_on with
    | hp =>
      exact isClosed_le
        ((continuous_const_smul _).dist (continuous_const_smul _))
        (continuous_const.mul (continuous_id.dist continuous_const))
    | ih x =>
      rw [← coe_smul, ← coe_smul, Completion.dist_eq, ← coe_zero, Completion.dist_eq]
      exact dist_pair_smul c₁ c₂ x

end UniformSpace.Completion

open UniformSpace Completion NNReal

theorem LipschitzWith.completion_extension [MetricSpace β] [CompleteSpace β] {f : α → β}
    {K : ℝ≥0} (h : LipschitzWith K f) : LipschitzWith K (Completion.extension f) :=
  LipschitzWith.of_dist_le_mul fun x y => induction_on₂ x y
    (isClosed_le (by fun_prop) (by fun_prop)) <| by
      simpa only [extension_coe h.uniformContinuous, Completion.dist_eq] using h.dist_le_mul

theorem LipschitzWith.completion_map [PseudoMetricSpace β] {f : α → β} {K : ℝ≥0}
    (h : LipschitzWith K f) : LipschitzWith K (Completion.map f) :=
  one_mul K ▸ (coe_isometry.lipschitz.comp h).completion_extension

theorem Isometry.completion_extension [MetricSpace β] [CompleteSpace β] {f : α → β}
    (h : Isometry f) : Isometry (Completion.extension f) :=
  Isometry.of_dist_eq fun x y => induction_on₂ x y
    (isClosed_eq (by fun_prop) (by fun_prop)) fun _ _ ↦ by
      simp only [extension_coe h.uniformContinuous, Completion.dist_eq, h.dist_eq]

theorem Isometry.completion_map [PseudoMetricSpace β] {f : α → β}
    (h : Isometry f) : Isometry (Completion.map f) :=
  (coe_isometry.comp h).completion_extension
