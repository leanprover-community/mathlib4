/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Instances.Real

#align_import topology.metric_space.completion from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

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
#align uniform_space.completion.uniform_continuous_dist UniformSpace.Completion.uniformContinuous_dist

/-- The new distance is continuous. -/
protected theorem continuous_dist [TopologicalSpace β] {f g : β → Completion α} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x ↦ dist (f x) (g x) :=
  Completion.uniformContinuous_dist.continuous.comp (hf.prod_mk hg : _)
#align uniform_space.completion.continuous_dist UniformSpace.Completion.continuous_dist

/-- The new distance is an extension of the original distance. -/
@[simp]
protected theorem dist_eq (x y : α) : dist (x : Completion α) y = dist x y :=
  Completion.extension₂_coe_coe uniformContinuous_dist _ _
#align uniform_space.completion.dist_eq UniformSpace.Completion.dist_eq

/- Let us check that the new distance satisfies the axioms of a distance, by starting from the
properties on α and extending them to `Completion α` by continuity. -/
protected theorem dist_self (x : Completion α) : dist x x = 0 := by
  refine' induction_on x _ _
  -- ⊢ IsClosed {a | dist a a = 0}
  · refine' isClosed_eq _ continuous_const
    -- ⊢ Continuous fun a => dist a a
    exact Completion.continuous_dist continuous_id continuous_id
    -- 🎉 no goals
  · intro a
    -- ⊢ dist (↑α a) (↑α a) = 0
    rw [Completion.dist_eq, dist_self]
    -- 🎉 no goals
#align uniform_space.completion.dist_self UniformSpace.Completion.dist_self

protected theorem dist_comm (x y : Completion α) : dist x y = dist y x := by
  refine' induction_on₂ x y _ _
  -- ⊢ IsClosed {x | dist x.fst x.snd = dist x.snd x.fst}
  · exact isClosed_eq (Completion.continuous_dist continuous_fst continuous_snd)
        (Completion.continuous_dist continuous_snd continuous_fst)
  · intro a b
    -- ⊢ dist (↑α a) (↑α b) = dist (↑α b) (↑α a)
    rw [Completion.dist_eq, Completion.dist_eq, dist_comm]
    -- 🎉 no goals
#align uniform_space.completion.dist_comm UniformSpace.Completion.dist_comm

protected theorem dist_triangle (x y z : Completion α) : dist x z ≤ dist x y + dist y z := by
  refine' induction_on₃ x y z _ _
  -- ⊢ IsClosed {x | dist x.fst x.snd.snd ≤ dist x.fst x.snd.fst + dist x.snd.fst x …
  · refine' isClosed_le _ (Continuous.add _ _) <;>
      apply_rules [Completion.continuous_dist, Continuous.fst, Continuous.snd, continuous_id]
      -- 🎉 no goals
      -- 🎉 no goals
      -- 🎉 no goals
  · intro a b c
    -- ⊢ dist (↑α a) (↑α c) ≤ dist (↑α a) (↑α b) + dist (↑α b) (↑α c)
    rw [Completion.dist_eq, Completion.dist_eq, Completion.dist_eq]
    -- ⊢ dist a c ≤ dist a b + dist b c
    exact dist_triangle a b c
    -- 🎉 no goals
#align uniform_space.completion.dist_triangle UniformSpace.Completion.dist_triangle

/-- Elements of the uniformity (defined generally for completions) can be characterized in terms
of the distance. -/
protected theorem mem_uniformity_dist (s : Set (Completion α × Completion α)) :
    s ∈ 𝓤 (Completion α) ↔ ∃ ε > 0, ∀ {a b}, dist a b < ε → (a, b) ∈ s := by
  constructor
  -- ⊢ s ∈ 𝓤 (Completion α) → ∃ ε, ε > 0 ∧ ∀ {a b : Completion α}, dist a b < ε → ( …
  · /- Start from an entourage `s`. It contains a closed entourage `t`. Its pullback in `α` is an
      entourage, so it contains an `ε`-neighborhood of the diagonal by definition of the entourages
      in metric spaces. Then `t` contains an `ε`-neighborhood of the diagonal in `Completion α`, as
      closed properties pass to the completion. -/
    intro hs
    -- ⊢ ∃ ε, ε > 0 ∧ ∀ {a b : Completion α}, dist a b < ε → (a, b) ∈ s
    rcases mem_uniformity_isClosed hs with ⟨t, ht, ⟨tclosed, ts⟩⟩
    -- ⊢ ∃ ε, ε > 0 ∧ ∀ {a b : Completion α}, dist a b < ε → (a, b) ∈ s
    have A : { x : α × α | (↑x.1, ↑x.2) ∈ t } ∈ uniformity α :=
      uniformContinuous_def.1 (uniformContinuous_coe α) t ht
    rcases mem_uniformity_dist.1 A with ⟨ε, εpos, hε⟩
    -- ⊢ ∃ ε, ε > 0 ∧ ∀ {a b : Completion α}, dist a b < ε → (a, b) ∈ s
    refine' ⟨ε, εpos, @fun x y hxy ↦ _⟩
    -- ⊢ (x, y) ∈ s
    have : ε ≤ dist x y ∨ (x, y) ∈ t := by
      refine' induction_on₂ x y _ _
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
    simp only [not_le.mpr hxy, false_or_iff, not_le] at this
    -- ⊢ (x, y) ∈ s
    exact ts this
    -- 🎉 no goals
  · /- Start from a set `s` containing an ε-neighborhood of the diagonal in `Completion α`. To show
        that it is an entourage, we use the fact that `dist` is uniformly continuous on
        `Completion α × Completion α` (this is a general property of the extension of uniformly
        continuous functions). Therefore, the preimage of the ε-neighborhood of the diagonal in ℝ
        is an entourage in `Completion α × Completion α`. Massaging this property, it follows that
        the ε-neighborhood of the diagonal is an entourage in `Completion α`, and therefore this is
        also the case of `s`. -/
    rintro ⟨ε, εpos, hε⟩
    -- ⊢ s ∈ 𝓤 (Completion α)
    let r : Set (ℝ × ℝ) := { p | dist p.1 p.2 < ε }
    -- ⊢ s ∈ 𝓤 (Completion α)
    have : r ∈ uniformity ℝ := Metric.dist_mem_uniformity εpos
    -- ⊢ s ∈ 𝓤 (Completion α)
    have T := uniformContinuous_def.1 (@Completion.uniformContinuous_dist α _) r this
    -- ⊢ s ∈ 𝓤 (Completion α)
    simp only [uniformity_prod_eq_prod, mem_prod_iff, exists_prop, Filter.mem_map,
      Set.mem_setOf_eq] at T
    rcases T with ⟨t1, ht1, t2, ht2, ht⟩
    -- ⊢ s ∈ 𝓤 (Completion α)
    refine' mem_of_superset ht1 _
    -- ⊢ t1 ⊆ s
    have A : ∀ a b : Completion α, (a, b) ∈ t1 → dist a b < ε := by
      intro a b hab
      have : ((a, b), (a, a)) ∈ t1 ×ˢ t2 := ⟨hab, refl_mem_uniformity ht2⟩
      have I := ht this
      simp [Completion.dist_self, Real.dist_eq, Completion.dist_comm] at I
      exact lt_of_le_of_lt (le_abs_self _) I
    show t1 ⊆ s
    -- ⊢ t1 ⊆ s
    · rintro ⟨a, b⟩ hp
      -- ⊢ (a, b) ∈ s
      have : dist a b < ε := A a b hp
      -- ⊢ (a, b) ∈ s
      exact hε this
      -- 🎉 no goals
#align uniform_space.completion.mem_uniformity_dist UniformSpace.Completion.mem_uniformity_dist

/-- If two points are at distance 0, then they coincide. -/
protected theorem eq_of_dist_eq_zero (x y : Completion α) (h : dist x y = 0) : x = y := by
  /- This follows from the separation of `Completion α` and from the description of
    entourages in terms of the distance. -/
  have : SeparatedSpace (Completion α) := by infer_instance
  -- ⊢ x = y
  refine' separated_def.1 this x y fun s hs ↦ _
  -- ⊢ (x, y) ∈ s
  rcases (Completion.mem_uniformity_dist s).1 hs with ⟨ε, εpos, hε⟩
  -- ⊢ (x, y) ∈ s
  rw [← h] at εpos
  -- ⊢ (x, y) ∈ s
  exact hε εpos
  -- 🎉 no goals
#align uniform_space.completion.eq_of_dist_eq_zero UniformSpace.Completion.eq_of_dist_eq_zero

/-- Reformulate `Completion.mem_uniformity_dist` in terms that are suitable for the definition
of the metric space structure. -/
protected theorem uniformity_dist' :
    𝓤 (Completion α) = ⨅ ε : { ε : ℝ // 0 < ε }, 𝓟 { p | dist p.1 p.2 < ε.val } := by
  ext s; rw [mem_iInf_of_directed]
  -- ⊢ s ∈ 𝓤 (Completion α) ↔ s ∈ ⨅ (ε : { ε // 0 < ε }), 𝓟 {p | dist p.fst p.snd < …
         -- ⊢ s ∈ 𝓤 (Completion α) ↔ ∃ i, s ∈ 𝓟 {p | dist p.fst p.snd < ↑i}
  · simp [Completion.mem_uniformity_dist, subset_def]
    -- 🎉 no goals
  · rintro ⟨r, hr⟩ ⟨p, hp⟩
    -- ⊢ ∃ z, (fun x x_1 => x ≥ x_1) ((fun ε => 𝓟 {p | dist p.fst p.snd < ↑ε}) { val  …
    use ⟨min r p, lt_min hr hp⟩
    -- ⊢ (fun x x_1 => x ≥ x_1) ((fun ε => 𝓟 {p | dist p.fst p.snd < ↑ε}) { val := r, …
    simp (config := { contextual := true }) [lt_min_iff]
    -- 🎉 no goals
#align uniform_space.completion.uniformity_dist' UniformSpace.Completion.uniformity_dist'

protected theorem uniformity_dist : 𝓤 (Completion α) = ⨅ ε > 0, 𝓟 { p | dist p.1 p.2 < ε } := by
  simpa [iInf_subtype] using @Completion.uniformity_dist' α _
  -- 🎉 no goals
#align uniform_space.completion.uniformity_dist UniformSpace.Completion.uniformity_dist

/-- Metric space structure on the completion of a pseudo_metric space. -/
instance instMetricSpace : MetricSpace (Completion α) where
  dist_self := Completion.dist_self
  eq_of_dist_eq_zero := Completion.eq_of_dist_eq_zero _ _
  dist_comm := Completion.dist_comm
  dist_triangle := Completion.dist_triangle
  dist := dist
  toUniformSpace := by infer_instance
                       -- 🎉 no goals
  uniformity_dist := Completion.uniformity_dist
  edist_dist := fun x y ↦ rfl
#align uniform_space.completion.metric_space UniformSpace.Completion.instMetricSpace

/-- The embedding of a metric space in its completion is an isometry. -/
theorem coe_isometry : Isometry ((↑) : α → Completion α) :=
  Isometry.of_dist_eq Completion.dist_eq
#align uniform_space.completion.coe_isometry UniformSpace.Completion.coe_isometry

@[simp]
protected theorem edist_eq (x y : α) : edist (x : Completion α) y = edist x y :=
  coe_isometry x y
#align uniform_space.completion.edist_eq UniformSpace.Completion.edist_eq

end UniformSpace.Completion

open UniformSpace Completion NNReal

theorem LipschitzWith.completion_extension [MetricSpace β] [CompleteSpace β] {f : α → β}
    {K : ℝ≥0} (h : LipschitzWith K f) : LipschitzWith K (Completion.extension f) :=
  LipschitzWith.of_dist_le_mul fun x y => induction_on₂ x y
    (isClosed_le (by continuity) (by continuity)) <| by
                     -- 🎉 no goals
                                     -- 🎉 no goals
      simpa only [extension_coe h.uniformContinuous, Completion.dist_eq] using h.dist_le_mul
      -- 🎉 no goals

theorem LipschitzWith.completion_map [PseudoMetricSpace β] {f : α → β} {K : ℝ≥0}
    (h : LipschitzWith K f) : LipschitzWith K (Completion.map f) :=
  one_mul K ▸ (coe_isometry.lipschitz.comp h).completion_extension

theorem Isometry.completion_extension [MetricSpace β] [CompleteSpace β] {f : α → β}
    (h : Isometry f) : Isometry (Completion.extension f) :=
  Isometry.of_dist_eq fun x y => induction_on₂ x y
    (isClosed_eq (by continuity) (by continuity)) fun _ _ ↦ by
                     -- 🎉 no goals
                                     -- 🎉 no goals
      simp only [extension_coe h.uniformContinuous, Completion.dist_eq, h.dist_eq]
      -- 🎉 no goals

theorem Isometry.completion_map [PseudoMetricSpace β] {f : α → β}
    (h : Isometry f) : Isometry (Completion.map f) :=
  (coe_isometry.comp h).completion_extension
