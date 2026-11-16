/-
Copyright (c) 2026 Felix Pernegger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Pernegger
-/
module

public import Mathlib.Topology.Bornology.Real
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Instances.ENat
public import Mathlib.Topology.Instances.Nat
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.Order.WithTop

/-!
# Lemmas around weak (pseudo) extended metric spaces.

In this file we show that whenever `(↑) : α → WithTop α` is an open embedding and `α` is a
`WeakPseudoEMetricSpace`, then `WithTop α` is as well in a natural manner. We then use this to prove
`ℝ≥0∞` and `EReal` are weak extended metric spaces.

## Main statements

* `WithTop.weakPseudoEMetricSpace_of_isOpenEmbedding`: states that under a weak condition, if `α` is
  a weak pseudo extended space, so is `WithTop α`.
* `instWeakPseudoEMetricSpaceOnePoint`: The one point compactification of a weak pseudo extended
  metric space is a weak pseudo extended metric space.
* `instWeakEMetricSpaceENNReal`: `ℝ≥0∞` is a weak extended metric space.
* `instWeakEMetricSpaceEReal`: `EReal` is a weak extended metric space.

TODO: Some lemmas around order topologies can likely be generalised from linear orders to pre-
or partial orders.
-/

@[expose] public section

open Set Filter Topology WithTop WithBot

open scoped Uniformity Topology NNReal ENNReal Pointwise

universe u

variable {α : Type u} [t : TopologicalSpace α]

section

namespace WithTop

/-- Given some (extended) distance function on `α`, it can be extended to a distance function on
`WithTop α` by defining `edist ⊤ a = 0` if `a = ⊤` and `∞` otherwise. -/
@[to_dual /-- Given some (extended) distance function on `α`, it can be extended to a distance
function on `WithBot α` by defining `edist ⊥ a = 0` if `a = ⊥` and `∞` otherwise. -/]
instance (priority := low) toEDist {α : Type u} [EDist α] : EDist (WithTop α) where
  edist
  | ⊤, (x : α) => ∞
  | ⊤, ⊤ => 0
  | (x : α), ⊤ => ∞
  | (x : α), (y : α) => edist x y

variable [m : WeakPseudoEMetricSpace α]

@[to_dual (attr := simp)]
theorem edist_top_top : edist (self := WithTop.toEDist (α := α))
    ⊤ ⊤ = 0 := rfl

@[to_dual (attr := simp)]
theorem edist_top_coe {a : α} :
    edist (self := WithTop.toEDist (α := α)) ⊤ a = ⊤ := rfl

@[to_dual (attr := simp)]
theorem edist_coe_top {a : α} :
    edist (self := WithTop.toEDist (α := α)) a ⊤ = ⊤ := rfl

@[to_dual (attr := simp)]
theorem edist_coe_coe {a b : α} :
    edist (self := WithTop.toEDist (α := α)) a b = edist a b := rfl

@[to_dual]
theorem coe_image_eball (a : α) (r : ENNReal) :
    (↑) '' Metric.eball a r = Metric.eball (α := WithTop α) a r := by
  ext x
  constructor <;> intro h
  · obtain ⟨y, yh, yx⟩ := h
    rw [← yx]
    simpa
  match x with
  | ⊤ => simp at h
  | (y : α) =>
    exact ⟨y, h, rfl⟩

@[to_dual]
lemma edist_self' {α : Type u} [TopologicalSpace α] (m : WeakPseudoEMetricSpace α) :
    ∀ x : WithTop α, edist x x = 0
  | (_ : α) => by simp
  | ⊤ => rfl

@[to_dual]
lemma edist_comm' {α : Type u} [TopologicalSpace α] (m : WeakPseudoEMetricSpace α) :
    ∀ x y : WithTop α, edist x y = edist y x
  | (_ : α), (_ : α) => by simp [m.edist_comm]
  | (_ : α), ⊤ => by simp
  | ⊤, (_ : α) => by simp
  | ⊤, ⊤ => by simp

@[to_dual]
lemma edist_triangle' {α : Type u} [TopologicalSpace α] (m : WeakPseudoEMetricSpace α) :
    ∀ x y z : WithTop α, edist x z ≤ edist x y + edist y z
  | (_ : α), (_ : α), (_ : α) => by simp [m.edist_triangle]
  | ⊤, (_ : α), (_ : α) => by simp
  | (_ : α), ⊤, (_ : α) => by simp
  | ⊤, ⊤, (_ : α) => by simp
  | (_ : α), (_ : α), ⊤ => by simp
  | ⊤, (_ : α), ⊤ => by simp
  | (_ : α), ⊤, ⊤ => by simp
  | ⊤, ⊤, ⊤ => by simp

@[to_dual]
theorem ball_infty_of_pos {r : ENNReal} (hr : 0 < r) :
    Metric.eball (⊤ : WithTop α) r = {⊤} := by
  refine eq_singleton_iff_unique_mem.mpr ⟨Metric.mem_eball.mpr hr, ?_⟩
  intro x
  match x with
  | (_ : α) => simp
  | ⊤ => tauto

/-- If `(↑) : α → WithTop α` is an open embedding and `α` is has a weak pseudo extended metric
structure, the structure extends naturally to `WithTop α`. -/
@[to_dual /-- If `(↑) : α → WithBot α` is an open embedding and `α` is has a weak pseudo extended
metric structure, the structure extends naturally to `WithBot α`. -/]
abbrev WeakPseudoEMetricSpace.OfIsOpenEmbedding {α : Type u} [t : TopologicalSpace α]
    [TopologicalSpace (WithTop α)] [m : WeakPseudoEMetricSpace α] [inst : EDist (WithTop α)]
    (h_edist : inst = WithTop.toEDist) (h : IsOpenEmbedding ((↑) : α → WithTop α)) :
    WeakPseudoEMetricSpace (WithTop α) where
  edist := edist
  edist_self := h_edist ▸ edist_self' m
  edist_comm := h_edist ▸ edist_comm' m
  edist_triangle := h_edist ▸ edist_triangle' m
  topology_le s so := by
    apply (@EMetric.isOpen_iff (WithTop α) _ (PseudoEMetricSpace.ofEDist edist
      (h_edist ▸ edist_self' m) (h_edist ▸ edist_comm' m) (h_edist ▸ edist_triangle' m))).mpr
    intro x xs
    suffices ∃ ε > 0, @Metric.eball (WithTop α) WithTop.toEDist x ε ⊆ s by rwa [← h_edist] at this
    match x with
    | ⊤ =>
      exact ⟨1, by norm_num, by simpa [ball_infty_of_pos]⟩
    | (x : α) =>
      obtain ⟨ε, εp, εt⟩ := (@EMetric.isOpen_iff α _ (PseudoEMetricSpace.ofEDist edist
        m.edist_self m.edist_comm m.edist_triangle)).mp
          (m.topology_le _ <| h.continuous.isOpen_preimage s so) x (mem_preimage.mpr xs)
      exact ⟨ε, εp, coe_image_eball x ε ▸ image_subset_iff.mpr εt⟩
  topology_eq_on_restrict := by
    intro x r
    rw [h_edist]
    match x with
    | (x : α) =>
      obtain ⟨s', s'o, s's⟩ := m.topology_eq_on_restrict x r
      refine ⟨(↑) '' s', ?_, ?_⟩
      · exact (IsOpenEmbedding.isOpen_iff_image_isOpen h).mp s'o
      ext ⟨y, yh⟩
      match y with
      | ⊤ => contradiction
      | (z : α) =>
        apply Set.ext_iff.mp at s's
        simp only [mem_preimage, Subtype.forall, Metric.mem_eball, mem_image] at s's ⊢ yh
        specialize s's z yh
        refine ⟨fun ⟨r, rh, rh'⟩ ↦ ?_, fun _ ↦ ⟨z, by tauto⟩⟩
        exact s's.1 <| h.injective rh' ▸ rh
    | ⊤ =>
      apply discreteTopology_iff_forall_isOpen.mp
      rw [ball_infty_of_pos ENNReal.zero_lt_top]
      exact Subsingleton.discreteTopology

/-- If `(↑) : α → WithTop α` is an open embedding and `α` is has a weak pseudo extended metric
structure, the structure extends naturally to `WithTop α`. -/
@[to_dual /-- If `(↑) : α → WithBot α` is an open embedding and `α` is has a weak pseudo extended
metric structure, the structure extends naturally to `WithBot α`. -/]
abbrev WeakEMetricSpace.OfIsOpenEmbedding {α : Type u} [t : TopologicalSpace α]
    [TopologicalSpace (WithTop α)] [m : WeakEMetricSpace α] [inst : EDist (WithTop α)]
    (h_edist : inst = WithTop.toEDist) (h : IsOpenEmbedding ((↑) : α → WithTop α)) :
    WeakEMetricSpace (WithTop α) :=
  { toWeakPseudoEMetricSpace := WeakPseudoEMetricSpace.OfIsOpenEmbedding h_edist h,
    eq_of_edist_eq_zero {x y} xy := by
      rw [congr(@edist _ $h_edist x y)] at xy
      cases x <;> cases y
      · rfl
      · simp at xy
      · simp at xy
      rw [m.eq_of_edist_eq_zero xy]
    }

end WithTop

variable [LinearOrder α] [OrderTopology α]

@[to_dual]
instance [EDist α] : EDist (WithTop α) where
  edist
  | ⊤, (x : α) => ∞
  | ⊤, ⊤ => 0
  | (x : α), ⊤ => ∞
  | (x : α), (y : α) => edist x y

/-- If `α` has a topology induced by a linear order and is a weak pseudo extended metric space,
so doises `WithTop α`. -/
@[to_dual /-- If `α` has a topology induced by a linear order and is a weak pseudo extended metric
space, so is `WithBot α`. -/]
instance instWeakPseudoEMetricSpaceWithTop [m : WeakPseudoEMetricSpace α] :
    WeakPseudoEMetricSpace (WithTop α) :=
  letI : TopologicalSpace (WithTop α) := TopologicalSpace.instWithTopOfOrderTopology
  WithTop.WeakPseudoEMetricSpace.OfIsOpenEmbedding rfl WithTop.isOpenEmbedding_coe

/-- If `α` has a topology induced by a linear order and is a weak extended metric space,
so is `WithTop α`. -/
@[to_dual /-- If `α` has a topology induced by a linear order and is a weak extended metric space,
so is `WithBot α`. -/]
instance instWeakEMetricSpaceWithTop [m : WeakEMetricSpace α] : WeakEMetricSpace (WithTop α) :=
  let : TopologicalSpace (WithTop α) := TopologicalSpace.instWithTopOfOrderTopology
  WithTop.WeakEMetricSpace.OfIsOpenEmbedding rfl WithTop.isOpenEmbedding_coe

open scoped OnePoint in
instance [EDist α] : EDist (OnePoint α) where
  edist
  | ∞, (x : α) => ⊤
  | ∞, ∞ => 0
  | (x : α), ∞ => ⊤
  | (x : α), (y : α) => edist x y

/-- The one point compactification of a weak pseudo extended metric space is again a weak pseudo
extended metric space. -/
instance instWeakPseudoEMetricSpaceOnePoint [m : WeakPseudoEMetricSpace α] :
    WeakPseudoEMetricSpace (OnePoint α) :=
  let : TopologicalSpace (WithTop α) := OnePoint.instTopologicalSpace
  let : WeakPseudoEMetricSpace (WithTop α) := WithTop.WeakPseudoEMetricSpace.OfIsOpenEmbedding
    (inst := instEDistOnePoint) rfl OnePoint.isOpenEmbedding_coe
  inferInstanceAs <| WeakPseudoEMetricSpace (WithTop α)

/-- The one point compactification of a weak extended metric space is again a weak extended metric
space. -/
instance instWeakEMetricSpaceOnePoint [m : WeakEMetricSpace α] :
    WeakEMetricSpace (OnePoint α) :=
  let : TopologicalSpace (WithTop α) := OnePoint.instTopologicalSpace
  let : WeakEMetricSpace (WithTop α) := WithTop.WeakEMetricSpace.OfIsOpenEmbedding
    (inst := instEDistOnePoint) rfl OnePoint.isOpenEmbedding_coe
  inferInstanceAs <| WeakEMetricSpace (WithTop α)

/-- `ℝ≥0∞` is a weak extended metric space with its usual distance function. -/
noncomputable instance instWeakEMetricSpaceENNReal : WeakEMetricSpace ℝ≥0∞ :=
  inferInstanceAs <| WeakEMetricSpace (WithTop ℝ≥0)

/-- `EReal` is a weak extended metric space with its usual distance function. -/
noncomputable instance instWeakEMetricSpaceEReal : WeakEMetricSpace EReal :=
  inferInstanceAs <| WeakEMetricSpace (WithBot (WithTop ℝ))

/-- `ℕ∞` is a weak extended metric space with its usual distance function. -/
noncomputable instance instWeakEMetricSpaceENat : WeakEMetricSpace ℕ∞ :=
  inferInstanceAs <| WeakEMetricSpace (WithTop ℕ)

namespace ENNReal

@[simp]
theorem edist_top_coe (a : ℝ≥0) : edist ∞ ↑a = ∞ :=
  rfl

@[simp]
theorem edist_coe_top (a : ℝ≥0) : edist ↑a ∞ = ∞ :=
  rfl

@[simp, norm_cast]
theorem edist_coe (a b : ℝ≥0) : edist (a : ℝ≥0∞) b = edist a b :=
  rfl

@[simp]
theorem edist_eq_top_iff (a b : ℝ≥0∞) : edist a b = ∞ ↔ a ≠ b ∧ (a = ∞ ∨ b = ∞) := by
  cases a <;> cases b <;> simp

theorem edist_eq_max (a b : ℝ≥0∞) : edist a b = max (a - b) (b - a) := by
  cases a <;> cases b
  case coe.coe =>
    rw [edist_coe, ← coe_nnreal_ennreal_nndist, NNReal.nndist_eq]
    norm_cast
  all_goals simp

theorem edist_le_iff_le_add_left (a b c : ℝ≥0∞) : edist a b ≤ c ↔ a ≤ c + b ∧ b ≤ c + a := by
  simp [edist_eq_max]

theorem edist_le_iff_le_add_right (a b c : ℝ≥0∞) : edist a b ≤ c ↔ a ≤ b + c ∧ b ≤ a + c := by
  simp only [edist_le_iff_le_add_left, add_comm]

theorem sub_le_dist (a b : ℝ≥0∞) : a - b ≤ edist a b := by
  grw [edist_eq_max, ← le_max_left]

theorem le_add_edist (a b : ℝ≥0∞) : a ≤ b + edist a b := by
  grw [← sub_le_dist, ← le_add_tsub]

@[simp]
theorem edist_zero_left (a : ℝ≥0∞) : edist 0 a = a := by
  simp [edist_eq_max]

@[simp]
theorem edist_zero_right (a : ℝ≥0∞) : edist a 0 = a := by
  simp [edist_eq_max]

@[simp]
theorem edist_add_left (a b : ℝ≥0∞) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    edist (c + a) (c + b) = edist a b := by
  simp only [edist_eq_max, add_sub_add_eq_sub_left hc]

@[simp]
theorem edist_add_right (a b : ℝ≥0∞) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    edist (a + c) (b + c) = edist a b := by
  simp only [edist_eq_max, add_sub_add_eq_sub_right hc]

theorem edist_mul_left (a b : ℝ≥0∞) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    edist (c * a) (c * b) = c * edist a b := by
  simp_rw [edist_eq_max, mul_max, ENNReal.mul_sub fun _ _ => hc]

theorem edist_mul_right (a b : ℝ≥0∞) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    edist (a * c) (b * c) = edist a b * c := by
  simp_rw [edist_eq_max, max_mul, ENNReal.sub_mul fun _ _ => hc]

end ENNReal

--TODO: Add lemmas about `edist` on `ℕ∞` etc.
