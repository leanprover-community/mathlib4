/-
Copyright (c) 2026 Felix Pernegger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Pernegger
-/
module

public import Mathlib.Topology.EMetricSpace.Basic
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Bornology.Real
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Lemmas around weak (pseudo) extended metric spaces.

In this file we show that whenever `some : α → Option α` is an open embedding and `α` is a
`WeakPseudoEMetricSpace`, then `Option α` is as well in a natural manner. We then use this to prove
`ℝ≥0` and `EReal` are weak extended metric spaces.

## Main definitions and lemmas

* `Option.weakPseudoEMetricSpace_of_isOpenEmbedding`: states that under a weak condition, if `α` is
  a weak pseudo extended space, so is `Option α`.
* `instWeakPseudoEMetricSpaceOnePoint`: The one point compactification of a weak pseudo extended
  metric space is a weak pseudo extended metric space.
* `instWeakEMetricSpaceENNReal`: `ℝ≥0∞` is a weak extended metric space.
* `instWeakEMetricSpaceEReal`: `EReal` is a weak extended metric space.

TODO: Some lemmas around order topologies can likely be generalised from linear orders to pre-
or partial orders.

-/

@[expose] public section

open Set Filter Topology

open scoped Uniformity Topology NNReal ENNReal Pointwise

universe u

variable {α : Type u} [t : TopologicalSpace α]

@[to_dual]
instance [Preorder α] [OrderTopology α] : TopologicalSpace (WithTop α) :=
  Preorder.topology (WithTop α)

@[to_dual]
instance [Preorder α] [OrderTopology α] : OrderTopology (WithTop α) where
  topology_eq_generate_intervals := rfl

section

namespace Option

/-- Given some (extended) distance function on `α`, it can be extended to a distance function on
`Option α` by defining `edist none a = 0` if `a = none` and `∞` otherwise. -/
instance toEDist {α : Type u} [EDist α] : EDist (Option α) where
  edist
  | none, (x : α) => ∞
  | none, none => 0
  | (x : α), none => ∞
  | (x : α), (y : α) => edist x y

variable [m : WeakPseudoEMetricSpace α]

@[simp]
theorem edist_none_none : edist (self := Option.toEDist (α := α))
  none none = 0 := rfl

@[simp]
theorem edist_none_left {a : α} :
    edist (self := Option.toEDist (α := α)) none a = ⊤ := rfl

@[simp]
theorem edist_none_right {a : α} :
    edist (self := Option.toEDist (α := α)) a none = ⊤ := rfl

@[simp]
theorem edist_cast_cast {a b : α} :
    edist (self := Option.toEDist (α := α)) a b = edist a b := rfl

theorem some_eball (a : α) (r : ENNReal) :
    Option.some '' Metric.eball a r = Metric.eball (α := Option α) a r := by
  ext x
  dsimp
  constructor <;> intro h
  · obtain ⟨y, yh, yx⟩ := h
    rw [← yx]
    simpa
  match x with
  | none => simp at h
  | (y : α) =>
    exact ⟨y, h, rfl⟩

lemma edist_self' {α : Type u} [TopologicalSpace α] (m : WeakPseudoEMetricSpace α) :
    ∀ x : Option α, edist x x = 0
  | (_ : α) => by simp [m.edist_self]
  | none => rfl

lemma edist_comm' {α : Type u} [TopologicalSpace α] (m : WeakPseudoEMetricSpace α) :
    ∀ x y : Option α, edist x y = edist y x
  | (_ : α), (_ : α) => by simp [m.edist_comm]
  | (_ : α), none => by simp
  | none, (_ : α) => by simp
  | none, none => by simp

lemma edist_triangle' {α : Type u} [TopologicalSpace α] (m : WeakPseudoEMetricSpace α) :
    ∀ x y z : Option α, edist x z ≤ edist x y + edist y z
  | (_ : α), (_ : α), (_ : α) => by simp [m.edist_triangle]
  | none, (_ : α), (_ : α) => by simp
  | (_ : α), none, (_ : α) => by simp
  | none, none, (_ : α) => by simp
  | (_ : α), (_ : α), none => by simp
  | none, (_ : α), none => by simp
  | (_ : α), none, none => by simp
  | none, none, none => by simp

theorem ball_infty_of_pos {r : ENNReal} (hr : 0 < r) :
    Metric.eball (none : Option α) r = {none} := by
  refine eq_singleton_iff_unique_mem.mpr ⟨Metric.mem_eball.mpr hr, ?_⟩
  intro x
  match x with
  | (_ : α) => simp
  | none => tauto

/-- If `some : α → Option α` is an open embedding and `α` is has a weak pseudo extended metric
structure, the structure extends naturally to `Option α`. -/
abbrev weakPseudoEMetricSpace_of_isOpenEmbedding {α : Type u} [t : TopologicalSpace α]
    [TopologicalSpace (Option α)] [m : WeakPseudoEMetricSpace α]
    (h : IsOpenEmbedding (some (α := α))) : WeakPseudoEMetricSpace (Option α) where
  edist := edist
  edist_self := edist_self' m
  edist_comm := edist_comm' m
  edist_triangle := edist_triangle' m
  topology_le s so := by
    apply (@EMetric.isOpen_iff (Option α) (PseudoEMetricSpace.ofEDist edist
      (edist_self' m) (edist_comm' m) (edist_triangle' m))).mpr
    intro x xs
    match x with
    | none =>
      exact ⟨1, by simpa [ball_infty_of_pos]⟩
    | (x : α) =>
      obtain ⟨ε, εp, εt⟩ := (@EMetric.isOpen_iff α (PseudoEMetricSpace.ofEDist edist
        m.edist_self m.edist_comm m.edist_triangle)).mp
          (m.topology_le _ <| h.continuous.isOpen_preimage s so) x (mem_preimage.mpr xs)
      exact ⟨ε, εp, some_eball x ε ▸ image_subset_iff.mpr εt⟩
  topology_eq_on_restrict := by
    intro x r
    match x with
    | (x : α) =>
      obtain ⟨s', s'o, s's⟩ := m.topology_eq_on_restrict x r
      refine ⟨some '' s', ?_, ?_⟩
      · exact (IsOpenEmbedding.isOpen_iff_image_isOpen h).mp s'o
      ext ⟨y, yh⟩
      match y with
      | none => contradiction
      | (z : α) =>
        apply Set.ext_iff.mp at s's
        simp only [mem_preimage, Subtype.forall, Metric.mem_eball, mem_image] at s's ⊢ yh
        specialize s's z yh
        refine ⟨fun ⟨r, rh, rh'⟩ ↦ ?_, fun _ ↦ ⟨z, by tauto⟩⟩
        exact s's.1 <| h.injective rh' ▸ rh
    | none =>
      apply discreteTopology_iff_forall_isOpen.mp
      rw [ball_infty_of_pos ENNReal.zero_lt_top]
      exact Subsingleton.discreteTopology

end Option

variable [LinearOrder α] [OrderTopology α]

variable (α) in
/-- If `α` has a linear order topology, `some : α → WithTop α` is an open embedding with respect to
the order topologies. -/
@[to_dual]
theorem WithTop.isOpenEmbedding_some : IsOpenEmbedding (some (α := α)) :=
  ⟨WithTop.coe_strictMono.isEmbedding_of_ordConnected (range_coe (α := α) ▸ ordConnected_Iio),
   range_coe (α := α) ▸ isOpen_Iio' ⊤⟩

/-- If `α` has a topology induced by a linear order in is a weak pseudo extended metric space,
so if `WithTop α` -/
@[to_dual]
instance instWeakPseudoEMetricSpaceWithTop [m : WeakPseudoEMetricSpace α] :
    WeakPseudoEMetricSpace (WithTop α) :=
  let : TopologicalSpace (Option α) := instTopologicalSpaceWithTopOfOrderTopology
  Option.weakPseudoEMetricSpace_of_isOpenEmbedding (WithTop.isOpenEmbedding_some α)

/-- If `α` has a topology induced by a linear order in is a weak extended metric space,
so if `WithTop α` -/
@[to_dual]
instance instWeakEMetricSpaceWithTop [m : WeakEMetricSpace α] : WeakEMetricSpace (WithTop α) where
  eq_of_edist_eq_zero {x y} h := by
    cases x <;> cases y
    · rfl
    · contrapose! h
      exact ENNReal.top_ne_zero
    · contrapose! h
      exact ENNReal.top_ne_zero
    · congr 1
      apply m.eq_of_edist_eq_zero
      rw [← h]
      rfl

/-- The one point compactification of a weak pseudo extended metric space is again a weak pseudo
extended metric space. -/
instance instWeakPseudoEMetricSpaceOnePoint [m : WeakPseudoEMetricSpace α] :
    WeakPseudoEMetricSpace (OnePoint α) :=
  let : TopologicalSpace (Option α) := OnePoint.instTopologicalSpace
  Option.weakPseudoEMetricSpace_of_isOpenEmbedding OnePoint.isOpenEmbedding_coe

/-- `ℝ≥0∞` is a weak extended metric space with its usual distance function. -/
noncomputable instance instWeakEMetricSpaceENNReal : WeakEMetricSpace ℝ≥0∞ :=
  instWeakEMetricSpaceWithTop

/-- `EReal` is a weak extended metric space with its usual distance function. -/
noncomputable instance instWeakEMetricSpaceEReal : WeakEMetricSpace EReal :=
  instWeakEMetricSpaceWithBot

theorem ENNReal.edist_eq_top_iff (a b : ℝ≥0∞) : edist a b = ⊤ ↔ a ≠ b ∧ (a = ⊤ ∨ b = ⊤) := by
  cases a <;> cases b <;> simp only [ne_eq, not_true_eq_false, or_self, and_true, iff_false,
    top_ne_coe, not_false_eq_true, coe_ne_top, or_false, and_self, or_true, and_self, iff_true,
    coe_inj, and_false, iff_false]
  · exact zero_ne_top
  · rfl
  · rfl
  · exact edist_ne_top _ _

--TODO: Many more lemmas around `edist` on `ℝ≥0∞` to add
