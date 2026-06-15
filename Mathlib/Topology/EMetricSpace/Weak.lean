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

In this file we show that whenever `some : α → Option α` is an open embedding and `α` is a
`WeakPseudoEMetricSpace`, then `Option α` is as well in a natural manner. We then use this to prove
`ℝ≥0` and `EReal` are weak extended metric spaces.

## Main statements

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

open Set Filter Topology WithTop WithBot

open scoped Uniformity Topology NNReal ENNReal Pointwise

universe u

variable {α : Type u} [t : TopologicalSpace α]

section

namespace Option

/-- Given some (extended) distance function on `α`, it can be extended to a distance function on
`Option α` by defining `edist none a = 0` if `a = none` and `∞` otherwise. -/
instance (priority := low) toEDist {α : Type u} [EDist α] : EDist (Option α) where
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
theorem edist_none_some {a : α} :
    edist (self := Option.toEDist (α := α)) none a = ⊤ := rfl

@[simp]
theorem edist_some_none {a : α} :
    edist (self := Option.toEDist (α := α)) a none = ⊤ := rfl

@[simp]
theorem edist_some_some {a b : α} :
    edist (self := Option.toEDist (α := α)) a b = edist a b := rfl

theorem some_eball (a : α) (r : ENNReal) :
    Option.some '' Metric.eball a r = Metric.eball (α := Option α) a r := by
  ext x
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
abbrev WeakPseudoEMetricSpace.OfIsOpenEmbedding {α : Type u} [t : TopologicalSpace α]
    [TopologicalSpace (Option α)] [m : WeakPseudoEMetricSpace α] [inst : EDist (Option α)]
    (h_edist : inst = Option.toEDist) (h : IsOpenEmbedding (some (α := α))) :
    WeakPseudoEMetricSpace (Option α) where
  edist := edist
  edist_self := h_edist ▸ edist_self' m
  edist_comm := h_edist ▸ edist_comm' m
  edist_triangle := h_edist ▸ edist_triangle' m
  topology_le s so := by
    apply (@EMetric.isOpen_iff (Option α) (PseudoEMetricSpace.ofEDist edist
      (h_edist ▸ edist_self' m) (h_edist ▸ edist_comm' m) (h_edist ▸ edist_triangle' m))).mpr
    intro x xs
    suffices ∃ ε > 0, @Metric.eball (Option α) Option.toEDist x ε ⊆ s by rwa [← h_edist] at this
    match x with
    | none =>
      exact ⟨1, by norm_num, by simpa [ball_infty_of_pos]⟩
    | (x : α) =>
      obtain ⟨ε, εp, εt⟩ := (@EMetric.isOpen_iff α (PseudoEMetricSpace.ofEDist edist
        m.edist_self m.edist_comm m.edist_triangle)).mp
          (m.topology_le _ <| h.continuous.isOpen_preimage s so) x (mem_preimage.mpr xs)
      exact ⟨ε, εp, some_eball x ε ▸ image_subset_iff.mpr εt⟩
  topology_eq_on_restrict := by
    intro x r
    rw [h_edist]
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

/-- If `some : α → Option α` is an open embedding and `α` is has a weak pseudo extended metric
structure, the structure extends naturally to `Option α`. -/
abbrev WeakEMetricSpace.OfIsOpenEmbedding {α : Type u} [t : TopologicalSpace α]
    [TopologicalSpace (Option α)] [m : WeakEMetricSpace α] [inst : EDist (Option α)]
    (h_edist : inst = Option.toEDist) (h : IsOpenEmbedding (some (α := α))) :
    WeakEMetricSpace (Option α) :=
  { toWeakPseudoEMetricSpace := WeakPseudoEMetricSpace.OfIsOpenEmbedding h_edist h,
    eq_of_edist_eq_zero {x y} xy := by
      rw [congr(@edist _ $h_edist x y)] at xy
      cases x <;> cases y
      · rfl
      · simp at xy
      · simp at xy
      rw [m.eq_of_edist_eq_zero xy]
    }

end Option

variable [LinearOrder α] [OrderTopology α]

/-- If `α` has a linear order topology, `some : α → WithTop α` is an open embedding with respect to
the order topologies. -/
@[to_dual]
theorem WithTop.isOpenEmbedding_some : IsOpenEmbedding (some (α := α)) :=
  ⟨WithTop.coe_strictMono.isEmbedding_of_ordConnected (range_coe (α := α) ▸ ordConnected_Iio),
   range_coe (α := α) ▸ isOpen_Iio' ⊤⟩

@[to_dual]
instance [EDist α] : EDist (WithTop α) where
  edist
  | ⊤, (x : α) => ∞
  | ⊤, ⊤ => 0
  | (x : α), ⊤ => ∞
  | (x : α), (y : α) => edist x y

/-- If `α` has a topology induced by a linear order and is a weak pseudo extended metric space,
so is `WithTop α` -/
@[to_dual]
instance instWeakPseudoEMetricSpaceWithTop [m : WeakPseudoEMetricSpace α] :
    WeakPseudoEMetricSpace (WithTop α) :=
  letI : TopologicalSpace (Option α) := TopologicalSpace.instWithTopOfOrderTopology
  letI : WeakPseudoEMetricSpace (Option α) :=
    Option.WeakPseudoEMetricSpace.OfIsOpenEmbedding (inst := instEDistWithTop) rfl
    WithTop.isOpenEmbedding_some
  inferInstanceAs <| WeakPseudoEMetricSpace (Option α)

/-- If `α` has a topology induced by a linear order and is a weak extended metric space,
so is `WithTop α` -/
@[to_dual]
instance instWeakEMetricSpaceWithTop [m : WeakEMetricSpace α] : WeakEMetricSpace (WithTop α) :=
  let : TopologicalSpace (Option α) := TopologicalSpace.instWithTopOfOrderTopology
  let : WeakEMetricSpace (Option α) := Option.WeakEMetricSpace.OfIsOpenEmbedding
    (inst := instEDistWithTop) rfl WithTop.isOpenEmbedding_some
  inferInstanceAs <| WeakEMetricSpace (Option α)

open scoped OnePoint in
instance [EDist α] : EDist (OnePoint α) where
  edist
  | ∞, (x : α) => none
  | ∞, ∞ => 0
  | (x : α), ∞ => none
  | (x : α), (y : α) => edist x y

/-- The one point compactification of a weak pseudo extended metric space is again a weak pseudo
extended metric space. -/
instance instWeakPseudoEMetricSpaceOnePoint [m : WeakPseudoEMetricSpace α] :
    WeakPseudoEMetricSpace (OnePoint α) :=
  let : TopologicalSpace (Option α) := OnePoint.instTopologicalSpace
  let : WeakPseudoEMetricSpace (Option α) := Option.WeakPseudoEMetricSpace.OfIsOpenEmbedding
    (inst := instEDistOnePoint) rfl OnePoint.isOpenEmbedding_coe
  inferInstanceAs <| WeakPseudoEMetricSpace (Option α)

/-- The one point compactification of a weak extended metric space is again a weak extended metric
space. -/
instance instWeakEMetricSpaceOnePoint [m : WeakEMetricSpace α] :
    WeakEMetricSpace (OnePoint α) :=
  let : TopologicalSpace (Option α) := OnePoint.instTopologicalSpace
  let : WeakEMetricSpace (Option α) := Option.WeakEMetricSpace.OfIsOpenEmbedding
    (inst := instEDistOnePoint) rfl OnePoint.isOpenEmbedding_coe
  inferInstanceAs <| WeakEMetricSpace (Option α)

/-- `ℝ≥0∞` is a weak extended metric space with its usual distance function. -/
noncomputable instance instWeakEMetricSpaceENNReal : WeakEMetricSpace ℝ≥0∞ :=
  inferInstanceAs <| WeakEMetricSpace (WithTop ℝ≥0)

/-- `EReal` is a weak extended metric space with its usual distance function. -/
noncomputable instance instWeakEMetricSpaceEReal : WeakEMetricSpace EReal :=
  inferInstanceAs <| WeakEMetricSpace (WithBot (WithTop ℝ))

/-- `ℕ∞` is a weak extended metric space with its usual distance function. -/
noncomputable instance instWeakEMetricSpaceENat : WeakEMetricSpace ℕ∞ :=
  inferInstanceAs <| WeakEMetricSpace (WithTop ℕ)

theorem ENNReal.edist_eq_top_iff (a b : ℝ≥0∞) : edist a b = ∞ ↔ a ≠ b ∧ (a = ∞ ∨ b = ∞) := by
  cases a <;> cases b <;> simp only [ne_eq, not_true_eq_false, or_self, and_true, iff_false,
    top_ne_coe, not_false_eq_true, coe_ne_top, or_false, and_self, or_true, and_self, iff_true,
    coe_inj, and_false, iff_false]
  · exact zero_ne_top
  · rfl
  · rfl
  · exact edist_ne_top _ _

--TODO: Many more lemmas around `edist` on `ℝ≥0∞` etc. to add
