/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel,
  Felix Pernegger
-/
module

public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Topology.UniformSpace.Basic
public import Mathlib.Topology.UniformSpace.OfFun

/-!
# Extended metric spaces

This file is devoted to the definition and study of `EMetricSpace`s, i.e., metric
spaces in which the distance is allowed to take the value ∞. This extended distance is
called `eDist`, and takes values in `ℝ≥0∞`.

Many definitions and theorems expected on emetric spaces are already introduced on uniform spaces
and topological spaces. For example: open and closed sets, compactness, completeness, continuity and
uniform continuity.

The class `EMetricSpace` therefore extends `UniformSpace` (and `TopologicalSpace`).

Since a lot of elementary properties don't require `eq_of_eDist_eq_zero` we start setting up the
theory of `PseudoEMetricSpace`, where we don't require `eDist x y = 0 → x = y` and we specialize
to `EMetricSpace` at the end.
-/

@[expose] public section


assert_not_exists Nat.instLocallyFiniteOrder IsUniformEmbedding.prod TendstoUniformlyOnFilter

open Filter Set Topology Set.Notation

universe u v w

variable {α : Type u} {β : Type v} {X : Type*}

/-- Characterizing uniformities associated to a (generalized) distance function `D`
in terms of the elements of the uniformity. -/
theorem uniformity_dist_of_mem_uniformity [LT β] {U : Filter (α × α)} (z : β)
    (D : α → α → β) (H : ∀ s, s ∈ U ↔ ∃ ε > z, ∀ {a b : α}, D a b < ε → (a, b) ∈ s) :
    U = ⨅ ε > z, 𝓟 { p : α × α | D p.1 p.2 < ε } :=
  HasBasis.eq_biInf ⟨fun s => by simp only [H, subset_def, Prod.forall, mem_ofPred]⟩

open scoped Uniformity Topology Filter NNReal ENNReal Pointwise

/-- `EDist α` means that `α` is equipped with an extended distance. -/
@[ext]
class EDist (α : Type*) where
  /-- Extended distance between two points -/
  eDist : α → α → ℝ≥0∞

export EDist (eDist)

namespace Metric

variable {x y : α} {ε ε₁ ε₂ : ℝ≥0∞} [EDist α]

/-- `Metric.eball x ε` is the set of all points `y` with `eDist y x < ε` -/
def eball (x : α) (ε : ℝ≥0∞) : Set α :=
  { y | eDist y x < ε }

@[simp] theorem mem_eball {x y : α} {ε : ℝ≥0∞} : y ∈ eball x ε ↔ eDist y x < ε := Iff.rfl

@[gcongr]
theorem eball_subset_eball (h : ε₁ ≤ ε₂) : eball x ε₁ ⊆ eball x ε₂ := fun _y (yx : _ < ε₁) =>
  lt_of_lt_of_le yx h

/-- The points at finite distance from `a`. -/
def boundedComponent (a : α) : Set α := {x | eDist a x ≠ ∞}

@[simp]
theorem mem_boundedComponent_iff {a x : α} :
    x ∈ boundedComponent a ↔ eDist a x ≠ ∞ := Iff.rfl

end Metric

/-- Creating a uniform space from an extended distance. -/
@[reducible]
noncomputable def uniformSpaceOfEDist (eDist : α → α → ℝ≥0∞) (eDist_self : ∀ x : α, eDist x x = 0)
    (eDist_comm : ∀ x y : α, eDist x y = eDist y x)
    (eDist_triangle : ∀ x y z : α, eDist x z ≤ eDist x y + eDist y z) : UniformSpace α :=
  .ofFun eDist eDist_self eDist_comm eDist_triangle fun ε ε0 =>
    ⟨ε / 2, ENNReal.half_pos ε0.ne', fun _ h₁ _ h₂ =>
      (ENNReal.add_lt_add h₁ h₂).trans_eq (ENNReal.add_halves _)⟩

/-- Creating a uniform space from an extended distance. We assume that
there is a preexisting topology, for which the neighborhoods can be expressed using the distance,
and we make sure that the uniform space structure we construct has a topology which is defeq
to the original one. -/
@[reducible] noncomputable def uniformSpaceOfEDistOfHasBasis [TopologicalSpace α]
    (eDist : α → α → ℝ≥0∞)
    (eDist_self : ∀ x : α, eDist x x = 0)
    (eDist_comm : ∀ x y : α, eDist x y = eDist y x)
    (eDist_triangle : ∀ x y z : α, eDist x z ≤ eDist x y + eDist y z)
    (basis : ∀ x, (𝓝 x).HasBasis (fun c ↦ 0 < c) (fun c ↦ {y | eDist x y < c})) :
    UniformSpace α :=
  .ofFunOfHasBasis eDist eDist_self eDist_comm eDist_triangle (fun ε ε0 =>
    ⟨ε / 2, ENNReal.half_pos ε0.ne', fun _ h₁ _ h₂ =>
      (ENNReal.add_lt_add h₁ h₂).trans_eq (ENNReal.add_halves _)⟩) basis

/-- A pseudo extended metric space is a type endowed with a `ℝ≥0∞`-valued distance `eDist`
satisfying reflexivity `eDist x x = 0`, commutativity `eDist x y = eDist y x`, and the triangle
inequality `eDist x z ≤ eDist x y + eDist y z`.

Note that we do not require `eDist x y = 0 → x = y`. See extended metric spaces (`EMetricSpace`) for
the similar class with that stronger assumption.

Any pseudo extended metric space is a topological space and a uniform space (see `TopologicalSpace`,
`UniformSpace`), where the topology and uniformity come from the metric.
Note that a T1 pseudo extended metric space is just an extended metric space.

We make the uniformity/topology part of the data instead of deriving it from the metric. This e.g.
ensures that we do not get a diamond when doing
`[PseudoEMetricSpace α] [PseudoEMetricSpace β] : TopologicalSpace (α × β)`:
The product metric and product topology agree, but not definitionally so.
See Note [forgetful inheritance]. -/
class PseudoEMetricSpace (α : Type u) : Type u extends EDist α where
  eDist_self : ∀ x : α, eDist x x = 0
  eDist_comm : ∀ x y : α, eDist x y = eDist y x
  eDist_triangle : ∀ x y z : α, eDist x z ≤ eDist x y + eDist y z
  toUniformSpace : UniformSpace α := uniformSpaceOfEDist eDist eDist_self eDist_comm eDist_triangle
  uniformity_eDist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | eDist p.1 p.2 < ε } := by rfl

attribute [instance_reducible, instance] PseudoEMetricSpace.toUniformSpace

/- Pseudoemetric spaces are less common than metric spaces. Therefore, we work in a dedicated
namespace, while notions associated to metric spaces are mostly in the root namespace. -/

/-- Two pseudo emetric space structures with the same edistance function coincide. -/
@[ext]
protected theorem PseudoEMetricSpace.ext {α : Type*} {m m' : PseudoEMetricSpace α}
    (h : m.toEDist = m'.toEDist) : m = m' := by
  obtain ⟨_, _, _, U, hU⟩ := m; rename EDist α => ed
  obtain ⟨_, _, _, U', hU'⟩ := m'; rename EDist α => ed'
  congr 1
  exact UniformSpace.ext (((show ed = ed' from h) ▸ hU).trans hU'.symm)

variable {x : α} {s t : Set α}

section

open Metric

variable [PseudoEMetricSpace α]

/-- Reformulation of the uniform structure in terms of the extended distance -/
theorem uniformity_pseudoedist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | eDist p.1 p.2 < ε } :=
  PseudoEMetricSpace.uniformity_eDist

theorem uniformSpace_eDist :
    ‹PseudoEMetricSpace α›.toUniformSpace =
      uniformSpaceOfEDist (α := α) eDist PseudoEMetricSpace.eDist_self PseudoEMetricSpace.eDist_comm
        PseudoEMetricSpace.eDist_triangle :=
  UniformSpace.ext uniformity_pseudoedist

theorem uniformity_basis_eDist :
    (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => { p : α × α | eDist p.1 p.2 < ε } :=
  (@uniformSpace_eDist α _).symm ▸ UniformSpace.hasBasis_ofFun ⟨1, one_pos⟩ _ _ _ _ _

theorem Metric.nhds_basis_eball : (𝓝 x).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) (Metric.eball x) :=
  nhds_basis_uniformity uniformity_basis_eDist

/-- Characterization of the elements of the uniformity in terms of the extended distance -/
theorem mem_uniformity_eDist {s : Set (α × α)} :
    s ∈ 𝓤 α ↔ ∃ ε > 0, ∀ {a b : α}, eDist a b < ε → (a, b) ∈ s :=
  uniformity_basis_eDist.mem_uniformity_iff

theorem EMetric.nhds_eq : 𝓝 x = ⨅ ε > 0, 𝓟 (Metric.eball x ε) :=
  nhds_basis_eball.eq_biInf

theorem EMetric.mem_nhds_iff : s ∈ 𝓝 x ↔ ∃ ε > 0, eball x ε ⊆ s :=
  nhds_basis_eball.mem_iff

theorem Metric.nhdsWithin_basis_eball :
    (𝓝[s] x).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => eball x ε ∩ s :=
  nhdsWithin_hasBasis nhds_basis_eball s

theorem EMetric.mem_nhdsWithin_iff : s ∈ 𝓝[t] x ↔ ∃ ε > 0, eball x ε ∩ t ⊆ s :=
  nhdsWithin_basis_eball.mem_iff

theorem EMetric.isOpen_iff : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, eball x ε ⊆ s := by
  simp [isOpen_iff_nhds, mem_nhds_iff]

@[simp] theorem Metric.isOpen_eball {r : ℝ≥0∞} : IsOpen (eball x r) := by
  apply EMetric.isOpen_iff.mpr fun y hy ↦ ?_
  refine ⟨r - eDist x y, by simp_all [PseudoEMetricSpace.eDist_comm], fun a ha ↦ ?_⟩
  simp only [mem_eball, PseudoEMetricSpace.eDist_comm y x] at hy ha ⊢
  grw [PseudoEMetricSpace.eDist_triangle a y x, PseudoEMetricSpace.eDist_comm y x,
    ← tsub_add_cancel_of_le hy.le, (ENNReal.add_lt_add_iff_right (LT.lt.ne_top hy)).mpr ha]

end

/-- A `WeakPseudoEMetricSpace` is a topological space endowed with a `ℝ≥0∞`-value distance `eDist`
which is *almost* an extended pseudometric space: the `eDist` is reflexive, commutative and
satisfies the triangle inequality, but the topology on `α` need not *equal* the topology induced
by the `eDist`. (It must be at least as fine, and agree with it on eballs of finite radius.)

This generalises both pseudo extended metric spaces and `ℝ≥0∞` (which have an extended distance,
which does not induce the order topology there). -/
class WeakPseudoEMetricSpace
    (α : Type u) [τ : TopologicalSpace α] : Type u extends EDist α  where
  eDist_self : ∀ x : α, eDist x x = 0
  eDist_comm : ∀ x y : α, eDist x y = eDist y x
  eDist_triangle : ∀ x y z : α, eDist x z ≤ eDist x y + eDist y z
  /-- The topology on `α` is at most as fine as the topology generated by the `eDist`. -/
  topology_le :
    (uniformSpaceOfEDist eDist eDist_self eDist_comm eDist_triangle).toTopologicalSpace ≤ τ
  /-- The ambient topology on `α` matches the `eDist` topology on eballs. -/
  topology_eq_on_restrict :
    ∀ (x : α) (r : ℝ≥0∞), IsOpen (Metric.eball x ⊤ ↓∩ Metric.eball x r)

@[ext]
protected theorem WeakPseudoEMetricSpace.ext
    {α : Type*} [TopologicalSpace α] {m m' : WeakPseudoEMetricSpace α}
      (h : m.toEDist = m'.toEDist) : m = m' := by
  cases m; cases m'; congr

/-- Every `PseudoEMetricSpace` has a `WeakPseudoEMetricSpace` structure by
using the topology induced by `eDist`. -/
instance PseudoEMetricSpace.toWeakPseudoEMetricSpace (α : Type u) [inst : PseudoEMetricSpace α] :
    WeakPseudoEMetricSpace α where
  eDist_self := eDist_self
  eDist_comm := eDist_comm
  eDist_triangle := eDist_triangle
  topology_le := by rw [uniformSpace_eDist]
  topology_eq_on_restrict x r := Metric.isOpen_eball.preimage_val

export WeakPseudoEMetricSpace (eDist_self eDist_comm eDist_triangle)

attribute [simp] eDist_self

section

variable [TopologicalSpace α] [WeakPseudoEMetricSpace α]

/-- Triangle inequality for the extended distance -/
theorem eDist_triangle_left (x y z : α) : eDist x y ≤ eDist z x + eDist z y := by
  rw [eDist_comm z]; apply eDist_triangle

theorem eDist_triangle_right (x y z : α) : eDist x y ≤ eDist x z + eDist y z := by
  rw [eDist_comm y]; apply eDist_triangle

theorem eDist_congr_right {x y z : α} (h : eDist x y = 0) : eDist x z = eDist y z := by
  apply le_antisymm
  · rw [← zero_add (eDist y z), ← h]
    apply eDist_triangle
  · rw [eDist_comm] at h
    rw [← zero_add (eDist x z), ← h]
    apply eDist_triangle

theorem eDist_congr_left {x y z : α} (h : eDist x y = 0) : eDist z x = eDist z y := by
  rw [eDist_comm z x, eDist_comm z y]
  apply eDist_congr_right h

theorem eDist_congr {w x y z : α} (hl : eDist w x = 0) (hr : eDist y z = 0) :
    eDist w y = eDist x z :=
  (eDist_congr_right hl).trans (eDist_congr_left hr)

theorem eDist_triangle4 (x y z t : α) : eDist x t ≤ eDist x y + eDist y z + eDist z t := by
  grw [eDist_triangle _ z, eDist_triangle]

/-- Make a `PseudoEMetricSpace` from a metric. Warning: the uniformity and topology included herein
are the ones generated by the metric. If the type has a pre-existing topology or uniformity,
`PseudoEMetricSpace.ofEDistOfTopology` should be used instead. -/
noncomputable abbrev PseudoEMetricSpace.ofEDist
    {α : Type u} (eDist : α → α → ℝ≥0∞) (eDist_self : ∀ x : α, eDist x x = 0)
    (eDist_comm : ∀ x y : α, eDist x y = eDist y x) (eDist_triangle : ∀ x y z :
    α, eDist x z ≤ eDist x y + eDist y z) : PseudoEMetricSpace α where
  eDist := eDist
  eDist_self := eDist_self
  eDist_comm := eDist_comm
  eDist_triangle := eDist_triangle
  toUniformSpace := uniformSpaceOfEDist eDist eDist_self eDist_comm eDist_triangle
  uniformity_eDist := by rfl

theorem EMetric.toUniformSpace_ofEDist {α : Type u} [EDist α] (eDist_self : ∀ x : α, eDist x x = 0)
    (eDist_comm : ∀ x y : α, eDist x y = eDist y x)
    (eDist_triangle : ∀ x y z : α, eDist x z ≤ eDist x y + eDist y z) :
    (PseudoEMetricSpace.ofEDist eDist eDist_self eDist_comm eDist_triangle).toUniformSpace =
      (uniformSpaceOfEDist eDist eDist_self eDist_comm eDist_triangle) := by rfl

end

section

variable [PseudoEMetricSpace α]

/-- Given `f : β → ℝ≥0∞`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then `f i`-neighborhoods of the diagonal form a basis of `𝓤 α`.

For specific bases see `uniformity_basis_eDist`, `uniformity_basis_eDist'`,
`uniformity_basis_eDist_nnreal`, and `uniformity_basis_eDist_inv_nat`. -/
protected theorem EMetric.mk_uniformity_basis {β : Type*} {p : β → Prop}
    {f : β → ℝ≥0∞} (hf₀ : ∀ x, p x → 0 < f x) (hf : ∀ ε, 0 < ε → ∃ x, p x ∧ f x ≤ ε) :
    (𝓤 α).HasBasis p fun x => { p : α × α | eDist p.1 p.2 < f x } := by
  refine ⟨fun s => uniformity_basis_eDist.mem_iff.trans ?_⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases hf ε ε₀ with ⟨i, hi, H⟩
    exact ⟨i, hi, fun x hx => hε <| lt_of_lt_of_le hx.out H⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, H⟩

/-- Given `f : β → ℝ≥0∞`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then closed `f i`-neighborhoods of the diagonal form a basis of `𝓤 α`.

For specific bases see `uniformity_basis_eDist_le` and `uniformity_basis_eDist_le'`. -/
protected theorem EMetric.mk_uniformity_basis_le {β : Type*} {p : β → Prop} {f : β → ℝ≥0∞}
    (hf₀ : ∀ x, p x → 0 < f x) (hf : ∀ ε, 0 < ε → ∃ x, p x ∧ f x ≤ ε) :
    (𝓤 α).HasBasis p fun x => { p : α × α | eDist p.1 p.2 ≤ f x } := by
  refine ⟨fun s => uniformity_basis_eDist.mem_iff.trans ?_⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases exists_between ε₀ with ⟨ε', hε'⟩
    rcases hf ε' hε'.1 with ⟨i, hi, H⟩
    exact ⟨i, hi, fun x hx => hε <| lt_of_le_of_lt (le_trans hx.out H) hε'.2⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, fun x hx => H (le_of_lt hx.out)⟩

theorem uniformity_basis_eDist_le :
    (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => { p : α × α | eDist p.1 p.2 ≤ ε } :=
  EMetric.mk_uniformity_basis_le (fun _ => id) fun ε ε₀ => ⟨ε, ε₀, le_refl ε⟩

theorem uniformity_basis_eDist' (ε' : ℝ≥0∞) (hε' : 0 < ε') :
    (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => ε ∈ Ioo 0 ε') fun ε => { p : α × α | eDist p.1 p.2 < ε } :=
  EMetric.mk_uniformity_basis (fun _ => And.left) fun ε ε₀ =>
    let ⟨δ, hδ⟩ := exists_between hε'
    ⟨min ε δ, ⟨lt_min ε₀ hδ.1, lt_of_le_of_lt (min_le_right _ _) hδ.2⟩, min_le_left _ _⟩

theorem uniformity_basis_eDist_le' (ε' : ℝ≥0∞) (hε' : 0 < ε') :
    (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => ε ∈ Ioo 0 ε') fun ε => { p : α × α | eDist p.1 p.2 ≤ ε } :=
  EMetric.mk_uniformity_basis_le (fun _ => And.left) fun ε ε₀ =>
    let ⟨δ, hδ⟩ := exists_between hε'
    ⟨min ε δ, ⟨lt_min ε₀ hδ.1, lt_of_le_of_lt (min_le_right _ _) hδ.2⟩, min_le_left _ _⟩

theorem uniformity_basis_eDist_nnreal :
    (𝓤 α).HasBasis (fun ε : ℝ≥0 => 0 < ε) fun ε => { p : α × α | eDist p.1 p.2 < ε } :=
  EMetric.mk_uniformity_basis (fun _ => ENNReal.coe_pos.2) fun _ε ε₀ =>
    let ⟨δ, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ε₀
    ⟨δ, ENNReal.coe_pos.1 hδ.1, le_of_lt hδ.2⟩

theorem uniformity_basis_eDist_nnreal_le :
    (𝓤 α).HasBasis (fun ε : ℝ≥0 => 0 < ε) fun ε => { p : α × α | eDist p.1 p.2 ≤ ε } :=
  EMetric.mk_uniformity_basis_le (fun _ => ENNReal.coe_pos.2) fun _ε ε₀ =>
    let ⟨δ, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ε₀
    ⟨δ, ENNReal.coe_pos.1 hδ.1, le_of_lt hδ.2⟩

theorem uniformity_basis_eDist_inv_nat :
    (𝓤 α).HasBasis (fun _ => True) fun n : ℕ => { p : α × α | eDist p.1 p.2 < (↑n)⁻¹ } :=
  EMetric.mk_uniformity_basis (fun n _ ↦ ENNReal.inv_pos.2 <| ENNReal.natCast_ne_top n) fun _ε ε₀ ↦
    let ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (ne_of_gt ε₀)
    ⟨n, trivial, le_of_lt hn⟩

theorem uniformity_basis_eDist_inv_two_pow :
    (𝓤 α).HasBasis (fun _ => True) fun n : ℕ => { p : α × α | eDist p.1 p.2 < 2⁻¹ ^ n } :=
  EMetric.mk_uniformity_basis (fun _ _ ↦ ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _)
    fun _ε ε₀ ↦
    let ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt (ne_of_gt ε₀)
    ⟨n, trivial, le_of_lt hn⟩

/-- Fixed size neighborhoods of the diagonal belong to the uniform structure -/
theorem eDist_mem_uniformity {ε : ℝ≥0∞} (ε0 : 0 < ε) : { p : α × α | eDist p.1 p.2 < ε } ∈ 𝓤 α :=
  mem_uniformity_eDist.2 ⟨ε, ε0, id⟩

namespace EMetric

instance (priority := 900) instIsCountablyGeneratedUniformity : IsCountablyGenerated (𝓤 α) :=
  isCountablyGenerated_of_seq ⟨_, uniformity_basis_eDist_inv_nat.eq_iInf⟩

/-- ε-δ characterization of uniform continuity on a set for pseudoemetric spaces -/
theorem uniformContinuousOn_iff [PseudoEMetricSpace β] {f : α → β} {s : Set α} :
    UniformContinuousOn f s ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {a}, a ∈ s → ∀ {b}, b ∈ s → eDist a b < δ → eDist (f a) (f b) < ε :=
  uniformity_basis_eDist.uniformContinuousOn_iff uniformity_basis_eDist

/-- ε-δ characterization of uniform continuity on pseudoemetric spaces -/
theorem uniformContinuous_iff [PseudoEMetricSpace β] {f : α → β} :
    UniformContinuous f ↔ ∀ ε > 0, ∃ δ > 0, ∀ {a b : α}, eDist a b < δ → eDist (f a) (f b) < ε :=
  uniformity_basis_eDist.uniformContinuous_iff uniformity_basis_eDist

/-- Version of `EMetric.uniformContinuousOn_iff` with non-strict inequalities. -/
theorem uniformContinuousOn_iff_le [PseudoEMetricSpace β] {f : α → β} {s : Set α} :
    UniformContinuousOn f s ↔
      ∀ ε > 0, ∃ δ > 0, ∀ a ∈ s, ∀ b ∈ s, eDist a b ≤ δ → eDist (f a) (f b) ≤ ε :=
  uniformity_basis_eDist_le.uniformContinuousOn_iff uniformity_basis_eDist_le

/-- Version of `EMetric.uniformContinuous_iff` with non-strict inequalities. -/
theorem uniformContinuous_iff_le [PseudoEMetricSpace β] {f : α → β} :
    UniformContinuous f ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃a b : α⦄, eDist a b ≤ δ → eDist (f a) (f b) ≤ ε :=
  uniformity_basis_eDist_le.uniformContinuous_iff uniformity_basis_eDist_le

end EMetric

end

open EMetric

/-- Auxiliary function to replace the uniformity on a pseudoemetric space with
a uniformity which is equal to the original one, but maybe not defeq.
This is useful if one wants to construct a pseudoemetric space with a
specified uniformity. See Note [forgetful inheritance] explaining why having definitionally
the right uniformity is often important.
See note [reducible non-instances].
-/
abbrev PseudoEMetricSpace.replaceUniformity {α} [U : UniformSpace α] (m : PseudoEMetricSpace α)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : PseudoEMetricSpace α where
  eDist := @eDist _ m.toEDist
  eDist_self := eDist_self
  eDist_comm := eDist_comm
  eDist_triangle := eDist_triangle
  toUniformSpace := U
  uniformity_eDist := H.trans (@PseudoEMetricSpace.uniformity_eDist α _)

/-- The extended pseudometric induced by a function taking values in a pseudoemetric space.
See note [reducible non-instances]. -/
abbrev PseudoEMetricSpace.induced {α β} (f : α → β) (m : PseudoEMetricSpace β) :
    PseudoEMetricSpace α where
  eDist x y := eDist (f x) (f y)
  eDist_self _ := eDist_self _
  eDist_comm _ _ := eDist_comm _ _
  eDist_triangle _ _ _ := eDist_triangle _ _ _
  toUniformSpace := UniformSpace.comap f m.toUniformSpace
  uniformity_eDist := (uniformity_basis_eDist.comap (Prod.map f f)).eq_biInf

/-- `WeakPseudoEMetricSpace` can be induced backwards. -/
abbrev WeakPseudoEMetricSpace.IsInducing {α β : Type*} [e : TopologicalSpace α]
  [n : TopologicalSpace β] {f : α → β} (hf : IsInducing f) (m : WeakPseudoEMetricSpace β) :
    WeakPseudoEMetricSpace α where
  eDist := fun x y ↦ eDist (f x) (f y)
  eDist_self x := eDist_self (f x)
  eDist_comm x y := eDist_comm (f x) (f y)
  eDist_triangle x y z := eDist_triangle (f x) (f y) (f z)
  topology_le := by
    let hα := PseudoEMetricSpace.ofEDist (fun x y ↦ eDist (f x) (f y))
      (fun x ↦ eDist_self (f x)) (fun x y ↦ eDist_comm (f x) (f y))
      (fun x y z ↦ eDist_triangle (f x) (f y) (f z))
    let hβ := PseudoEMetricSpace.ofEDist m.eDist eDist_self eDist_comm eDist_triangle
    rw [(isInducing_iff f).mp hf]
    refine (continuous_le_rng m.topology_le ?_).le_induced
    refine @Continuous.mk α β hα.toUniformSpace.toTopologicalSpace
      hβ.toUniformSpace.toTopologicalSpace f fun s hs ↦ ?_
    rw [EMetric.isOpen_iff] at hs ⊢
    intro x (hx : f x ∈ s)
    obtain ⟨ε, hε, hεs⟩ := hs (f x) hx
    exact ⟨ε, hε, fun y hy ↦ hεs hy⟩
  topology_eq_on_restrict x r := by
    obtain ⟨u, hu, uy⟩ := m.topology_eq_on_restrict (f x) r
    rw [(isInducing_iff f).mp hf]
    exact ⟨f ⁻¹' u, isOpen_induced hu, by aesop (add simp [Set.ext_iff])⟩

/-- Weak pseudo-emetric space instance on subsets of weak pseudo-emetric spaces -/
instance {α : Type*} {p : α → Prop} [TopologicalSpace α] [WeakPseudoEMetricSpace α] :
    WeakPseudoEMetricSpace (Subtype p) :=
  WeakPseudoEMetricSpace.IsInducing IsInducing.subtypeVal ‹_›

/-- Pseudoemetric space instance on subsets of pseudoemetric spaces -/
instance {α : Type*} {p : α → Prop} [PseudoEMetricSpace α] : PseudoEMetricSpace (Subtype p) :=
  PseudoEMetricSpace.induced Subtype.val ‹_›

section

variable [TopologicalSpace α] [WeakPseudoEMetricSpace α]

/-- The extended pseudodistance on a subset of a pseudoemetric space is the restriction of
the original pseudodistance, by definition. -/
theorem Subtype.eDist_eq {p : α → Prop} (x y : Subtype p) : eDist x y = eDist (x : α) y := rfl

/-- The extended pseudodistance on a subtype of a pseudoemetric space is the restriction of
the original pseudodistance, by definition. -/
@[simp]
theorem Subtype.eDist_mk_mk {p : α → Prop} {x y : α} (hx : p x) (hy : p y) :
    eDist (⟨x, hx⟩ : Subtype p) ⟨y, hy⟩ = eDist x y :=
  rfl

/-- Consider an extended distance on a topological space, for which the neighborhoods can be
expressed in terms of the distance. Then we define the emetric space structure associated to this
distance, with a topology defeq to the initial one. -/
@[reducible] noncomputable def PseudoEMetricSpace.ofEDistOfTopology {α : Type*} [TopologicalSpace α]
    (d : α → α → ℝ≥0∞) (h_self : ∀ x, d x x = 0) (h_comm : ∀ x y, d x y = d y x)
    (h_triangle : ∀ x y z, d x z ≤ d x y + d y z)
    (h_basis : ∀ x, (𝓝 x).HasBasis (fun c ↦ 0 < c) (fun c ↦ {y | d x y < c})) :
    PseudoEMetricSpace α where
  eDist := d
  eDist_self := h_self
  eDist_comm := h_comm
  eDist_triangle := h_triangle
  toUniformSpace := uniformSpaceOfEDistOfHasBasis d h_self h_comm h_triangle h_basis
  uniformity_eDist := rfl

end

variable {α : Type*} [PseudoEMetricSpace α]

section ULift

instance : PseudoEMetricSpace (ULift α) :=
  PseudoEMetricSpace.induced ULift.down ‹_›

theorem ULift.eDist_eq (x y : ULift α) : eDist x y = eDist x.down y.down := rfl

@[simp]
theorem ULift.eDist_up_up (x y : α) : eDist (ULift.up x) (ULift.up y) = eDist x y := rfl

end ULift

/-- The product of two pseudoemetric spaces, with the max distance, is an extended
pseudometric spaces. We make sure that the uniform structure thus constructed is the one
corresponding to the product of uniform spaces, to avoid diamond problems. -/
instance Prod.pseudoEMetricSpaceMax [PseudoEMetricSpace β] :
    PseudoEMetricSpace (α × β) where
  eDist x y := eDist x.1 y.1 ⊔ eDist x.2 y.2
  eDist_self x := by simp
  eDist_comm x y := by simp [eDist_comm]
  eDist_triangle _ _ _ :=
    max_le (le_trans (eDist_triangle _ _ _) (add_le_add (le_max_left _ _) (le_max_left _ _)))
      (le_trans (eDist_triangle _ _ _) (add_le_add (le_max_right _ _) (le_max_right _ _)))
  uniformity_eDist := uniformity_prod.trans <| by
    simp [PseudoEMetricSpace.uniformity_eDist, ← iInf_inf_eq, ofPred_and]
  toUniformSpace := inferInstance

theorem Prod.eDist_eq [PseudoEMetricSpace β] (x y : α × β) :
    eDist x y = max (eDist x.1 y.1) (eDist x.2 y.2) :=
  rfl

namespace Metric

variable {α : Type*} [TopologicalSpace α] [WeakPseudoEMetricSpace α] {x y z : α} {ε ε₁ ε₂ : ℝ≥0∞}
  {s : Set α}

theorem mem_eball' : y ∈ eball x ε ↔ eDist x y < ε := by rw [eDist_comm, mem_eball]

/-- `Metric.closedEBall x ε` is the set of all points `y` with `eDist y x ≤ ε` -/
def closedEBall {α : Type*} [h : EDist α] (x : α) (ε : ℝ≥0∞) :=
  { y | eDist y x ≤ ε }

@[simp] theorem mem_closedEBall {α : Type*} [EDist α] {x y : α} :
  y ∈ closedEBall x ε ↔ eDist y x ≤ ε := Iff.rfl

theorem mem_closedEBall' : y ∈ closedEBall x ε ↔ eDist x y ≤ ε := by
  rw [eDist_comm, mem_closedEBall]

@[simp]
theorem closedEBall_top {α : Type*} [EDist α] (x : α) : closedEBall x ∞ = univ :=
  eq_univ_of_forall fun _ => mem_ofPred.2 le_top

theorem eball_subset_closedEBall {α : Type*} [EDist α] {x : α} :
    eball x ε ⊆ closedEBall x ε := fun _ h => le_of_lt h.out

theorem pos_of_mem_eball {α : Type*} [EDist α] {x y : α} (hy : y ∈ eball x ε) : 0 < ε :=
  hy.pos

theorem mem_eball_self (h : 0 < ε) : x ∈ eball x ε := by
  rwa [mem_eball, eDist_self]

theorem mem_closedEBall_self : x ∈ closedEBall x ε := by
  rw [mem_closedEBall, eDist_self]; apply zero_le

theorem mem_eball_comm : x ∈ eball y ε ↔ y ∈ eball x ε := by rw [mem_eball', mem_eball]

theorem mem_closedEBall_comm : x ∈ closedEBall y ε ↔ y ∈ closedEBall x ε := by
  rw [mem_closedEBall', mem_closedEBall]

@[gcongr]
theorem closedEBall_subset_closedEBall {α : Type*} [EDist α] {x : α} (h : ε₁ ≤ ε₂) :
    closedEBall x ε₁ ⊆ closedEBall x ε₂ :=
  fun _y (yx : _ ≤ ε₁) => le_trans yx h

theorem eball_disjoint (h : ε₁ + ε₂ ≤ eDist x y) : Disjoint (eball x ε₁) (eball y ε₂) :=
  Set.disjoint_left.mpr fun z h₁ h₂ =>
    (eDist_triangle_left x y z).not_gt <| (ENNReal.add_lt_add h₁ h₂).trans_le h

theorem eball_subset (h : eDist x y + ε₁ ≤ ε₂) (h' : eDist x y ≠ ∞) : eball x ε₁ ⊆ eball y ε₂ :=
  fun z zx =>
  calc
    eDist z y ≤ eDist z x + eDist x y := eDist_triangle _ _ _
    _ = eDist x y + eDist z x := add_comm _ _
    _ < eDist x y + ε₁ := ENNReal.add_lt_add_left h' zx
    _ ≤ ε₂ := h

theorem exists_eball_subset_eball (h : y ∈ eball x ε) : ∃ ε' > 0, eball y ε' ⊆ eball x ε := by
  have : 0 < ε - eDist y x := by simpa using h
  refine ⟨ε - eDist y x, this, eball_subset ?_ (ne_top_of_lt h)⟩
  exact (add_tsub_cancel_of_le (mem_eball.mp h).le).le

theorem eball_eq_empty_iff : eball x ε = ∅ ↔ ε = 0 :=
  eq_empty_iff_forall_notMem.trans
    ⟨fun h => le_bot_iff.1 (le_of_not_gt fun ε0 => h _ (mem_eball_self ε0)), fun ε0 _ h =>
      not_lt_of_ge (le_of_eq ε0) (pos_of_mem_eball h)⟩

theorem ordConnected_setOfPred_closedEBall_subset (x : α) (s : Set α) :
    OrdConnected { r | closedEBall x r ⊆ s } :=
  ⟨fun _ _ _ h₁ _ h₂ => (closedEBall_subset_closedEBall h₂.2).trans h₁⟩

@[deprecated (since := "2026-07-09")]
alias ordConnected_setOf_closedEBall_subset := ordConnected_setOfPred_closedEBall_subset

theorem ordConnected_setOfPred_eball_subset (x : α) (s : Set α) :
    OrdConnected { r | eball x r ⊆ s } :=
  ⟨fun _ _ _ h₁ _ h₂ => (eball_subset_eball h₂.2).trans h₁⟩

@[deprecated (since := "2026-07-09")]
alias ordConnected_setOf_eball_subset := ordConnected_setOfPred_eball_subset

/-- Relation “two points are at a finite edistance” is an equivalence relation. -/
@[instance_reducible]
def edistLtTopSetoid : Setoid α where
  r x y := eDist x y < ⊤
  iseqv :=
    { refl x := by rw [eDist_self]; exact ENNReal.coe_lt_top
      symm h := by rwa [eDist_comm]
      trans hxy hyz := lt_of_le_of_lt (eDist_triangle _ _ _) (ENNReal.add_lt_top.2 ⟨hxy, hyz⟩) }

theorem boundedComponent_eq {a b : α} (h : b ∈ boundedComponent a) :
    boundedComponent a = boundedComponent b := by
  ext x
  simp only [mem_boundedComponent_iff, ← lt_top_iff_ne_top] at h ⊢
  exact ⟨edistLtTopSetoid.trans (edistLtTopSetoid.symm h), edistLtTopSetoid.trans h⟩

@[simp]
theorem eball_zero {α : Type*} [EDist α] {x : α} : eball x 0 = ∅ := by
  ext
  simp

theorem nhds_basis_closedEBall {α : Type*} [PseudoEMetricSpace α] {x : α} :
    (𝓝 x).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) (closedEBall x) :=
  nhds_basis_uniformity uniformity_basis_eDist_le

theorem nhdsWithin_basis_closedEBall {α : Type*} [PseudoEMetricSpace α] {s : Set α} {x : α} :
    (𝓝[s] x).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => closedEBall x ε ∩ s :=
  nhdsWithin_hasBasis nhds_basis_closedEBall s

end Metric

namespace EMetric
variable {x : α} {ε : ℝ≥0∞} {s t : Set α}

open Metric

/-- ε-characterization of the closure in pseudoemetric spaces -/
theorem mem_closure_iff : x ∈ closure s ↔ ∀ ε > 0, ∃ y ∈ s, eDist x y < ε :=
  (mem_closure_iff_nhds_basis nhds_basis_eball).trans <| by simp only [mem_eball, eDist_comm x]

lemma dense_iff : Dense s ↔ ∀ (x : α), ∀ r > 0, (eball x r ∩ s).Nonempty :=
  forall_congr' fun x => by
    simp only [mem_closure_iff, Set.Nonempty, mem_inter_iff, and_comm, mem_eball']

theorem tendsto_nhds {f : Filter β} {u : β → α} {a : α} :
    Tendsto u f (𝓝 a) ↔ ∀ ε > 0, ∀ᶠ x in f, eDist (u x) a < ε :=
  nhds_basis_eball.tendsto_right_iff

theorem tendsto_atTop [Nonempty β] [SemilatticeSup β] {u : β → α} {a : α} :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, eDist (u n) a < ε :=
  (atTop_basis.tendsto_iff nhds_basis_eball).trans <| by
    simp only [true_and, mem_Ici, mem_eball]

section

variable [PseudoEMetricSpace β] {f : α → β}

theorem tendsto_nhdsWithin_nhdsWithin {t : Set β} {a b} :
    Tendsto f (𝓝[s] a) (𝓝[t] b) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ ⦃x⦄, x ∈ s → eDist x a < δ → f x ∈ t ∧ eDist (f x) b < ε :=
  (nhdsWithin_basis_eball.tendsto_iff nhdsWithin_basis_eball).trans <|
    forall₂_congr fun ε _ => exists_congr fun δ => and_congr_right fun _ =>
      forall_congr' fun x => by simp; tauto

theorem tendsto_nhdsWithin_nhds {a b} :
    Tendsto f (𝓝[s] a) (𝓝 b) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {x : α}, x ∈ s → eDist x a < δ → eDist (f x) b < ε := by
  rw [← nhdsWithin_univ b, tendsto_nhdsWithin_nhdsWithin]
  simp only [mem_univ, true_and]

theorem tendsto_nhds_nhds {a b} :
    Tendsto f (𝓝 a) (𝓝 b) ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃x⦄, eDist x a < δ → eDist (f x) b < ε :=
  nhds_basis_eball.tendsto_iff nhds_basis_eball

theorem continuousAt_iff {a} :
    ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : α⦄, eDist x a < δ → eDist (f x) (f a) < ε := by
  rw [ContinuousAt, tendsto_nhds_nhds]

theorem continuousWithinAt_iff {a s} :
    ContinuousWithinAt f s a ↔
      ∀ ε > 0, ∃ δ > 0, ∀ ⦃x : α⦄, x ∈ s → eDist x a < δ → eDist (f x) (f a) < ε := by
  rw [ContinuousWithinAt, tendsto_nhdsWithin_nhds]

theorem continuousOn_iff {s} :
    ContinuousOn f s ↔
      ∀ b ∈ s, ∀ ε > 0, ∃ δ > 0, ∀ a ∈ s, eDist a b < δ → eDist (f a) (f b) < ε := by
  simp [ContinuousOn, continuousWithinAt_iff]

theorem continuous_iff :
    Continuous f ↔ ∀ b, ∀ ε > 0, ∃ δ > 0, ∀ a, eDist a b < δ → eDist (f a) (f b) < ε :=
  continuous_iff_continuousAt.trans <| forall_congr' fun _ ↦ tendsto_nhds_nhds

end

section

variable [TopologicalSpace β] {f : β → α}

theorem continuousAt_iff' {b} :
    ContinuousAt f b ↔ ∀ ε > 0, ∀ᶠ x in 𝓝 b, eDist (f x) (f b) < ε := by
  rw [ContinuousAt, tendsto_nhds]

theorem continuousWithinAt_iff' {b s} :
    ContinuousWithinAt f s b ↔ ∀ ε > 0, ∀ᶠ x in 𝓝[s] b, eDist (f x) (f b) < ε := by
  rw [ContinuousWithinAt, tendsto_nhds]

theorem continuousOn_iff' {s} :
    ContinuousOn f s ↔ ∀ b ∈ s, ∀ ε > 0, ∀ᶠ x in 𝓝[s] b, eDist (f x) (f b) < ε := by
  simp [ContinuousOn, continuousWithinAt_iff']

theorem continuous_iff' :
    Continuous f ↔ ∀ a, ∀ ε > 0, ∀ᶠ x in 𝓝 a, eDist (f x) (f a) < ε :=
  continuous_iff_continuousAt.trans <| forall_congr' fun _ ↦ tendsto_nhds

end

end EMetric

namespace Metric
variable {x : α} {ε : ℝ≥0∞}

theorem isClosed_eball_top : IsClosed (eball x ⊤) :=
  isOpen_compl_iff.1 <| EMetric.isOpen_iff.2 fun _y hy =>
    ⟨⊤, ENNReal.coe_lt_top, fun _z hzy hzx =>
      hy (edistLtTopSetoid.trans (edistLtTopSetoid.symm hzy) hzx)⟩

theorem isClopen_eball_top : IsClopen (eball x ⊤) := ⟨isClosed_eball_top, isOpen_eball⟩

variable (x)

theorem eball_mem_nhds (ε0 : 0 < ε) : eball x ε ∈ 𝓝 x :=
  isOpen_eball.mem_nhds (mem_eball_self ε0)

theorem closedEBall_mem_nhds (ε0 : 0 < ε) : closedEBall x ε ∈ 𝓝 x :=
  mem_of_superset (eball_mem_nhds x ε0) eball_subset_closedEBall

theorem eball_prod_same [PseudoEMetricSpace β] (x : α) (y : β) (r : ℝ≥0∞) :
    eball x r ×ˢ eball y r = eball (x, y) r :=
  ext fun z => by simp [Prod.eDist_eq]

theorem closedEBall_prod_same [PseudoEMetricSpace β] (x : α) (y : β) (r : ℝ≥0∞) :
    closedEBall x r ×ˢ closedEBall y r = closedEBall (x, y) r :=
  ext fun z => by simp [Prod.eDist_eq]

end Metric

namespace Subtype

variable {α : Type*} [EDist α] {p : α → Prop}

instance : EDist (Subtype p) where
  eDist x y := eDist x.val y.val

open Metric

@[simp]
theorem preimage_eball (a : {a // p a}) (r : ℝ≥0∞) :
    Subtype.val ⁻¹' (eball a.val r) = eball a r :=
  rfl

@[simp]
theorem preimage_closedEBall (a : {a // p a}) (r : ℝ≥0∞) :
    Subtype.val ⁻¹' (closedEBall a.val r) = closedEBall a r :=
  rfl

@[simp]
theorem image_eball (a : {a // p a}) (r : ℝ≥0∞) :
    Subtype.val '' (eball a r) = eball a.val r ∩ {a | p a} := by
  rw [← preimage_eball, image_preimage_eq_inter_range, range_val_subtype]

@[simp]
theorem image_closedEBall (a : {a // p a}) (r : ℝ≥0∞) :
    Subtype.val '' (closedEBall a r) = closedEBall a.val r ∩ {a | p a} := by
  rw [← preimage_closedEBall, image_preimage_eq_inter_range, range_val_subtype]

end Subtype

/-- An extended metric space is a type endowed with a `ℝ≥0∞`-valued distance `eDist` satisfying
`eDist x y = 0 ↔ x = y`, commutativity `eDist x y = eDist y x`, and the triangle inequality
`eDist x z ≤ eDist x y + eDist y z`.

See pseudo extended metric spaces (`PseudoEMetricSpace`) for the similar class with the
`eDist x y = 0 ↔ x = y` assumption weakened to `eDist x x = 0`.

Any extended metric space is a T1 topological space and a uniform space (see `TopologicalSpace`,
`T1Space`, `UniformSpace`), where the topology and uniformity come from the metric.

We make the uniformity/topology part of the data instead of deriving it from the metric.
This e.g. ensures that we do not get a diamond when doing
`[EMetricSpace α] [EMetricSpace β] : TopologicalSpace (α × β)`:
The product metric and product topology agree, but not definitionally so.
See Note [forgetful inheritance]. -/
class EMetricSpace (α : Type u) : Type u extends PseudoEMetricSpace α where
  eq_of_eDist_eq_zero : ∀ {x y : α}, eDist x y = 0 → x = y

@[ext]
protected theorem EMetricSpace.ext
    {α : Type*} {m m' : EMetricSpace α} (h : m.toEDist = m'.toEDist) : m = m' := by
  cases m
  cases m'
  congr
  ext1
  assumption

/-- A weak extended metric space extends a `WeakPseudoEMetricSpace` with the condition
`eDist x y = 0 ↔ x = y`. -/
class WeakEMetricSpace
    (α : Type u) [TopologicalSpace α] : Type u extends WeakPseudoEMetricSpace α where
  eq_of_eDist_eq_zero : ∀ {x y : α}, eDist x y = 0 → x = y

@[ext]
protected theorem WeakEMetricSpace.ext {α : Type*} [TopologicalSpace α] {m m' : WeakEMetricSpace α}
    (h : m.toEDist = m'.toEDist) : m = m' := by
  cases m
  cases m'
  congr
  ext1
  assumption

/--
Every `EMetricSpace` has a `WeakEMetricSpace` structure by using the topology induced by its
`eDist`. -/
instance EMetricSpace.toWeakEMetricSpace (α : Type u) [EMetricSpace α] :
    WeakEMetricSpace α where
  eq_of_eDist_eq_zero := eq_of_eDist_eq_zero

variable {γ : Type w} [TopologicalSpace γ] [WeakEMetricSpace γ]

export WeakEMetricSpace (eq_of_eDist_eq_zero)

/-- Characterize the equality of points by the vanishing of their extended distance -/
@[simp]
theorem eDist_eq_zero {x y : γ} : eDist x y = 0 ↔ x = y :=
  ⟨eq_of_eDist_eq_zero, fun h => h ▸ eDist_self _⟩

@[simp]
theorem zero_eq_eDist {x y : γ} : 0 = eDist x y ↔ x = y := eq_comm.trans eDist_eq_zero

theorem eDist_le_zero {x y : γ} : eDist x y ≤ 0 ↔ x = y :=
  nonpos_iff_eq_zero.trans eDist_eq_zero

@[simp]
theorem eDist_pos {x y : γ} : 0 < eDist x y ↔ x ≠ y := by simp [← not_le]

@[simp] lemma Metric.closedEBall_zero (x : γ) : closedEBall x 0 = {x} := by ext; simp

/-- Two points coincide if their distance is `< ε` for all positive ε -/
theorem eq_of_forall_eDist_le {x y : γ} (h : ∀ ε > 0, eDist x y ≤ ε) : x = y :=
  eq_of_eDist_eq_zero (eq_of_le_of_forall_lt_imp_le_of_dense bot_le h)

/-- Auxiliary function to replace the uniformity on an emetric space with
a uniformity which is equal to the original one, but maybe not defeq.
This is useful if one wants to construct an emetric space with a
specified uniformity. See Note [forgetful inheritance] explaining why having definitionally
the right uniformity is often important.
See note [reducible non-instances].
-/
abbrev EMetricSpace.replaceUniformity {γ} [U : UniformSpace γ] (m : EMetricSpace γ)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : EMetricSpace γ where
  eDist := @eDist _ m.toEDist
  eDist_self := eDist_self (τ := m.toUniformSpace.toTopologicalSpace)
  eq_of_eDist_eq_zero := @eq_of_eDist_eq_zero _ _
  eDist_comm := eDist_comm (τ := m.toUniformSpace.toTopologicalSpace)
  eDist_triangle := eDist_triangle (τ := m.toUniformSpace.toTopologicalSpace)
  toUniformSpace := U
  uniformity_eDist := H.trans (@PseudoEMetricSpace.uniformity_eDist γ _)

/-- Auxiliary function to replace the topology on an emetric space with
a topology which is equal to the original one, but maybe not defeq.
This is useful if one wants to construct an emetric space with a
specified topology. See Note [forgetful inheritance] explaining why having definitionally
the right topology is often important.
See note [reducible non-instances].
-/
abbrev EMetricSpace.replaceTopology {γ} [T : TopologicalSpace γ] (m : EMetricSpace γ)
    (H : T = m.toUniformSpace.toTopologicalSpace) : EMetricSpace γ where
  eDist := @eDist _ m.toEDist
  eDist_self := eDist_self (τ := m.toUniformSpace.toTopologicalSpace)
  eq_of_eDist_eq_zero := @eq_of_eDist_eq_zero _ _
  eDist_comm := eDist_comm (τ := m.toUniformSpace.toTopologicalSpace)
  eDist_triangle := eDist_triangle (τ := m.toUniformSpace.toTopologicalSpace)
  toUniformSpace := m.toUniformSpace.replaceTopology H
  uniformity_eDist := PseudoEMetricSpace.uniformity_eDist

/-- The extended metric induced by an injective function taking values in an emetric space.
See Note [reducible non-instances]. -/
abbrev EMetricSpace.induced {γ β} (f : γ → β) (hf : Function.Injective f) (m : EMetricSpace β) :
    EMetricSpace γ :=
  { PseudoEMetricSpace.induced f m.toPseudoEMetricSpace with
    eq_of_eDist_eq_zero := fun h => hf (eDist_eq_zero.1 h) }

/-- EMetric space instance on subsets of emetric spaces -/
instance {α : Type*} {p : α → Prop} [EMetricSpace α] : EMetricSpace (Subtype p) :=
  EMetricSpace.induced Subtype.val Subtype.coe_injective ‹_›

/-- EMetric space instance on the multiplicative opposite of an emetric space. -/
@[to_additive /-- EMetric space instance on the additive opposite of an emetric space. -/]
instance {α : Type*} [EMetricSpace α] : EMetricSpace αᵐᵒᵖ :=
  EMetricSpace.induced MulOpposite.unop MulOpposite.unop_injective ‹_›

instance {α : Type*} [EMetricSpace α] : EMetricSpace (ULift α) :=
  EMetricSpace.induced ULift.down ULift.down_injective ‹_›

/-- Reformulation of the uniform structure in terms of the extended distance -/
theorem uniformity_eDist {γ} [EMetricSpace γ] :
    𝓤 γ = ⨅ ε > 0, 𝓟 { p : γ × γ | eDist p.1 p.2 < ε } :=
  PseudoEMetricSpace.uniformity_eDist

/-!
### `Additive`, `Multiplicative`

The distance on those type synonyms is inherited without change.
-/


open Additive Multiplicative

section

variable [EDist X]

instance : EDist (Additive X) := ‹EDist X›
instance : EDist (Multiplicative X) := ‹EDist X›

@[simp]
theorem eDist_ofMul (a b : X) : eDist (ofMul a) (ofMul b) = eDist a b :=
  rfl

@[simp]
theorem eDist_ofAdd (a b : X) : eDist (ofAdd a) (ofAdd b) = eDist a b :=
  rfl

@[simp]
theorem eDist_toMul (a b : Additive X) : eDist a.toMul b.toMul = eDist a b :=
  rfl

@[simp]
theorem eDist_toAdd (a b : Multiplicative X) : eDist a.toAdd b.toAdd = eDist a b :=
  rfl

end

instance [PseudoEMetricSpace X] : PseudoEMetricSpace (Additive X) := ‹PseudoEMetricSpace X›
instance [PseudoEMetricSpace X] : PseudoEMetricSpace (Multiplicative X) := ‹PseudoEMetricSpace X›
instance [EMetricSpace X] : EMetricSpace (Additive X) := ‹EMetricSpace X›
instance [EMetricSpace X] : EMetricSpace (Multiplicative X) := ‹EMetricSpace X›

/-!
### Order dual

The distance on this type synonym is inherited without change.
-/


open OrderDual

section

variable [EDist X]

instance : EDist Xᵒᵈ := ‹EDist X›

@[simp]
theorem eDist_toDual (a b : X) : eDist (toDual a) (toDual b) = eDist a b :=
  rfl

@[simp]
theorem eDist_ofDual (a b : Xᵒᵈ) : eDist (ofDual a) (ofDual b) = eDist a b :=
  rfl

end

section

/-- The `WeakEMetric` space induced by pulling back a topology along an injective function. -/
abbrev WeakEMetricSpace.induced
  {α β : Type*} [n : TopologicalSpace β]
  {f : α → β} (hf : Function.Injective f) (m : WeakEMetricSpace β) :
    @WeakEMetricSpace α (TopologicalSpace.induced f n) :=
  letI := TopologicalSpace.induced f n
  { WeakPseudoEMetricSpace.IsInducing (f := f) {eq_induced := rfl} m.toWeakPseudoEMetricSpace with
    eq_of_eDist_eq_zero := fun h => hf (m.eq_of_eDist_eq_zero h) }

/-- `WeakEMetricSpace` instance on subsets of emetric spaces -/
instance {α : Type*} {p : α → Prop} [TopologicalSpace α] [WeakEMetricSpace α] :
    WeakEMetricSpace (Subtype p) :=
  WeakEMetricSpace.induced Subtype.coe_injective ‹_›

end

instance [TopologicalSpace X] [WeakPseudoEMetricSpace X] : WeakPseudoEMetricSpace Xᵒᵈ :=
  ‹WeakPseudoEMetricSpace X›
instance [TopologicalSpace X] [WeakEMetricSpace X] : WeakEMetricSpace Xᵒᵈ :=
  ‹WeakEMetricSpace X›
instance [PseudoEMetricSpace X] : PseudoEMetricSpace Xᵒᵈ :=
  ‹PseudoEMetricSpace X›
instance [EMetricSpace X] : EMetricSpace Xᵒᵈ :=
  ‹EMetricSpace X›
