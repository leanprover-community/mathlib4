/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Topology.UniformSpace.Basic
public import Mathlib.Topology.UniformSpace.OfFun
public import Mathlib.Data.ENNReal.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Set.Disjoint
import Mathlib.Init
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Map
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToAdditive
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.NhdsWithin

/-!
# Extended metric spaces

This file is devoted to the definition and study of `EMetricSpace`s, i.e., metric
spaces in which the distance is allowed to take the value ∞. This extended distance is
called `edist`, and takes values in `ℝ≥0∞`.

Many definitions and theorems expected on emetric spaces are already introduced on uniform spaces
and topological spaces. For example: open and closed sets, compactness, completeness, continuity and
uniform continuity.

The class `EMetricSpace` therefore extends `UniformSpace` (and `TopologicalSpace`).

Since a lot of elementary properties don't require `eq_of_edist_eq_zero` we start setting up the
theory of `PseudoEMetricSpace`, where we don't require `edist x y = 0 → x = y` and we specialize
to `EMetricSpace` at the end.
-/

@[expose] public section


assert_not_exists Nat.instLocallyFiniteOrder IsUniformEmbedding.prod TendstoUniformlyOnFilter

open Filter Set Topology

universe u v w

variable {α : Type u} {β : Type v} {X : Type*}

/-- Characterizing uniformities associated to a (generalized) distance function `D`
in terms of the elements of the uniformity. -/
theorem uniformity_dist_of_mem_uniformity [LT β] {U : Filter (α × α)} (z : β)
    (D : α → α → β) (H : ∀ s, s ∈ U ↔ ∃ ε > z, ∀ {a b : α}, D a b < ε → (a, b) ∈ s) :
    U = ⨅ ε > z, 𝓟 { p : α × α | D p.1 p.2 < ε } :=
  HasBasis.eq_biInf ⟨fun s => by simp only [H, subset_def, Prod.forall, mem_setOf]⟩

open scoped Uniformity Topology Filter NNReal ENNReal Pointwise

/-- `EDist α` means that `α` is equipped with an extended distance. -/
@[ext]
class EDist (α : Type*) where
  /-- Extended distance between two points -/
  edist : α → α → ℝ≥0∞

export EDist (edist)

/-- Creating a uniform space from an extended distance. -/
@[reducible] noncomputable def uniformSpaceOfEDist
    (edist : α → α → ℝ≥0∞) (edist_self : ∀ x : α, edist x x = 0)
    (edist_comm : ∀ x y : α, edist x y = edist y x)
    (edist_triangle : ∀ x y z : α, edist x z ≤ edist x y + edist y z) : UniformSpace α :=
  .ofFun edist edist_self edist_comm edist_triangle fun ε ε0 =>
    ⟨ε / 2, ENNReal.half_pos ε0.ne', fun _ h₁ _ h₂ =>
      (ENNReal.add_lt_add h₁ h₂).trans_eq (ENNReal.add_halves _)⟩

/-- Creating a uniform space from an extended distance. We assume that
there is a preexisting topology, for which the neighborhoods can be expressed using the distance,
and we make sure that the uniform space structure we construct has a topology which is defeq
to the original one. -/
@[reducible] noncomputable def uniformSpaceOfEDistOfHasBasis [TopologicalSpace α]
    (edist : α → α → ℝ≥0∞)
    (edist_self : ∀ x : α, edist x x = 0)
    (edist_comm : ∀ x y : α, edist x y = edist y x)
    (edist_triangle : ∀ x y z : α, edist x z ≤ edist x y + edist y z)
    (basis : ∀ x, (𝓝 x).HasBasis (fun c ↦ 0 < c) (fun c ↦ {y | edist x y < c})) :
    UniformSpace α :=
  .ofFunOfHasBasis edist edist_self edist_comm edist_triangle (fun ε ε0 =>
    ⟨ε / 2, ENNReal.half_pos ε0.ne', fun _ h₁ _ h₂ =>
      (ENNReal.add_lt_add h₁ h₂).trans_eq (ENNReal.add_halves _)⟩) basis

/-- A pseudo extended metric space is a type endowed with a `ℝ≥0∞`-valued distance `edist`
satisfying reflexivity `edist x x = 0`, commutativity `edist x y = edist y x`, and the triangle
inequality `edist x z ≤ edist x y + edist y z`.

Note that we do not require `edist x y = 0 → x = y`. See extended metric spaces (`EMetricSpace`) for
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
  edist_self : ∀ x : α, edist x x = 0
  edist_comm : ∀ x y : α, edist x y = edist y x
  edist_triangle : ∀ x y z : α, edist x z ≤ edist x y + edist y z
  toUniformSpace : UniformSpace α := uniformSpaceOfEDist edist edist_self edist_comm edist_triangle
  uniformity_edist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | edist p.1 p.2 < ε } := by rfl

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

variable [PseudoEMetricSpace α]

export PseudoEMetricSpace (edist_self edist_comm edist_triangle)

attribute [simp] edist_self

/-- Triangle inequality for the extended distance -/
theorem edist_triangle_left (x y z : α) : edist x y ≤ edist z x + edist z y := by
  rw [edist_comm z]; apply edist_triangle

theorem edist_triangle_right (x y z : α) : edist x y ≤ edist x z + edist y z := by
  rw [edist_comm y]; apply edist_triangle

theorem edist_congr_right {x y z : α} (h : edist x y = 0) : edist x z = edist y z := by
  apply le_antisymm
  · rw [← zero_add (edist y z), ← h]
    apply edist_triangle
  · rw [edist_comm] at h
    rw [← zero_add (edist x z), ← h]
    apply edist_triangle

theorem edist_congr_left {x y z : α} (h : edist x y = 0) : edist z x = edist z y := by
  rw [edist_comm z x, edist_comm z y]
  apply edist_congr_right h

-- new theorem
theorem edist_congr {w x y z : α} (hl : edist w x = 0) (hr : edist y z = 0) :
    edist w y = edist x z :=
  (edist_congr_right hl).trans (edist_congr_left hr)

theorem edist_triangle4 (x y z t : α) : edist x t ≤ edist x y + edist y z + edist z t := by
  grw [edist_triangle _ z, edist_triangle]

/-- Reformulation of the uniform structure in terms of the extended distance -/
theorem uniformity_pseudoedist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | edist p.1 p.2 < ε } :=
  PseudoEMetricSpace.uniformity_edist

theorem uniformSpace_edist :
    ‹PseudoEMetricSpace α›.toUniformSpace =
      uniformSpaceOfEDist edist edist_self edist_comm edist_triangle :=
  UniformSpace.ext uniformity_pseudoedist

theorem uniformity_basis_edist :
    (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε } :=
  (@uniformSpace_edist α _).symm ▸ UniformSpace.hasBasis_ofFun ⟨1, one_pos⟩ _ _ _ _ _

/-- Characterization of the elements of the uniformity in terms of the extended distance -/
theorem mem_uniformity_edist {s : Set (α × α)} :
    s ∈ 𝓤 α ↔ ∃ ε > 0, ∀ {a b : α}, edist a b < ε → (a, b) ∈ s :=
  uniformity_basis_edist.mem_uniformity_iff

/-- Given `f : β → ℝ≥0∞`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then `f i`-neighborhoods of the diagonal form a basis of `𝓤 α`.

For specific bases see `uniformity_basis_edist`, `uniformity_basis_edist'`,
`uniformity_basis_edist_nnreal`, and `uniformity_basis_edist_inv_nat`. -/
protected theorem EMetric.mk_uniformity_basis {β : Type*} {p : β → Prop} {f : β → ℝ≥0∞}
    (hf₀ : ∀ x, p x → 0 < f x) (hf : ∀ ε, 0 < ε → ∃ x, p x ∧ f x ≤ ε) :
    (𝓤 α).HasBasis p fun x => { p : α × α | edist p.1 p.2 < f x } := by
  refine ⟨fun s => uniformity_basis_edist.mem_iff.trans ?_⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases hf ε ε₀ with ⟨i, hi, H⟩
    exact ⟨i, hi, fun x hx => hε <| lt_of_lt_of_le hx.out H⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, H⟩

/-- Given `f : β → ℝ≥0∞`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then closed `f i`-neighborhoods of the diagonal form a basis of `𝓤 α`.

For specific bases see `uniformity_basis_edist_le` and `uniformity_basis_edist_le'`. -/
protected theorem EMetric.mk_uniformity_basis_le {β : Type*} {p : β → Prop} {f : β → ℝ≥0∞}
    (hf₀ : ∀ x, p x → 0 < f x) (hf : ∀ ε, 0 < ε → ∃ x, p x ∧ f x ≤ ε) :
    (𝓤 α).HasBasis p fun x => { p : α × α | edist p.1 p.2 ≤ f x } := by
  refine ⟨fun s => uniformity_basis_edist.mem_iff.trans ?_⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases exists_between ε₀ with ⟨ε', hε'⟩
    rcases hf ε' hε'.1 with ⟨i, hi, H⟩
    exact ⟨i, hi, fun x hx => hε <| lt_of_le_of_lt (le_trans hx.out H) hε'.2⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, fun x hx => H (le_of_lt hx.out)⟩

theorem uniformity_basis_edist_le :
    (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 ≤ ε } :=
  EMetric.mk_uniformity_basis_le (fun _ => id) fun ε ε₀ => ⟨ε, ε₀, le_refl ε⟩

theorem uniformity_basis_edist' (ε' : ℝ≥0∞) (hε' : 0 < ε') :
    (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => ε ∈ Ioo 0 ε') fun ε => { p : α × α | edist p.1 p.2 < ε } :=
  EMetric.mk_uniformity_basis (fun _ => And.left) fun ε ε₀ =>
    let ⟨δ, hδ⟩ := exists_between hε'
    ⟨min ε δ, ⟨lt_min ε₀ hδ.1, lt_of_le_of_lt (min_le_right _ _) hδ.2⟩, min_le_left _ _⟩

theorem uniformity_basis_edist_le' (ε' : ℝ≥0∞) (hε' : 0 < ε') :
    (𝓤 α).HasBasis (fun ε : ℝ≥0∞ => ε ∈ Ioo 0 ε') fun ε => { p : α × α | edist p.1 p.2 ≤ ε } :=
  EMetric.mk_uniformity_basis_le (fun _ => And.left) fun ε ε₀ =>
    let ⟨δ, hδ⟩ := exists_between hε'
    ⟨min ε δ, ⟨lt_min ε₀ hδ.1, lt_of_le_of_lt (min_le_right _ _) hδ.2⟩, min_le_left _ _⟩

theorem uniformity_basis_edist_nnreal :
    (𝓤 α).HasBasis (fun ε : ℝ≥0 => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε } :=
  EMetric.mk_uniformity_basis (fun _ => ENNReal.coe_pos.2) fun _ε ε₀ =>
    let ⟨δ, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ε₀
    ⟨δ, ENNReal.coe_pos.1 hδ.1, le_of_lt hδ.2⟩

theorem uniformity_basis_edist_nnreal_le :
    (𝓤 α).HasBasis (fun ε : ℝ≥0 => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 ≤ ε } :=
  EMetric.mk_uniformity_basis_le (fun _ => ENNReal.coe_pos.2) fun _ε ε₀ =>
    let ⟨δ, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ε₀
    ⟨δ, ENNReal.coe_pos.1 hδ.1, le_of_lt hδ.2⟩

theorem uniformity_basis_edist_inv_nat :
    (𝓤 α).HasBasis (fun _ => True) fun n : ℕ => { p : α × α | edist p.1 p.2 < (↑n)⁻¹ } :=
  EMetric.mk_uniformity_basis (fun n _ ↦ ENNReal.inv_pos.2 <| ENNReal.natCast_ne_top n) fun _ε ε₀ ↦
    let ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (ne_of_gt ε₀)
    ⟨n, trivial, le_of_lt hn⟩

theorem uniformity_basis_edist_inv_two_pow :
    (𝓤 α).HasBasis (fun _ => True) fun n : ℕ => { p : α × α | edist p.1 p.2 < 2⁻¹ ^ n } :=
  EMetric.mk_uniformity_basis (fun _ _ ↦ ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _)
    fun _ε ε₀ ↦
    let ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt (ne_of_gt ε₀)
    ⟨n, trivial, le_of_lt hn⟩

/-- Fixed size neighborhoods of the diagonal belong to the uniform structure -/
theorem edist_mem_uniformity {ε : ℝ≥0∞} (ε0 : 0 < ε) : { p : α × α | edist p.1 p.2 < ε } ∈ 𝓤 α :=
  mem_uniformity_edist.2 ⟨ε, ε0, id⟩

namespace EMetric

instance (priority := 900) instIsCountablyGeneratedUniformity : IsCountablyGenerated (𝓤 α) :=
  isCountablyGenerated_of_seq ⟨_, uniformity_basis_edist_inv_nat.eq_iInf⟩

/-- ε-δ characterization of uniform continuity on a set for pseudoemetric spaces -/
theorem uniformContinuousOn_iff [PseudoEMetricSpace β] {f : α → β} {s : Set α} :
    UniformContinuousOn f s ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {a}, a ∈ s → ∀ {b}, b ∈ s → edist a b < δ → edist (f a) (f b) < ε :=
  uniformity_basis_edist.uniformContinuousOn_iff uniformity_basis_edist

/-- ε-δ characterization of uniform continuity on pseudoemetric spaces -/
theorem uniformContinuous_iff [PseudoEMetricSpace β] {f : α → β} :
    UniformContinuous f ↔ ∀ ε > 0, ∃ δ > 0, ∀ {a b : α}, edist a b < δ → edist (f a) (f b) < ε :=
  uniformity_basis_edist.uniformContinuous_iff uniformity_basis_edist

end EMetric

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
  edist := @edist _ m.toEDist
  edist_self := edist_self
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := U
  uniformity_edist := H.trans (@PseudoEMetricSpace.uniformity_edist α _)

/-- The extended pseudometric induced by a function taking values in a pseudoemetric space.
See note [reducible non-instances]. -/
abbrev PseudoEMetricSpace.induced {α β} (f : α → β) (m : PseudoEMetricSpace β) :
    PseudoEMetricSpace α where
  edist x y := edist (f x) (f y)
  edist_self _ := edist_self _
  edist_comm _ _ := edist_comm _ _
  edist_triangle _ _ _ := edist_triangle _ _ _
  toUniformSpace := UniformSpace.comap f m.toUniformSpace
  uniformity_edist := (uniformity_basis_edist.comap (Prod.map f f)).eq_biInf

/-- Pseudoemetric space instance on subsets of pseudoemetric spaces -/
instance {α : Type*} {p : α → Prop} [PseudoEMetricSpace α] : PseudoEMetricSpace (Subtype p) :=
  PseudoEMetricSpace.induced Subtype.val ‹_›

/-- The extended pseudodistance on a subset of a pseudoemetric space is the restriction of
the original pseudodistance, by definition. -/
theorem Subtype.edist_eq {p : α → Prop} (x y : Subtype p) : edist x y = edist (x : α) y := rfl

/-- The extended pseudodistance on a subtype of a pseudoemetric space is the restriction of
the original pseudodistance, by definition. -/
@[simp]
theorem Subtype.edist_mk_mk {p : α → Prop} {x y : α} (hx : p x) (hy : p y) :
    edist (⟨x, hx⟩ : Subtype p) ⟨y, hy⟩ = edist x y :=
  rfl

/-- Consider an extended distance on a topological space, for which the neighborhoods can be
expressed in terms of the distance. Then we define the emetric space structure associated to this
distance, with a topology defeq to the initial one. -/
@[reducible] noncomputable def PseudoEMetricSpace.ofEDistOfTopology {α : Type*} [TopologicalSpace α]
    (d : α → α → ℝ≥0∞) (h_self : ∀ x, d x x = 0) (h_comm : ∀ x y, d x y = d y x)
    (h_triangle : ∀ x y z, d x z ≤ d x y + d y z)
    (h_basis : ∀ x, (𝓝 x).HasBasis (fun c ↦ 0 < c) (fun c ↦ {y | d x y < c})) :
    PseudoEMetricSpace α where
  edist := d
  edist_self := h_self
  edist_comm := h_comm
  edist_triangle := h_triangle
  toUniformSpace := uniformSpaceOfEDistOfHasBasis d h_self h_comm h_triangle h_basis
  uniformity_edist := rfl

@[deprecated (since := "2026-01-08")]
alias PseudoEmetricSpace.ofEdistOfTopology := PseudoEMetricSpace.ofEDistOfTopology

namespace MulOpposite

/-- Pseudoemetric space instance on the multiplicative opposite of a pseudoemetric space. -/
@[to_additive
/-- Pseudoemetric space instance on the additive opposite of a pseudoemetric space. -/]
instance {α : Type*} [PseudoEMetricSpace α] : PseudoEMetricSpace αᵐᵒᵖ :=
  PseudoEMetricSpace.induced unop ‹_›

@[to_additive]
theorem edist_unop (x y : αᵐᵒᵖ) : edist (unop x) (unop y) = edist x y := rfl

@[to_additive]
theorem edist_op (x y : α) : edist (op x) (op y) = edist x y := rfl

end MulOpposite

section ULift

instance : PseudoEMetricSpace (ULift α) := PseudoEMetricSpace.induced ULift.down ‹_›

theorem ULift.edist_eq (x y : ULift α) : edist x y = edist x.down y.down := rfl

@[simp]
theorem ULift.edist_up_up (x y : α) : edist (ULift.up x) (ULift.up y) = edist x y := rfl

end ULift

/-- The product of two pseudoemetric spaces, with the max distance, is an extended
pseudometric spaces. We make sure that the uniform structure thus constructed is the one
corresponding to the product of uniform spaces, to avoid diamond problems. -/
instance Prod.pseudoEMetricSpaceMax [PseudoEMetricSpace β] :
    PseudoEMetricSpace (α × β) where
  edist x y := edist x.1 y.1 ⊔ edist x.2 y.2
  edist_self x := by simp
  edist_comm x y := by simp [edist_comm]
  edist_triangle _ _ _ :=
    max_le (le_trans (edist_triangle _ _ _) (add_le_add (le_max_left _ _) (le_max_left _ _)))
      (le_trans (edist_triangle _ _ _) (add_le_add (le_max_right _ _) (le_max_right _ _)))
  uniformity_edist := uniformity_prod.trans <| by
    simp [PseudoEMetricSpace.uniformity_edist, ← iInf_inf_eq, setOf_and]
  toUniformSpace := inferInstance

theorem Prod.edist_eq [PseudoEMetricSpace β] (x y : α × β) :
    edist x y = max (edist x.1 y.1) (edist x.2 y.2) :=
  rfl

namespace Metric

variable {x y z : α} {ε ε₁ ε₂ : ℝ≥0∞} {s t : Set α}

/-- `Metric.eball x ε` is the set of all points `y` with `edist y x < ε` -/
def eball (x : α) (ε : ℝ≥0∞) : Set α :=
  {y | edist y x < ε}

@[simp] theorem mem_eball : y ∈ eball x ε ↔ edist y x < ε := Iff.rfl

theorem mem_eball' : y ∈ eball x ε ↔ edist x y < ε := by rw [edist_comm, mem_eball]

/-- `Metric.closedEBall x ε` is the set of all points `y` with `edist y x ≤ ε` -/
def closedEBall (x : α) (ε : ℝ≥0∞) :=
  { y | edist y x ≤ ε }

@[simp] theorem mem_closedEBall : y ∈ closedEBall x ε ↔ edist y x ≤ ε := Iff.rfl

theorem mem_closedEBall' : y ∈ closedEBall x ε ↔ edist x y ≤ ε := by
  rw [edist_comm, mem_closedEBall]

@[simp]
theorem closedEBall_top (x : α) : closedEBall x ∞ = univ :=
  eq_univ_of_forall fun _ => mem_setOf.2 le_top

theorem eball_subset_closedEBall : eball x ε ⊆ closedEBall x ε := fun _ h => le_of_lt h.out

theorem pos_of_mem_eball (hy : y ∈ eball x ε) : 0 < ε :=
  lt_of_le_of_lt (zero_le _) hy

theorem mem_eball_self (h : 0 < ε) : x ∈ eball x ε := by
  rwa [mem_eball, edist_self]

theorem mem_closedEBall_self : x ∈ closedEBall x ε := by
  rw [mem_closedEBall, edist_self]; apply zero_le

theorem mem_eball_comm : x ∈ eball y ε ↔ y ∈ eball x ε := by rw [mem_eball', mem_eball]

theorem mem_closedEBall_comm : x ∈ closedEBall y ε ↔ y ∈ closedEBall x ε := by
  rw [mem_closedEBall', mem_closedEBall]

@[gcongr]
theorem eball_subset_eball (h : ε₁ ≤ ε₂) : eball x ε₁ ⊆ eball x ε₂ := fun _y (yx : _ < ε₁) =>
  lt_of_lt_of_le yx h

@[gcongr]
theorem closedEBall_subset_closedEBall (h : ε₁ ≤ ε₂) : closedEBall x ε₁ ⊆ closedEBall x ε₂ :=
  fun _y (yx : _ ≤ ε₁) => le_trans yx h

theorem eball_disjoint (h : ε₁ + ε₂ ≤ edist x y) : Disjoint (eball x ε₁) (eball y ε₂) :=
  Set.disjoint_left.mpr fun z h₁ h₂ =>
    (edist_triangle_left x y z).not_gt <| (ENNReal.add_lt_add h₁ h₂).trans_le h

theorem eball_subset (h : edist x y + ε₁ ≤ ε₂) (h' : edist x y ≠ ∞) : eball x ε₁ ⊆ eball y ε₂ :=
  fun z zx =>
  calc
    edist z y ≤ edist z x + edist x y := edist_triangle _ _ _
    _ = edist x y + edist z x := add_comm _ _
    _ < edist x y + ε₁ := ENNReal.add_lt_add_left h' zx
    _ ≤ ε₂ := h

theorem exists_eball_subset_eball (h : y ∈ eball x ε) : ∃ ε' > 0, eball y ε' ⊆ eball x ε := by
  have : 0 < ε - edist y x := by simpa using h
  refine ⟨ε - edist y x, this, eball_subset ?_ (ne_top_of_lt h)⟩
  exact (add_tsub_cancel_of_le (mem_eball.mp h).le).le

theorem eball_eq_empty_iff : eball x ε = ∅ ↔ ε = 0 :=
  eq_empty_iff_forall_notMem.trans
    ⟨fun h => le_bot_iff.1 (le_of_not_gt fun ε0 => h _ (mem_eball_self ε0)), fun ε0 _ h =>
      not_lt_of_ge (le_of_eq ε0) (pos_of_mem_eball h)⟩

theorem ordConnected_setOf_closedEBall_subset (x : α) (s : Set α) :
    OrdConnected { r | closedEBall x r ⊆ s } :=
  ⟨fun _ _ _ h₁ _ h₂ => (closedEBall_subset_closedEBall h₂.2).trans h₁⟩

theorem ordConnected_setOf_eball_subset (x : α) (s : Set α) : OrdConnected { r | eball x r ⊆ s } :=
  ⟨fun _ _ _ h₁ _ h₂ => (eball_subset_eball h₂.2).trans h₁⟩

/-- Relation “two points are at a finite edistance” is an equivalence relation. -/
@[implicit_reducible]
def edistLtTopSetoid : Setoid α where
  r x y := edist x y < ⊤
  iseqv :=
    { refl x := by rw [edist_self]; exact ENNReal.coe_lt_top
      symm h := by rwa [edist_comm]
      trans hxy hyz := lt_of_le_of_lt (edist_triangle _ _ _) (ENNReal.add_lt_top.2 ⟨hxy, hyz⟩) }

@[simp]
theorem eball_zero : eball x 0 = ∅ := by rw [eball_eq_empty_iff]

theorem nhds_basis_eball : (𝓝 x).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) (eball x) :=
  nhds_basis_uniformity uniformity_basis_edist

theorem nhdsWithin_basis_eball : (𝓝[s] x).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => eball x ε ∩ s :=
  nhdsWithin_hasBasis nhds_basis_eball s

theorem nhds_basis_closedEBall : (𝓝 x).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) (closedEBall x) :=
  nhds_basis_uniformity uniformity_basis_edist_le

theorem nhdsWithin_basis_closedEBall :
    (𝓝[s] x).HasBasis (fun ε : ℝ≥0∞ => 0 < ε) fun ε => closedEBall x ε ∩ s :=
  nhdsWithin_hasBasis nhds_basis_closedEBall s

end Metric

namespace EMetric
variable {x : α} {ε : ℝ≥0∞} {s t : Set α}

open Metric

theorem nhds_eq : 𝓝 x = ⨅ ε > 0, 𝓟 (eball x ε) :=
  nhds_basis_eball.eq_biInf

theorem mem_nhds_iff : s ∈ 𝓝 x ↔ ∃ ε > 0, eball x ε ⊆ s :=
  nhds_basis_eball.mem_iff

theorem mem_nhdsWithin_iff : s ∈ 𝓝[t] x ↔ ∃ ε > 0, eball x ε ∩ t ⊆ s :=
  nhdsWithin_basis_eball.mem_iff

theorem isOpen_iff : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, eball x ε ⊆ s := by
  simp [isOpen_iff_nhds, mem_nhds_iff]

/-- ε-characterization of the closure in pseudoemetric spaces -/
theorem mem_closure_iff : x ∈ closure s ↔ ∀ ε > 0, ∃ y ∈ s, edist x y < ε :=
  (mem_closure_iff_nhds_basis nhds_basis_eball).trans <| by simp only [mem_eball, edist_comm x]

lemma dense_iff : Dense s ↔ ∀ (x : α), ∀ r > 0, (eball x r ∩ s).Nonempty :=
  forall_congr' fun x => by
    simp only [mem_closure_iff, Set.Nonempty, mem_inter_iff, and_comm, mem_eball']

theorem tendsto_nhds {f : Filter β} {u : β → α} {a : α} :
    Tendsto u f (𝓝 a) ↔ ∀ ε > 0, ∀ᶠ x in f, edist (u x) a < ε :=
  nhds_basis_eball.tendsto_right_iff

theorem tendsto_atTop [Nonempty β] [SemilatticeSup β] {u : β → α} {a : α} :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, edist (u n) a < ε :=
  (atTop_basis.tendsto_iff nhds_basis_eball).trans <| by
    simp only [true_and, mem_Ici, mem_eball]

variable [PseudoEMetricSpace β] {f : α → β}

theorem tendsto_nhdsWithin_nhdsWithin {t : Set β} {a b} :
    Tendsto f (𝓝[s] a) (𝓝[t] b) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ ⦃x⦄, x ∈ s → edist x a < δ → f x ∈ t ∧ edist (f x) b < ε :=
  (nhdsWithin_basis_eball.tendsto_iff nhdsWithin_basis_eball).trans <|
    forall₂_congr fun ε _ => exists_congr fun δ => and_congr_right fun _ =>
      forall_congr' fun x => by simp; tauto

theorem tendsto_nhdsWithin_nhds {a b} :
    Tendsto f (𝓝[s] a) (𝓝 b) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {x : α}, x ∈ s → edist x a < δ → edist (f x) b < ε := by
  rw [← nhdsWithin_univ b, tendsto_nhdsWithin_nhdsWithin]
  simp only [mem_univ, true_and]

theorem tendsto_nhds_nhds {a b} :
    Tendsto f (𝓝 a) (𝓝 b) ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃x⦄, edist x a < δ → edist (f x) b < ε :=
  nhds_basis_eball.tendsto_iff nhds_basis_eball

end EMetric

namespace Metric
variable {x : α} {ε : ℝ≥0∞} {s t : Set α}

@[simp] theorem isOpen_eball : IsOpen (eball x ε) :=
  EMetric.isOpen_iff.2 fun _ => exists_eball_subset_eball

theorem isClosed_eball_top : IsClosed (eball x ⊤) :=
  isOpen_compl_iff.1 <| EMetric.isOpen_iff.2 fun _y hy =>
    ⟨⊤, ENNReal.coe_lt_top, fun _z hzy hzx =>
      hy (edistLtTopSetoid.trans (edistLtTopSetoid.symm hzy) hzx)⟩

theorem eball_mem_nhds (x : α) {ε : ℝ≥0∞} (ε0 : 0 < ε) : eball x ε ∈ 𝓝 x :=
  isOpen_eball.mem_nhds (mem_eball_self ε0)

theorem closedEBall_mem_nhds (x : α) {ε : ℝ≥0∞} (ε0 : 0 < ε) : closedEBall x ε ∈ 𝓝 x :=
  mem_of_superset (eball_mem_nhds x ε0) eball_subset_closedEBall

theorem eball_prod_same [PseudoEMetricSpace β] (x : α) (y : β) (r : ℝ≥0∞) :
    eball x r ×ˢ eball y r = eball (x, y) r :=
  ext fun z => by simp [Prod.edist_eq]

theorem closedEBall_prod_same [PseudoEMetricSpace β] (x : α) (y : β) (r : ℝ≥0∞) :
    closedEBall x r ×ˢ closedEBall y r = closedEBall (x, y) r :=
  ext fun z => by simp [Prod.edist_eq]

end Metric

namespace EMetric

open Metric

@[deprecated (since := "2026-01-24")] alias ball := eball
@[deprecated (since := "2026-01-24")] alias mem_ball := mem_eball
@[deprecated (since := "2026-01-24")] alias mem_ball' := mem_eball'
@[deprecated (since := "2026-01-24")] alias closedBall := closedEBall
@[deprecated (since := "2026-01-24")] alias mem_closedBall := mem_closedEBall
@[deprecated (since := "2026-01-24")] alias mem_closedBall' := mem_closedEBall'
@[deprecated (since := "2026-01-24")] alias closedBall_top := closedEBall_top
@[deprecated (since := "2026-01-24")] alias ball_subset_closedBall := eball_subset_closedEBall
@[deprecated (since := "2026-01-24")] alias pos_of_mem_ball := pos_of_mem_eball
@[deprecated (since := "2026-01-24")] alias mem_ball_self := mem_eball_self
@[deprecated (since := "2026-01-24")] alias mem_closedBall_self := mem_closedEBall_self
@[deprecated (since := "2026-01-24")] alias mem_ball_comm := mem_eball_comm
@[deprecated (since := "2026-01-24")] alias mem_closedBall_comm := mem_closedEBall_comm
@[deprecated (since := "2026-01-24")] alias ball_subset_ball := eball_subset_eball

@[deprecated (since := "2026-01-24")]
alias closedBall_subset_closedBall := closedEBall_subset_closedEBall

@[deprecated (since := "2026-01-24")] alias ball_disjoint := eball_disjoint
@[deprecated (since := "2026-01-24")] alias ball_subset := eball_subset
@[deprecated (since := "2026-01-24")] alias exists_ball_subset_ball := exists_eball_subset_eball
@[deprecated (since := "2026-01-24")] alias ball_eq_empty_iff := eball_eq_empty_iff

@[deprecated (since := "2026-01-24")]
alias ordConnected_setOf_closedBall_subset := ordConnected_setOf_closedEBall_subset

@[deprecated (since := "2026-01-24")]
alias ordConnected_setOf_ball_subset := ordConnected_setOf_eball_subset

@[deprecated (since := "2026-01-24")] alias edistLtTopSetoid := edistLtTopSetoid
@[deprecated (since := "2026-01-24")] alias ball_zero := eball_zero

@[deprecated (since := "2026-01-24")]
protected alias nhds_basis_eball := nhds_basis_eball

@[deprecated (since := "2026-01-24")] alias nhdsWithin_basis_eball := nhdsWithin_basis_eball
@[deprecated (since := "2026-01-24")] alias nhds_basis_closed_eball := nhds_basis_closedEBall

@[deprecated (since := "2026-01-24")]
alias nhdsWithin_basis_closed_eball := nhdsWithin_basis_closedEBall

@[deprecated (since := "2026-01-24")] alias isOpen_ball := isOpen_eball
@[deprecated (since := "2026-01-24")] alias isClosed_ball_top := isClosed_eball_top
@[deprecated (since := "2026-01-24")] alias ball_mem_nhds := eball_mem_nhds
@[deprecated (since := "2026-01-24")] alias closedBall_mem_nhds := closedEBall_mem_nhds
@[deprecated (since := "2026-01-24")] alias ball_prod_same := eball_prod_same
@[deprecated (since := "2026-01-24")] alias closedBall_prod_same := closedEBall_prod_same

end EMetric

namespace Subtype

open Metric

@[simp]
theorem preimage_eball {p : α → Prop} (a : {a // p a}) (r : ℝ≥0∞) :
    Subtype.val ⁻¹' (eball a.1 r) = eball a r :=
  rfl

@[deprecated (since := "2026-01-24")]
alias preimage_emetricBall := preimage_eball

@[simp]
theorem preimage_closedEBall {p : α → Prop} (a : {a // p a}) (r : ℝ≥0∞) :
    Subtype.val ⁻¹' (closedEBall a.1 r) = closedEBall a r :=
  rfl

@[deprecated (since := "2026-01-24")]
alias preimage_emetricClosedBall := preimage_closedEBall

@[simp]
theorem image_eball {p : α → Prop} (a : {a // p a}) (r : ℝ≥0∞) :
    Subtype.val '' (eball a r) = eball a.1 r ∩ {a | p a} := by
  rw [← preimage_eball, image_preimage_eq_inter_range, range_val_subtype]

@[deprecated (since := "2026-01-24")]
alias image_emetricBall := image_eball

@[simp]
theorem image_closedEBall {p : α → Prop} (a : {a // p a}) (r : ℝ≥0∞) :
    Subtype.val '' (closedEBall a r) = closedEBall a.1 r ∩ {a | p a} := by
  rw [← preimage_closedEBall, image_preimage_eq_inter_range, range_val_subtype]

@[deprecated (since := "2026-01-24")]
alias image_emetricClosedBall := image_closedEBall

end Subtype

/-- An extended metric space is a type endowed with a `ℝ≥0∞`-valued distance `edist` satisfying
`edist x y = 0 ↔ x = y`, commutativity `edist x y = edist y x`, and the triangle inequality
`edist x z ≤ edist x y + edist y z`.

See pseudo extended metric spaces (`PseudoEMetricSpace`) for the similar class with the
`edist x y = 0 ↔ x = y` assumption weakened to `edist x x = 0`.

Any extended metric space is a T1 topological space and a uniform space (see `TopologicalSpace`,
`T1Space`, `UniformSpace`), where the topology and uniformity come from the metric.

We make the uniformity/topology part of the data instead of deriving it from the metric.
This e.g. ensures that we do not get a diamond when doing
`[EMetricSpace α] [EMetricSpace β] : TopologicalSpace (α × β)`:
The product metric and product topology agree, but not definitionally so.
See Note [forgetful inheritance]. -/
class EMetricSpace (α : Type u) : Type u extends PseudoEMetricSpace α where
  eq_of_edist_eq_zero : ∀ {x y : α}, edist x y = 0 → x = y

@[ext]
protected theorem EMetricSpace.ext
    {α : Type*} {m m' : EMetricSpace α} (h : m.toEDist = m'.toEDist) : m = m' := by
  cases m
  cases m'
  congr
  ext1
  assumption

variable {γ : Type w} [EMetricSpace γ]

export EMetricSpace (eq_of_edist_eq_zero)

/-- Characterize the equality of points by the vanishing of their extended distance -/
@[simp]
theorem edist_eq_zero {x y : γ} : edist x y = 0 ↔ x = y :=
  ⟨eq_of_edist_eq_zero, fun h => h ▸ edist_self _⟩

@[simp]
theorem zero_eq_edist {x y : γ} : 0 = edist x y ↔ x = y := eq_comm.trans edist_eq_zero

theorem edist_le_zero {x y : γ} : edist x y ≤ 0 ↔ x = y :=
  nonpos_iff_eq_zero.trans edist_eq_zero

@[simp]
theorem edist_pos {x y : γ} : 0 < edist x y ↔ x ≠ y := by simp [← not_le]

@[simp] lemma Metric.closedEBall_zero (x : γ) : closedEBall x 0 = {x} := by ext; simp

@[deprecated (since := "2026-01-24")]
alias EMetric.closedBall_zero := Metric.closedEBall_zero

/-- Two points coincide if their distance is `< ε` for all positive ε -/
theorem eq_of_forall_edist_le {x y : γ} (h : ∀ ε > 0, edist x y ≤ ε) : x = y :=
  eq_of_edist_eq_zero (eq_of_le_of_forall_lt_imp_le_of_dense bot_le h)

/-- Auxiliary function to replace the uniformity on an emetric space with
a uniformity which is equal to the original one, but maybe not defeq.
This is useful if one wants to construct an emetric space with a
specified uniformity. See Note [forgetful inheritance] explaining why having definitionally
the right uniformity is often important.
See note [reducible non-instances].
-/
abbrev EMetricSpace.replaceUniformity {γ} [U : UniformSpace γ] (m : EMetricSpace γ)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : EMetricSpace γ where
  edist := @edist _ m.toEDist
  edist_self := edist_self
  eq_of_edist_eq_zero := @eq_of_edist_eq_zero _ _
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := U
  uniformity_edist := H.trans (@PseudoEMetricSpace.uniformity_edist γ _)

/-- Auxiliary function to replace the topology on an emetric space with
a topology which is equal to the original one, but maybe not defeq.
This is useful if one wants to construct an emetric space with a
specified topology. See Note [forgetful inheritance] explaining why having definitionally
the right topology is often important.
See note [reducible non-instances].
-/
abbrev EMetricSpace.replaceTopology {γ} [T : TopologicalSpace γ] (m : EMetricSpace γ)
    (H : T = m.toUniformSpace.toTopologicalSpace) : EMetricSpace γ where
  edist := @edist _ m.toEDist
  edist_self := edist_self
  eq_of_edist_eq_zero := @eq_of_edist_eq_zero _ _
  edist_comm := edist_comm
  edist_triangle := edist_triangle
  toUniformSpace := m.toUniformSpace.replaceTopology H
  uniformity_edist := PseudoEMetricSpace.uniformity_edist

/-- The extended metric induced by an injective function taking values in an emetric space.
See Note [reducible non-instances]. -/
abbrev EMetricSpace.induced {γ β} (f : γ → β) (hf : Function.Injective f) (m : EMetricSpace β) :
    EMetricSpace γ :=
  { PseudoEMetricSpace.induced f m.toPseudoEMetricSpace with
    eq_of_edist_eq_zero := fun h => hf (edist_eq_zero.1 h) }

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
theorem uniformity_edist : 𝓤 γ = ⨅ ε > 0, 𝓟 { p : γ × γ | edist p.1 p.2 < ε } :=
  PseudoEMetricSpace.uniformity_edist

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
theorem edist_ofMul (a b : X) : edist (ofMul a) (ofMul b) = edist a b :=
  rfl

@[simp]
theorem edist_ofAdd (a b : X) : edist (ofAdd a) (ofAdd b) = edist a b :=
  rfl

@[simp]
theorem edist_toMul (a b : Additive X) : edist a.toMul b.toMul = edist a b :=
  rfl

@[simp]
theorem edist_toAdd (a b : Multiplicative X) : edist a.toAdd b.toAdd = edist a b :=
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
theorem edist_toDual (a b : X) : edist (toDual a) (toDual b) = edist a b :=
  rfl

@[simp]
theorem edist_ofDual (a b : Xᵒᵈ) : edist (ofDual a) (ofDual b) = edist a b :=
  rfl

end

instance [PseudoEMetricSpace X] : PseudoEMetricSpace Xᵒᵈ := ‹PseudoEMetricSpace X›
instance [EMetricSpace X] : EMetricSpace Xᵒᵈ := ‹EMetricSpace X›
