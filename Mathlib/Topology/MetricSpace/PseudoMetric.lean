/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.Bornology.Constructions

/-!
## Pseudo-metric spaces
TODO insert proper docstring
definition of pseudometric space, distance, extended distance and basic API
noteworthy result: triangle ineq for polygons
ball, closed ball, sphere
noteworthy: forall_of_forall_mem_Ball, forall_of_forall_mem_closedBall

-/
-- TODO: go over copyright, author, imports, variables etc.


open Set Filter TopologicalSpace Bornology
open scoped BigOperators ENNReal NNReal Uniformity Topology

universe u v w

variable {α : Type u} {β : Type v} {X ι : Type*}

/-- Construct a uniform structure from a distance function and metric space axioms -/
def UniformSpace.ofDist (dist : α → α → ℝ) (dist_self : ∀ x : α, dist x x = 0)
    (dist_comm : ∀ x y : α, dist x y = dist y x)
    (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z) : UniformSpace α :=
  .ofFun dist dist_self dist_comm dist_triangle fun ε ε0 =>
    ⟨ε / 2, half_pos ε0, fun _x hx _y hy => add_halves ε ▸ add_lt_add hx hy⟩
#align uniform_space_of_dist UniformSpace.ofDist

-- porting note: dropped the `dist_self` argument
/-- Construct a bornology from a distance function and metric space axioms. -/
@[reducible]
def Bornology.ofDist {α : Type*} (dist : α → α → ℝ) (dist_comm : ∀ x y, dist x y = dist y x)
    (dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z) : Bornology α :=
  Bornology.ofBounded { s : Set α | ∃ C, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → dist x y ≤ C }
    ⟨0, fun x hx y => hx.elim⟩ (fun s ⟨c, hc⟩ t h => ⟨c, fun x hx y hy => hc (h hx) (h hy)⟩)
    (fun s hs t ht => by
      rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
      · rwa [empty_union]
      rcases t.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
      · rwa [union_empty]
      rsuffices ⟨C, hC⟩ : ∃ C, ∀ z ∈ s ∪ t, dist x z ≤ C
      · refine ⟨C + C, fun a ha b hb => (dist_triangle a x b).trans ?_⟩
        simpa only [dist_comm] using add_le_add (hC _ ha) (hC _ hb)
      rcases hs with ⟨Cs, hs⟩; rcases ht with ⟨Ct, ht⟩
      refine ⟨max Cs (dist x y + Ct), fun z hz => hz.elim
        (fun hz => (hs hx hz).trans (le_max_left _ _))
        (fun hz => (dist_triangle x y z).trans <|
          (add_le_add le_rfl (ht hy hz)).trans (le_max_right _ _))⟩)
    fun z => ⟨dist z z, forall_eq.2 <| forall_eq.2 le_rfl⟩
#align bornology.of_dist Bornology.ofDistₓ

/-- The distance function (given an ambient metric space on `α`), which returns
  a nonnegative real number `dist x y` given `x y : α`. -/
@[ext]
class Dist (α : Type*) where
  dist : α → α → ℝ
#align has_dist Dist

export Dist (dist)

-- the uniform structure and the emetric space structure are embedded in the metric space structure
-- to avoid instance diamond issues. See Note [forgetful inheritance].
/-- This is an internal lemma used inside the default of `PseudoMetricSpace.edist`. -/
private theorem dist_nonneg' {α} {x y : α} (dist : α → α → ℝ)
    (dist_self : ∀ x : α, dist x x = 0) (dist_comm : ∀ x y : α, dist x y = dist y x)
    (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z) : 0 ≤ dist x y :=
  have : 0 ≤ 2 * dist x y :=
    calc 0 = dist x x := (dist_self _).symm
    _ ≤ dist x y + dist y x := dist_triangle _ _ _
    _ = 2 * dist x y := by rw [two_mul, dist_comm]
  nonneg_of_mul_nonneg_right this two_pos

#noalign pseudo_metric_space.edist_dist_tac -- porting note: todo: restore

/-- Pseudo metric and Metric spaces

A pseudo metric space is endowed with a distance for which the requirement `d(x,y)=0 → x = y` might
not hold. A metric space is a pseudo metric space such that `d(x,y)=0 → x = y`.
Each pseudo metric space induces a canonical `UniformSpace` and hence a canonical
`TopologicalSpace` This is enforced in the type class definition, by extending the `UniformSpace`
structure. When instantiating a `PseudoMetricSpace` structure, the uniformity fields are not
necessary, they will be filled in by default. In the same way, each (pseudo) metric space induces a
(pseudo) emetric space structure. It is included in the structure, but filled in by default.
-/
class PseudoMetricSpace (α : Type u) extends Dist α : Type u where
  dist_self : ∀ x : α, dist x x = 0
  dist_comm : ∀ x y : α, dist x y = dist y x
  dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z
  edist : α → α → ℝ≥0∞ := fun x y => ENNReal.some ⟨dist x y, dist_nonneg' _ ‹_› ‹_› ‹_›⟩
  edist_dist : ∀ x y : α, edist x y = ENNReal.ofReal (dist x y) -- porting note: todo: add := by _
  toUniformSpace : UniformSpace α := .ofDist dist dist_self dist_comm dist_triangle
  uniformity_dist : 𝓤 α = ⨅ ε > 0, 𝓟 { p : α × α | dist p.1 p.2 < ε } := by intros; rfl
  toBornology : Bornology α := Bornology.ofDist dist dist_comm dist_triangle
  cobounded_sets : (Bornology.cobounded α).sets =
    { s | ∃ C : ℝ, ∀ x ∈ sᶜ, ∀ y ∈ sᶜ, dist x y ≤ C } := by intros; rfl
#align pseudo_metric_space PseudoMetricSpace

/-- Two pseudo metric space structures with the same distance function coincide. -/
@[ext]
theorem PseudoMetricSpace.ext {α : Type*} {m m' : PseudoMetricSpace α}
    (h : m.toDist = m'.toDist) : m = m' := by
  cases' m with d _ _ _ ed hed U hU B hB
  cases' m' with d' _ _ _ ed' hed' U' hU' B' hB'
  obtain rfl : d = d' := h
  congr
  · ext x y : 2
    rw [hed, hed']
  · exact UniformSpace.ext (hU.trans hU'.symm)
  · ext : 2
    rw [← Filter.mem_sets, ← Filter.mem_sets, hB, hB']
#align pseudo_metric_space.ext PseudoMetricSpace.ext

variable [PseudoMetricSpace α]

attribute [instance] PseudoMetricSpace.toUniformSpace PseudoMetricSpace.toBornology

-- see Note [lower instance priority]
instance (priority := 200) PseudoMetricSpace.toEDist : EDist α :=
  ⟨PseudoMetricSpace.edist⟩
#align pseudo_metric_space.to_has_edist PseudoMetricSpace.toEDist

/-- Construct a pseudo-metric space structure whose underlying topological space structure
(definitionally) agrees which a pre-existing topology which is compatible with a given distance
function. -/
def PseudoMetricSpace.ofDistTopology {α : Type u} [TopologicalSpace α] (dist : α → α → ℝ)
    (dist_self : ∀ x : α, dist x x = 0) (dist_comm : ∀ x y : α, dist x y = dist y x)
    (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)
    (H : ∀ s : Set α, IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, dist x y < ε → y ∈ s) :
    PseudoMetricSpace α :=
  { dist := dist
    dist_self := dist_self
    dist_comm := dist_comm
    dist_triangle := dist_triangle
    edist_dist := fun x y => by exact ENNReal.coe_nnreal_eq _
    toUniformSpace :=
      { toCore := (UniformSpace.ofDist dist dist_self dist_comm dist_triangle).toCore
        isOpen_uniformity := fun s => (H s).trans <| forall₂_congr fun x _ =>
          ((UniformSpace.hasBasis_ofFun (exists_gt (0 : ℝ)) dist _ _ _ _).comap
            (Prod.mk x)).mem_iff.symm.trans mem_comap_prod_mk }
    uniformity_dist := rfl
    toBornology := Bornology.ofDist dist dist_comm dist_triangle
    cobounded_sets := rfl }
#align pseudo_metric_space.of_dist_topology PseudoMetricSpace.ofDistTopology

@[simp]
theorem dist_self (x : α) : dist x x = 0 :=
  PseudoMetricSpace.dist_self x
#align dist_self dist_self

theorem dist_comm (x y : α) : dist x y = dist y x :=
  PseudoMetricSpace.dist_comm x y
#align dist_comm dist_comm

theorem edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y) :=
  PseudoMetricSpace.edist_dist x y
#align edist_dist edist_dist

theorem dist_triangle (x y z : α) : dist x z ≤ dist x y + dist y z :=
  PseudoMetricSpace.dist_triangle x y z
#align dist_triangle dist_triangle

theorem dist_triangle_left (x y z : α) : dist x y ≤ dist z x + dist z y := by
  rw [dist_comm z]; apply dist_triangle
#align dist_triangle_left dist_triangle_left

theorem dist_triangle_right (x y z : α) : dist x y ≤ dist x z + dist y z := by
  rw [dist_comm y]; apply dist_triangle
#align dist_triangle_right dist_triangle_right

theorem dist_triangle4 (x y z w : α) : dist x w ≤ dist x y + dist y z + dist z w :=
  calc
    dist x w ≤ dist x z + dist z w := dist_triangle x z w
    _ ≤ dist x y + dist y z + dist z w := add_le_add_right (dist_triangle x y z) _
#align dist_triangle4 dist_triangle4

theorem dist_triangle4_left (x₁ y₁ x₂ y₂ : α) :
    dist x₂ y₂ ≤ dist x₁ y₁ + (dist x₁ x₂ + dist y₁ y₂) := by
  rw [add_left_comm, dist_comm x₁, ← add_assoc]
  apply dist_triangle4
#align dist_triangle4_left dist_triangle4_left

theorem dist_triangle4_right (x₁ y₁ x₂ y₂ : α) :
    dist x₁ y₁ ≤ dist x₁ x₂ + dist y₁ y₂ + dist x₂ y₂ := by
  rw [add_right_comm, dist_comm y₁]
  apply dist_triangle4
#align dist_triangle4_right dist_triangle4_right

/-- The triangle (polygon) inequality for sequences of points; `Finset.Ico` version. -/
theorem dist_le_Ico_sum_dist (f : ℕ → α) {m n} (h : m ≤ n) :
    dist (f m) (f n) ≤ ∑ i in Finset.Ico m n, dist (f i) (f (i + 1)) := by
  induction n, h using Nat.le_induction with
  | base => rw [Finset.Ico_self, Finset.sum_empty, dist_self]
  | succ n hle ihn =>
    calc
      dist (f m) (f (n + 1)) ≤ dist (f m) (f n) + dist (f n) (f (n + 1)) := dist_triangle _ _ _
      _ ≤ (∑ i in Finset.Ico m n, _) + _ := add_le_add ihn le_rfl
      _ = ∑ i in Finset.Ico m (n + 1), _ := by
      { rw [Nat.Ico_succ_right_eq_insert_Ico hle, Finset.sum_insert, add_comm]; simp }
#align dist_le_Ico_sum_dist dist_le_Ico_sum_dist

/-- The triangle (polygon) inequality for sequences of points; `Finset.range` version. -/
theorem dist_le_range_sum_dist (f : ℕ → α) (n : ℕ) :
    dist (f 0) (f n) ≤ ∑ i in Finset.range n, dist (f i) (f (i + 1)) :=
  Nat.Ico_zero_eq_range ▸ dist_le_Ico_sum_dist f (Nat.zero_le n)
#align dist_le_range_sum_dist dist_le_range_sum_dist

/-- A version of `dist_le_Ico_sum_dist` with each intermediate distance replaced
with an upper estimate. -/
theorem dist_le_Ico_sum_of_dist_le {f : ℕ → α} {m n} (hmn : m ≤ n) {d : ℕ → ℝ}
    (hd : ∀ {k}, m ≤ k → k < n → dist (f k) (f (k + 1)) ≤ d k) :
    dist (f m) (f n) ≤ ∑ i in Finset.Ico m n, d i :=
  le_trans (dist_le_Ico_sum_dist f hmn) <|
    Finset.sum_le_sum fun _k hk => hd (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2
#align dist_le_Ico_sum_of_dist_le dist_le_Ico_sum_of_dist_le

/-- A version of `dist_le_range_sum_dist` with each intermediate distance replaced
with an upper estimate. -/
theorem dist_le_range_sum_of_dist_le {f : ℕ → α} (n : ℕ) {d : ℕ → ℝ}
    (hd : ∀ {k}, k < n → dist (f k) (f (k + 1)) ≤ d k) :
    dist (f 0) (f n) ≤ ∑ i in Finset.range n, d i :=
  Nat.Ico_zero_eq_range ▸ dist_le_Ico_sum_of_dist_le (zero_le n) fun _ => hd
#align dist_le_range_sum_of_dist_le dist_le_range_sum_of_dist_le

theorem swap_dist : Function.swap (@dist α _) = dist := by funext x y; exact dist_comm _ _
#align swap_dist swap_dist

theorem abs_dist_sub_le (x y z : α) : |dist x z - dist y z| ≤ dist x y :=
  abs_sub_le_iff.2
    ⟨sub_le_iff_le_add.2 (dist_triangle _ _ _), sub_le_iff_le_add.2 (dist_triangle_left _ _ _)⟩
#align abs_dist_sub_le abs_dist_sub_le

theorem dist_nonneg {x y : α} : 0 ≤ dist x y :=
  dist_nonneg' dist dist_self dist_comm dist_triangle
#align dist_nonneg dist_nonneg

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: distances are nonnegative. -/
@[positivity Dist.dist _ _]
def evalDist : PositivityExt where eval {_ _} _zα _pα e := do
  let .app (.app _ a) b ← whnfR e | throwError "not dist"
  let p ← mkAppOptM ``dist_nonneg #[none, none, a, b]
  pure (.nonnegative p)

end Mathlib.Meta.Positivity

example {x y : α} : 0 ≤ dist x y := by positivity

@[simp] theorem abs_dist {a b : α} : |dist a b| = dist a b := abs_of_nonneg dist_nonneg
#align abs_dist abs_dist

/-- A version of `Dist` that takes value in `ℝ≥0`. -/
class NNDist (α : Type*) where
  nndist : α → α → ℝ≥0
#align has_nndist NNDist

export NNDist (nndist)

-- see Note [lower instance priority]
/-- Distance as a nonnegative real number. -/
instance (priority := 100) PseudoMetricSpace.toNNDist : NNDist α :=
  ⟨fun a b => ⟨dist a b, dist_nonneg⟩⟩
#align pseudo_metric_space.to_has_nndist PseudoMetricSpace.toNNDist

/-- Express `dist` in terms of `nndist`-/
theorem dist_nndist (x y : α) : dist x y = nndist x y := rfl
#align dist_nndist dist_nndist

@[simp, norm_cast]
theorem coe_nndist (x y : α) : ↑(nndist x y) = dist x y := rfl
#align coe_nndist coe_nndist

/-- Express `edist` in terms of `nndist`-/
theorem edist_nndist (x y : α) : edist x y = nndist x y := by
  rw [edist_dist, dist_nndist, ENNReal.ofReal_coe_nnreal]
#align edist_nndist edist_nndist

/-- Express `nndist` in terms of `edist`-/
theorem nndist_edist (x y : α) : nndist x y = (edist x y).toNNReal := by
  simp [edist_nndist]
#align nndist_edist nndist_edist

@[simp, norm_cast]
theorem coe_nnreal_ennreal_nndist (x y : α) : ↑(nndist x y) = edist x y :=
  (edist_nndist x y).symm
#align coe_nnreal_ennreal_nndist coe_nnreal_ennreal_nndist

@[simp, norm_cast]
theorem edist_lt_coe {x y : α} {c : ℝ≥0} : edist x y < c ↔ nndist x y < c := by
  rw [edist_nndist, ENNReal.coe_lt_coe]
#align edist_lt_coe edist_lt_coe

@[simp, norm_cast]
theorem edist_le_coe {x y : α} {c : ℝ≥0} : edist x y ≤ c ↔ nndist x y ≤ c := by
  rw [edist_nndist, ENNReal.coe_le_coe]
#align edist_le_coe edist_le_coe

/-- In a pseudometric space, the extended distance is always finite-/
theorem edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) : edist x y < ⊤ :=
  (edist_dist x y).symm ▸ ENNReal.ofReal_lt_top
#align edist_lt_top edist_lt_top

/-- In a pseudometric space, the extended distance is always finite-/
theorem edist_ne_top (x y : α) : edist x y ≠ ⊤ :=
  (edist_lt_top x y).ne
#align edist_ne_top edist_ne_top

/-- `nndist x x` vanishes-/
@[simp]
theorem nndist_self (a : α) : nndist a a = 0 :=
  (NNReal.coe_eq_zero _).1 (dist_self a)
#align nndist_self nndist_self

-- porting note: `dist_nndist` and `coe_nndist` moved up

@[simp, norm_cast]
theorem dist_lt_coe {x y : α} {c : ℝ≥0} : dist x y < c ↔ nndist x y < c :=
  Iff.rfl
#align dist_lt_coe dist_lt_coe

@[simp, norm_cast]
theorem dist_le_coe {x y : α} {c : ℝ≥0} : dist x y ≤ c ↔ nndist x y ≤ c :=
  Iff.rfl
#align dist_le_coe dist_le_coe

@[simp]
theorem edist_lt_ofReal {x y : α} {r : ℝ} : edist x y < ENNReal.ofReal r ↔ dist x y < r := by
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg]
#align edist_lt_of_real edist_lt_ofReal

@[simp]
theorem edist_le_ofReal {x y : α} {r : ℝ} (hr : 0 ≤ r) :
    edist x y ≤ ENNReal.ofReal r ↔ dist x y ≤ r := by
  rw [edist_dist, ENNReal.ofReal_le_ofReal_iff hr]
#align edist_le_of_real edist_le_ofReal

/-- Express `nndist` in terms of `dist`-/
theorem nndist_dist (x y : α) : nndist x y = Real.toNNReal (dist x y) := by
  rw [dist_nndist, Real.toNNReal_coe]
#align nndist_dist nndist_dist

theorem nndist_comm (x y : α) : nndist x y = nndist y x := NNReal.eq <| dist_comm x y
#align nndist_comm nndist_comm

/-- Triangle inequality for the nonnegative distance-/
theorem nndist_triangle (x y z : α) : nndist x z ≤ nndist x y + nndist y z :=
  dist_triangle _ _ _
#align nndist_triangle nndist_triangle

theorem nndist_triangle_left (x y z : α) : nndist x y ≤ nndist z x + nndist z y :=
  dist_triangle_left _ _ _
#align nndist_triangle_left nndist_triangle_left

theorem nndist_triangle_right (x y z : α) : nndist x y ≤ nndist x z + nndist y z :=
  dist_triangle_right _ _ _
#align nndist_triangle_right nndist_triangle_right

/-- Express `dist` in terms of `edist`-/
theorem dist_edist (x y : α) : dist x y = (edist x y).toReal := by
  rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg]
#align dist_edist dist_edist

namespace Metric

-- instantiate pseudometric space as a topology
variable {x y z : α} {δ ε ε₁ ε₂ : ℝ} {s : Set α}

/-- `ball x ε` is the set of all points `y` with `dist y x < ε` -/
def ball (x : α) (ε : ℝ) : Set α :=
  { y | dist y x < ε }
#align metric.ball Metric.ball

@[simp]
theorem mem_ball : y ∈ ball x ε ↔ dist y x < ε :=
  Iff.rfl
#align metric.mem_ball Metric.mem_ball

theorem mem_ball' : y ∈ ball x ε ↔ dist x y < ε := by rw [dist_comm, mem_ball]
#align metric.mem_ball' Metric.mem_ball'

theorem pos_of_mem_ball (hy : y ∈ ball x ε) : 0 < ε :=
  dist_nonneg.trans_lt hy
#align metric.pos_of_mem_ball Metric.pos_of_mem_ball

theorem mem_ball_self (h : 0 < ε) : x ∈ ball x ε := by
  rwa [mem_ball, dist_self]
#align metric.mem_ball_self Metric.mem_ball_self

@[simp]
theorem nonempty_ball : (ball x ε).Nonempty ↔ 0 < ε :=
  ⟨fun ⟨_x, hx⟩ => pos_of_mem_ball hx, fun h => ⟨x, mem_ball_self h⟩⟩
#align metric.nonempty_ball Metric.nonempty_ball

@[simp]
theorem ball_eq_empty : ball x ε = ∅ ↔ ε ≤ 0 := by
  rw [← not_nonempty_iff_eq_empty, nonempty_ball, not_lt]
#align metric.ball_eq_empty Metric.ball_eq_empty

@[simp]
theorem ball_zero : ball x 0 = ∅ := by rw [ball_eq_empty]
#align metric.ball_zero Metric.ball_zero

/-- If a point belongs to an open ball, then there is a strictly smaller radius whose ball also
contains it.

See also `exists_lt_subset_ball`. -/
theorem exists_lt_mem_ball_of_mem_ball (h : x ∈ ball y ε) : ∃ ε' < ε, x ∈ ball y ε' := by
  simp only [mem_ball] at h ⊢
  exact ⟨(dist x y + ε) / 2, by linarith, by linarith⟩
#align metric.exists_lt_mem_ball_of_mem_ball Metric.exists_lt_mem_ball_of_mem_ball

theorem ball_eq_ball (ε : ℝ) (x : α) :
    UniformSpace.ball x { p | dist p.2 p.1 < ε } = Metric.ball x ε :=
  rfl
#align metric.ball_eq_ball Metric.ball_eq_ball

theorem ball_eq_ball' (ε : ℝ) (x : α) :
    UniformSpace.ball x { p | dist p.1 p.2 < ε } = Metric.ball x ε := by
  ext
  simp [dist_comm, UniformSpace.ball]
#align metric.ball_eq_ball' Metric.ball_eq_ball'

@[simp]
theorem iUnion_ball_nat (x : α) : ⋃ n : ℕ, ball x n = univ :=
  iUnion_eq_univ_iff.2 fun y => exists_nat_gt (dist y x)
#align metric.Union_ball_nat Metric.iUnion_ball_nat

@[simp]
theorem iUnion_ball_nat_succ (x : α) : ⋃ n : ℕ, ball x (n + 1) = univ :=
  iUnion_eq_univ_iff.2 fun y => (exists_nat_gt (dist y x)).imp fun _ h => h.trans (lt_add_one _)
#align metric.Union_ball_nat_succ Metric.iUnion_ball_nat_succ

/-- `closedBall x ε` is the set of all points `y` with `dist y x ≤ ε` -/
def closedBall (x : α) (ε : ℝ) :=
  { y | dist y x ≤ ε }
#align metric.closed_ball Metric.closedBall

@[simp] theorem mem_closedBall : y ∈ closedBall x ε ↔ dist y x ≤ ε := Iff.rfl
#align metric.mem_closed_ball Metric.mem_closedBall

theorem mem_closedBall' : y ∈ closedBall x ε ↔ dist x y ≤ ε := by rw [dist_comm, mem_closedBall]
#align metric.mem_closed_ball' Metric.mem_closedBall'

/-- `sphere x ε` is the set of all points `y` with `dist y x = ε` -/
def sphere (x : α) (ε : ℝ) := { y | dist y x = ε }
#align metric.sphere Metric.sphere

@[simp] theorem mem_sphere : y ∈ sphere x ε ↔ dist y x = ε := Iff.rfl
#align metric.mem_sphere Metric.mem_sphere

theorem mem_sphere' : y ∈ sphere x ε ↔ dist x y = ε := by rw [dist_comm, mem_sphere]
#align metric.mem_sphere' Metric.mem_sphere'

theorem ne_of_mem_sphere (h : y ∈ sphere x ε) (hε : ε ≠ 0) : y ≠ x :=
  ne_of_mem_of_not_mem h <| by simpa using hε.symm
#align metric.ne_of_mem_sphere Metric.ne_of_mem_sphere

theorem nonneg_of_mem_sphere (hy : y ∈ sphere x ε) : 0 ≤ ε :=
  dist_nonneg.trans_eq hy
#align metric.nonneg_of_mem_sphere Metric.nonneg_of_mem_sphere

@[simp]
theorem sphere_eq_empty_of_neg (hε : ε < 0) : sphere x ε = ∅ :=
  Set.eq_empty_iff_forall_not_mem.mpr fun _y hy => (nonneg_of_mem_sphere hy).not_lt hε
#align metric.sphere_eq_empty_of_neg Metric.sphere_eq_empty_of_neg

theorem sphere_eq_empty_of_subsingleton [Subsingleton α] (hε : ε ≠ 0) : sphere x ε = ∅ :=
  Set.eq_empty_iff_forall_not_mem.mpr fun _ h => ne_of_mem_sphere h hε (Subsingleton.elim _ _)
#align metric.sphere_eq_empty_of_subsingleton Metric.sphere_eq_empty_of_subsingleton

theorem sphere_isEmpty_of_subsingleton [Subsingleton α] (hε : ε ≠ 0) : IsEmpty (sphere x ε) := by
  rw [sphere_eq_empty_of_subsingleton hε]; infer_instance
#align metric.sphere_is_empty_of_subsingleton Metric.sphere_isEmpty_of_subsingleton

theorem mem_closedBall_self (h : 0 ≤ ε) : x ∈ closedBall x ε := by
  rwa [mem_closedBall, dist_self]
#align metric.mem_closed_ball_self Metric.mem_closedBall_self

@[simp]
theorem nonempty_closedBall : (closedBall x ε).Nonempty ↔ 0 ≤ ε :=
  ⟨fun ⟨_x, hx⟩ => dist_nonneg.trans hx, fun h => ⟨x, mem_closedBall_self h⟩⟩
#align metric.nonempty_closed_ball Metric.nonempty_closedBall

@[simp]
theorem closedBall_eq_empty : closedBall x ε = ∅ ↔ ε < 0 := by
  rw [← not_nonempty_iff_eq_empty, nonempty_closedBall, not_le]
#align metric.closed_ball_eq_empty Metric.closedBall_eq_empty

/-- Closed balls and spheres coincide when the radius is non-positive -/
theorem closedBall_eq_sphere_of_nonpos (hε : ε ≤ 0) : closedBall x ε = sphere x ε :=
  Set.ext fun _ => (hε.trans dist_nonneg).le_iff_eq
#align metric.closed_ball_eq_sphere_of_nonpos Metric.closedBall_eq_sphere_of_nonpos

theorem ball_subset_closedBall : ball x ε ⊆ closedBall x ε := fun _y hy =>
  mem_closedBall.2 (le_of_lt hy)
#align metric.ball_subset_closed_ball Metric.ball_subset_closedBall

theorem sphere_subset_closedBall : sphere x ε ⊆ closedBall x ε := fun _ => le_of_eq
#align metric.sphere_subset_closed_ball Metric.sphere_subset_closedBall

theorem closedBall_disjoint_ball (h : δ + ε ≤ dist x y) : Disjoint (closedBall x δ) (ball y ε) :=
  Set.disjoint_left.mpr fun _a ha1 ha2 =>
    (h.trans <| dist_triangle_left _ _ _).not_lt <| add_lt_add_of_le_of_lt ha1 ha2
#align metric.closed_ball_disjoint_ball Metric.closedBall_disjoint_ball

theorem ball_disjoint_closedBall (h : δ + ε ≤ dist x y) : Disjoint (ball x δ) (closedBall y ε) :=
  (closedBall_disjoint_ball <| by rwa [add_comm, dist_comm]).symm
#align metric.ball_disjoint_closed_ball Metric.ball_disjoint_closedBall

theorem ball_disjoint_ball (h : δ + ε ≤ dist x y) : Disjoint (ball x δ) (ball y ε) :=
  (closedBall_disjoint_ball h).mono_left ball_subset_closedBall
#align metric.ball_disjoint_ball Metric.ball_disjoint_ball

theorem closedBall_disjoint_closedBall (h : δ + ε < dist x y) :
    Disjoint (closedBall x δ) (closedBall y ε) :=
  Set.disjoint_left.mpr fun _a ha1 ha2 =>
    h.not_le <| (dist_triangle_left _ _ _).trans <| add_le_add ha1 ha2
#align metric.closed_ball_disjoint_closed_ball Metric.closedBall_disjoint_closedBall

theorem sphere_disjoint_ball : Disjoint (sphere x ε) (ball x ε) :=
  Set.disjoint_left.mpr fun _y hy₁ hy₂ => absurd hy₁ <| ne_of_lt hy₂
#align metric.sphere_disjoint_ball Metric.sphere_disjoint_ball

@[simp]
theorem ball_union_sphere : ball x ε ∪ sphere x ε = closedBall x ε :=
  Set.ext fun _y => (@le_iff_lt_or_eq ℝ _ _ _).symm
#align metric.ball_union_sphere Metric.ball_union_sphere

@[simp]
theorem sphere_union_ball : sphere x ε ∪ ball x ε = closedBall x ε := by
  rw [union_comm, ball_union_sphere]
#align metric.sphere_union_ball Metric.sphere_union_ball

@[simp]
theorem closedBall_diff_sphere : closedBall x ε \ sphere x ε = ball x ε := by
  rw [← ball_union_sphere, Set.union_diff_cancel_right sphere_disjoint_ball.symm.le_bot]
#align metric.closed_ball_diff_sphere Metric.closedBall_diff_sphere

@[simp]
theorem closedBall_diff_ball : closedBall x ε \ ball x ε = sphere x ε := by
  rw [← ball_union_sphere, Set.union_diff_cancel_left sphere_disjoint_ball.symm.le_bot]
#align metric.closed_ball_diff_ball Metric.closedBall_diff_ball

theorem mem_ball_comm : x ∈ ball y ε ↔ y ∈ ball x ε := by rw [mem_ball', mem_ball]
#align metric.mem_ball_comm Metric.mem_ball_comm

theorem mem_closedBall_comm : x ∈ closedBall y ε ↔ y ∈ closedBall x ε := by
  rw [mem_closedBall', mem_closedBall]
#align metric.mem_closed_ball_comm Metric.mem_closedBall_comm

theorem mem_sphere_comm : x ∈ sphere y ε ↔ y ∈ sphere x ε := by rw [mem_sphere', mem_sphere]
#align metric.mem_sphere_comm Metric.mem_sphere_comm

theorem ball_subset_ball (h : ε₁ ≤ ε₂) : ball x ε₁ ⊆ ball x ε₂ := fun _y yx =>
  lt_of_lt_of_le (mem_ball.1 yx) h
#align metric.ball_subset_ball Metric.ball_subset_ball

theorem closedBall_eq_bInter_ball : closedBall x ε = ⋂ δ > ε, ball x δ := by
  ext y; rw [mem_closedBall, ← forall_lt_iff_le', mem_iInter₂]; rfl
#align metric.closed_ball_eq_bInter_ball Metric.closedBall_eq_bInter_ball

theorem ball_subset_ball' (h : ε₁ + dist x y ≤ ε₂) : ball x ε₁ ⊆ ball y ε₂ := fun z hz =>
  calc
    dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
    _ < ε₁ + dist x y := add_lt_add_right (mem_ball.1 hz) _
    _ ≤ ε₂ := h
#align metric.ball_subset_ball' Metric.ball_subset_ball'

theorem closedBall_subset_closedBall (h : ε₁ ≤ ε₂) : closedBall x ε₁ ⊆ closedBall x ε₂ :=
  fun _y (yx : _ ≤ ε₁) => le_trans yx h
#align metric.closed_ball_subset_closed_ball Metric.closedBall_subset_closedBall

theorem closedBall_subset_closedBall' (h : ε₁ + dist x y ≤ ε₂) :
    closedBall x ε₁ ⊆ closedBall y ε₂ := fun z hz =>
  calc
    dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
    _ ≤ ε₁ + dist x y := add_le_add_right (mem_closedBall.1 hz) _
    _ ≤ ε₂ := h
#align metric.closed_ball_subset_closed_ball' Metric.closedBall_subset_closedBall'

theorem closedBall_subset_ball (h : ε₁ < ε₂) : closedBall x ε₁ ⊆ ball x ε₂ :=
  fun y (yh : dist y x ≤ ε₁) => lt_of_le_of_lt yh h
#align metric.closed_ball_subset_ball Metric.closedBall_subset_ball

theorem closedBall_subset_ball' (h : ε₁ + dist x y < ε₂) :
    closedBall x ε₁ ⊆ ball y ε₂ := fun z hz =>
  calc
    dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
    _ ≤ ε₁ + dist x y := add_le_add_right (mem_closedBall.1 hz) _
    _ < ε₂ := h
#align metric.closed_ball_subset_ball' Metric.closedBall_subset_ball'

theorem dist_le_add_of_nonempty_closedBall_inter_closedBall
    (h : (closedBall x ε₁ ∩ closedBall y ε₂).Nonempty) : dist x y ≤ ε₁ + ε₂ :=
  let ⟨z, hz⟩ := h
  calc
    dist x y ≤ dist z x + dist z y := dist_triangle_left _ _ _
    _ ≤ ε₁ + ε₂ := add_le_add hz.1 hz.2
#align metric.dist_le_add_of_nonempty_closed_ball_inter_closed_ball Metric.dist_le_add_of_nonempty_closedBall_inter_closedBall

theorem dist_lt_add_of_nonempty_closedBall_inter_ball (h : (closedBall x ε₁ ∩ ball y ε₂).Nonempty) :
    dist x y < ε₁ + ε₂ :=
  let ⟨z, hz⟩ := h
  calc
    dist x y ≤ dist z x + dist z y := dist_triangle_left _ _ _
    _ < ε₁ + ε₂ := add_lt_add_of_le_of_lt hz.1 hz.2
#align metric.dist_lt_add_of_nonempty_closed_ball_inter_ball Metric.dist_lt_add_of_nonempty_closedBall_inter_ball

theorem dist_lt_add_of_nonempty_ball_inter_closedBall (h : (ball x ε₁ ∩ closedBall y ε₂).Nonempty) :
    dist x y < ε₁ + ε₂ := by
  rw [inter_comm] at h
  rw [add_comm, dist_comm]
  exact dist_lt_add_of_nonempty_closedBall_inter_ball h
#align metric.dist_lt_add_of_nonempty_ball_inter_closed_ball Metric.dist_lt_add_of_nonempty_ball_inter_closedBall

theorem dist_lt_add_of_nonempty_ball_inter_ball (h : (ball x ε₁ ∩ ball y ε₂).Nonempty) :
    dist x y < ε₁ + ε₂ :=
  dist_lt_add_of_nonempty_closedBall_inter_ball <|
    h.mono (inter_subset_inter ball_subset_closedBall Subset.rfl)
#align metric.dist_lt_add_of_nonempty_ball_inter_ball Metric.dist_lt_add_of_nonempty_ball_inter_ball

@[simp]
theorem iUnion_closedBall_nat (x : α) : ⋃ n : ℕ, closedBall x n = univ :=
  iUnion_eq_univ_iff.2 fun y => exists_nat_ge (dist y x)
#align metric.Union_closed_ball_nat Metric.iUnion_closedBall_nat

theorem iUnion_inter_closedBall_nat (s : Set α) (x : α) : ⋃ n : ℕ, s ∩ closedBall x n = s := by
  rw [← inter_iUnion, iUnion_closedBall_nat, inter_univ]
#align metric.Union_inter_closed_ball_nat Metric.iUnion_inter_closedBall_nat

theorem ball_subset (h : dist x y ≤ ε₂ - ε₁) : ball x ε₁ ⊆ ball y ε₂ := fun z zx => by
  rw [← add_sub_cancel'_right ε₁ ε₂]
  exact lt_of_le_of_lt (dist_triangle z x y) (add_lt_add_of_lt_of_le zx h)
#align metric.ball_subset Metric.ball_subset

theorem ball_half_subset (y) (h : y ∈ ball x (ε / 2)) : ball y (ε / 2) ⊆ ball x ε :=
  ball_subset <| by rw [sub_self_div_two]; exact le_of_lt h
#align metric.ball_half_subset Metric.ball_half_subset

theorem exists_ball_subset_ball (h : y ∈ ball x ε) : ∃ ε' > 0, ball y ε' ⊆ ball x ε :=
  ⟨_, sub_pos.2 h, ball_subset <| by rw [sub_sub_self]⟩
#align metric.exists_ball_subset_ball Metric.exists_ball_subset_ball

/-- If a property holds for all points in closed balls of arbitrarily large radii, then it holds for
all points. -/
theorem forall_of_forall_mem_closedBall (p : α → Prop) (x : α)
    (H : ∃ᶠ R : ℝ in atTop, ∀ y ∈ closedBall x R, p y) (y : α) : p y := by
  obtain ⟨R, hR, h⟩ : ∃ R ≥ dist y x, ∀ z : α, z ∈ closedBall x R → p z :=
    frequently_iff.1 H (Ici_mem_atTop (dist y x))
  exact h _ hR
#align metric.forall_of_forall_mem_closed_ball Metric.forall_of_forall_mem_closedBall

/-- If a property holds for all points in balls of arbitrarily large radii, then it holds for all
points. -/
theorem forall_of_forall_mem_ball (p : α → Prop) (x : α)
    (H : ∃ᶠ R : ℝ in atTop, ∀ y ∈ ball x R, p y) (y : α) : p y := by
  obtain ⟨R, hR, h⟩ : ∃ R > dist y x, ∀ z : α, z ∈ ball x R → p z :=
    frequently_iff.1 H (Ioi_mem_atTop (dist y x))
  exact h _ hR
#align metric.forall_of_forall_mem_ball Metric.forall_of_forall_mem_ball

-- TODO(MR): needed for replaceBornology
theorem isBounded_iff {s : Set α} :
    IsBounded s ↔ ∃ C : ℝ, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → dist x y ≤ C := by
  rw [isBounded_def, ← Filter.mem_sets, @PseudoMetricSpace.cobounded_sets α, mem_setOf_eq,
    compl_compl]
#align metric.is_bounded_iff Metric.isBounded_iff

theorem isBounded_iff_eventually {s : Set α} :
    IsBounded s ↔ ∀ᶠ C in atTop, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → dist x y ≤ C :=
  isBounded_iff.trans
    ⟨fun ⟨C, h⟩ => eventually_atTop.2 ⟨C, fun _C' hC' _x hx _y hy => (h hx hy).trans hC'⟩,
      Eventually.exists⟩
#align metric.is_bounded_iff_eventually Metric.isBounded_iff_eventually

theorem isBounded_iff_exists_ge {s : Set α} (c : ℝ) :
    IsBounded s ↔ ∃ C, c ≤ C ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → dist x y ≤ C :=
  ⟨fun h => ((eventually_ge_atTop c).and (isBounded_iff_eventually.1 h)).exists, fun h =>
    isBounded_iff.2 <| h.imp fun _ => And.right⟩
#align metric.is_bounded_iff_exists_ge Metric.isBounded_iff_exists_ge

theorem isBounded_iff_nndist {s : Set α} :
    IsBounded s ↔ ∃ C : ℝ≥0, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → nndist x y ≤ C := by
  simp only [isBounded_iff_exists_ge 0, NNReal.exists, ← NNReal.coe_le_coe, ← dist_nndist,
    NNReal.coe_mk, exists_prop]
#align metric.is_bounded_iff_nndist Metric.isBounded_iff_nndist

theorem toUniformSpace_eq :
    ‹PseudoMetricSpace α›.toUniformSpace = .ofDist dist dist_self dist_comm dist_triangle :=
  UniformSpace.ext PseudoMetricSpace.uniformity_dist
#align metric.to_uniform_space_eq Metric.toUniformSpace_eq

theorem uniformity_basis_dist :
    (𝓤 α).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε } := by
  rw [toUniformSpace_eq]
  exact UniformSpace.hasBasis_ofFun (exists_gt _) _ _ _ _ _
#align metric.uniformity_basis_dist Metric.uniformity_basis_dist

/-- Given `f : β → ℝ`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then `f i`-neighborhoods of the diagonal form a basis of `𝓤 α`.

For specific bases see `uniformity_basis_dist`, `uniformity_basis_dist_inv_nat_succ`,
and `uniformity_basis_dist_inv_nat_pos`. -/
protected theorem mk_uniformity_basis {β : Type*} {p : β → Prop} {f : β → ℝ}
    (hf₀ : ∀ i, p i → 0 < f i) (hf : ∀ ⦃ε⦄, 0 < ε → ∃ i, p i ∧ f i ≤ ε) :
    (𝓤 α).HasBasis p fun i => { p : α × α | dist p.1 p.2 < f i } := by
  refine' ⟨fun s => uniformity_basis_dist.mem_iff.trans _⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases hf ε₀ with ⟨i, hi, H⟩
    exact ⟨i, hi, fun x (hx : _ < _) => hε <| lt_of_lt_of_le hx H⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, H⟩
#align metric.mk_uniformity_basis Metric.mk_uniformity_basis

theorem uniformity_basis_dist_rat :
    (𝓤 α).HasBasis (fun r : ℚ => 0 < r) fun r => { p : α × α | dist p.1 p.2 < r } :=
  Metric.mk_uniformity_basis (fun _ => Rat.cast_pos.2) fun _ε hε =>
    let ⟨r, hr0, hrε⟩ := exists_rat_btwn hε
    ⟨r, Rat.cast_pos.1 hr0, hrε.le⟩
#align metric.uniformity_basis_dist_rat Metric.uniformity_basis_dist_rat

theorem uniformity_basis_dist_inv_nat_succ :
    (𝓤 α).HasBasis (fun _ => True) fun n : ℕ => { p : α × α | dist p.1 p.2 < 1 / (↑n + 1) } :=
  Metric.mk_uniformity_basis (fun n _ => div_pos zero_lt_one <| Nat.cast_add_one_pos n) fun _ε ε0 =>
    (exists_nat_one_div_lt ε0).imp fun _n hn => ⟨trivial, le_of_lt hn⟩
#align metric.uniformity_basis_dist_inv_nat_succ Metric.uniformity_basis_dist_inv_nat_succ

theorem uniformity_basis_dist_inv_nat_pos :
    (𝓤 α).HasBasis (fun n : ℕ => 0 < n) fun n : ℕ => { p : α × α | dist p.1 p.2 < 1 / ↑n } :=
  Metric.mk_uniformity_basis (fun n hn => div_pos zero_lt_one <| Nat.cast_pos.2 hn) fun ε ε0 =>
    let ⟨n, hn⟩ := exists_nat_one_div_lt ε0
    ⟨n + 1, Nat.succ_pos n, by exact_mod_cast hn.le⟩
#align metric.uniformity_basis_dist_inv_nat_pos Metric.uniformity_basis_dist_inv_nat_pos

theorem uniformity_basis_dist_pow {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    (𝓤 α).HasBasis (fun _ : ℕ => True) fun n : ℕ => { p : α × α | dist p.1 p.2 < r ^ n } :=
  Metric.mk_uniformity_basis (fun _ _ => pow_pos h0 _) fun _ε ε0 =>
    let ⟨n, hn⟩ := exists_pow_lt_of_lt_one ε0 h1
    ⟨n, trivial, hn.le⟩
#align metric.uniformity_basis_dist_pow Metric.uniformity_basis_dist_pow

theorem uniformity_basis_dist_lt {R : ℝ} (hR : 0 < R) :
    (𝓤 α).HasBasis (fun r : ℝ => 0 < r ∧ r < R) fun r => { p : α × α | dist p.1 p.2 < r } :=
  Metric.mk_uniformity_basis (fun _ => And.left) fun r hr =>
    ⟨min r (R / 2), ⟨lt_min hr (half_pos hR), min_lt_iff.2 <| Or.inr (half_lt_self hR)⟩,
      min_le_left _ _⟩
#align metric.uniformity_basis_dist_lt Metric.uniformity_basis_dist_lt

/-- Given `f : β → ℝ`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then closed neighborhoods of the diagonal of sizes `{f i | p i}`
form a basis of `𝓤 α`.

Currently we have only one specific basis `uniformity_basis_dist_le` based on this constructor.
More can be easily added if needed in the future. -/
protected theorem mk_uniformity_basis_le {β : Type*} {p : β → Prop} {f : β → ℝ}
    (hf₀ : ∀ x, p x → 0 < f x) (hf : ∀ ε, 0 < ε → ∃ x, p x ∧ f x ≤ ε) :
    (𝓤 α).HasBasis p fun x => { p : α × α | dist p.1 p.2 ≤ f x } := by
  refine' ⟨fun s => uniformity_basis_dist.mem_iff.trans _⟩
  constructor
  · rintro ⟨ε, ε₀, hε⟩
    rcases exists_between ε₀ with ⟨ε', hε'⟩
    rcases hf ε' hε'.1 with ⟨i, hi, H⟩
    exact ⟨i, hi, fun x (hx : _ ≤ _) => hε <| lt_of_le_of_lt (le_trans hx H) hε'.2⟩
  · exact fun ⟨i, hi, H⟩ => ⟨f i, hf₀ i hi, fun x (hx : _ < _) => H (mem_setOf.2 hx.le)⟩
#align metric.mk_uniformity_basis_le Metric.mk_uniformity_basis_le

/-- Constant size closed neighborhoods of the diagonal form a basis
of the uniformity filter. -/
theorem uniformity_basis_dist_le :
    (𝓤 α).HasBasis ((0 : ℝ) < ·) fun ε => { p : α × α | dist p.1 p.2 ≤ ε } :=
  Metric.mk_uniformity_basis_le (fun _ => id) fun ε ε₀ => ⟨ε, ε₀, le_refl ε⟩
#align metric.uniformity_basis_dist_le Metric.uniformity_basis_dist_le

theorem uniformity_basis_dist_le_pow {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    (𝓤 α).HasBasis (fun _ : ℕ => True) fun n : ℕ => { p : α × α | dist p.1 p.2 ≤ r ^ n } :=
  Metric.mk_uniformity_basis_le (fun _ _ => pow_pos h0 _) fun _ε ε0 =>
    let ⟨n, hn⟩ := exists_pow_lt_of_lt_one ε0 h1
    ⟨n, trivial, hn.le⟩
#align metric.uniformity_basis_dist_le_pow Metric.uniformity_basis_dist_le_pow

theorem mem_uniformity_dist {s : Set (α × α)} :
    s ∈ 𝓤 α ↔ ∃ ε > 0, ∀ {a b : α}, dist a b < ε → (a, b) ∈ s :=
  uniformity_basis_dist.mem_uniformity_iff
#align metric.mem_uniformity_dist Metric.mem_uniformity_dist

/-- A constant size neighborhood of the diagonal is an entourage. -/
theorem dist_mem_uniformity {ε : ℝ} (ε0 : 0 < ε) : { p : α × α | dist p.1 p.2 < ε } ∈ 𝓤 α :=
  mem_uniformity_dist.2 ⟨ε, ε0, id⟩
#align metric.dist_mem_uniformity Metric.dist_mem_uniformity

theorem uniformContinuous_iff [PseudoMetricSpace β] {f : α → β} :
    UniformContinuous f ↔ ∀ ε > 0, ∃ δ > 0, ∀ {a b : α}, dist a b < δ → dist (f a) (f b) < ε :=
  uniformity_basis_dist.uniformContinuous_iff uniformity_basis_dist
#align metric.uniform_continuous_iff Metric.uniformContinuous_iff

theorem uniformContinuousOn_iff [PseudoMetricSpace β] {f : α → β} {s : Set α} :
    UniformContinuousOn f s ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x ∈ s, ∀ y ∈ s, dist x y < δ → dist (f x) (f y) < ε :=
  Metric.uniformity_basis_dist.uniformContinuousOn_iff Metric.uniformity_basis_dist
#align metric.uniform_continuous_on_iff Metric.uniformContinuousOn_iff

theorem uniformContinuousOn_iff_le [PseudoMetricSpace β] {f : α → β} {s : Set α} :
    UniformContinuousOn f s ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ δ → dist (f x) (f y) ≤ ε :=
  Metric.uniformity_basis_dist_le.uniformContinuousOn_iff Metric.uniformity_basis_dist_le
#align metric.uniform_continuous_on_iff_le Metric.uniformContinuousOn_iff_le

nonrec theorem uniformInducing_iff [PseudoMetricSpace β] {f : α → β} :
    UniformInducing f ↔ UniformContinuous f ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ :=
  uniformInducing_iff'.trans <| Iff.rfl.and <|
    ((uniformity_basis_dist.comap _).le_basis_iff uniformity_basis_dist).trans <| by
      simp only [subset_def, Prod.forall, gt_iff_lt, preimage_setOf_eq, Prod_map, mem_setOf]

nonrec theorem uniformEmbedding_iff [PseudoMetricSpace β] {f : α → β} :
    UniformEmbedding f ↔ Function.Injective f ∧ UniformContinuous f ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ := by
  rw [uniformEmbedding_iff, and_comm, uniformInducing_iff]
#align metric.uniform_embedding_iff Metric.uniformEmbedding_iff

/-- If a map between pseudometric spaces is a uniform embedding then the distance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y`. -/
theorem controlled_of_uniformEmbedding [PseudoMetricSpace β] {f : α → β} (h : UniformEmbedding f) :
    (∀ ε > 0, ∃ δ > 0, ∀ {a b : α}, dist a b < δ → dist (f a) (f b) < ε) ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ :=
  ⟨uniformContinuous_iff.1 h.uniformContinuous, (uniformEmbedding_iff.1 h).2.2⟩
#align metric.controlled_of_uniform_embedding Metric.controlled_of_uniformEmbedding

theorem totallyBounded_iff {s : Set α} :
    TotallyBounded s ↔ ∀ ε > 0, ∃ t : Set α, t.Finite ∧ s ⊆ ⋃ y ∈ t, ball y ε :=
  uniformity_basis_dist.totallyBounded_iff
#align metric.totally_bounded_iff Metric.totallyBounded_iff

/-- A pseudometric space is totally bounded if one can reconstruct up to any ε>0 any element of the
space from finitely many data. -/
theorem totallyBounded_of_finite_discretization {s : Set α}
    (H : ∀ ε > (0 : ℝ),
        ∃ (β : Type u) (_ : Fintype β) (F : s → β), ∀ x y, F x = F y → dist (x : α) y < ε) :
    TotallyBounded s := by
  cases' s.eq_empty_or_nonempty with hs hs
  · rw [hs]
    exact totallyBounded_empty
  rcases hs with ⟨x0, hx0⟩
  haveI : Inhabited s := ⟨⟨x0, hx0⟩⟩
  refine' totallyBounded_iff.2 fun ε ε0 => _
  rcases H ε ε0 with ⟨β, fβ, F, hF⟩
  let Finv := Function.invFun F
  refine' ⟨range (Subtype.val ∘ Finv), finite_range _, fun x xs => _⟩
  let x' := Finv (F ⟨x, xs⟩)
  have : F x' = F ⟨x, xs⟩ := Function.invFun_eq ⟨⟨x, xs⟩, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_range]
  exact ⟨_, ⟨F ⟨x, xs⟩, rfl⟩, hF _ _ this.symm⟩
#align metric.totally_bounded_of_finite_discretization Metric.totallyBounded_of_finite_discretization

theorem finite_approx_of_totallyBounded {s : Set α} (hs : TotallyBounded s) :
    ∀ ε > 0, ∃ t, t ⊆ s ∧ Set.Finite t ∧ s ⊆ ⋃ y ∈ t, ball y ε := by
  intro ε ε_pos
  rw [totallyBounded_iff_subset] at hs
  exact hs _ (dist_mem_uniformity ε_pos)
#align metric.finite_approx_of_totally_bounded Metric.finite_approx_of_totallyBounded

/-- Expressing uniform convergence using `dist` -/
theorem tendstoUniformlyOnFilter_iff {F : ι → β → α} {f : β → α} {p : Filter ι} {p' : Filter β} :
    TendstoUniformlyOnFilter F f p p' ↔
      ∀ ε > 0, ∀ᶠ n : ι × β in p ×ˢ p', dist (f n.snd) (F n.fst n.snd) < ε := by
  refine' ⟨fun H ε hε => H _ (dist_mem_uniformity hε), fun H u hu => _⟩
  rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩
  refine' (H ε εpos).mono fun n hn => hε hn
#align metric.tendsto_uniformly_on_filter_iff Metric.tendstoUniformlyOnFilter_iff

/-- Expressing locally uniform convergence on a set using `dist`. -/
theorem tendstoLocallyUniformlyOn_iff [TopologicalSpace β] {F : ι → β → α} {f : β → α}
    {p : Filter ι} {s : Set β} :
    TendstoLocallyUniformlyOn F f p s ↔
      ∀ ε > 0, ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, ∀ᶠ n in p, ∀ y ∈ t, dist (f y) (F n y) < ε := by
  refine' ⟨fun H ε hε => H _ (dist_mem_uniformity hε), fun H u hu x hx => _⟩
  rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩
  rcases H ε εpos x hx with ⟨t, ht, Ht⟩
  exact ⟨t, ht, Ht.mono fun n hs x hx => hε (hs x hx)⟩
#align metric.tendsto_locally_uniformly_on_iff Metric.tendstoLocallyUniformlyOn_iff

/-- Expressing uniform convergence on a set using `dist`. -/
theorem tendstoUniformlyOn_iff {F : ι → β → α} {f : β → α} {p : Filter ι} {s : Set β} :
    TendstoUniformlyOn F f p s ↔ ∀ ε > 0, ∀ᶠ n in p, ∀ x ∈ s, dist (f x) (F n x) < ε := by
  refine' ⟨fun H ε hε => H _ (dist_mem_uniformity hε), fun H u hu => _⟩
  rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩
  exact (H ε εpos).mono fun n hs x hx => hε (hs x hx)
#align metric.tendsto_uniformly_on_iff Metric.tendstoUniformlyOn_iff

/-- Expressing locally uniform convergence using `dist`. -/
theorem tendstoLocallyUniformly_iff [TopologicalSpace β] {F : ι → β → α} {f : β → α}
    {p : Filter ι} :
    TendstoLocallyUniformly F f p ↔
      ∀ ε > 0, ∀ x : β, ∃ t ∈ 𝓝 x, ∀ᶠ n in p, ∀ y ∈ t, dist (f y) (F n y) < ε := by
  simp only [← tendstoLocallyUniformlyOn_univ, tendstoLocallyUniformlyOn_iff, nhdsWithin_univ,
    mem_univ, forall_const, exists_prop]
#align metric.tendsto_locally_uniformly_iff Metric.tendstoLocallyUniformly_iff

/-- Expressing uniform convergence using `dist`. -/
theorem tendstoUniformly_iff {F : ι → β → α} {f : β → α} {p : Filter ι} :
    TendstoUniformly F f p ↔ ∀ ε > 0, ∀ᶠ n in p, ∀ x, dist (f x) (F n x) < ε := by
  rw [← tendstoUniformlyOn_univ, tendstoUniformlyOn_iff]
  simp
#align metric.tendsto_uniformly_iff Metric.tendstoUniformly_iff
end Metric
