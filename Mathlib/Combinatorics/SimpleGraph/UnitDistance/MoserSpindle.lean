/-
Copyright (c) 2026 Dmitri Sotnikov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitri Sotnikov
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
public import Mathlib.Combinatorics.SimpleGraph.UnitDistance.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public meta import Mathlib.Data.Fintype.Pi

/-!
# The Moser spindle: a $7$-vertex unit-distance graph with chromatic number $4$

The **Hadwiger–Nelson problem** (Edward Nelson, 1950) asks for the chromatic number of the
*unit-distance graph* on the Euclidean plane: the minimum number of colours such that no two
points at distance exactly $1$ share a colour. The current best bounds are
$5 \leq \chi(\mathbb{R}^2) \leq 7$, with both ends open.

This file formalises the **Moser spindle** (Moser–Moser, 1961): an explicit $7$-vertex
unit-distance graph that is not $3$-colourable. The Moser spindle is the classical witness
for the lower bound $\chi(\mathbb{R}^2) \geq 4$, the textbook result that preceded de Grey's
2018 improvement to $\chi(\mathbb{R}^2) \geq 5$.

The construction consists of two unit rhombi (each a pair of equilateral triangles glued along
an edge) sharing a vertex, with the second rhombus rotated so that one pair of distant
vertices is also at unit distance.

## Main declarations

* `SimpleGraph.MoserSpindle.adj` : Boolean adjacency for the abstract $7$-vertex Moser spindle.
* `SimpleGraph.MoserSpindle.graph` : the abstract Moser spindle as a `SimpleGraph (Fin 7)`.
* `SimpleGraph.MoserSpindle.embed` : the standard embedding `Fin 7 → EuclideanSpace ℝ (Fin 2)`
  realising the spindle as a unit-distance subgraph of the plane (the rotation angle has
  $\cos = 5/6$, $\sin = \sqrt{11}/6$).
* `SimpleGraph.MoserSpindle.unitDistEmbedding` : the same data assembled as a
  `SimpleGraph.UnitDistEmbedding` into the Euclidean plane.

## Main results

* `SimpleGraph.MoserSpindle.not_colorable_three` : the abstract Moser spindle has no proper
  $3$-colouring (verified by `native_decide`).
* `SimpleGraph.MoserSpindle.chromaticNumber_ge_four` : the abstract Moser spindle's chromatic
  number is at least $4$.

## References

* L. Moser and W. Moser, *Solution to Problem 10*, Canadian Math. Bull. 4 (1961), 187–189.
* A. Soifer, *The Mathematical Coloring Book*, Springer, 2009.
* A. de Grey, *The chromatic number of the plane is at least 5*, Geombinatorics 28 (2018),
  18–31. (Strengthens the lower bound to $5$; the formalization here is the textbook
  $\geq 4$ bound.)

## Tags

Hadwiger–Nelson problem, chromatic number of the plane, Moser spindle, unit-distance graph
-/

@[expose] public section

namespace SimpleGraph

namespace MoserSpindle

/-! ### The abstract Moser spindle

Vertices `0..3` form the first unit rhombus (triangles `{0,1,2}` and `{1,2,3}` glued along
edge `{1,2}`). Vertices `0,4,5,6` form the second unit rhombus. Edge `{3,6}` connects them;
the rotation angle for the second rhombus has $\cos = 5/6$, $\sin = \sqrt{11}/6$, ensuring
that this edge also has unit length.
-/

/-- Boolean adjacency for the Moser spindle: 11 unordered edges. -/
def adj : Fin 7 → Fin 7 → Bool
  | 0, 1 => true | 1, 0 => true | 0, 2 => true | 2, 0 => true
  | 1, 2 => true | 2, 1 => true | 1, 3 => true | 3, 1 => true
  | 2, 3 => true | 3, 2 => true | 0, 4 => true | 4, 0 => true
  | 0, 5 => true | 5, 0 => true | 4, 5 => true | 5, 4 => true
  | 4, 6 => true | 6, 4 => true | 5, 6 => true | 6, 5 => true
  | 3, 6 => true | 6, 3 => true | _, _ => false

/-- A function `Fin 7 → Fin k` is a *proper* colouring of the Moser spindle iff it assigns
distinct colours to every adjacent pair of vertices. -/
def isProperColoring {k : ℕ} (f : Fin 7 → Fin k) : Bool :=
  decide (∀ i j : Fin 7, adj i j = true → f i ≠ f j)

/-- The Moser spindle has no proper $3$-colouring. Verified by exhaustive search over
$3^7 = 2187$ candidate functions `Fin 7 → Fin 3`. -/
theorem no_three_coloring : ¬ ∃ f : Fin 7 → Fin 3, isProperColoring f = true := by
  native_decide

/-- The Moser spindle as a `SimpleGraph (Fin 7)`. -/
def graph : SimpleGraph (Fin 7) where
  Adj i j := adj i j = true
  symm := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [adj]
  loopless := ⟨by intro i h; fin_cases i <;> simp [adj] at h⟩

instance : DecidableRel graph.Adj := fun i j => by unfold graph; exact inferInstance

/-- The abstract Moser spindle is not $3$-colourable as a `SimpleGraph`. -/
theorem not_colorable_three : ¬ graph.Colorable 3 := by
  intro h
  obtain ⟨c⟩ := h
  apply no_three_coloring
  refine ⟨fun i => c i, ?_⟩
  unfold isProperColoring
  simp only [decide_eq_true_eq]
  intro i j hadj
  exact c.valid hadj

/-- The Moser spindle's chromatic number is at least $4$. -/
theorem chromaticNumber_ge_four : 4 ≤ graph.chromaticNumber := by
  by_contra h
  rw [not_le] at h
  have hle : graph.chromaticNumber ≤ 3 := by
    have : graph.chromaticNumber < (3 : ℕ∞) + 1 := h
    exact Order.le_of_lt_add_one this
  have : graph.Colorable 3 := by
    rw [show (3 : ℕ∞) = ((3 : ℕ) : ℕ∞) from rfl] at hle
    exact (SimpleGraph.chromaticNumber_le_iff_colorable).mp hle
  exact not_colorable_three this

/-! ### The unit-distance embedding into `EuclideanSpace ℝ (Fin 2)`

We work in the Euclidean plane `EuclideanSpace ℝ (Fin 2)`; the squared-norm formula
`dist !₂[x₀,y₀] !₂[x₁,y₁] = ((x₀ - x₁)² + (y₀ - y₁)²)^(1/2)` is what we need. The bridge
between Mathlib's `dist` and the squared-distance form used in our proofs is provided by
`dist_eq_one_iff` below. -/

/-- Notation for the Euclidean plane. -/
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- The unit-distance condition in the Euclidean plane, expressed as a squared-coordinate
equation. -/
private lemma dist_eq_one_iff {x₀ y₀ x₁ y₁ : ℝ} :
    dist (!₂[x₀, y₀] : Plane) (!₂[x₁, y₁] : Plane) = 1
      ↔ (x₀ - x₁) ^ 2 + (y₀ - y₁) ^ 2 = 1 := by
  simp [dist_eq_norm_sub, PiLp.norm_eq_of_L2]

/-- The standard embedding of the Moser spindle's $7$ vertices into the Euclidean plane.
The rotation angle for the second rhombus has $\cos = 5/6$, $\sin = \sqrt{11}/6$. -/
noncomputable def embed : Fin 7 → Plane
  | 0 => !₂[0, 0]
  | 1 => !₂[1, 0]
  | 2 => !₂[1/2, Real.sqrt 3 / 2]
  | 3 => !₂[3/2, Real.sqrt 3 / 2]
  | 4 => !₂[5/6, Real.sqrt 11 / 6]
  | 5 => !₂[(5 - Real.sqrt 33) / 12, (Real.sqrt 11 + 5 * Real.sqrt 3) / 12]
  | 6 => !₂[(15 - Real.sqrt 33) / 12, (3 * Real.sqrt 11 + 5 * Real.sqrt 3) / 12]

/-! #### Per-edge unit-distance lemmas

The 11 edges of the Moser spindle are checked one at a time. Edges of rhombus 1 use only
`Real.sqrt 3`. The edge `{0, 4}` uses `Real.sqrt 11`. Edges involving vertex `5` or `6` use
the multiplicative identity `Real.sqrt 3 * Real.sqrt 11 = Real.sqrt 33`. The two hardest
edges, `{5, 6}` and `{3, 6}`, require pre-simplifying $\Delta x$ and $\Delta y$ via `ring`
before invoking `nlinarith`.
-/

private theorem dist_embed_0_1 : dist (embed 0) (embed 1) = 1 := by
  rw [embed, embed, dist_eq_one_iff]; norm_num

private theorem dist_embed_0_2 : dist (embed 0) (embed 2) = 1 := by
  rw [embed, embed, dist_eq_one_iff]
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by positivity)
  nlinarith [h3]

private theorem dist_embed_1_2 : dist (embed 1) (embed 2) = 1 := by
  rw [embed, embed, dist_eq_one_iff]
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by positivity)
  nlinarith [h3]

private theorem dist_embed_1_3 : dist (embed 1) (embed 3) = 1 := by
  rw [embed, embed, dist_eq_one_iff]
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by positivity)
  nlinarith [h3]

private theorem dist_embed_2_3 : dist (embed 2) (embed 3) = 1 := by
  rw [embed, embed, dist_eq_one_iff]; ring

private theorem dist_embed_0_4 : dist (embed 0) (embed 4) = 1 := by
  rw [embed, embed, dist_eq_one_iff]
  have h11 : Real.sqrt 11 * Real.sqrt 11 = 11 := Real.mul_self_sqrt (by positivity)
  nlinarith [h11]

private theorem dist_embed_0_5 : dist (embed 0) (embed 5) = 1 := by
  rw [embed, embed, dist_eq_one_iff]
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by positivity)
  have h11 : Real.sqrt 11 * Real.sqrt 11 = 11 := Real.mul_self_sqrt (by positivity)
  have h33 : Real.sqrt 33 * Real.sqrt 33 = 33 := Real.mul_self_sqrt (by positivity)
  have h3_11 : Real.sqrt 3 * Real.sqrt 11 = Real.sqrt 33 := by
    rw [← Real.sqrt_mul (by positivity : (3 : ℝ) ≥ 0)]; norm_num
  nlinarith [h3, h11, h33, h3_11]

private theorem dist_embed_4_5 : dist (embed 4) (embed 5) = 1 := by
  rw [embed, embed, dist_eq_one_iff]
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by positivity)
  have h11 : Real.sqrt 11 * Real.sqrt 11 = 11 := Real.mul_self_sqrt (by positivity)
  have h33 : Real.sqrt 33 * Real.sqrt 33 = 33 := Real.mul_self_sqrt (by positivity)
  have h3_11 : Real.sqrt 3 * Real.sqrt 11 = Real.sqrt 33 := by
    rw [← Real.sqrt_mul (by positivity : (3 : ℝ) ≥ 0)]; norm_num
  nlinarith [h3, h11, h33, h3_11]

private theorem dist_embed_4_6 : dist (embed 4) (embed 6) = 1 := by
  rw [embed, embed, dist_eq_one_iff]
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by positivity)
  have h11 : Real.sqrt 11 * Real.sqrt 11 = 11 := Real.mul_self_sqrt (by positivity)
  have h33 : Real.sqrt 33 * Real.sqrt 33 = 33 := Real.mul_self_sqrt (by positivity)
  have h3_11 : Real.sqrt 3 * Real.sqrt 11 = Real.sqrt 33 := by
    rw [← Real.sqrt_mul (by positivity : (3 : ℝ) ≥ 0)]; norm_num
  nlinarith [h3, h11, h33, h3_11]

private theorem dist_embed_5_6 : dist (embed 5) (embed 6) = 1 := by
  rw [embed, embed, dist_eq_one_iff]
  have h_dx : (((5 : ℝ) - Real.sqrt 33) / 12 - ((15 : ℝ) - Real.sqrt 33) / 12) = -5/6 := by
    ring
  have h_dy : ((Real.sqrt 11 + 5 * Real.sqrt 3) / 12
               - (3 * Real.sqrt 11 + 5 * Real.sqrt 3) / 12)
             = -Real.sqrt 11 / 6 := by ring
  rw [h_dx, h_dy]
  have h11 : Real.sqrt 11 * Real.sqrt 11 = 11 := Real.mul_self_sqrt (by positivity)
  nlinarith [h11]

private theorem dist_embed_3_6 : dist (embed 3) (embed 6) = 1 := by
  rw [embed, embed, dist_eq_one_iff]
  have h_dx : ((3 : ℝ)/2 - ((15 : ℝ) - Real.sqrt 33) / 12)
            = (3 + Real.sqrt 33) / 12 := by ring
  have h_dy : (Real.sqrt 3 / 2 - (3 * Real.sqrt 11 + 5 * Real.sqrt 3) / 12)
            = (Real.sqrt 3 - 3 * Real.sqrt 11) / 12 := by ring
  rw [h_dx, h_dy]
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by positivity)
  have h11 : Real.sqrt 11 * Real.sqrt 11 = 11 := Real.mul_self_sqrt (by positivity)
  have h33 : Real.sqrt 33 * Real.sqrt 33 = 33 := Real.mul_self_sqrt (by positivity)
  have h3_11 : Real.sqrt 3 * Real.sqrt 11 = Real.sqrt 33 := by
    rw [← Real.sqrt_mul (by positivity : (3 : ℝ) ≥ 0)]; norm_num
  nlinarith [h3, h11, h33, h3_11]

/-- For every edge of the abstract Moser spindle, the embedding sends it to a pair of points
at unit distance in the Euclidean plane. -/
private theorem dist_embed_eq_one (i j : Fin 7) (hadj : adj i j = true) :
    dist (embed i) (embed j) = 1 := by
  fin_cases i <;> fin_cases j <;> simp_all [adj] <;> first
    | exact dist_embed_0_1 | (rw [dist_comm]; exact dist_embed_0_1)
    | exact dist_embed_0_2 | (rw [dist_comm]; exact dist_embed_0_2)
    | exact dist_embed_1_2 | (rw [dist_comm]; exact dist_embed_1_2)
    | exact dist_embed_1_3 | (rw [dist_comm]; exact dist_embed_1_3)
    | exact dist_embed_2_3 | (rw [dist_comm]; exact dist_embed_2_3)
    | exact dist_embed_0_4 | (rw [dist_comm]; exact dist_embed_0_4)
    | exact dist_embed_0_5 | (rw [dist_comm]; exact dist_embed_0_5)
    | exact dist_embed_4_5 | (rw [dist_comm]; exact dist_embed_4_5)
    | exact dist_embed_4_6 | (rw [dist_comm]; exact dist_embed_4_6)
    | exact dist_embed_5_6 | (rw [dist_comm]; exact dist_embed_5_6)
    | exact dist_embed_3_6 | (rw [dist_comm]; exact dist_embed_3_6)

/-- The first (x-) coordinate of the embedding, used to prove injectivity. -/
noncomputable def embedX (i : Fin 7) : ℝ := (embed i).ofLp 0

theorem embedX_eq : ∀ i : Fin 7, embedX i =
    match i with
    | 0 => 0
    | 1 => 1
    | 2 => 1/2
    | 3 => 3/2
    | 4 => 5/6
    | 5 => (5 - Real.sqrt 33) / 12
    | 6 => (15 - Real.sqrt 33) / 12 := by
  intro i
  fin_cases i <;> rfl

/-- The embedding `embed` is injective: all seven vertices have distinct first coordinates. -/
theorem embed_injective : embed.Injective := by
  -- Strategy: distinct first-coordinates suffice.
  have hxinj : Function.Injective embedX := by
    -- 33 is between 25 and 36, so 5 < √33 < 6.
    have h33_gt_5 : (5 : ℝ) < Real.sqrt 33 := by
      have h25 : Real.sqrt 25 = 5 := by
        rw [show (25 : ℝ) = 5 ^ 2 from by norm_num]
        exact Real.sqrt_sq (by norm_num)
      rw [← h25]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have h33_lt_6 : Real.sqrt 33 < 6 := by
      have h36 : Real.sqrt 36 = 6 := by
        rw [show (36 : ℝ) = 6 ^ 2 from by norm_num]
        exact Real.sqrt_sq (by norm_num)
      rw [← h36]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    intro i j heq
    rw [embedX_eq, embedX_eq] at heq
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | (exfalso; revert heq; norm_num; intro heq; nlinarith [h33_gt_5, h33_lt_6])
        | (exfalso; revert heq; norm_num)
  intro i j heq
  apply hxinj
  unfold embedX
  rw [heq]

/-- The standard unit-distance embedding of the Moser spindle into the Euclidean plane. -/
noncomputable def unitDistEmbedding : graph.UnitDistEmbedding Plane where
  p := ⟨embed, embed_injective⟩
  unit_dist {i j} h := by
    simp only [Function.Embedding.coeFn_mk]
    exact dist_embed_eq_one i j h

end MoserSpindle

end SimpleGraph
