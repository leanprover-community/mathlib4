/-
Copyright (c) 2026 Tianyu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianyu (forxhunter)
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto

/-!
# The abstract polymer model and the Kotecký–Preiss convergence criterion

This file develops the finite abstract polymer model of statistical mechanics: a graph
`G : SimpleGraph α` of *incompatibilities* between polymers, activities (weights) `w : α → R`,
and the partition function over a finite family `Λ : Finset α`

`G.indepPartitionFunction w Λ = ∑ S ⊆ Λ independent in G, ∏ v ∈ S, w v`.

As a graph invariant this is the **multivariate independence polynomial** of the subgraph
induced on `Λ`, evaluated at `w` (Scott–Sokal call it the independent-set polynomial; it is
also the grand-canonical partition function of the hard-core lattice gas on `G`).

The heart of the file is the convergence machinery of cluster-expansion theory for *signed*
activities: the classical sufficient criteria of Dobrushin and of Kotecký–Preiss, packaged as
structures, and the resulting positivity, ratio, and logarithmic bounds on the partition
function. The proofs follow the modern inductive route (Bissacot–Fernández–Procacci): a strong
induction on the polymer family through the deletion identity, with no analyticity or cluster
combinatorics.

For nonnegative activities all the bounds below are essentially unconditional
(`one_le_indepPartitionFunction`, `indepPartitionFunction_le_prod`); the criteria have content
only in the signed regime, where cancellations can make the partition function vanish.

## Main definitions

* `SimpleGraph.closedNeighborFinset G v`: the closed neighborhood `N[v] = {v} ∪ N(v)` as a
  `Finset`.
* `SimpleGraph.indepPartitionFunction G w Λ`: the polymer partition function, i.e. the
  multivariate independence polynomial of `G` restricted to `Λ` evaluated at `w`.
* `SimpleGraph.DobrushinCriterion G w x`: Dobrushin's condition — a damping ansatz
  `x : α → ℝ` with `0 ≤ x v < 1` and `|w v| ≤ x v * ∏ u ∈ N(v), (1 - x u)`.
* `SimpleGraph.KoteckyPreissCriterion G w a`: the Kotecký–Preiss condition — an entropy
  budget `a : α → ℝ` with `∑ u ∈ N[v], |w u| * exp (a u) ≤ a v`.

## Main results

* `SimpleGraph.indepPartitionFunction_deletion`: the deletion identity
  `Z Λ = Z (Λ.erase v) + w v * Z (Λ \ N[v])`, the induction backbone.
* `SimpleGraph.KoteckyPreissCriterion.toDobrushinCriterion`: Kotecký–Preiss implies Dobrushin,
  with the explicit ansatz `x v = 1 - exp (-(|w v| * exp (a v)))`.
* `SimpleGraph.DobrushinCriterion.indepPartitionFunction_pos`: under Dobrushin's criterion the
  partition function of every finite family is strictly positive (nonvanishing), for signed
  activities.
* `SimpleGraph.DobrushinCriterion.abs_log_sub_log_le`: the telescoped two-sided log-ratio
  bound `|log (Z Λ) - log (Z Λ')| ≤ ∑ v ∈ Λ \ Λ', -log (1 - x v)` for `Λ' ⊆ Λ`.
* `SimpleGraph.KoteckyPreissCriterion.indepPartitionFunction_pos` and
  `SimpleGraph.KoteckyPreissCriterion.abs_log_sub_log_le`: the finite Kotecký–Preiss theorem
  with the classical constants — positivity, `exp (-∑ a)`-ratio bounds, and
  `|log (Z Λ) - log (Z Λ')| ≤ ∑ v ∈ Λ \ Λ', |w v| * exp (a v) ≤ ∑ v ∈ Λ \ Λ', a v`.

## References

* R. Kotecký, D. Preiss, *Cluster expansion for abstract polymer models*,
  Comm. Math. Phys. 103 (1986), 491–498.
* R. L. Dobrushin, *Estimates of semi-invariants for the Ising model at low temperatures*,
  Amer. Math. Soc. Transl. 177 (1996), 59–81.
* R. Fernández, A. Procacci, *Cluster expansion for abstract polymer models: new bounds from
  an old approach*, Comm. Math. Phys. 274 (2007), 123–140.
* R. Bissacot, R. Fernández, A. Procacci, *On the convergence of cluster expansions for
  polymer gases*, J. Stat. Phys. 139 (2010), 598–617.
* A. D. Scott, A. D. Sokal, *The repulsive lattice gas, the independent-set polynomial, and
  the Lovász local lemma*, J. Stat. Phys. 118 (2005), 1151–1261.

## Tags

polymer model, cluster expansion, independence polynomial, Kotecký–Preiss, Dobrushin,
partition function, hard-core gas
-/

@[expose] public section

open Finset Real

namespace SimpleGraph

variable {α : Type*}

/-! ### Independent sets, membership form -/

section IsIndepSet

variable {G : SimpleGraph α}

/-- Two members of an independent set are never adjacent. Unlike the definitional
`Set.Pairwise`, this needs no distinctness hypothesis: adjacency is irreflexive. -/
theorem IsIndepSet.not_adj {s : Set α} (h : G.IsIndepSet s) {v u : α} (hv : v ∈ s)
    (hu : u ∈ s) : ¬G.Adj v u := by
  rcases eq_or_ne v u with rfl | hne
  · exact G.irrefl
  · exact h hv hu hne

/-- Independence of a `Finset` of vertices, in unconditional membership form. -/
theorem isIndepSet_coe_iff {S : Finset α} :
    G.IsIndepSet (S : Set α) ↔ ∀ v ∈ S, ∀ u ∈ S, ¬G.Adj v u :=
  ⟨fun h _ hv _ hu => h.not_adj (mem_coe.mpr hv) (mem_coe.mpr hu),
    fun h v hv u hu _ => h v (mem_coe.mp hv) u (mem_coe.mp hu)⟩

end IsIndepSet

/-! ### Closed neighborhoods as finsets -/

section ClosedNeighborFinset

variable [DecidableEq α] (G : SimpleGraph α) (v : α) [Fintype (G.neighborSet v)]

/-- The closed neighborhood of a vertex, as a `Finset`: the vertex together with its
neighbors. In the polymer-model reading this is the set of polymers incompatible with `v`,
including `v` itself. -/
def closedNeighborFinset : Finset α := insert v (G.neighborFinset v)

theorem mem_closedNeighborFinset {u : α} :
    u ∈ G.closedNeighborFinset v ↔ u = v ∨ G.Adj v u := by
  simp [closedNeighborFinset, mem_neighborFinset]

theorem self_mem_closedNeighborFinset : v ∈ G.closedNeighborFinset v :=
  mem_insert_self _ _

theorem neighborFinset_subset_closedNeighborFinset :
    G.neighborFinset v ⊆ G.closedNeighborFinset v :=
  subset_insert _ _

end ClosedNeighborFinset

/-! ### The partition function -/

section IndepPartitionFunction

variable [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]
variable {R : Type*} [CommSemiring R]

/-- The polymer partition function of `G` on the finite family `Λ` with activities `w`: the
sum over independent subsets of `Λ` of the product of their activities. As a graph invariant
this is the multivariate independence polynomial of the subgraph induced on `Λ`, evaluated at
`w`; in statistical mechanics it is the partition function of the abstract polymer model
(equivalently, of the hard-core lattice gas) with incompatibility graph `G`. -/
def indepPartitionFunction (w : α → R) (Λ : Finset α) : R :=
  ∑ S ∈ Λ.powerset.filter (fun S : Finset α => G.IsIndepSet (S : Set α)), ∏ v ∈ S, w v

@[simp]
theorem indepPartitionFunction_empty (w : α → R) : G.indepPartitionFunction w ∅ = 1 := by
  simp [indepPartitionFunction, filter_singleton]

/-- **Deletion identity.** Splitting the sum according to whether the distinguished polymer
`v` occurs: `Z Λ = Z (Λ.erase v) + w v * Z (Λ \ N[v])`. Every convergence proof in this file
inducts through this identity. -/
theorem indepPartitionFunction_deletion (w : α → R) {Λ : Finset α} {v : α}
    [Fintype (G.neighborSet v)] (hv : v ∈ Λ) :
    G.indepPartitionFunction w Λ =
      G.indepPartitionFunction w (Λ.erase v) +
        w v * G.indepPartitionFunction w (Λ \ G.closedNeighborFinset v) := by
  classical
  rw [indepPartitionFunction,
    ← Finset.sum_filter_add_sum_filter_not
      (Λ.powerset.filter (fun S : Finset α => G.IsIndepSet (S : Set α))) (fun S => v ∉ S)]
  congr 1
  · -- families avoiding `v` = families inside `Λ.erase v`
    rw [Finset.filter_filter, indepPartitionFunction]
    apply Finset.sum_congr _ fun _ _ => rfl
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_erase]
    tauto
  · -- families containing `v` = `v` joined to families avoiding `N[v]`
    rw [Finset.filter_filter, indepPartitionFunction, Finset.mul_sum]
    refine Finset.sum_bij' (fun S _ => S.erase v) (fun T _ => insert v T) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset, not_not] at hS
      obtain ⟨hSΛ, hSc, hvS⟩ := hS
      simp only [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨fun u hu => ?_, hSc.mono (coe_subset.mpr (Finset.erase_subset _ _))⟩
      obtain ⟨huv, huS⟩ := Finset.mem_erase.mp hu
      refine Finset.mem_sdiff.mpr ⟨hSΛ huS, fun hmem => ?_⟩
      rcases (G.mem_closedNeighborFinset v).mp hmem with h | h
      · exact huv h
      · exact hSc.not_adj (mem_coe.mpr hvS) (mem_coe.mpr huS) h
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_powerset] at hT
      obtain ⟨hTsub, hTc⟩ := hT
      simp only [Finset.mem_filter, Finset.mem_powerset, not_not]
      refine ⟨Finset.insert_subset hv (hTsub.trans Finset.sdiff_subset), ?_,
        Finset.mem_insert_self _ _⟩
      rw [isIndepSet_coe_iff]
      intro y hy z hz
      rcases Finset.mem_insert.mp hy with rfl | hyT
      · rcases Finset.mem_insert.mp hz with rfl | hzT
        · exact G.irrefl
        · exact fun h => (Finset.mem_sdiff.mp (hTsub hzT)).2
            ((G.mem_closedNeighborFinset y).mpr (Or.inr h))
      · rcases Finset.mem_insert.mp hz with rfl | hzT
        · exact fun h => (Finset.mem_sdiff.mp (hTsub hyT)).2
            ((G.mem_closedNeighborFinset z).mpr (Or.inr h.symm))
        · exact hTc.not_adj (mem_coe.mpr hyT) (mem_coe.mpr hzT)
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset, not_not] at hS
      exact Finset.insert_erase hS.2.2
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_powerset] at hT
      exact Finset.erase_insert fun hmem =>
        (Finset.mem_sdiff.mp (hT.1 hmem)).2 (G.self_mem_closedNeighborFinset v)
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset, not_not] at hS
      exact (Finset.mul_prod_erase _ _ hS.2.2).symm

/-- On a single polymer the partition function is `1 + w v`. -/
theorem indepPartitionFunction_singleton (w : α → R) (v : α) :
    G.indepPartitionFunction w {v} = 1 + w v := by
  have hem : G.IsIndepSet ((∅ : Finset α) : Set α) := by simp
  have hv : G.IsIndepSet (({v} : Finset α) : Set α) := by simp
  have hpow : ({v} : Finset α).powerset = {∅, {v}} := by
    ext S
    simp [Finset.subset_singleton_iff]
  rw [indepPartitionFunction, hpow, Finset.filter_insert, ite_eq_left hem,
    filter_singleton, ite_eq_left hv,
    Finset.sum_insert (by simp [(Finset.singleton_ne_empty v).symm]),
    Finset.sum_singleton, Finset.prod_empty, Finset.prod_singleton]

/-! #### Estimates for nonnegative activities

For nonnegative activities the partition function is monotone, at least `1`, and dominated
by the free product `∏ (1 + w v)` — all with no convergence criterion whatsoever. The
convergence criteria below only have content for signed activities. -/

theorem indepPartitionFunction_nonneg {w : α → ℝ} (hw : ∀ v, 0 ≤ w v) (Λ : Finset α) :
    0 ≤ G.indepPartitionFunction w Λ :=
  Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun v _ => hw v

/-- The empty family always contributes `1`. -/
theorem one_le_indepPartitionFunction {w : α → ℝ} (hw : ∀ v, 0 ≤ w v) (Λ : Finset α) :
    1 ≤ G.indepPartitionFunction w Λ := by
  have hempty : (∅ : Finset α) ∈
      Λ.powerset.filter (fun S : Finset α => G.IsIndepSet (S : Set α)) := by
    simp [isIndepSet_coe_iff]
  simpa [indepPartitionFunction] using
    Finset.single_le_sum (f := fun S => ∏ v ∈ S, w v)
      (fun S _ => Finset.prod_nonneg fun v _ => hw v) hempty

/-- Monotonicity in the polymer family, for nonnegative activities. -/
theorem indepPartitionFunction_mono {w : α → ℝ} (hw : ∀ v, 0 ≤ w v) {Λ' Λ : Finset α}
    (h : Λ' ⊆ Λ) : G.indepPartitionFunction w Λ' ≤ G.indepPartitionFunction w Λ := by
  simp only [indepPartitionFunction]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset_filter _ (Finset.powerset_mono.mpr h))
    fun S _ _ => Finset.prod_nonneg fun v _ => hw v

/-- Dropping the independence constraint: `Z Λ ≤ ∏ v ∈ Λ, (1 + w v)` for nonnegative
activities. -/
theorem indepPartitionFunction_le_prod {w : α → ℝ} (hw : ∀ v, 0 ≤ w v) (Λ : Finset α) :
    G.indepPartitionFunction w Λ ≤ ∏ v ∈ Λ, (1 + w v) := by
  have expand : ∏ v ∈ Λ, (w v + 1) = ∑ S ∈ Λ.powerset, ∏ v ∈ S, w v := by
    rw [Finset.prod_add]
    exact Finset.sum_congr rfl fun S _ => by simp
  calc G.indepPartitionFunction w Λ
      ≤ ∑ S ∈ Λ.powerset, ∏ v ∈ S, w v := by
        simp only [indepPartitionFunction]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun S _ _ => Finset.prod_nonneg fun v _ => hw v
    _ = ∏ v ∈ Λ, (w v + 1) := expand.symm
    _ = ∏ v ∈ Λ, (1 + w v) := by simp [add_comm]

/-- The signed partition function is dominated by the one with absolute activities. -/
theorem abs_indepPartitionFunction_le (w : α → ℝ) (Λ : Finset α) :
    |G.indepPartitionFunction w Λ| ≤ G.indepPartitionFunction (fun v => |w v|) Λ := by
  simp only [indepPartitionFunction]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun S _ => ?_)
  rw [Finset.abs_prod]

end IndepPartitionFunction

/-! ### The convergence criteria -/

/-- **Dobrushin's convergence condition** for the polymer model with signed activities `w`:
a damping ansatz `x` assigning each polymer a factor in `[0, 1)`, such that each activity is
bounded by its own damping factor times the damping the ansatz grants its neighborhood. This
is the condition the convergence induction consumes directly. -/
structure DobrushinCriterion (G : SimpleGraph α) [G.LocallyFinite] (w x : α → ℝ) : Prop where
  /-- The damping factors are nonnegative. -/
  damping_nonneg : ∀ v, 0 ≤ x v
  /-- The damping factors are strictly below `1`. -/
  damping_lt_one : ∀ v, x v < 1
  /-- Each activity is damped by its own factor times the neighborhood damping. -/
  activity_damped : ∀ v, |w v| ≤ x v * ∏ u ∈ G.neighborFinset v, (1 - x u)

/-- **The Kotecký–Preiss condition** for the polymer model with signed activities `w`: an
entropy budget `a` such that for every polymer the `exp a`-boosted total activity of its
closed neighborhood `N[v]` stays within the budget of `v`. The sum runs over the *closed*
neighborhood; the open-neighborhood variant of the condition is genuinely insufficient. -/
structure KoteckyPreissCriterion [DecidableEq α] (G : SimpleGraph α) [G.LocallyFinite]
    (w a : α → ℝ) : Prop where
  /-- The entropy budget is nonnegative. -/
  budget_nonneg : ∀ v, 0 ≤ a v
  /-- The boosted activity of each closed neighborhood is within the center's budget. -/
  neighborhood_budget : ∀ v, ∑ u ∈ G.closedNeighborFinset v, |w u| * exp (a u) ≤ a v

namespace KoteckyPreissCriterion

variable [DecidableEq α] {G : SimpleGraph α} [G.LocallyFinite] {w a : α → ℝ}

/-- The Kotecký–Preiss budget dominates each polymer's own boosted activity. -/
theorem abs_mul_exp_le (h : G.KoteckyPreissCriterion w a) (v : α) :
    |w v| * exp (a v) ≤ a v :=
  le_trans
    (Finset.single_le_sum (f := fun u => |w u| * exp (a u))
      (fun _ _ => mul_nonneg (abs_nonneg _) (exp_pos _).le)
      (G.self_mem_closedNeighborFinset v))
    (h.neighborhood_budget v)

/-- The open-neighborhood part of the Kotecký–Preiss budget. -/
private theorem sum_neighborFinset_bound (h : G.KoteckyPreissCriterion w a) (v : α) :
    ∑ u ∈ G.neighborFinset v, |w u| * exp (a u) ≤ a v - |w v| * exp (a v) := by
  have hsum := h.neighborhood_budget v
  rw [closedNeighborFinset, Finset.sum_insert (G.notMem_neighborFinset_self v)] at hsum
  linarith

/-- **Kotecký–Preiss implies Dobrushin**, with the explicit damping ansatz
`x v = 1 - exp (-(|w v| * exp (a v)))`.

The textbook-looking substitution `x v = 1 - exp (-(a v))` does not work pointwise; this one
does because `1 - exp (-b) ≥ b * exp (-b)` turns the damping requirement into exactly the
closed-neighborhood Kotecký–Preiss budget at `v`. -/
theorem toDobrushinCriterion (h : G.KoteckyPreissCriterion w a) :
    G.DobrushinCriterion w fun v => 1 - exp (-(|w v| * exp (a v))) := by
  set b : α → ℝ := fun v => |w v| * exp (a v)
  have hb_nonneg : ∀ v, 0 ≤ b v := fun v => mul_nonneg (abs_nonneg _) (exp_pos _).le
  refine ⟨?_, ?_, ?_⟩
  · intro v
    have hle : exp (-(b v)) ≤ 1 := by
      rw [exp_le_one_iff]; linarith [hb_nonneg v]
    change 0 ≤ 1 - exp (-(b v))
    linarith [hle]
  · intro v
    change 1 - exp (-(b v)) < 1
    linarith [exp_pos (-(b v))]
  · intro v
    change |w v| ≤ (1 - exp (-(b v))) * ∏ u ∈ G.neighborFinset v, (1 - (1 - exp (-(b u))))
    have hprod : ∏ u ∈ G.neighborFinset v, (1 - (1 - exp (-(b u)))) =
        exp (-(∑ u ∈ G.neighborFinset v, b u)) := by
      rw [← Finset.sum_neg_distrib, Real.exp_sum]
      exact Finset.prod_congr rfl fun u _ => by ring_nf
    rw [hprod]
    -- Goal: `|w v| ≤ (1 - exp (-(b v))) * exp (-∑ N(v) b)`
    have hkey : b v * exp (-(b v)) ≤ 1 - exp (-(b v)) := by
      have h1 : b v + 1 ≤ exp (b v) := add_one_le_exp _
      have h2 : 0 < exp (-(b v)) := exp_pos _
      have h3 : exp (b v) * exp (-(b v)) = 1 := by rw [← exp_add]; simp
      nlinarith [h1, h2, h3]
    have hbudget : ∑ u ∈ G.neighborFinset v, b u ≤ a v - b v :=
      h.sum_neighborFinset_bound v
    have hmono : exp (-(a v - b v)) ≤ exp (-(∑ u ∈ G.neighborFinset v, b u)) := by
      rw [exp_le_exp]; linarith
    have hchain : |w v| ≤ b v * exp (-(b v)) * exp (-(a v - b v)) := by
      have hbeq : b v = |w v| * exp (a v) := rfl
      have hsplit : b v * exp (-(b v)) * exp (-(a v - b v)) =
          |w v| * exp (a v + (-(b v) + -(a v - b v))) := by
        rw [exp_add, exp_add, hbeq]; ring
      have hzero : a v + (-(b v) + -(a v - b v)) = 0 := by ring
      rw [hsplit, hzero, exp_zero, mul_one]
    calc |w v| ≤ b v * exp (-(b v)) * exp (-(a v - b v)) := hchain
      _ ≤ (1 - exp (-(b v))) * exp (-(a v - b v)) :=
          mul_le_mul_of_nonneg_right hkey (exp_pos _).le
      _ ≤ (1 - exp (-(b v))) * exp (-(∑ u ∈ G.neighborFinset v, b u)) := by
          have hle : exp (-(b v)) ≤ 1 := by
            rw [exp_le_one_iff]; linarith [hb_nonneg v]
          exact mul_le_mul_of_nonneg_left hmono (by linarith [hle])

end KoteckyPreissCriterion

namespace DobrushinCriterion

variable {G : SimpleGraph α} [G.LocallyFinite] {w x : α → ℝ}

theorem one_sub_pos (h : G.DobrushinCriterion w x) (v : α) : 0 < 1 - x v := by
  linarith [h.damping_lt_one v]

/-- Dropping neighborhood factors only weakens the Dobrushin damping. -/
theorem abs_le_mul_prod (h : G.DobrushinCriterion w x) (v : α) {D : Finset α}
    (hD : D ⊆ G.neighborFinset v) : |w v| ≤ x v * ∏ u ∈ D, (1 - x u) := by
  classical
  refine (h.activity_damped v).trans ?_
  rw [← Finset.prod_sdiff hD]
  have h1 : ∏ u ∈ G.neighborFinset v \ D, (1 - x u) ≤ 1 :=
    Finset.prod_le_one (fun u _ => (h.one_sub_pos u).le)
      (fun u _ => by linarith [h.damping_nonneg u])
  have h2 : 0 ≤ ∏ u ∈ D, (1 - x u) := Finset.prod_nonneg fun u _ => (h.one_sub_pos u).le
  exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left h2 h1) (h.damping_nonneg v)

end DobrushinCriterion

/-! ### The convergence engine

A strong induction on the polymer family through the deletion identity, following
Bissacot–Fernández–Procacci. The private lemmas below telescope the one-step ratio bounds and
run the induction; the public results follow. -/

section Engine

variable [DecidableEq α] {G : SimpleGraph α} [DecidableRel G.Adj] [G.LocallyFinite]

omit [G.LocallyFinite] in
/-- One-step lower ratio bounds telescope over a removed subfamily. Stated with the one-step
bounds as a hypothesis so that it can be invoked both inside the strong induction (from the
inductive hypothesis) and globally afterwards. -/
private theorem telescope_lower {w x : α → ℝ} (hx1 : ∀ v, x v ≤ 1) {M : Finset α}
    (H : ∀ Λ ⊆ M, ∀ v ∈ Λ,
      (1 - x v) * G.indepPartitionFunction w (Λ.erase v) ≤ G.indepPartitionFunction w Λ)
    (D : Finset α) (hD : D ⊆ M) :
    (∏ v ∈ D, (1 - x v)) * G.indepPartitionFunction w (M \ D) ≤
      G.indepPartitionFunction w M := by
  classical
  revert hD
  induction D using Finset.induction_on with
  | empty => intro _; simp
  | @insert v D hvD ih =>
    intro hins
    have hD' : D ⊆ M := (Finset.subset_insert v D).trans hins
    have hvM : v ∈ M := hins (Finset.mem_insert_self v D)
    have hvMD : v ∈ M \ D := Finset.mem_sdiff.mpr ⟨hvM, hvD⟩
    have hrw : (M \ D).erase v = M \ insert v D := by
      ext u
      simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]
      tauto
    have hprod_nonneg : 0 ≤ ∏ u ∈ D, (1 - x u) :=
      Finset.prod_nonneg fun u _ => by linarith [hx1 u]
    calc (∏ u ∈ insert v D, (1 - x u)) * G.indepPartitionFunction w (M \ insert v D)
        = (∏ u ∈ D, (1 - x u)) *
            ((1 - x v) * G.indepPartitionFunction w (M \ insert v D)) := by
          rw [Finset.prod_insert hvD]; ring
      _ ≤ (∏ u ∈ D, (1 - x u)) * G.indepPartitionFunction w (M \ D) := by
          apply mul_le_mul_of_nonneg_left _ hprod_nonneg
          calc (1 - x v) * G.indepPartitionFunction w (M \ insert v D)
              = (1 - x v) * G.indepPartitionFunction w ((M \ D).erase v) := by rw [hrw]
            _ ≤ G.indepPartitionFunction w (M \ D) := H (M \ D) Finset.sdiff_subset v hvMD
      _ ≤ G.indepPartitionFunction w M := ih hD'

omit [G.LocallyFinite] in
/-- One-step upper ratio bounds telescope over a removed subfamily. -/
private theorem telescope_upper {w x : α → ℝ} (hx0 : ∀ v, 0 ≤ x v) {M : Finset α}
    (H : ∀ Λ ⊆ M, ∀ v ∈ Λ,
      G.indepPartitionFunction w Λ ≤ (1 + x v) * G.indepPartitionFunction w (Λ.erase v))
    (D : Finset α) (hD : D ⊆ M) :
    G.indepPartitionFunction w M ≤
      (∏ v ∈ D, (1 + x v)) * G.indepPartitionFunction w (M \ D) := by
  classical
  revert hD
  induction D using Finset.induction_on with
  | empty => intro _; simp
  | @insert v D hvD ih =>
    intro hins
    have hD' : D ⊆ M := (Finset.subset_insert v D).trans hins
    have hvM : v ∈ M := hins (Finset.mem_insert_self v D)
    have hvMD : v ∈ M \ D := Finset.mem_sdiff.mpr ⟨hvM, hvD⟩
    have hrw : (M \ D).erase v = M \ insert v D := by
      ext u
      simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]
      tauto
    have hprod_nonneg : 0 ≤ ∏ u ∈ D, (1 + x u) :=
      Finset.prod_nonneg fun u _ => by linarith [hx0 u]
    calc G.indepPartitionFunction w M
        ≤ (∏ u ∈ D, (1 + x u)) * G.indepPartitionFunction w (M \ D) := ih hD'
      _ ≤ (∏ u ∈ D, (1 + x u)) *
            ((1 + x v) * G.indepPartitionFunction w (M \ insert v D)) := by
          apply mul_le_mul_of_nonneg_left _ hprod_nonneg
          have := H (M \ D) Finset.sdiff_subset v hvMD
          rwa [hrw] at this
      _ = (∏ u ∈ insert v D, (1 + x u)) * G.indepPartitionFunction w (M \ insert v D) := by
          rw [Finset.prod_insert hvD]; ring

/-- The inductive claim of the convergence engine: positivity together with the two-sided
one-step ratio bound at every polymer of the family. -/
private def EngineClaim (G : SimpleGraph α) [DecidableRel G.Adj] (w x : α → ℝ)
    (Λ : Finset α) : Prop :=
  0 < G.indepPartitionFunction w Λ ∧ ∀ v ∈ Λ,
    (1 - x v) * G.indepPartitionFunction w (Λ.erase v) ≤ G.indepPartitionFunction w Λ ∧
      G.indepPartitionFunction w Λ ≤ (1 + x v) * G.indepPartitionFunction w (Λ.erase v)

/-- The engine induction: strong induction on the polymer family through the deletion
identity; the Dobrushin condition closes the one-step estimate against the telescoped
inductive bounds. -/
private theorem engine {w x : α → ℝ} (h : G.DobrushinCriterion w x) :
    ∀ Λ : Finset α, EngineClaim G w x Λ := by
  classical
  intro Λ₀
  refine Finset.strongInductionOn Λ₀ ?_
  intro Λ IH
  -- The two-sided one-step bound at each `v ∈ Λ`, from the inductive hypothesis on `Λ \ v`.
  have key : ∀ v ∈ Λ,
      (1 - x v) * G.indepPartitionFunction w (Λ.erase v) ≤ G.indepPartitionFunction w Λ ∧
        G.indepPartitionFunction w Λ ≤
          (1 + x v) * G.indepPartitionFunction w (Λ.erase v) := by
    intro v hv
    have hM : Λ.erase v ⊂ Λ := Finset.erase_ssubset hv
    -- Telescope the inductive lower one-step bounds inside `Λ.erase v`.
    have Hlow : ∀ Λ' ⊆ Λ.erase v, ∀ u ∈ Λ',
        (1 - x u) * G.indepPartitionFunction w (Λ'.erase u) ≤
          G.indepPartitionFunction w Λ' := by
      intro Λ' hΛ' u hu
      have : Λ' ⊂ Λ := Finset.ssubset_of_subset_of_ssubset hΛ' hM
      exact ((IH _ this).2 u hu).1
    set D₀ : Finset α := G.neighborFinset v ∩ Λ.erase v with hD₀def
    have hD₀sub : D₀ ⊆ Λ.erase v := Finset.inter_subset_right
    have hsdiff : Λ.erase v \ D₀ = Λ \ G.closedNeighborFinset v := by
      ext u
      simp only [hD₀def, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_inter,
        mem_closedNeighborFinset, SimpleGraph.mem_neighborFinset]
      tauto
    have htele := telescope_lower (fun u => (h.damping_lt_one u).le) Hlow D₀ hD₀sub
    rw [hsdiff] at htele
    have hNpos : 0 < G.indepPartitionFunction w (Λ \ G.closedNeighborFinset v) := by
      have hsub : Λ \ G.closedNeighborFinset v ⊂ Λ := by
        refine Finset.ssubset_iff_of_subset Finset.sdiff_subset |>.mpr ?_
        exact ⟨v, hv, fun hmem =>
          (Finset.mem_sdiff.mp hmem).2 (G.self_mem_closedNeighborFinset v)⟩
      exact (IH _ hsub).1
    -- The Dobrushin estimate: `|w v| * Z (Λ \ N[v]) ≤ x v * Z (Λ.erase v)`.
    have hdamp : |w v| * G.indepPartitionFunction w (Λ \ G.closedNeighborFinset v) ≤
        x v * G.indepPartitionFunction w (Λ.erase v) := by
      have h1 : |w v| ≤ x v * ∏ u ∈ D₀, (1 - x u) :=
        h.abs_le_mul_prod v Finset.inter_subset_left
      calc |w v| * G.indepPartitionFunction w (Λ \ G.closedNeighborFinset v)
          ≤ (x v * ∏ u ∈ D₀, (1 - x u)) *
              G.indepPartitionFunction w (Λ \ G.closedNeighborFinset v) :=
            mul_le_mul_of_nonneg_right h1 hNpos.le
        _ = x v * ((∏ u ∈ D₀, (1 - x u)) *
              G.indepPartitionFunction w (Λ \ G.closedNeighborFinset v)) := by ring
        _ ≤ x v * G.indepPartitionFunction w (Λ.erase v) :=
            mul_le_mul_of_nonneg_left htele (h.damping_nonneg v)
    -- Assemble through the deletion identity.
    have hdel := G.indepPartitionFunction_deletion w hv
    have habs : |w v * G.indepPartitionFunction w (Λ \ G.closedNeighborFinset v)| ≤
        x v * G.indepPartitionFunction w (Λ.erase v) := by
      rw [abs_mul, abs_of_pos hNpos]
      exact hdamp
    have hpair := abs_le.mp habs
    constructor
    · nlinarith [hpair.1, hpair.2, hdel]
    · nlinarith [hpair.1, hpair.2, hdel]
  refine ⟨?_, key⟩
  rcases Finset.eq_empty_or_nonempty Λ with rfl | ⟨v, hv⟩
  · simp
  · have hM : Λ.erase v ⊂ Λ := Finset.erase_ssubset hv
    have hMpos : 0 < G.indepPartitionFunction w (Λ.erase v) := (IH _ hM).1
    have hlow := (key v hv).1
    linarith [hlow, mul_pos (h.one_sub_pos v) hMpos]

namespace DobrushinCriterion

variable {w x : α → ℝ}

/-- **Nonvanishing** of the polymer partition function for signed activities under
Dobrushin's criterion. (For nonnegative activities this is unconditional; the criterion is
what buys it on the signed domain.) -/
theorem indepPartitionFunction_pos (h : G.DobrushinCriterion w x) (Λ : Finset α) :
    0 < G.indepPartitionFunction w Λ :=
  (engine h Λ).1

/-- The one-step lower ratio bound: `(1 - x v) * Z (Λ.erase v) ≤ Z Λ`. -/
theorem mul_indepPartitionFunction_erase_le (h : G.DobrushinCriterion w x) {Λ : Finset α}
    {v : α} (hv : v ∈ Λ) :
    (1 - x v) * G.indepPartitionFunction w (Λ.erase v) ≤ G.indepPartitionFunction w Λ :=
  ((engine h Λ).2 v hv).1

/-- The one-step upper ratio bound: `Z Λ ≤ (1 + x v) * Z (Λ.erase v)`. -/
theorem indepPartitionFunction_le_mul_erase (h : G.DobrushinCriterion w x) {Λ : Finset α}
    {v : α} (hv : v ∈ Λ) :
    G.indepPartitionFunction w Λ ≤ (1 + x v) * G.indepPartitionFunction w (Λ.erase v) :=
  ((engine h Λ).2 v hv).2

/-- The restricted-vs-full ratio bound, lower direction:
`(∏ v ∈ Λ \ Λ', (1 - x v)) * Z Λ' ≤ Z Λ` for `Λ' ⊆ Λ`. -/
theorem prod_mul_indepPartitionFunction_le (h : G.DobrushinCriterion w x) {Λ' Λ : Finset α}
    (hsub : Λ' ⊆ Λ) :
    (∏ v ∈ Λ \ Λ', (1 - x v)) * G.indepPartitionFunction w Λ' ≤
      G.indepPartitionFunction w Λ := by
  have := telescope_lower (G := G) (fun u => (h.damping_lt_one u).le)
    (fun Λ'' _ u hu => h.mul_indepPartitionFunction_erase_le hu) (Λ \ Λ')
    Finset.sdiff_subset
  rwa [Finset.sdiff_sdiff_eq_self hsub] at this

/-- The restricted-vs-full ratio bound, upper direction:
`Z Λ ≤ (∏ v ∈ Λ \ Λ', (1 + x v)) * Z Λ'` for `Λ' ⊆ Λ`. -/
theorem indepPartitionFunction_le_prod_mul (h : G.DobrushinCriterion w x) {Λ' Λ : Finset α}
    (hsub : Λ' ⊆ Λ) :
    G.indepPartitionFunction w Λ ≤
      (∏ v ∈ Λ \ Λ', (1 + x v)) * G.indepPartitionFunction w Λ' := by
  have := telescope_upper (G := G) h.damping_nonneg
    (fun Λ'' _ u hu => h.indepPartitionFunction_le_mul_erase hu) (Λ \ Λ')
    Finset.sdiff_subset
  rwa [Finset.sdiff_sdiff_eq_self hsub] at this

/-- **The telescoped log-ratio bound** under Dobrushin's criterion: for `Λ' ⊆ Λ`,
`|log (Z Λ) - log (Z Λ')| ≤ ∑ v ∈ Λ \ Λ', -log (1 - x v)`. -/
theorem abs_log_sub_log_le (h : G.DobrushinCriterion w x) {Λ' Λ : Finset α}
    (hsub : Λ' ⊆ Λ) :
    |log (G.indepPartitionFunction w Λ) - log (G.indepPartitionFunction w Λ')| ≤
      ∑ v ∈ Λ \ Λ', -log (1 - x v) := by
  have hZ := h.indepPartitionFunction_pos Λ
  have hZ' := h.indepPartitionFunction_pos Λ'
  have hprod_lower_pos : 0 < ∏ v ∈ Λ \ Λ', (1 - x v) :=
    Finset.prod_pos fun v _ => h.one_sub_pos v
  have hprod_upper_pos : 0 < ∏ v ∈ Λ \ Λ', (1 + x v) :=
    Finset.prod_pos fun v _ => by linarith [h.damping_nonneg v]
  rw [abs_le]
  constructor
  · -- lower: `log (Z Λ) ≥ ∑ log (1 - x) + log (Z Λ')`
    have hlog := (Real.log_le_log_iff (mul_pos hprod_lower_pos hZ') hZ).mpr
      (h.prod_mul_indepPartitionFunction_le hsub)
    rw [Real.log_mul hprod_lower_pos.ne' hZ'.ne',
      Real.log_prod (fun v _ => (h.one_sub_pos v).ne')] at hlog
    have hneg : -∑ v ∈ Λ \ Λ', -log (1 - x v) = ∑ v ∈ Λ \ Λ', log (1 - x v) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun v _ => neg_neg _
    linarith [hlog, hneg]
  · -- upper: `log (Z Λ) ≤ ∑ log (1 + x) + log (Z Λ') ≤ ∑ -log (1 - x) + log (Z Λ')`
    have hlog := (Real.log_le_log_iff hZ (mul_pos hprod_upper_pos hZ')).mpr
      (h.indepPartitionFunction_le_prod_mul hsub)
    rw [Real.log_mul hprod_upper_pos.ne' hZ'.ne',
      Real.log_prod (fun v _ =>
        (by linarith [h.damping_nonneg v] : (0 : ℝ) < 1 + x v).ne')] at hlog
    have hpt : ∀ v ∈ Λ \ Λ', log (1 + x v) ≤ -log (1 - x v) := by
      intro v _
      have h1 : 0 < 1 - x v := h.one_sub_pos v
      have h0 : 0 ≤ x v := h.damping_nonneg v
      have hmul : (1 + x v) * (1 - x v) ≤ 1 := by nlinarith [h0, h1]
      have hlog2 : log ((1 + x v) * (1 - x v)) ≤ 0 :=
        Real.log_nonpos (by nlinarith [h0, h1]) hmul
      rw [Real.log_mul (by linarith : (0 : ℝ) < 1 + x v).ne' h1.ne'] at hlog2
      linarith
    linarith [hlog, Finset.sum_le_sum hpt]

end DobrushinCriterion

/-! ### The Kotecký–Preiss theorem, finite form

Every engine conclusion under the Kotecký–Preiss condition, with the classical constants:
the damping ansatz `x v = 1 - exp (-(|w v| * exp (a v)))` turns `-log (1 - x v)` into
exactly the classical increment `|w v| * exp (a v) ≤ a v`. -/

namespace KoteckyPreissCriterion

variable {w a : α → ℝ}

/-- **The Kotecký–Preiss theorem, positivity**: under the Kotecký–Preiss budget the signed
partition function is strictly positive on every finite family. -/
theorem indepPartitionFunction_pos (h : G.KoteckyPreissCriterion w a) (Λ : Finset α) :
    0 < G.indepPartitionFunction w Λ :=
  h.toDobrushinCriterion.indepPartitionFunction_pos Λ

/-- **The Kotecký–Preiss ratio bound, lower direction**, with the classical constant:
`exp (-∑ v ∈ Λ \ Λ', a v) * Z Λ' ≤ Z Λ` for `Λ' ⊆ Λ`. -/
theorem exp_neg_mul_indepPartitionFunction_le (h : G.KoteckyPreissCriterion w a)
    {Λ' Λ : Finset α} (hsub : Λ' ⊆ Λ) :
    exp (-∑ v ∈ Λ \ Λ', a v) * G.indepPartitionFunction w Λ' ≤
      G.indepPartitionFunction w Λ := by
  have hbase := h.toDobrushinCriterion.prod_mul_indepPartitionFunction_le hsub
  have hZ' := (h.toDobrushinCriterion.indepPartitionFunction_pos Λ').le
  refine le_trans (mul_le_mul_of_nonneg_right ?_ hZ') hbase
  -- `exp (-∑ a) ≤ ∏ (1 - x) = exp (-∑ |w| * exp a)`
  change exp (-∑ v ∈ Λ \ Λ', a v) ≤
    ∏ v ∈ Λ \ Λ', (1 - (1 - exp (-(|w v| * exp (a v)))))
  have hprod : ∏ v ∈ Λ \ Λ', (1 - (1 - exp (-(|w v| * exp (a v))))) =
      exp (-(∑ v ∈ Λ \ Λ', |w v| * exp (a v))) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    exact Finset.prod_congr rfl fun v _ => by ring_nf
  rw [hprod, exp_le_exp, neg_le_neg_iff]
  exact Finset.sum_le_sum fun v _ => h.abs_mul_exp_le v

/-- **The Kotecký–Preiss telescoped log bound** with the exact classical constant: for
`Λ' ⊆ Λ`, `|log (Z Λ) - log (Z Λ')| ≤ ∑ v ∈ Λ \ Λ', |w v| * exp (a v)`. -/
theorem abs_log_sub_log_le (h : G.KoteckyPreissCriterion w a) {Λ' Λ : Finset α}
    (hsub : Λ' ⊆ Λ) :
    |log (G.indepPartitionFunction w Λ) - log (G.indepPartitionFunction w Λ')| ≤
      ∑ v ∈ Λ \ Λ', |w v| * exp (a v) := by
  have hbase := h.toDobrushinCriterion.abs_log_sub_log_le hsub
  refine hbase.trans (le_of_eq (Finset.sum_congr rfl fun v _ => ?_))
  show -log (1 - (1 - exp (-(|w v| * exp (a v))))) = |w v| * exp (a v)
  have hclean : (1 : ℝ) - (1 - exp (-(|w v| * exp (a v)))) =
      exp (-(|w v| * exp (a v))) := by ring
  rw [hclean, Real.log_exp]
  ring

/-- The coarser, most-quoted form of the Kotecký–Preiss log bound: for `Λ' ⊆ Λ`,
`|log (Z Λ) - log (Z Λ')| ≤ ∑ v ∈ Λ \ Λ', a v`. -/
theorem abs_log_sub_log_le_sum (h : G.KoteckyPreissCriterion w a) {Λ' Λ : Finset α}
    (hsub : Λ' ⊆ Λ) :
    |log (G.indepPartitionFunction w Λ) - log (G.indepPartitionFunction w Λ')| ≤
      ∑ v ∈ Λ \ Λ', a v :=
  (h.abs_log_sub_log_le hsub).trans (Finset.sum_le_sum fun v _ => h.abs_mul_exp_le v)

/-- **The Kotecký–Preiss ratio bound, upper direction**, with the classical constant:
`Z Λ ≤ exp (∑ v ∈ Λ \ Λ', a v) * Z Λ'` for `Λ' ⊆ Λ`. -/
theorem indepPartitionFunction_le_exp_mul (h : G.KoteckyPreissCriterion w a)
    {Λ' Λ : Finset α} (hsub : Λ' ⊆ Λ) :
    G.indepPartitionFunction w Λ ≤
      exp (∑ v ∈ Λ \ Λ', a v) * G.indepPartitionFunction w Λ' := by
  have hZ := h.indepPartitionFunction_pos Λ
  have hZ' := h.indepPartitionFunction_pos Λ'
  have hlog := (abs_le.mp (h.abs_log_sub_log_le_sum hsub)).2
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_sub, Real.exp_log hZ, Real.exp_log hZ'] at hexp
  have hdiv := mul_le_mul_of_nonneg_right hexp hZ'.le
  rwa [div_mul_cancel₀ _ hZ'.ne'] at hdiv

end KoteckyPreissCriterion

end Engine

end SimpleGraph
