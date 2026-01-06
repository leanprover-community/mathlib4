/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Path
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.Order
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Connected.LocPathConnected
public import Mathlib.Topology.UnitInterval

/-!
# Semilocally simply connected spaces

A topological space is semilocally simply connected if every point has a neighborhood
such that loops in that neighborhood are nullhomotopic in the whole space.

## Main definitions

* `SemilocallySimplyConnected X` - A space where every point has a neighborhood with
  trivial fundamental group relative to the ambient space.

## Main theorems

* `semilocallySimplyConnected_iff` - Characterization in terms of loops
  being nullhomotopic.
* `SemilocallySimplyConnected.of_simplyConnected` - Simply connected spaces are semilocally
  simply connected.
* `Path.Homotopic.Quotient.discreteTopology` - In a semilocally simply connected,
  locally path-connected space, the quotient of paths by homotopy has the discrete topology.
-/

@[expose] public section

noncomputable section

open CategoryTheory FundamentalGroupoid Topology

variable {X : Type*} [TopologicalSpace X]

/-- A topological space is semilocally simply connected if every point has a neighborhood `U`
such that the inclusion map from `π₁(U, base)` to `π₁(X, base)` is trivial for all basepoints
in `U`. Equivalently, every loop in `U` is nullhomotopic in `X`. -/
def SemilocallySimplyConnected (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∀ (base : U),
      (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) base).range = ⊥

namespace SemilocallySimplyConnected

variable {X : Type*} [TopologicalSpace X]

/-- Simply connected spaces are semilocally simply connected. -/
theorem of_simplyConnected [SimplyConnectedSpace X] : SemilocallySimplyConnected X := fun x =>
  ⟨Set.univ, isOpen_univ, Set.mem_univ x, fun base => by
    simp only [MonoidHom.range_eq_bot_iff]
    ext
    exact Subsingleton.elim (α := Path.Homotopic.Quotient base.val base.val) _ _⟩

theorem semilocallySimplyConnected_iff :
    SemilocallySimplyConnected X ↔
    ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ {u : U} (γ : Path u.val u.val) (_ : Set.range γ ⊆ U),
        Path.Homotopic γ (Path.refl u.val) := by
  constructor
  · -- Forward direction: SemilocallySimplyConnected implies small loops are null
    intro h x
    obtain ⟨U, hU_open, hx_in_U, hU_loops⟩ := h x
    use U, hU_open, hx_in_U
    intro u γ hγ_range
    -- Restrict γ to a path in the subspace U
    have hγ_mem : ∀ t, γ t ∈ U := fun t => hγ_range ⟨t, rfl⟩
    let γ_U := γ.codRestrict hγ_mem
    -- The map from π₁(U, u) to π₁(X, u.val) has trivial range
    have h_range := hU_loops u
    rw [MonoidHom.range_eq_bot_iff] at h_range
    have h_map : FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ u
            (FundamentalGroup.fromPath ⟦γ_U⟧) =
           FundamentalGroup.fromPath ⟦Path.refl u.val⟧ := by
      rw [h_range]; rfl
    rw [show FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ u
            (FundamentalGroup.fromPath ⟦γ_U⟧) =
           FundamentalGroup.fromPath ⟦γ_U.map continuous_subtype_val⟧ from rfl,
        Path.map_codRestrict] at h_map
    exact Quotient.eq.mp h_map
  · -- Backward direction: small loops null implies SemilocallySimplyConnected
    intro h x
    obtain ⟨U, hU_open, hx_in_U, hU_loops_null⟩ := h x
    use U, hU_open, hx_in_U; intro base
    simp only [MonoidHom.range_eq_bot_iff]; ext p
    obtain ⟨γ', rfl⟩ := Quotient.exists_rep (FundamentalGroup.toPath p)
    have hrange : Set.range (γ'.map continuous_subtype_val) ⊆ U := by
      rintro _ ⟨t, rfl⟩
      exact (γ' t).property
    have hhom := hU_loops_null (γ'.map continuous_subtype_val) hrange
    rw [show FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ base
            (FundamentalGroup.fromPath ⟦γ'⟧) =
           FundamentalGroup.fromPath ⟦γ'.map continuous_subtype_val⟧ from rfl,
        Quotient.sound hhom]
    rfl

/-! ### Helper lemmas for discreteness of path homotopy quotients -/

/-- In an SLSC neighborhood where loops are nullhomotopic, any two paths with the same
endpoints are homotopic. This is derived by composing one path with the reverse of the other
to form a loop. -/
theorem Path.homotopic_of_loops_nullhomotopic_in_neighborhood {x y : X} (U : Set X)
    (h_loops : ∀ {z : X} (γ : Path z z), z ∈ U → Set.range γ ⊆ U → Path.Homotopic γ (Path.refl z))
    {p q : Path x y} (hp : Set.range p ⊆ U) (hq : Set.range q ⊆ U) :
    Path.Homotopic p q := by
  have hx : x ∈ U := by simpa using hp (Set.mem_range_self (0 : unitInterval))
  -- The loop p · q⁻¹ is nullhomotopic
  have h_loop : Path.Homotopic (p.trans q.symm) (Path.refl x) := by
    apply h_loops (p.trans q.symm) hx
    intro z hz
    obtain ⟨t, rfl⟩ := hz
    simp only [Path.trans_apply]
    split_ifs <;> [exact hp (Set.mem_range_self _); exact hq (Set.mem_range_self _)]
  -- Move to quotient and work there
  replace h_loop := Path.Homotopic.Quotient.eq.mpr h_loop
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.mk_refl] at h_loop
  apply Path.Homotopic.Quotient.exact
  generalize Path.Homotopic.Quotient.mk p = p' at h_loop ⊢
  generalize Path.Homotopic.Quotient.mk q = q' at h_loop ⊢
  calc p' = p'.trans (q'.symm.trans q') := by simp
    _ = (p'.trans q'.symm).trans q' := by simp
    _ = (Path.Homotopic.Quotient.refl x).trans q' := by rw [h_loop]
    _ = q' := by simp

/-- In an SLSC space, every point has an open neighborhood U such that for any two points
in U, there is a unique (up to homotopy) path between them.

This is a key reformulation of the SLSC property: it says that SLSC neighborhoods are
"locally simply connected" in the sense that path homotopy classes are determined by endpoints.

This is derived from the basic SLSC definition by composing paths: if p and q are two paths
from a to b in U, then p · q⁻¹ is a loop at a contained in U, hence nullhomotopic by SLSC,
which implies p ≃ q. -/
theorem exists_uniquePath_neighborhood (hX : SemilocallySimplyConnected X) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      (∀ {a b : X}, a ∈ U → b ∈ U → ∀ (p q : Path a b),
        Set.range p ⊆ U → Set.range q ⊆ U → Path.Homotopic p q) := by
  rw [semilocallySimplyConnected_iff] at hX
  obtain ⟨U, hU_open, hx_in_U, hU_loops⟩ := hX x
  refine ⟨U, hU_open, hx_in_U, ?_⟩
  intro a b ha hb p q hp_range hq_range
  apply Path.homotopic_of_loops_nullhomotopic_in_neighborhood U
  · intro z γ hz hγ_range
    exact @hU_loops ⟨z, hz⟩ γ hγ_range
  · exact hp_range
  · exact hq_range

/-- An SLSC neighborhood can be chosen to be path-connected. In a locally path-connected space,
we can use the path component of x in an SLSC neighborhood V to get a neighborhood that is both
open, path-connected, and has the SLSC property (paths with same endpoints in U are homotopic). -/
theorem exists_pathConnected_slsc_neighborhood (hX : SemilocallySimplyConnected X)
    [LocPathConnectedSpace X] (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPathConnected U ∧
      (∀ {a b : X}, a ∈ U → b ∈ U → ∀ (p q : Path a b),
        Set.range p ⊆ U → Set.range q ⊆ U → Path.Homotopic p q) := by
  -- Get an SLSC neighborhood from the SLSC property
  obtain ⟨V, hV_open, hx_in_V, hV_slsc⟩ := exists_uniquePath_neighborhood hX x
  -- The path component of x in V is open (since V is open and X is locally path-connected)
  let W := pathComponentIn V x
  refine ⟨W, hV_open.pathComponentIn x, mem_pathComponentIn_self hx_in_V,
    isPathConnected_pathComponentIn hx_in_V, ?_⟩
  intro a b ha hb p q hp hq
  -- W ⊆ V, so a, b ∈ V and p, q have ranges in V, hence are homotopic by SLSC property of V
  have hW_subset : W ⊆ V := pathComponentIn_subset
  apply @hV_slsc a b (hW_subset ha) (hW_subset hb) p q
  · exact Set.Subset.trans hp hW_subset
  · exact Set.Subset.trans hq hW_subset

/-! ### Tube data structures -/

/-- A partition of the unit interval [0,1] into n segments.
This bundles a strictly monotone sequence 0 = t₀ < t₁ < ... < tₙ = 1. -/
-- If this proves more generally useful, we should move it to `UnitInterval.lean`
-- and providfe further API (e.g. compositions, induction principles, ...)
structure IntervalPartition (n : ℕ) where
  /-- Partition points 0 = t₀ < t₁ < ... < tₙ = 1 -/
  t : Fin (n + 1) → unitInterval
  /-- t is strictly monotone -/
  h_mono : StrictMono t
  /-- t starts at 0 -/
  h_start : t 0 = 0
  /-- t ends at 1 -/
  h_end : t (Fin.last n) = 1

namespace IntervalPartition

attribute [simp, grind =] h_start h_end

/-- IntervalPartition 0 is impossible because it requires a single point
to be both 0 and 1. -/
lemma not_zero (part : IntervalPartition 0) : False := by
  have h0 : part.t 0 = 0 := part.h_start
  have h1 : part.t (Fin.last 0) = 1 := part.h_end
  have : Fin.last 0 = 0 := rfl
  rw [this] at h1
  rw [h0] at h1
  exact zero_ne_one h1

end IntervalPartition

/-- Data for a tubular neighborhood in an SLSC space.
This is completely abstract: just neighborhoods and their properties.
The connection to paths and intervals is made via the partition parameter in `PathInTube`.

Consists of:
- Segment neighborhoods U[i] (for n segments)
- Point neighborhoods V[j] at ALL partition points (including endpoints)
  - At endpoints: V[0] ⊆ U[0], V[n] ⊆ U[n-1]
  - At interior points: V[j] ⊆ U[j-1] ∩ U[j]
- All required properties (openness, path-connectivity, SLSC conditions) -/
structure TubeData (X : Type*) [TopologicalSpace X] (x y : X) (n : ℕ) where
  /-- Segment neighborhoods -/
  U : Fin n → Set X
  /-- Point neighborhoods at ALL partition points (including endpoints) -/
  V : Fin (n + 1) → Set X
  /-- Each U[i] is open -/
  h_U_open : ∀ i, IsOpen (U i)
  /-- Each U[i] is path-connected -/
  h_U_pathConn : ∀ i, IsPathConnected (U i)
  /-- SLSC property: paths in U[i] with same endpoints are homotopic -/
  h_U_slsc : ∀ i, ∀ {a b : X}, a ∈ U i → b ∈ U i →
    ∀ (p q : Path a b), Set.range p ⊆ U i → Set.range q ⊆ U i → Path.Homotopic p q
  /-- Each V[j] is open -/
  h_V_open : ∀ j, IsOpen (V j)
  /-- Each V[j] is path-connected -/
  h_V_pathConn : ∀ j, IsPathConnected (V j)
  /-- For each segment i, the left endpoint neighborhood V[i.castSucc] is in U[i] -/
  h_V_left_subset : ∀ i : Fin n, V i.castSucc ⊆ U i
  /-- For each segment i, the right endpoint neighborhood V[i.succ] is in U[i] -/
  h_V_right_subset : ∀ i : Fin n, V i.succ ⊆ U i

/-- A path γ is in the tube defined by partition `part` and tube data T.
This means:
1. γ stays in the segment neighborhoods U[i] on each interval [t[i], t[i+1]]
2. γ passes through the point neighborhoods V[j] at ALL partition points -/
structure PathInTube {X : Type*} [TopologicalSpace X] {x y : X} {n : ℕ}
    (γ : Path x y) (part : IntervalPartition n) (T : TubeData X x y n) : Prop where
  /-- γ stays in the segment neighborhoods U[i] on each interval [t[i], t[i+1]] -/
  stays_in_U : ∀ i (s : unitInterval),
    (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → γ s ∈ T.U i
  /-- γ passes through the point neighborhoods V[j] at ALL partition points -/
  passes_through_V : ∀ j, γ (part.t j) ∈ T.V j

/-- If γ is in a tube, then its subpath on segment i has range in U[i]. -/
lemma PathInTube.subpathOn_range_subset {X : Type*} [TopologicalSpace X] {x y : X} {n : ℕ}
    {γ : Path x y} {part : IntervalPartition n} {T : TubeData X x y n}
    (hγ : PathInTube γ part T) (i : Fin n) :
    Set.range (γ.subpathOn (part.t i.castSucc) (part.t i.succ)
      (part.h_mono.monotone i.castSucc_lt_succ.le)) ⊆ T.U i := by
  intro z hz
  obtain ⟨t, rfl⟩ := hz
  apply hγ.stays_in_U i
  have h_mono : (part.t i.castSucc : ℝ) ≤ part.t i.succ :=
    part.h_mono.monotone i.castSucc_lt_succ.le
  constructor
  · apply le_add_of_nonneg_right
    apply mul_nonneg t.2.1
    linarith
  · calc (part.t i.castSucc : ℝ) + t * (part.t i.succ - part.t i.castSucc)
        ≤ part.t i.castSucc + 1 * (part.t i.succ - part.t i.castSucc) := by
          apply add_le_add_right
          apply mul_le_mul_of_nonneg_right t.2.2
          linarith
      _ = part.t i.succ := by ring

/-- Convert TubeData with partition to the set of paths in the tube -/
def TubeData.toSet {X : Type*} [TopologicalSpace X] {x y : X} {n : ℕ}
    (part : IntervalPartition n) (T : TubeData X x y n) : Set (Path x y) :=
  {γ | PathInTube γ part T}

/-- In an SLSC space, given a path γ, there exists a tubular neighborhood structure
such that γ stays in the tube. This uses compactness of the path's image and the
Lebesgue number lemma. -/
theorem Path.exists_partition_in_slsc_neighborhoods (hX : SemilocallySimplyConnected X)
    [LocPathConnectedSpace X] {x y : X} (γ : Path x y) :
    ∃ (n : ℕ) (part : IntervalPartition n) (T : TubeData X x y n), PathInTube γ part T := by
  -- Apply the generic partition lemma with the property:
  -- "U is path-connected and paths in U with same endpoints are homotopic"
  obtain ⟨n, t, h_mono, h_start, h_end, h_partition⟩ := γ.exists_partition_with_property
    (fun U => IsPathConnected U ∧
      ∀ {a b : X}, a ∈ U → b ∈ U → ∀ (p q : Path a b),
        Set.range p ⊆ U → Set.range q ⊆ U → Path.Homotopic p q)
    (by
      intro z hz
      -- For each point z on the path, we get a path-connected SLSC neighborhood
      exact exists_pathConnected_slsc_neighborhood hX z
    )
  -- Extract U sets from the partition using choice
  choose U hU_open hU_prop hU_contains using h_partition
  -- For each point j, construct V[j] as the intersection of all U[i] where j is an endpoint
  -- Using iterated intersection: ⋂ i, ⋂ (_ : j is endpoint of i), U i
  -- This makes finiteness manifest (exactly n iterations) and openness automatic
  have V_data : ∀ (j : Fin (n + 1)),
      ∃ V : Set X, IsOpen V ∧ IsPathConnected V ∧ γ (t j) ∈ V ∧
        (∀ i : Fin n, j = i.castSucc → V ⊆ U i) ∧ (∀ i : Fin n, j = i.succ → V ⊆ U i) := by
    intro j
    -- Define intersection as: ⋂ i : Fin n, ⋂ (_ : j = i.castSucc ∨ j = i.succ), U i
    let U_inter := ⋂ i : Fin n, ⋂ (_ : j = i.castSucc ∨ j = i.succ), U i
    -- γ(t_j) is in all relevant U sets
    have hγ_in_inter : γ (t j) ∈ U_inter := by
      simp only [U_inter, Set.mem_iInter]
      intro i hi
      apply hU_contains i (t j)
      cases hi with
      | inl h => constructor <;> apply h_mono.monotone <;> simp [h, Fin.le_def]
      | inr h => constructor <;> apply h_mono.monotone <;> simp [h, Fin.le_def, Fin.succ]
    -- Take the path component of γ(t_j) in the intersection
    refine ⟨pathComponentIn U_inter (γ (t j)),
      ?_, isPathConnected_pathComponentIn hγ_in_inter,
      mem_pathComponentIn_self hγ_in_inter, ?_, ?_⟩
    · -- Prove open: finite intersection of open sets, then path component
      apply IsOpen.pathComponentIn
      apply isOpen_iInter_of_finite
      intro i
      apply isOpen_iInter_of_finite
      intro _
      exact hU_open i
    · -- Prove V ⊆ U i when j = i.castSucc
      intro i hi
      trans U_inter
      · apply pathComponentIn_subset
      · apply Set.iInter_subset_of_subset i
        apply Set.iInter_subset_of_subset (Or.inl hi)
        rfl
    · -- Prove V ⊆ U i when j = i.succ
      intro i hi
      trans U_inter
      · apply pathComponentIn_subset
      · apply Set.iInter_subset_of_subset i
        apply Set.iInter_subset_of_subset (Or.inr hi)
        rfl
  choose V hV_open hV_pathConn hγ_in_V hV_left hV_right using V_data
  -- Construct IntervalPartition
  let part : IntervalPartition n := {
    t := t
    h_mono := h_mono
    h_start := h_start
    h_end := h_end
  }
  -- Construct TubeData
  let T : TubeData X x y n := {
    U := U
    V := V
    h_U_open := hU_open
    h_U_pathConn := fun i => (hU_prop i).1
    h_U_slsc := fun i => (hU_prop i).2
    h_V_open := hV_open
    h_V_pathConn := hV_pathConn
    h_V_left_subset := fun i => hV_left i.castSucc i rfl
    h_V_right_subset := fun i => hV_right i.succ i rfl
  }
  -- Prove PathInTube
  refine ⟨n, part, T, ?_⟩
  exact { stays_in_U := hU_contains, passes_through_V := hγ_in_V }

/-- Given a partition and tube data, the set of paths in the tube is open in the path space.
This follows from the compact-open topology: it's a finite intersection of:
1. Sets {γ' | γ' maps [t i, t i+1] into U i} (open by compact-open topology)
2. Sets {γ' | γ'(t j) ∈ V[j]} (open by continuity of evaluation) -/
theorem TubeData.isOpen {x y : X} {n : ℕ}
    (part : IntervalPartition n) (T : TubeData X x y n) :
    IsOpen (T.toSet part) := by
  -- The tube is the intersection of two conditions
  have : T.toSet part =
    {γ' : Path x y | ∀ i (s : unitInterval),
      (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → γ' s ∈ T.U i} ∩
    {γ' : Path x y | ∀ j, γ' (part.t j) ∈ T.V j} := by
    ext γ'
    simp only [TubeData.toSet, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨h.stays_in_U, h.passes_through_V⟩
    · intro ⟨h1, h2⟩
      exact ⟨h1, h2⟩
  rw [this]
  apply IsOpen.inter
  -- First part: paths staying in U[i] on each segment
  · -- This is a finite intersection of open sets in the compact-open topology
    have : {γ' : Path x y | ∀ i (s : unitInterval),
        (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → γ' s ∈ T.U i} =
      ⋂ i : Fin n, {γ' : Path x y | ∀ s : unitInterval,
        (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → γ' s ∈ T.U i} := by
      ext γ'
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [this]
    apply isOpen_iInter_of_finite
    intro i
    -- Each segment condition defines an open set
    let K_i : Set unitInterval := Set.Icc (part.t i.castSucc) (part.t i.succ)
    have h_compact_K : IsCompact K_i := isCompact_Icc
    have h_eq : {γ' : Path x y | ∀ s : unitInterval,
        (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → γ' s ∈ T.U i} =
      {γ' : Path x y | Set.MapsTo γ' K_i (T.U i)} := by
      ext γ'
      simp only [Set.mem_setOf_eq, Set.MapsTo, K_i, Set.mem_Icc]
      refine forall_congr' fun s => ?_
      constructor
      · intro h hs; exact h hs
      · intro h hs; exact h hs
    rw [h_eq]
    have : {γ' : Path x y | Set.MapsTo γ' K_i (T.U i)} =
        (↑) ⁻¹' {f : C(unitInterval, X) | Set.MapsTo f K_i (T.U i)} := by
      rfl
    rw [this]
    exact (ContinuousMap.isOpen_setOf_mapsTo h_compact_K (T.h_U_open i)).preimage
      continuous_induced_dom
  -- Second part: paths passing through V[j] at all points
  · -- This is a finite intersection of open sets (by continuity of evaluation)
    have : {γ' : Path x y | ∀ j, γ' (part.t j) ∈ T.V j} =
        ⋂ j : Fin (n + 1), {γ' : Path x y | γ' (part.t j) ∈ T.V j} := by
      ext γ'
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [this]
    apply isOpen_iInter_of_finite
    intro j
    -- Show {γ' | γ'(part.t j) ∈ V[j]} is open
    change IsOpen ((fun γ' : Path x y => γ' (part.t j)) ⁻¹' (T.V j))
    apply IsOpen.preimage _ (T.h_V_open j)
    -- Evaluation is continuous: coercion then evaluation
    change Continuous fun γ' : Path x y => (γ' : C(unitInterval, X)) (part.t j)
    exact (continuous_eval_const (part.t j)).comp continuous_induced_dom

/-! ### Proof strategy for discrete topology on Path.Homotopic.Quotient

The main theorem `Path.Homotopic.Quotient.discreteTopology` states that in a semilocally
simply connected space, the quotient `Path.Homotopic.Quotient x y` carries the discrete topology.
This is proved by showing that every homotopy class (singleton in the quotient) is open.

**Overall proof strategy:**

Given a path `p : Path x y`, we show that its homotopy class `{p' | Path.Homotopic p' p}` is open.

1. **Partition construction** (`exists_partition_in_slsc_neighborhoods`):
   Use compactness of `p`'s image and the Lebesgue number lemma to find a finite partition
   `0 = t₀ < t₁ < ... < tₙ = 1` such that each segment `p([tᵢ, tᵢ₊₁])` lies in an open,
   path-connected neighborhood `Uᵢ` where all paths with the same endpoints are homotopic.

   **Crucially**, we also obtain **overlap neighborhoods** `Vⱼ` at each interior partition
   point `tⱼ`:
   - Each `Vⱼ` is open and path-connected
   - `p(tⱼ) ∈ Vⱼ ⊆ Uⱼ₋₁ ∩ Uⱼ`
   - These overlaps are obtained using **local path-connectedness**: at each `tⱼ`, the
     intersection `Uⱼ₋₁ ∩ Uⱼ` is an open neighborhood of `p(tⱼ)`, so it contains a
     path-connected neighborhood `Vⱼ`.

   This ensures rungs can be constructed at interior points (where we need paths in the
   intersection).

2. **The tube is open** (`tube_isOpen`):
   The set of paths `p'` such that `p'([tᵢ, tᵢ₊₁]) ⊆ Uᵢ` for all `i` is open in the
   compact-open topology on `Path x y`. This follows because each segment `[tᵢ, tᵢ₊₁]` is
   compact and each `Uᵢ` is open, so the tube is a finite intersection of sets of the form
   `{f | MapsTo f K U}` which are open by definition of the compact-open topology.

3. **Ladder homotopy construction** (`tube_subset_homotopy_class`):
   Any path `p'` in the tube is homotopic to `p` via a "ladder homotopy":

   - **Rungs** (`exists_rung_paths`): For each partition point `tᵢ`, construct a path `αᵢ`
     from `p(tᵢ)` to `p'(tᵢ)`:
     * At interior points: use path-connectedness of the overlap neighborhood `Vⱼ` to connect
       `p(tⱼ)` to `p'(tⱼ)`. Since `Vⱼ ⊆ Uⱼ₋₁ ∩ Uⱼ`, the rung lies in both adjacent segments'
       neighborhoods as required.
     * At endpoints: use constant paths since `p` and `p'` share endpoints.

   - **Rectangle homotopies** (`segment_rung_homotopy`): For each segment `i`, we have
     a rectangle with:
     * Bottom edge: segment `pᵢ` of `p` from `p(tᵢ)` to `p(tᵢ₊₁)`
     * Top edge: segment `p'ᵢ` of `p'` from `p'(tᵢ)` to `p'(tᵢ₊₁)`
     * Left edge: rung `αᵢ` from `p(tᵢ)` to `p'(tᵢ)`
     * Right edge: rung `αᵢ₊₁` from `p(tᵢ₊₁)` to `p'(tᵢ₊₁)`

     Both `pᵢ` and `p'ᵢ` lie in the SLSC neighborhood `Uᵢ`, as do the rungs (by construction).
     By the SLSC property, `pᵢ · αᵢ₊₁ ≃ αᵢ · p'ᵢ` (both are paths from `p(tᵢ)` to `p'(tᵢ₊₁)`
     with ranges in `Uᵢ`).

   - **Pasting via telescoping** (`paste_segment_homotopies`): Compose the segment homotopies:
     ```
     p = p₀ · p₁ · ... · pₙ₋₁
       ≃ (α₀ · p'₀ · α₁⁻¹) · (α₁ · p'₁ · α₂⁻¹) · ... · (αₙ₋₁ · p'ₙ₋₁ · αₙ⁻¹)
       ≃ α₀ · (p'₀ · p'₁ · ... · p'ₙ₋₁) · αₙ⁻¹  (telescoping cancellation)
       ≃ α₀ · p' · αₙ⁻¹
       ≃ p'  (since α₀ and αₙ are constant paths)
     ```

4. **Tubular neighborhoods** (`exists_open_tubular_neighborhood_in_homotopy_class`):
   Combining steps 1-3, we have shown that for any path `p`:
   - Step 1 gives a partition `tᵢ` and SLSC neighborhoods `Uᵢ` for `p`
   - Step 2 shows the tube `T = {p' | ∀i, p'([tᵢ, tᵢ₊₁]) ⊆ Uᵢ}` is open
   - Step 3 shows `T ⊆ {p' | Homotopic p' p}` (the tube is contained in `p`'s homotopy class)

   **Therefore: Every path `p` has an open neighborhood contained in its homotopy class.**
   This is the key fact that bridges the local SLSC property to the global topological result.

5. **Homotopy classes are open** (`isOpen_setOf_homotopic`):
   Let `H(p) = {p' | Homotopic p' p}` be the homotopy class of `p`. To show `H(p)` is open:
   - Take any `q ∈ H(p)` (so `q` is homotopic to `p`)
   - By step 4, `q` has an open neighborhood `T_q` with `T_q ⊆ H(q)`
   - Since homotopy is an equivalence relation, `H(q) = H(p)`
   - Therefore `q ∈ T_q ⊆ H(p)`, so `q` has an open neighborhood in `H(p)`

   Since every point in `H(p)` has an open neighborhood contained in `H(p)`, the set `H(p)`
   is open.

6. **Discrete topology** (`discreteTopology`):
   In the quotient `Path.Homotopic.Quotient x y`, singletons `{⟦p⟧}` correspond to homotopy
   classes `H(p)` under the quotient map. By step 5, `H(p)` is open, so its image `{⟦p⟧}` is
   open in the quotient topology. Since every singleton is open, the quotient has discrete
   topology.

This proof strategy shows that SLSC spaces have "locally unique" path homotopy classes,
which is the key to constructing universal covers.
-/

/-! ### Construction of "rung" paths for the ladder homotopy -/

/-- Given two paths γ and γ' in a tube with partition points t_i, we can construct connecting
"rung" paths α_i from γ(t_i) to γ'(t_i), where each rung αᵢ lies in neighborhoods Uᵢ₋₁ and Uᵢ
(the neighborhoods of the adjacent segments). The rungs at the endpoints (α_0 and α_n) are
constant paths since γ and γ' share endpoints. -/
theorem Path.exists_rung_paths {x y : X} {n : ℕ} (γ γ' : Path x y)
    (part : IntervalPartition n) (T : TubeData X x y n)
    (hγ : PathInTube γ part T) (hγ' : PathInTube γ' part T) :
    ∃ α : (i : Fin (n + 1)) → Path (γ (part.t i)) (γ' (part.t i)),
      (∀ (i : Fin n), Set.range (α i.castSucc) ⊆ T.U i ∧ Set.range (α i.succ) ⊆ T.U i) := by
  -- For each point j, construct a rung path α_j from γ(t_j) to γ'(t_j)
  -- using the path-connected neighborhood V[j]
  have rung_exists : ∀ j, ∃ α_j : Path (γ (part.t j)) (γ' (part.t j)),
      Set.range α_j ⊆ T.V j := by
    intro j
    have hγ_in_V : γ (part.t j) ∈ T.V j := hγ.passes_through_V j
    have hγ'_in_V : γ' (part.t j) ∈ T.V j := hγ'.passes_through_V j
    obtain ⟨α_j, hα_range⟩ := IsPathConnected.exists_path (T.h_V_pathConn j) hγ_in_V hγ'_in_V
    exact ⟨α_j, hα_range⟩
  choose α hα_range using rung_exists
  -- Prove the range conditions using the subset properties
  refine ⟨α, fun i => ?_⟩
  constructor
  · calc Set.range (α i.castSucc) ⊆ T.V i.castSucc := hα_range i.castSucc
      _ ⊆ T.U i := T.h_V_left_subset i
  · calc Set.range (α i.succ) ⊆ T.V i.succ := hα_range i.succ
      _ ⊆ T.U i := T.h_V_right_subset i

/-! ### Single segment homotopy: the key step in the ladder construction -/

/-- For a single segment i, the path γ_i · α_{i+1} (along γ then down the next rung) is
homotopic to α_i · γ'_i (down the current rung then along γ'). Both paths lie entirely in
the SLSC neighborhood U_i, and since they share endpoints, the SLSC property implies they
are homotopic. This is the crucial "rectangle" homotopy for each segment. -/
theorem Path.segment_rung_homotopy {a b c d : X} (U : Set X)
    (h_slsc : ∀ {x y : X} (p q : Path x y), x ∈ U → y ∈ U →
      Set.range p ⊆ U → Set.range q ⊆ U → Path.Homotopic p q)
    (γ : Path a b) (γ' : Path c d) (α_start : Path a c) (α_end : Path b d)
    (hγ : Set.range γ ⊆ U) (hγ' : Set.range γ' ⊆ U)
    (hα_start : Set.range α_start ⊆ U) (hα_end : Set.range α_end ⊆ U) :
    Path.Homotopic (γ.trans α_end) (α_start.trans γ') := by
  -- Both paths go from a to d and lie entirely in U
  -- Endpoints are in U because they're on the paths
  have ha : a ∈ U := by
    convert hγ (Set.mem_range_self 0)
    exact γ.source.symm
  have hd : d ∈ U := by
    convert hγ' (Set.mem_range_self 1)
    exact γ'.target.symm
  -- So we can apply the SLSC property
  apply h_slsc
  · exact ha
  · exact hd
  · -- Show γ.trans α_end has range in U
    rw [Path.trans_range]
    exact Set.union_subset hγ hα_end
  · -- Show α_start.trans γ' has range in U
    rw [Path.trans_range]
    exact Set.union_subset hα_start hγ'

/-! ### Pasting lemma: telescoping cancellation of rungs -/

/-- The pasting lemma for segment homotopies. Works directly with path restrictions.

Given:
- γ and γ' are paths from x to y with a partition
- α : (i : Fin (n+1)) → Path (γ (t i)) (γ' (t i)) are rung paths connecting partition points
- For each segment i, the rectangle homotopy: γ|[t_i,t_{i+1}] · α_{i+1} ≃ α_i · γ'|[t_i,t_{i+1}]

Then by telescoping, we get: γ · αₙ ≃ α₀ · γ'

Since part.t 0 = 0 and part.t (Fin.last n) = 1:
- α₀ : Path (γ 0) (γ' 0) = Path x x (loop at x)
- αₙ : Path (γ 1) (γ' 1) = Path y y (loop at y)

When the endpoint loops are null-homotopic, we get γ ≃ γ'. -/
theorem Path.paste_segment_homotopies {x y : X} {n : ℕ} (γ γ' : Path x y)
    (part : IntervalPartition n)
    (α : (i : Fin (n + 1)) → Path (γ (part.t i)) (γ' (part.t i)))
    (h_rectangles : ∀ (i : Fin n),
        Path.Homotopic
          ((γ.subpathOn (part.t i.castSucc) (part.t i.succ)
            (part.h_mono.monotone i.castSucc_lt_succ.le)).trans (α i.succ))
          ((α i.castSucc).trans (γ'.subpathOn (part.t i.castSucc) (part.t i.succ)
            (part.h_mono.monotone i.castSucc_lt_succ.le)))) :
    Path.Homotopic
      (γ.trans ((α (Fin.last n)).cast
        (show y = γ (part.t (Fin.last n)) by rw [part.h_end, γ.target])
        (show y = γ' (part.t (Fin.last n)) by rw [part.h_end, γ'.target])))
      (((α 0).cast (show x = γ (part.t 0) by rw [part.h_start, γ.source])
                   (show x = γ' (part.t 0) by rw [part.h_start, γ'.source])).trans γ') := by
  open Path.Homotopic.Quotient in
  -- Define intermediate paths: γ_aux i follows γ up to t_i, crosses via α_i, then follows γ'
  let γ_aux : (i : Fin (n + 1)) → Path x y := fun i =>
    (((γ.subpathOn (part.t 0) (part.t i) (part.h_mono.monotone (Fin.zero_le i))).trans (α i)).trans
      (γ'.subpathOn (part.t i) (part.t (Fin.last n))
        (part.h_mono.monotone (Fin.le_last i)))).cast
      (by rw [part.h_start, γ.source])
      (by rw [part.h_end, γ'.target])
  -- Base case: γ_aux 0 ≃ α_0 · γ'
  -- At i=0, γ|[0,0] is constant, and γ'|[0,1] is all of γ', so this simplifies to α_0 · γ'
  have h_base : Path.Homotopic (γ_aux 0)
      (((α 0).cast (show x = γ (part.t 0) by rw [part.h_start, γ.source])
                   (show x = γ' (part.t 0) by rw [part.h_start, γ'.source])).trans γ') := by
    apply exact
    dsimp [γ_aux]
    simp
  -- Final case: γ_aux (Fin.last n) ≃ γ · α_n
  -- At i=n, γ|[0,1] is all of γ, and γ'|[1,1] is constant, so this simplifies to γ · α_n
  have h_final : Path.Homotopic (γ_aux (Fin.last n))
      (γ.trans ((α (Fin.last n)).cast
        (show y = γ (part.t (Fin.last n)) by rw [part.h_end, γ.target])
        (show y = γ' (part.t (Fin.last n)) by rw [part.h_end, γ'.target]))) := by
    apply exact
    dsimp [γ_aux]
    simp
  -- Lift h_rectangles to the quotient with an arbitrary suffix
  -- This allows simp to apply the rectangle homotopy in context
  have rectangle_with_suffix : ∀ (i : Fin n) {w : X}
      (suffix : Path.Homotopic.Quotient (γ' (part.t i.succ)) w),
      (Path.Homotopic.Quotient.mk (γ.subpathOn (part.t i.castSucc) (part.t i.succ)
          (part.h_mono.monotone i.castSucc_lt_succ.le))).trans
        ((Path.Homotopic.Quotient.mk (α i.succ)).trans suffix) =
      (Path.Homotopic.Quotient.mk (α i.castSucc)).trans
        ((Path.Homotopic.Quotient.mk (γ'.subpathOn (part.t i.castSucc) (part.t i.succ)
            (part.h_mono.monotone i.castSucc_lt_succ.le))).trans suffix) := by
    intro i w suffix
    induction suffix using Path.Homotopic.Quotient.ind with | mk suffix =>
    simp only [← mk_trans, eq]
    -- Chain homotopies: reassociate, apply rectangle, reassociate back
    exact ((Path.Homotopic.trans_assoc _ _ _).symm.trans
      (Path.Homotopic.hcomp (h_rectangles i) (Path.Homotopic.refl suffix))).trans
      (Path.Homotopic.trans_assoc _ _ _)
  -- Consecutive paths are homotopic: γ_aux i.succ ≃ γ_aux i.castSucc
  -- This follows from decomposing using subpathOn_trans and applying h_rectangles i
  have h_step : ∀ (i : Fin n), Path.Homotopic (γ_aux i.succ) (γ_aux i.castSucc) := by
    intro i
    apply exact
    simp only [γ_aux, mk_trans, mk_cast]
    -- Decompose γ|[0, i+1] = γ|[0, i] · γ|[i, i+1]
    rw [← subpathOn_trans γ
      (part.t 0) (part.t i.castSucc) (part.t i.succ)
      (part.h_mono.monotone (Fin.zero_le i.castSucc))
      (part.h_mono.monotone i.castSucc_lt_succ.le)]
    -- Decompose γ'|[i, last n] = γ'|[i, i+1] · γ'|[i+1, last n]
    rw [← subpathOn_trans γ'
      (part.t i.castSucc) (part.t i.succ) (part.t (Fin.last n))
      (part.h_mono.monotone i.castSucc_lt_succ.le)
      (part.h_mono.monotone (Fin.le_last i.succ))]
    -- Right-associate everything so rectangle_with_suffix can fire
    simp only [trans_assoc]
    -- Now apply the rectangle homotopy with suffix
    rw [rectangle_with_suffix]
  -- Chain all homotopies together
  -- γ · α_n ≃ γ_aux n ≃ γ_aux (n-1) ≃ ... ≃ γ_aux 0 ≃ α_0 · γ'
  -- Build a chain from any γ_aux i down to γ_aux 0 using h_step
  have h_chain : ∀ i : Fin (n + 1), Path.Homotopic (γ_aux i) (γ_aux 0) := by
    intro i
    induction i using Fin.induction with
    | zero => exact Path.Homotopic.refl _
    | succ i ih => exact (h_step i).trans ih
  -- Now combine everything: γ · α_n ≃ γ_aux n ≃ γ_aux 0 ≃ α_0 · γ'
  exact h_final.symm.trans ((h_chain (Fin.last n)).trans h_base)

/-- Stronger version of paste_segment_homotopies that directly gives γ ≃ γ' when the endpoint
loops live in SLSC neighborhoods.

Given the same rectangle homotopies, plus:
- U₀ is an SLSC neighborhood containing the range of α 0
- Uₙ₋₁ is an SLSC neighborhood containing the range of α (Fin.last n)

Then the endpoint loops are null-homotopic, and we get γ ≃ γ' directly. -/
theorem Path.paste_segment_homotopies_slsc {x y : X} {n : ℕ} (γ γ' : Path x y)
    (part : IntervalPartition n)
    (α : (i : Fin (n + 1)) → Path (γ (part.t i)) (γ' (part.t i)))
    (h_rectangles : ∀ (i : Fin n),
        Path.Homotopic
          ((γ.subpathOn (part.t i.castSucc) (part.t i.succ)
            (part.h_mono.monotone i.castSucc_lt_succ.le)).trans (α i.succ))
          ((α i.castSucc).trans (γ'.subpathOn (part.t i.castSucc) (part.t i.succ)
            (part.h_mono.monotone i.castSucc_lt_succ.le))))
    (U₀ : Set X) (h_U₀_slsc : ∀ {a b : X} (p q : Path a b), a ∈ U₀ → b ∈ U₀ →
      Set.range p ⊆ U₀ → Set.range q ⊆ U₀ → Path.Homotopic p q)
    (h_α₀_in_U₀ : Set.range (α 0) ⊆ U₀)
    (Uₙ : Set X) (h_Uₙ_slsc : ∀ {a b : X} (p q : Path a b), a ∈ Uₙ → b ∈ Uₙ →
      Set.range p ⊆ Uₙ → Set.range q ⊆ Uₙ → Path.Homotopic p q)
    (h_αₙ_in_Uₙ : Set.range (α (Fin.last n)) ⊆ Uₙ) :
    Path.Homotopic γ γ' := by
  -- Step 1: Apply the basic pasting lemma
  -- This gives us: γ · αₙ ≃ α₀ · γ'
  have h_paste := paste_segment_homotopies γ γ' part α h_rectangles
  -- Step 2: Define the endpoint loops with proper casts
  let α₀ := (α 0).cast (show x = γ (part.t 0) by rw [part.h_start, γ.source])
                       (show x = γ' (part.t 0) by rw [part.h_start, γ'.source])
  let αₙ := (α (Fin.last n)).cast
              (show y = γ (part.t (Fin.last n)) by rw [part.h_end, γ.target])
              (show y = γ' (part.t (Fin.last n)) by rw [part.h_end, γ'.target])
  -- Step 3: Show α₀ is null-homotopic using SLSC property of U₀
  have h_α₀_null : Path.Homotopic α₀ (Path.refl x) := by
    apply h_U₀_slsc
    · -- x ∈ U₀
      have : (α 0) 0 = x := by simp [(α 0).source, part.h_start, γ.source]
      rw [← this]
      exact h_α₀_in_U₀ ⟨0, rfl⟩
    · -- x ∈ U₀ (same proof)
      have : (α 0) 0 = x := by simp [(α 0).source, part.h_start, γ.source]
      rw [← this]
      exact h_α₀_in_U₀ ⟨0, rfl⟩
    · -- range α₀ ⊆ U₀
      show Set.range α₀ ⊆ U₀
      simp only [α₀, Path.cast, Set.range]
      exact h_α₀_in_U₀
    · -- range (refl x) ⊆ U₀
      intro z hz
      simp only [Path.refl, Path.coe_mk', ContinuousMap.coe_const, Set.mem_range,
        Function.const_apply, exists_const] at hz
      rw [← hz]
      have : (α 0) 0 = x := by simp [(α 0).source, part.h_start, γ.source]
      rw [← this]
      exact h_α₀_in_U₀ ⟨0, rfl⟩
  -- Step 4: Show αₙ is null-homotopic using SLSC property of Uₙ
  have h_αₙ_null : Path.Homotopic αₙ (Path.refl y) := by
    apply h_Uₙ_slsc
    · -- y ∈ Uₙ
      have : (α (Fin.last n)) 0 = y := by
        simp [(α (Fin.last n)).source, part.h_end]
      rw [← this]
      exact h_αₙ_in_Uₙ ⟨0, rfl⟩
    · -- y ∈ Uₙ (same proof)
      have : (α (Fin.last n)) 0 = y := by
        simp [(α (Fin.last n)).source, part.h_end]
      rw [← this]
      exact h_αₙ_in_Uₙ ⟨0, rfl⟩
    · -- range αₙ ⊆ Uₙ
      show Set.range αₙ ⊆ Uₙ
      simp only [αₙ, Path.cast, Set.range]
      exact h_αₙ_in_Uₙ
    · -- range (refl y) ⊆ Uₙ
      intro z hz
      simp only [Path.refl, Path.coe_mk', ContinuousMap.coe_const, Set.mem_range,
        Function.const_apply, exists_const] at hz
      rw [← hz]
      have : (α (Fin.last n)) 0 = y := by
        simp [(α (Fin.last n)).source, part.h_end]
      rw [← this]
      exact h_αₙ_in_Uₙ ⟨0, rfl⟩
  -- Step 5: Combine using homotopy manipulation
  -- From h_paste: γ · αₙ ≃ α₀ · γ'
  -- From h_α₀_null: α₀ ≃ refl x
  -- From h_αₙ_null: αₙ ≃ refl y
  -- Therefore: γ ≃ γ
  -- Left side: γ · αₙ ≃ γ · refl y ≃ γ
  have lhs : Path.Homotopic (γ.trans αₙ) γ := by
    have step1 : Path.Homotopic (γ.trans αₙ) (γ.trans (Path.refl y)) :=
      Path.Homotopic.hcomp (Path.Homotopic.refl γ) h_αₙ_null
    have step2 : Path.Homotopic (γ.trans (Path.refl y)) γ :=
      Path.Homotopic.trans_refl γ
    exact Path.Homotopic.trans step1 step2
  -- Right side: α₀ · γ' ≃ refl x · γ' ≃ γ'
  have rhs : Path.Homotopic (α₀.trans γ') γ' := by
    have step1 : Path.Homotopic (α₀.trans γ') ((Path.refl x).trans γ') :=
      Path.Homotopic.hcomp h_α₀_null (Path.Homotopic.refl γ')
    have step2 : Path.Homotopic ((Path.refl x).trans γ') γ' :=
      Path.Homotopic.refl_trans γ'
    exact Path.Homotopic.trans step1 step2
  -- Combine: γ ≃ γ · αₙ ≃ α₀ · γ' ≃ γ'
  exact Path.Homotopic.trans (Path.Homotopic.symm lhs) (Path.Homotopic.trans h_paste rhs)

/-- Given a path γ in an SLSC space, paths in the tube around γ are homotopic to γ.
This is the main result that combines all the previous lemmas:
1. Construct rung paths α_i using path-connectedness of V neighborhoods
2. For each segment, apply segment_rung_homotopy to get γ_i·α_{i+1} ≃ α_i·γ'_i
3. Use paste_segment_homotopies to get γ ≃ γ' by telescoping cancellation -/
theorem Path.tube_subset_homotopy_class {x y : X} {n : ℕ}
    (γ : Path x y) (part : IntervalPartition n) (T : TubeData X x y n)
    (hγ : PathInTube γ part T)
    (γ' : Path x y) (hγ' : PathInTube γ' part T) :
    Path.Homotopic γ' γ := by
  -- Step 1: Construct rungs connecting partition points
  obtain ⟨α, hα_ranges⟩ := Path.exists_rung_paths γ γ' part T hγ hγ'
  -- Step 2: For each segment i, prove the rectangle homotopy using segment_rung_homotopy
  -- The subpaths γ|[t_i, t_{i+1}] and γ'|[t_i, t_{i+1}] both lie in U_i
  -- The rungs α_i and α_{i+1} also lie in U_i
  -- By SLSC property of U_i, we get: γ_i · α_{i+1} ≃ α_i · γ'_i
  have h_rectangles : ∀ (i : Fin n),
      Path.Homotopic
        ((γ.subpathOn (part.t i.castSucc) (part.t i.succ)
          (part.h_mono.monotone i.castSucc_lt_succ.le)).trans (α i.succ))
        ((α i.castSucc).trans (γ'.subpathOn (part.t i.castSucc) (part.t i.succ)
          (part.h_mono.monotone i.castSucc_lt_succ.le))) := by
    intro i
    apply segment_rung_homotopy (T.U i)
      (fun p q hp_a hp_d hp_range hq_range => T.h_U_slsc i hp_a hp_d p q hp_range hq_range)
    · -- γ.subpathOn has range in U_i
      exact hγ.subpathOn_range_subset i
    · -- γ'.subpathOn has range in U_i
      exact hγ'.subpathOn_range_subset i
    · -- α i.castSucc has range in U_i
      exact (hα_ranges i).1
    · -- α i.succ has range in U_i
      exact (hα_ranges i).2
  -- Step 3: Apply the stronger pasting lemma that uses SLSC to handle endpoint loops
  -- We need to identify which neighborhoods contain the endpoint rungs
  -- First, handle the case where n = 0 separately
  cases n with
  | zero =>
    -- When n = 0, the partition is impossible (requires 0 = 1)
    exfalso; exact IntervalPartition.not_zero part
  | succ n' =>
    -- Now n = n' + 1, so we have at least one segment
    -- α 0 has range in V 0, and V 0 ⊆ U 0 (left endpoint of segment 0)
    -- α (Fin.last n) has range in V (Fin.last n), and V (Fin.last n) ⊆ U n'
    -- (right endpoint of last segment)
    -- For α 0: it has range in V 0 ⊆ U 0
    let i_first : Fin (n' + 1) := ⟨0, Nat.zero_lt_succ n'⟩
    have h_α₀_range : Set.range (α 0) ⊆ T.U i_first := by
      have h1 : i_first.castSucc = 0 := rfl
      rw [← h1]
      exact (hα_ranges i_first).1
    -- For α (Fin.last (n' + 1)): it has range in V (Fin.last (n' + 1)) ⊆ U n'
    let i_last : Fin (n' + 1) := ⟨n', Nat.lt_succ_self n'⟩
    have h_αₙ_range : Set.range (α (Fin.last (n' + 1))) ⊆ T.U i_last := by
      have h1 : i_last.succ = Fin.last (n' + 1) := rfl
      rw [← h1]
      exact (hα_ranges i_last).2
    -- Now apply the stronger pasting lemma and use symmetry
    apply Path.Homotopic.symm
    refine paste_segment_homotopies_slsc γ γ' part α h_rectangles
      (T.U i_first)
      (fun p q hp_a hp_d hp_range hq_range => T.h_U_slsc i_first hp_a hp_d p q hp_range hq_range)
      h_α₀_range
      (T.U i_last)
      (fun p q hp_a hp_d hp_range hq_range => T.h_U_slsc i_last hp_a hp_d p q hp_range hq_range)
      h_αₙ_range

/--
In an SLSC locally path-connected space, every path p has an open tubular neighborhood
contained in its homotopy class.

This shows that the SLSC property gives us not just any open set around p, but specifically
an open set where ALL paths are homotopic to p. This is what makes homotopy classes open.
-/
theorem Path.exists_open_tubular_neighborhood_in_homotopy_class
    (hX : SemilocallySimplyConnected X) [LocPathConnectedSpace X]
    {x y : X} (p : Path x y) :
    ∃ (T : Set (Path x y)), IsOpen T ∧ p ∈ T ∧ T ⊆ {p' | Path.Homotopic p' p} := by
  -- Step 1: Get partition and SLSC neighborhoods
  obtain ⟨n, part, T_data, hp_in_tube⟩ :=
    Path.exists_partition_in_slsc_neighborhoods hX p
  -- Step 2: The tube T is just T_data.toSet part
  refine ⟨T_data.toSet part, ?_, ?_, ?_⟩
  · -- Show T is open
    exact T_data.isOpen part
  · -- Show p ∈ T
    exact hp_in_tube
  · -- Show T ⊆ {p' | Homotopic p' p} using tube_subset_homotopy_class
    intro p' hp'
    apply Path.tube_subset_homotopy_class p part T_data
    · exact hp_in_tube
    · exact hp'

/-- In an SLSC locally path-connected space, for any path p, the set of paths homotopic to p
is open.

**Proof strategy:** To show the homotopy class H(p) = {p' | Homotopic p' p} is open, we show
that every point q ∈ H(p) has an open neighborhood contained in H(p):
1. Take any q ∈ H(p), so Homotopic q p
2. By `exists_open_tubular_neighborhood_in_homotopy_class`, q has an open tubular neighborhood
   T_q with T_q ⊆ {p' | Homotopic p' q}
3. Since homotopy is an equivalence relation, {p' | Homotopic p' q} = {p' | Homotopic p' p} = H(p)
4. Therefore q ∈ T_q ⊆ H(p), giving an open neighborhood of q in H(p)

Since every point in H(p) has an open neighborhood contained in H(p), the set H(p) is open.

This is the main topological consequence of the SLSC property: homotopy classes of paths are
not just equivalence classes, but also open sets in the path space. -/
theorem Path.isOpen_setOf_homotopic (hX : SemilocallySimplyConnected X)
    [LocPathConnectedSpace X] {x y : X} (p : Path x y) :
    IsOpen {p' : Path x y | Path.Homotopic p' p} := by
  -- Strategy: show every point in the homotopy class has an open neighborhood in the class
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  -- q is homotopic to p, so get a tubular neighborhood around q
  obtain ⟨T_q, hT_open, hq_in_T, hT_subset⟩ :=
    exists_open_tubular_neighborhood_in_homotopy_class hX q
  -- T_q is an open neighborhood of q, so we just need to show T_q ⊆ {p' | Homotopic p' p}
  rw [mem_nhds_iff]
  refine ⟨T_q, ?_, hT_open, hq_in_T⟩
  -- Use transitivity: p' ∈ T_q → p' ~ q, and q ~ p, so p' ~ p
  intro p' hp'
  have hp'q : Path.Homotopic p' q := hT_subset hp'
  exact hp'q.trans hq

/--
In a semilocally simply connected, locally path-connected space, the quotient of paths by
homotopy has discrete topology.
-/
theorem Path.Homotopic.Quotient.discreteTopology
    (hX : SemilocallySimplyConnected X) [LocPathConnectedSpace X] (x y : X) :
    DiscreteTopology (Path.Homotopic.Quotient x y) := by
  -- By `isOpen_setOf_homotopic`, every homotopy class H(p) = {p' | Homotopic p' p} is
  -- open in Path x y. Under the quotient map π : Path x y → Path.Homotopic.Quotient x y, the
  -- preimage π⁻¹({⟦p⟧}) = H(p) is open. Since preimages of singletons are open, every singleton
  -- in the quotient is open, giving the discrete topology.

  -- Show every singleton is open in the quotient
  rw [discreteTopology_iff_isOpen_singleton]
  intro a
  -- Use quotient induction to get a representative path
  induction a using Quotient.inductionOn with
  | h p =>
    -- The preimage of {⟦p⟧} is the homotopy class {p' | Homotopic p' p}, which is open
    rw [isOpen_coinduced]
    convert isOpen_setOf_homotopic hX p
    ext p'
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact Quotient.eq (r := Path.Homotopic.setoid x y)

end SemilocallySimplyConnected
