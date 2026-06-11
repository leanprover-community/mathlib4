/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.Subpath
public import Mathlib.Topology.Connected.LocPathConnected
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.UnitInterval

/-!
# Tube neighborhoods in path space

This file develops the "tube" technique for comparing paths in the compact-open topology:

* `IsPathHomotopyTrivial U`: any two paths in `U` with the same endpoints are homotopic in the
  ambient space.
* `IntervalPartition`, `TubeData`, `PathInTube`: a partition `0 = t₀ ≤ ⋯ ≤ tₙ = 1` together
  with open segment neighborhoods `Uᵢ` and path-connected vertex neighborhoods `Vⱼ`, and the
  predicate that a path stays inside them.
* `ContinuousMap.isOpen_setOf_mapsTo_forall_mem` and `TubeData.isOpen`: tubes are open in the
  compact-open topology.
* `Path.exists_pathInTube`: if every point has an open, path-connected, path-homotopy-trivial
  neighborhood, then every path fits in a tube.
* `Path.segment_rung_homotopy`, `Path.paste_segment_homotopies` (and the `_trivial` variants),
  `Path.tube_subset_homotopy_class`: the ladder-homotopy pasting argument showing that any two
  paths in a common tube are homotopic.

The application to semilocally simply connected spaces — openness of path-homotopy classes and
discreteness of `Path.Homotopic.Quotient` — is in
`Mathlib.AlgebraicTopology.FundamentalGroupoid.SemilocallySimplyConnected`.
-/

noncomputable section

open Set Topology

variable {X : Type*} [TopologicalSpace X]

/-- A subset `U` of a topological space `X` is *path-homotopy-trivial* if any two paths
in `X` whose images lie in `U` and which share endpoints are homotopic in `X`. (Equivalently,
by `paths_homotopic_iff_loops_nullhomotopic`, every loop with image in `U` is nullhomotopic
in `X`.) This is the form of "`U` is simply connected" used in the universal-cover
construction: it is weaker than `IsSimplyConnected U` because the homotopy is not required
to lie inside `U`. -/
@[expose] public def IsPathHomotopyTrivial (U : Set X) : Prop :=
  ∀ ⦃a b : X⦄ (p q : Path a b), range p ⊆ U → range q ⊆ U → Path.Homotopic p q

/-! ### Tube data structures -/

/-- A partition of the unit interval [0,1] into n segments.
This bundles a monotone sequence 0 = t₀ ≤ t₁ ≤ ... ≤ tₙ = 1. -/
-- If this proves more generally useful, we should move it to `UnitInterval.lean`
-- and provide further API (e.g. compositions, induction principles, ...)
public structure IntervalPartition (n : ℕ) where
  /-- Partition points 0 = t₀ ≤ t₁ ≤ ... ≤ tₙ = 1 -/
  t : Fin (n + 1) → unitInterval
  /-- t is monotone -/
  mono : Monotone t
  /-- t starts at 0 -/
  t_zero : t 0 = 0
  /-- t ends at 1 -/
  t_last : t (Fin.last n) = 1

namespace IntervalPartition

attribute [simp, grind =] t_zero t_last

/-- `IntervalPartition 0` is empty: a single partition point cannot be simultaneously
`0` (by `t_zero`) and `1` (by `t_last`). -/
public instance : IsEmpty (IntervalPartition 0) where
  false part := by
    have h0 : part.t 0 = 0 := part.t_zero
    have h1 : part.t 0 = 1 := part.t_last
    exact zero_ne_one (h0.symm.trans h1)

end IntervalPartition

/-- Data for a tubular neighborhood in path space.
This is completely abstract: just neighborhoods and their properties.
The connection to paths and intervals is made via the partition parameter in `PathInTube`.
The endpoints `x y` are phantom parameters: no field mentions them, but they pin down the
type `Path x y` of the paths the tube is for (see `TubeData.toSet`).

Consists of:
- Segment neighborhoods U[i] (for n segments)
- Point neighborhoods V[j] at ALL partition points (including endpoints)
  - At endpoints: V[0] ⊆ U[0], V[n] ⊆ U[n-1]
  - At interior points: V[j] ⊆ U[j-1] ∩ U[j]
- All required properties (openness, path-connectivity, path-homotopy-triviality) -/
public structure TubeData (X : Type*) [TopologicalSpace X] (x y : X) (n : ℕ) where
  /-- Segment neighborhoods -/
  U : Fin n → Set X
  /-- Point neighborhoods at ALL partition points (including endpoints) -/
  V : Fin (n + 1) → Set X
  /-- Each U[i] is open -/
  U_open : ∀ i, IsOpen (U i)
  /-- Triviality: paths in U[i] with the same endpoints are homotopic in X -/
  U_trivial : ∀ i, IsPathHomotopyTrivial (U i)
  /-- Each V[j] is open -/
  V_open : ∀ j, IsOpen (V j)
  /-- Each V[j] is path-connected -/
  V_pathConn : ∀ j, IsPathConnected (V j)
  /-- For each segment i, the left endpoint neighborhood V[i.castSucc] is in U[i] -/
  V_left_subset : ∀ i : Fin n, V i.castSucc ⊆ U i
  /-- For each segment i, the right endpoint neighborhood V[i.succ] is in U[i] -/
  V_right_subset : ∀ i : Fin n, V i.succ ⊆ U i

/-- A path γ is in the tube defined by partition `part` and tube data T.
This means:
1. γ stays in the segment neighborhoods U[i] on each interval [t[i], t[i+1]]
2. γ passes through the point neighborhoods V[j] at ALL partition points -/
public structure PathInTube {X : Type*} [TopologicalSpace X] {x y : X} {n : ℕ}
    (γ : Path x y) (part : IntervalPartition n) (T : TubeData X x y n) : Prop where
  /-- γ stays in the segment neighborhoods U[i] on each interval [t[i], t[i+1]] -/
  stays_in_U : ∀ i : Fin n, MapsTo γ (Icc (part.t i.castSucc) (part.t i.succ)) (T.U i)
  /-- γ passes through the point neighborhoods V[j] at ALL partition points -/
  passes_through_V : ∀ j, γ (part.t j) ∈ T.V j

/-- If γ is in a tube, then its subpath on segment i has range in U[i]. -/
public lemma PathInTube.subpath_range_subset {X : Type*} [TopologicalSpace X] {x y : X} {n : ℕ}
    {γ : Path x y} {part : IntervalPartition n} {T : TubeData X x y n}
    (hγ : PathInTube γ part T) (i : Fin n) :
    Set.range (γ.subpath (part.t i.castSucc) (part.t i.succ)) ⊆ T.U i := by
  intro z hz
  obtain ⟨t, rfl⟩ := hz
  have h_mono : (part.t i.castSucc : ℝ) ≤ part.t i.succ :=
    part.mono i.castSucc_lt_succ.le
  simpa [Path.subpath_apply] using
    hγ.stays_in_U i ⟨Set.Icc.le_convexComb h_mono t, Set.Icc.convexComb_le h_mono t⟩

/-- Convert TubeData with partition to the set of paths in the tube -/
@[expose] public def TubeData.toSet {X : Type*} [TopologicalSpace X] {x y : X} {n : ℕ}
    (part : IntervalPartition n) (T : TubeData X x y n) : Set (Path x y) :=
  {γ | PathInTube γ part T}

/-- Given segment neighborhoods covering each subpath of `γ`, construct the vertex neighborhoods
as path components of the finite intersections of adjacent segment neighborhoods. -/
private theorem Path.exists_vertexNeighborhood_family [LocPathConnectedSpace X]
    {x y : X} {γ : Path x y} {n : ℕ}
    {t : Fin (n + 1) → unitInterval} {U : Fin n → Set X}
    (h_mono : Monotone t) (hU_open : ∀ i, IsOpen (U i))
    (hU_contains : ∀ i : Fin n, MapsTo γ (Icc (t i.castSucc) (t i.succ)) (U i)) :
    ∃ V : Fin (n + 1) → Set X,
      (∀ j, IsOpen (V j)) ∧
      (∀ j, IsPathConnected (V j)) ∧
      (∀ j, γ (t j) ∈ V j) ∧
      (∀ i : Fin n, V i.castSucc ⊆ U i) ∧
      (∀ i : Fin n, V i.succ ⊆ U i) := by
  have V_data : ∀ j : Fin (n + 1),
      ∃ V : Set X, IsOpen V ∧ IsPathConnected V ∧ γ (t j) ∈ V ∧
        (∀ i : Fin n, j = i.castSucc → V ⊆ U i) ∧
        (∀ i : Fin n, j = i.succ → V ⊆ U i) := by
    intro j
    let U_inter := ⋂ i : Fin n, ⋂ (_ : j = i.castSucc ∨ j = i.succ), U i
    have hγ_in_inter : γ (t j) ∈ U_inter := by
      simp only [U_inter, Set.mem_iInter]
      intro i hi
      exact hU_contains i <| by
        cases hi with
        | inl h =>
            constructor <;> apply h_mono <;> simp [h, Fin.le_def]
        | inr h =>
            constructor <;> apply h_mono <;> simp [h, Fin.le_def, Fin.succ]
    refine ⟨pathComponentIn U_inter (γ (t j)), ?_, isPathConnected_pathComponentIn hγ_in_inter,
      mem_pathComponentIn_self hγ_in_inter, ?_, ?_⟩
    · apply IsOpen.pathComponentIn
      apply isOpen_iInter_of_finite
      intro i
      apply isOpen_iInter_of_finite
      intro _
      exact hU_open i
    · intro i hi
      trans U_inter
      · exact pathComponentIn_subset
      · exact Set.iInter_subset_of_subset i <| Set.iInter_subset_of_subset (Or.inl hi) <| subset_rfl
    · intro i hi
      trans U_inter
      · exact pathComponentIn_subset
      · exact Set.iInter_subset_of_subset i <| Set.iInter_subset_of_subset (Or.inr hi) <| subset_rfl
  choose V hV_open hV_pathConn hγ_in_V hV_left hV_right using V_data
  refine ⟨V, hV_open, hV_pathConn, hγ_in_V, ?_, ?_⟩
  · intro i
    exact hV_left i.castSucc i rfl
  · intro i
    exact hV_right i.succ i rfl

/-- If every point has an open, path-connected, path-homotopy-trivial neighborhood, then
every path fits in a tube: there is a partition of `[0, 1]` and tube data such that the path
stays in the segment neighborhoods and passes through the vertex neighborhoods. This uses
compactness of the path's image and the Lebesgue number lemma. -/
public theorem Path.exists_pathInTube [LocPathConnectedSpace X] {x y : X} (γ : Path x y)
    (h : ∀ z : X, ∃ U : Set X, IsOpen U ∧ z ∈ U ∧ IsPathConnected U ∧ IsPathHomotopyTrivial U) :
    ∃ (n : ℕ) (part : IntervalPartition n) (T : TubeData X x y n), PathInTube γ part T := by
  -- Apply the generic partition lemma with the property:
  -- "U is path-connected and paths in U with same endpoints are homotopic"
  obtain ⟨n, t, h_mono, h_start, h_end, h_partition⟩ := γ.exists_partition_with_property
    (fun U ↦ IsPathConnected U ∧ IsPathHomotopyTrivial U)
    (fun z _ ↦ h z)
  -- Extract U sets from the partition using choice
  choose U hU_open hU_prop hU_contains using h_partition
  obtain ⟨V, hV_open, hV_pathConn, hγ_in_V, hV_left, hV_right⟩ :=
    Path.exists_vertexNeighborhood_family h_mono hU_open hU_contains
  -- Construct IntervalPartition
  let part : IntervalPartition n := {
    t := t
    mono := h_mono
    t_zero := h_start
    t_last := h_end
  }
  -- Construct TubeData
  let T : TubeData X x y n := {
    U := U
    V := V
    U_open := hU_open
    U_trivial := fun i ↦ (hU_prop i).2
    V_open := hV_open
    V_pathConn := hV_pathConn
    V_left_subset := hV_left
    V_right_subset := hV_right
  }
  -- Prove PathInTube
  refine ⟨n, part, T, ?_⟩
  exact { stays_in_U := hU_contains, passes_through_V := hγ_in_V }

/-- The "tube" of continuous maps determined by finitely many compact-into-open constraints
together with finitely many open vertex constraints is open in the compact-open topology. -/
public theorem ContinuousMap.isOpen_setOf_mapsTo_forall_mem
    {α : Type*} [TopologicalSpace α] {n m : ℕ}
    {K : Fin n → Set α} (hK : ∀ i, IsCompact (K i)) {U : Fin n → Set X} (hU : ∀ i, IsOpen (U i))
    (p : Fin m → α) {V : Fin m → Set X} (hV : ∀ j, IsOpen (V j)) :
    IsOpen {f : C(α, X) | (∀ i, MapsTo f (K i) (U i)) ∧ ∀ j, f (p j) ∈ V j} := by
  have h₁ : IsOpen {f : C(α, X) | ∀ i, MapsTo f (K i) (U i)} := by
    rw [setOf_forall]
    exact isOpen_iInter_of_finite fun i ↦ ContinuousMap.isOpen_setOf_mapsTo (hK i) (hU i)
  have h₂ : IsOpen {f : C(α, X) | ∀ j, f (p j) ∈ V j} := by
    rw [setOf_forall]
    exact isOpen_iInter_of_finite fun j ↦ (hV j).preimage (continuous_eval_const (p j))
  exact h₁.inter h₂

/-- Given a partition and tube data, the set of paths in the tube is open in the path space:
it is the pullback, along the inclusion `Path x y → C(I, X)`, of a tube of continuous maps. -/
public theorem TubeData.isOpen {x y : X} {n : ℕ}
    (part : IntervalPartition n) (T : TubeData X x y n) :
    IsOpen (T.toSet part) := by
  have h : T.toSet part = (fun γ : Path x y ↦ γ.toContinuousMap) ⁻¹'
      {f : C(unitInterval, X) |
        (∀ i, MapsTo f (Icc (part.t i.castSucc) (part.t i.succ)) (T.U i)) ∧
        ∀ j, f (part.t j) ∈ T.V j} :=
    Set.ext fun γ' ↦
      ⟨fun hγ ↦ ⟨hγ.stays_in_U, hγ.passes_through_V⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, h2⟩⟩
  rw [h]
  exact (ContinuousMap.isOpen_setOf_mapsTo_forall_mem (fun _ ↦ isCompact_Icc) T.U_open
    _ T.V_open).preimage continuous_induced_dom

/-! ### Proof strategy for discrete topology on `Path.Homotopic.Quotient`

To prove that path-homotopy classes are open in the compact-open topology (and hence that
`Path.Homotopic.Quotient` is discrete; see
`Mathlib/AlgebraicTopology/FundamentalGroupoid/SemilocallySimplyConnected.lean`), one argues
as follows. Given `p : Path x y`, compactness and the Lebesgue number
lemma yield a partition `0 = t₀ < ⋯ < tₙ = 1` with each segment `p [tᵢ, tᵢ₊₁]` inside an open
path-homotopy-trivial `Uᵢ`, together with path-connected overlap neighborhoods
`p tⱼ ∈ Vⱼ ⊆ Uⱼ₋₁ ∩ Uⱼ` (`Path.exists_pathInTube`). The tube
`{p' | ∀ i, p' [tᵢ, tᵢ₊₁] ⊆ Uᵢ ∧ ∀ j, p' tⱼ ∈ Vⱼ}` is open (`TubeData.isOpen`) and contained
in the homotopy class of `p`: connect `p tⱼ` to `p' tⱼ` by rungs `αⱼ` inside `Vⱼ`
(`Path.exists_rung_paths`), homotope each segment across its rectangle of rungs
(`Path.segment_rung_homotopy`), and paste by telescoping cancellation
(`Path.paste_segment_homotopies`, then `_trivial_source`/`_trivial` to kill the boundary rungs);
this is `Path.tube_subset_homotopy_class`. Openness of homotopy classes
(`Path.isOpen_setOf_homotopic`) follows, and singletons in the quotient are open.
-/

/-! ### Construction of "rung" paths for the ladder homotopy -/

/-- Given two paths γ and γ' in a tube with partition points t_i, we can construct connecting
"rung" paths α_i from γ(t_i) to γ'(t_i), where each rung αᵢ lies in neighborhoods Uᵢ₋₁ and Uᵢ
(the neighborhoods of the adjacent segments). The rungs at the endpoints (α_0 and α_n) are
constant paths since γ and γ' share endpoints. -/
private theorem Path.exists_rung_paths {x y : X} {n : ℕ} (γ γ' : Path x y)
    (part : IntervalPartition n) (T : TubeData X x y n)
    (hγ : PathInTube γ part T) (hγ' : PathInTube γ' part T) :
    ∃ α : (i : Fin (n + 1)) → Path (γ (part.t i)) (γ' (part.t i)),
      (∀ (i : Fin n), Set.range (α i.castSucc) ⊆ T.U i ∧ Set.range (α i.succ) ⊆ T.U i) := by
  -- For each point j, construct a rung path α_j from γ(t_j) to γ'(t_j)
  -- using the path-connected neighborhood V[j]
  have rung_exists : ∀ j, ∃ α_j : Path (γ (part.t j)) (γ' (part.t j)),
      Set.range α_j ⊆ T.V j := fun j ↦
    (T.V_pathConn j).exists_path (hγ.passes_through_V j) (hγ'.passes_through_V j)
  choose α hα_range using rung_exists
  -- Prove the range conditions using the subset properties
  refine ⟨α, fun i ↦ ?_⟩
  constructor
  · calc Set.range (α i.castSucc) ⊆ T.V i.castSucc := hα_range i.castSucc
      _ ⊆ T.U i := T.V_left_subset i
  · calc Set.range (α i.succ) ⊆ T.V i.succ := hα_range i.succ
      _ ⊆ T.U i := T.V_right_subset i

/-! ### Single segment homotopy: the key step in the ladder construction -/

/-- For a single segment i, the path γ_i · α_{i+1} (along γ then down the next rung) is
homotopic to α_i · γ'_i (down the current rung then along γ'). Both paths lie entirely in
the path-homotopy-trivial set U_i, and since they share endpoints, triviality implies they
are homotopic. This is the crucial "rectangle" homotopy for each segment. -/
public theorem Path.segment_rung_homotopy {a b c d : X} (U : Set X)
    (hU : IsPathHomotopyTrivial U)
    (γ : Path a b) (γ' : Path c d) (α_start : Path a c) (α_end : Path b d)
    (hγ : Set.range γ ⊆ U) (hγ' : Set.range γ' ⊆ U)
    (hα_start : Set.range α_start ⊆ U) (hα_end : Set.range α_end ⊆ U) :
    Path.Homotopic (γ.trans α_end) (α_start.trans γ') := by
  apply hU
  · rw [Path.trans_range]; exact Set.union_subset hγ hα_end
  · rw [Path.trans_range]; exact Set.union_subset hα_start hγ'

/-! ### Pasting lemma: telescoping cancellation of rungs -/

/-- The cast'd quotient class of `p.subpath` over the endpoints of an `IntervalPartition`
equals the class of `p` itself. This packages `Path.Homotopic.Quotient.subpath_zero_one`
together with `part.t_zero` / `part.t_last`, sidestepping the dependent-type "motive"
obstruction one hits when rewriting `part.t 0 = 0` / `part.t (Fin.last n) = 1` directly
through `subpath`. -/
private theorem Path.Homotopic.Quotient.cast_mk_subpath_part_endpoints
    {x y : X} (p : Path x y) {n : ℕ} (part : IntervalPartition n)
    (h₁ : x = p (part.t 0)) (h₂ : y = p (part.t (Fin.last n))) :
    (Path.Homotopic.Quotient.mk (p.subpath (part.t 0) (part.t (Fin.last n)))).cast h₁ h₂ =
      Path.Homotopic.Quotient.mk p := by
  convert congrArg (fun q ↦ q.cast p.source.symm p.target.symm)
    (Path.Homotopic.Quotient.subpath_zero_one p)
  · simp [part.t_zero]
  · simp [part.t_last]

/-- The pasting lemma for segment homotopies. Works directly with path restrictions.

Given:
- γ is a path from x to y and γ' is a path from x to y' with a partition
- α : (i : Fin (n+1)) → Path (γ (t i)) (γ' (t i)) are rung paths connecting partition points
- For each segment i, the rectangle homotopy: γ|[t_i,t_{i+1}] · α_{i+1} ≃ α_i · γ'|[t_i,t_{i+1}]

Then by telescoping, we get: γ · αₙ ≃ α₀ · γ'

Since part.t 0 = 0 and part.t (Fin.last n) = 1:
- α₀ : Path (γ 0) (γ' 0) = Path x x (loop at x)
- αₙ : Path (γ 1) (γ' 1) = Path y y'

When the initial loop is null-homotopic, this identifies `γ'` with `γ` followed by the final
rung. If the final rung is also null-homotopic, we recover γ ≃ γ'. -/
public theorem Path.paste_segment_homotopies {x y y' : X} {n : ℕ}
    (γ : Path x y) (γ' : Path x y') (part : IntervalPartition n)
    (α : (i : Fin (n + 1)) → Path (γ (part.t i)) (γ' (part.t i)))
    (h_rectangles : ∀ (i : Fin n),
        Path.Homotopic
          ((γ.subpath (part.t i.castSucc) (part.t i.succ)).trans (α i.succ))
          ((α i.castSucc).trans (γ'.subpath (part.t i.castSucc) (part.t i.succ)))) :
    Path.Homotopic
      (γ.trans ((α (Fin.last n)).cast
        (show y = γ (part.t (Fin.last n)) by rw [part.t_last, γ.target])
        (show y' = γ' (part.t (Fin.last n)) by rw [part.t_last, γ'.target])))
      (((α 0).cast (show x = γ (part.t 0) by rw [part.t_zero, γ.source])
                   (show x = γ' (part.t 0) by rw [part.t_zero, γ'.source])).trans γ') := by
  open Path.Homotopic.Quotient in
  -- Define intermediate paths: γ_aux i follows γ up to t_i, crosses via α_i, then follows γ'
  let γ_aux : (i : Fin (n + 1)) → Path x y' := fun i ↦
    (((γ.subpath (part.t 0) (part.t i)).trans (α i)).trans
      (γ'.subpath (part.t i) (part.t (Fin.last n)))).cast
      (by rw [part.t_zero, γ.source])
      (by rw [part.t_last, γ'.target])
  -- Base case: γ_aux 0 ≃ α_0 · γ'
  -- At i=0, γ|[0,0] is constant, and γ'|[0,1] is all of γ', so this simplifies to α_0 · γ'
  have h_base : Path.Homotopic (γ_aux 0)
      (((α 0).cast (show x = γ (part.t 0) by rw [part.t_zero, γ.source])
                   (show x = γ' (part.t 0) by rw [part.t_zero, γ'.source])).trans γ') := by
    apply Path.Homotopic.Quotient.exact
    dsimp [γ_aux]
    rw [Path.Homotopic.Quotient.subpath_self,
        Path.Homotopic.Quotient.cast_mk_subpath_part_endpoints γ' part]
    simp
  -- Final case: γ_aux (Fin.last n) ≃ γ · α_n
  -- At i=n, γ|[0,1] is all of γ, and γ'|[1,1] is constant, so this simplifies to γ · α_n
  have h_final : Path.Homotopic (γ_aux (Fin.last n))
      (γ.trans ((α (Fin.last n)).cast
        (show y = γ (part.t (Fin.last n)) by rw [part.t_last, γ.target])
        (show y' = γ' (part.t (Fin.last n)) by rw [part.t_last, γ'.target]))) := by
    apply Path.Homotopic.Quotient.exact
    dsimp [γ_aux]
    rw [Path.Homotopic.Quotient.subpath_self,
        Path.Homotopic.Quotient.cast_mk_subpath_part_endpoints γ part]
    simp
  -- Lift h_rectangles to the quotient with an arbitrary suffix
  -- This allows simp to apply the rectangle homotopy in context
  have rectangle_with_suffix : ∀ (i : Fin n) {w : X}
      (suffix : Path.Homotopic.Quotient (γ' (part.t i.succ)) w),
      (Path.Homotopic.Quotient.mk (γ.subpath (part.t i.castSucc) (part.t i.succ))).trans
        ((Path.Homotopic.Quotient.mk (α i.succ)).trans suffix) =
      (Path.Homotopic.Quotient.mk (α i.castSucc)).trans
        ((Path.Homotopic.Quotient.mk
          (γ'.subpath (part.t i.castSucc) (part.t i.succ))).trans suffix) := by
    intro i w suffix
    induction suffix using Path.Homotopic.Quotient.ind with | mk suffix =>
    simp only [← mk_trans, eq]
    -- Chain homotopies: reassociate, apply rectangle, reassociate back
    exact ((Path.Homotopic.trans_assoc _ _ _).symm.trans
      (Path.Homotopic.hcomp (h_rectangles i) (Path.Homotopic.refl suffix))).trans
      (Path.Homotopic.trans_assoc _ _ _)
  -- Consecutive paths are homotopic: γ_aux i.succ ≃ γ_aux i.castSucc
  -- This follows from decomposing using subpath_trans and applying h_rectangles i
  have h_step : ∀ (i : Fin n), Path.Homotopic (γ_aux i.succ) (γ_aux i.castSucc) := by
    intro i
    apply exact
    simp only [γ_aux, mk_trans, mk_cast]
    -- Decompose γ|[0, i+1] = γ|[0, i] · γ|[i, i+1]
    rw [← Path.Homotopic.Quotient.subpath_trans γ
      (part.t 0) (part.t i.castSucc) (part.t i.succ)]
    -- Decompose γ'|[i, last n] = γ'|[i, i+1] · γ'|[i+1, last n]
    rw [← Path.Homotopic.Quotient.subpath_trans γ'
      (part.t i.castSucc) (part.t i.succ) (part.t (Fin.last n))]
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

/-- A loop in a path-homotopy-trivial set is null-homotopic if its range lies in that set. -/
public theorem IsPathHomotopyTrivial.nullhomotopic_of_range_subset {U : Set X}
    (hU : IsPathHomotopyTrivial U) {x : X} (γ : Path x x)
    (hxU : x ∈ U) (hγU : Set.range γ ⊆ U) :
    Path.Homotopic γ (Path.refl x) :=
  hU γ (Path.refl x) hγU <| by
    rintro _ ⟨_, rfl⟩
    simpa using hxU

/-- One-sided specialization of `paste_segment_homotopies` that kills the source loop.

Given the same rectangle homotopies, plus:
- U₀ is a path-homotopy-trivial set containing the range of α 0

Then `γ'` is homotopic to `γ` followed by the final rung. -/
public theorem Path.paste_segment_homotopies_trivial_source {x y y' : X} {n : ℕ}
    (γ : Path x y) (γ' : Path x y')
    (part : IntervalPartition n)
    (α : (i : Fin (n + 1)) → Path (γ (part.t i)) (γ' (part.t i)))
    (h_rectangles : ∀ (i : Fin n),
        Path.Homotopic
          ((γ.subpath (part.t i.castSucc) (part.t i.succ)).trans (α i.succ))
          ((α i.castSucc).trans (γ'.subpath (part.t i.castSucc) (part.t i.succ))))
    (U₀ : Set X) (hU₀ : IsPathHomotopyTrivial U₀)
    (h_α₀_in_U₀ : Set.range (α 0) ⊆ U₀) :
    Path.Homotopic
      (γ.trans ((α (Fin.last n)).cast
        (show y = γ (part.t (Fin.last n)) by rw [part.t_last, γ.target])
        (show y' = γ' (part.t (Fin.last n)) by rw [part.t_last, γ'.target])))
      γ' := by
  have h_paste := paste_segment_homotopies γ γ' part α h_rectangles
  let α₀ := (α 0).cast (show x = γ (part.t 0) by rw [part.t_zero, γ.source])
                       (show x = γ' (part.t 0) by rw [part.t_zero, γ'.source])
  have h_α₀_null : Path.Homotopic α₀ (Path.refl x) :=
    hU₀.nullhomotopic_of_range_subset α₀
      (α₀.source ▸ h_α₀_in_U₀ ⟨0, rfl⟩) (by simpa [α₀] using h_α₀_in_U₀)
  exact h_paste.trans <| Path.Homotopic.trans_left_of_nullhomotopic h_α₀_null

/--
Two-sided specialization of `paste_segment_homotopies`: if the source and target rungs live in
path-homotopy-trivial sets, then both endpoint loops are null-homotopic and we get γ ≃ γ' directly.
-/
public theorem Path.paste_segment_homotopies_trivial {x y : X} {n : ℕ} (γ γ' : Path x y)
    (part : IntervalPartition n)
    (α : (i : Fin (n + 1)) → Path (γ (part.t i)) (γ' (part.t i)))
    (h_rectangles : ∀ (i : Fin n),
        Path.Homotopic
          ((γ.subpath (part.t i.castSucc) (part.t i.succ)).trans (α i.succ))
          ((α i.castSucc).trans (γ'.subpath (part.t i.castSucc) (part.t i.succ))))
    (U₀ : Set X) (hU₀ : IsPathHomotopyTrivial U₀)
    (h_α₀_in_U₀ : Set.range (α 0) ⊆ U₀)
    (Uₙ : Set X) (hUₙ : IsPathHomotopyTrivial Uₙ)
    (h_αₙ_in_Uₙ : Set.range (α (Fin.last n)) ⊆ Uₙ) :
    Path.Homotopic γ γ' := by
  let αₙ := (α (Fin.last n)).cast
              (show y = γ (part.t (Fin.last n)) by rw [part.t_last, γ.target])
              (show y = γ' (part.t (Fin.last n)) by rw [part.t_last, γ'.target])
  have h_source : Path.Homotopic (γ.trans αₙ) γ' := by
    simpa only [αₙ] using
      paste_segment_homotopies_trivial_source γ γ' part α h_rectangles U₀ hU₀ h_α₀_in_U₀
  have h_αₙ_null : Path.Homotopic αₙ (Path.refl y) :=
    hUₙ.nullhomotopic_of_range_subset αₙ
      (αₙ.source ▸ h_αₙ_in_Uₙ ⟨0, rfl⟩) (by simpa [αₙ] using h_αₙ_in_Uₙ)
  exact (Path.Homotopic.trans_right_of_nullhomotopic h_αₙ_null).symm.trans h_source

/-- Paths in a common tube are homotopic.
This is the main result that combines all the previous lemmas:
1. Construct rung paths α_i using path-connectedness of V neighborhoods
2. For each segment, apply segment_rung_homotopy to get γ_i·α_{i+1} ≃ α_i·γ'_i
3. Use paste_segment_homotopies to get γ ≃ γ' by telescoping cancellation -/
public theorem Path.tube_subset_homotopy_class {x y : X} {n : ℕ}
    (γ : Path x y) (part : IntervalPartition n) (T : TubeData X x y n)
    (hγ : PathInTube γ part T)
    (γ' : Path x y) (hγ' : PathInTube γ' part T) :
    Path.Homotopic γ' γ := by
  obtain ⟨α, hα_ranges⟩ := Path.exists_rung_paths γ γ' part T hγ hγ'
  have h_rectangles : ∀ (i : Fin n),
      Path.Homotopic
        ((γ.subpath (part.t i.castSucc) (part.t i.succ)).trans (α i.succ))
        ((α i.castSucc).trans (γ'.subpath (part.t i.castSucc) (part.t i.succ))) := by
    intro i
    apply segment_rung_homotopy (T.U i) (T.U_trivial i)
    · -- γ.subpath has range in U_i
      exact hγ.subpath_range_subset i
    · -- γ'.subpath has range in U_i
      exact hγ'.subpath_range_subset i
    · -- α i.castSucc has range in U_i
      exact (hα_ranges i).1
    · -- α i.succ has range in U_i
      exact (hα_ranges i).2
  cases n with
  | zero => exact isEmptyElim part
  | succ n' =>
    let i_first : Fin (n' + 1) := ⟨0, Nat.zero_lt_succ n'⟩
    let i_last : Fin (n' + 1) := ⟨n', Nat.lt_succ_self n'⟩
    refine Path.Homotopic.symm <| paste_segment_homotopies_trivial γ γ' part α h_rectangles
      (T.U i_first) (T.U_trivial i_first) (hα_ranges i_first).1
      (T.U i_last) (T.U_trivial i_last) (hα_ranges i_last).2

end
