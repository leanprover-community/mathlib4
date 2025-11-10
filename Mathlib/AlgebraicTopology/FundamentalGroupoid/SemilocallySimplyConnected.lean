/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Path
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Order
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.UnitInterval

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
-/

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
  -- Need to show: p ≃ q where p, q : x → y
  -- We'll need x ∈ U and y ∈ U from the ranges
  have hx : x ∈ U := by simpa using hp (Set.mem_range_self (0 : unitInterval))
  have hy : y ∈ U := by simpa using hq (Set.mem_range_self (1 : unitInterval))
  -- Form the loop p · q.symm : x → x
  let loop := p.trans q.symm
  have h_loop_range : Set.range loop ⊆ U := by
    intro z hz
    obtain ⟨t, rfl⟩ := hz
    simp only [loop, Path.trans_apply]
    split_ifs <;> [exact hp (Set.mem_range_self _); exact hq (Set.mem_range_self _)]
  -- This loop is nullhomotopic
  have h_null : Path.Homotopic loop (Path.refl x) := h_loops loop hx h_loop_range
  -- Now: loop ≃ refl x means p · q.symm ≃ refl x
  -- Composing with q on the right: (p · q.symm) · q ≃ (refl x) · q
  have : Path.Homotopic ((p.trans q.symm).trans q) ((Path.refl x).trans q) :=
    Path.Homotopic.hcomp h_null (Path.Homotopic.refl q)
  -- Simplify using associativity and identity laws
  have h1 : Path.Homotopic (p.trans (q.symm.trans q)) ((p.trans q.symm).trans q) :=
    ⟨(Path.Homotopy.transAssoc p q.symm q).symm⟩
  have h2 : Path.Homotopic (q.symm.trans q) (Path.refl y) :=
    ⟨(Path.Homotopy.reflSymmTrans q).symm⟩
  have h3 : Path.Homotopic (p.trans (Path.refl y)) p :=
    ⟨Path.Homotopy.transRefl p⟩
  have h4 : Path.Homotopic ((Path.refl x).trans q) q :=
    ⟨Path.Homotopy.reflTrans q⟩
  -- p ≃ q via a chain of homotopies
  have step1 : Path.Homotopic p (p.trans (Path.refl y)) := h3.symm
  have step2 : Path.Homotopic (p.trans (Path.refl y)) (p.trans (q.symm.trans q)) :=
    Path.Homotopic.hcomp (Path.Homotopic.refl p) h2.symm
  have step3 : Path.Homotopic (p.trans (q.symm.trans q)) ((p.trans q.symm).trans q) := h1
  have step4 : Path.Homotopic ((p.trans q.symm).trans q) ((Path.refl x).trans q) := this
  have step5 : Path.Homotopic ((Path.refl x).trans q) q := h4
  exact step1.trans (step2.trans (step3.trans (step4.trans step5)))

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

/-- The preimage of a singleton homotopy class under the quotient map is the set of all paths
homotopic to a representative. -/
theorem Path.Homotopic.fiber_eq (x y : X) (p : Path x y) :
    letI : Setoid (Path x y) := Path.Homotopic.setoid x y
    (Quotient.mk' : Path x y → Path.Homotopic.Quotient x y) ⁻¹' {⟦p⟧} =
      {p' : Path x y | Path.Homotopic p' p} := by
  ext p'
  simp [Set.mem_preimage, Set.mem_singleton_iff]
  exact Quotient.eq

/-- A singleton in the quotient topology is open if and only if its preimage is open. -/
theorem Path.Homotopic.singleton_isOpen_iff (x y : X) (p : Path x y) :
    letI : Setoid (Path x y) := Path.Homotopic.setoid x y
    IsOpen ({⟦p⟧} : Set (Path.Homotopic.Quotient x y)) ↔
      IsOpen ((Quotient.mk' : Path x y → Path.Homotopic.Quotient x y) ⁻¹' {⟦p⟧}) := by
  -- The quotient topology is coinduced, so a set is open iff its preimage is open
  rfl

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

/-- In an SLSC space, given a path γ, there exists a finite partition of [0,1] such that
each segment of γ lies in a path-connected SLSC neighborhood. This uses compactness of the
path's image and the Lebesgue number lemma. -/
theorem Path.exists_partition_in_slsc_neighborhoods (hX : SemilocallySimplyConnected X)
    [LocPathConnectedSpace X] {x y : X} (γ : Path x y) :
    ∃ (n : ℕ) (t : Fin (n + 1) → unitInterval),
      StrictMono t ∧
      t 0 = 0 ∧
      t (Fin.last n) = 1 ∧
      (∀ i : Fin n, ∃ U : Set X, IsOpen U ∧ IsPathConnected U ∧
        (∀ s : unitInterval, (t i.castSucc : ℝ) ≤ s ∧ s ≤ (t i.succ : ℝ) → γ s ∈ U) ∧
        (∀ {p q : Path (γ (t i.castSucc)) (γ (t i.succ))},
          Set.range p ⊆ U → Set.range q ⊆ U → Path.Homotopic p q)) := by
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
  refine ⟨n, t, h_mono, h_start, h_end, ?_⟩
  intro i
  obtain ⟨U, hU_open, ⟨hU_pathConn, hU_homotopic⟩, hU_contains⟩ := h_partition i
  refine ⟨U, hU_open, hU_pathConn, hU_contains, ?_⟩
  intro p q hp hq
  -- The endpoints are in U because they're on the path segment
  have h_le : t i.castSucc ≤ t i.succ := h_mono.monotone (Fin.castSucc_lt_succ i).le
  have ha : γ (t i.castSucc) ∈ U := hU_contains (t i.castSucc) ⟨le_refl _, h_le⟩
  have hb : γ (t i.succ) ∈ U := hU_contains (t i.succ) ⟨h_le, le_refl _⟩
  exact @hU_homotopic (γ (t i.castSucc)) (γ (t i.succ)) ha hb p q hp hq

/-- Given a partition of the unit interval and open sets, the "tube" of paths that stay in the
corresponding open sets on each segment is open in the path space. This follows from the
compact-open topology: it's a finite intersection of sets {f | MapsTo f K U} where K is compact
and U is open. -/
theorem Path.tube_isOpen {x y : X}
    (n : ℕ) (t : Fin (n + 1) → unitInterval) (U : Fin n → Set X)
    (h_open : ∀ i, IsOpen (U i)) :
    IsOpen {γ' : Path x y | ∀ i (s : unitInterval),
      (t i.castSucc : ℝ) ≤ s ∧ s ≤ (t i.succ : ℝ) → γ' s ∈ U i} := by
  -- The tube is a finite intersection of open sets in the compact-open topology
  -- Each segment [t i, t i+1] is compact, so {γ' | γ' maps [t i, t i+1] into U i} is open
  have : {γ' : Path x y | ∀ i (s : unitInterval),
      (t i.castSucc : ℝ) ≤ s ∧ s ≤ (t i.succ : ℝ) → γ' s ∈ U i} =
    ⋂ i : Fin n, {γ' : Path x y | ∀ s : unitInterval,
      (t i.castSucc : ℝ) ≤ s ∧ s ≤ (t i.succ : ℝ) → γ' s ∈ U i} := by
    ext γ'
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  rw [this]
  -- Now show each set in the intersection is open
  apply isOpen_iInter_of_finite
  intro i
  -- The set {γ' | ∀ s ∈ [t i, t i+1], γ' s ∈ U i} is the same as {γ' | MapsTo γ' K_i (U i)}
  -- where K_i = Icc (t i.castSucc) (t i.succ) ⊆ unitInterval
  let K_i : Set unitInterval := Set.Icc (t i.castSucc) (t i.succ)
  have h_compact_K : IsCompact K_i := isCompact_Icc
  have h_eq : {γ' : Path x y | ∀ s : unitInterval,
      (t i.castSucc : ℝ) ≤ s ∧ s ≤ (t i.succ : ℝ) → γ' s ∈ U i} =
    {γ' : Path x y | Set.MapsTo γ' K_i (U i)} := by
    ext γ'
    simp only [Set.mem_setOf_eq, Set.MapsTo, K_i, Set.mem_Icc]
    refine forall_congr' fun s => ?_
    constructor
    · intro h hs; exact h hs
    · intro h hs; exact h hs
  rw [h_eq]
  -- Now use that this is open in the compact-open topology
  -- Path x y is a subtype of C(unitInterval, X), so we need to coerce
  have : {γ' : Path x y | Set.MapsTo γ' K_i (U i)} =
      (↑) ⁻¹' {f : C(unitInterval, X) | Set.MapsTo f K_i (U i)} := by
    rfl
  rw [this]
  exact (ContinuousMap.isOpen_setOf_mapsTo h_compact_K (h_open i)).preimage continuous_induced_dom

/-- In a path-connected set U, for any two points a and b in U, there exists a path from a to b
whose range is contained in U. -/
theorem exists_path_in_pathConnected_set {a b : X} (U : Set X) (hU : IsPathConnected U)
    (ha : a ∈ U) (hb : b ∈ U) :
    ∃ p : Path a b, Set.range p ⊆ U := by
  obtain ⟨x₀, hx₀, h_joined⟩ := hU
  have hab : JoinedIn U a b := (h_joined ha).symm.trans (h_joined hb)
  refine ⟨hab.somePath, ?_⟩
  intro y hy
  obtain ⟨t, rfl⟩ := hy
  exact hab.somePath_mem t

/-- For paths in the same SLSC neighborhood with the same endpoints, we can show they are
homotopic using the SLSC property applied to paths with same endpoints in U. -/
theorem Path.homotopic_in_slsc_neighborhood {a b : X} (U : Set X)
    (h_slsc : ∀ {x y : X} (p q : Path x y), x ∈ U → y ∈ U →
      Set.range p ⊆ U → Set.range q ⊆ U → Path.Homotopic p q)
    (γ γ' : Path a b)
    (hγ : Set.range γ ⊆ U) (hγ' : Set.range γ' ⊆ U)
    (ha : a ∈ U) (hb : b ∈ U) :
    Path.Homotopic γ γ' :=
  h_slsc γ γ' ha hb hγ hγ'

/-- Composing a path with a connecting path and then another path, all in an SLSC neighborhood,
gives a homotopy relationship useful for pasting segments together. This captures the idea that
γ · α ≃ α' · γ' when all paths lie in the same SLSC neighborhood. -/
theorem Path.trans_homotopy_in_slsc {a b c : X} (U : Set X)
    (h_slsc : ∀ {x y : X} (p q : Path x y), x ∈ U → y ∈ U →
      Set.range p ⊆ U → Set.range q ⊆ U → Path.Homotopic p q)
    (h_pathConn : IsPathConnected U)
    (γ : Path a b) (γ' : Path a c)
    (hγ : Set.range γ ⊆ U) (hγ' : Set.range γ' ⊆ U)
    (ha : a ∈ U) (hb : b ∈ U) (hc : c ∈ U) :
    ∃ (α : Path b c), Set.range α ⊆ U ∧ Path.Homotopic (γ.trans α) γ' := by
  obtain ⟨α, hα_range⟩ := exists_path_in_pathConnected_set U h_pathConn hb hc
  refine ⟨α, hα_range, ?_⟩
  apply h_slsc
  · exact ha
  · exact hc
  · exact Set.range_subset_iff.mpr fun t => by
      simp only [Path.trans_apply]
      split_ifs <;> [exact hγ (Set.mem_range_self _); exact hα_range (Set.mem_range_self _)]
  · exact hγ'

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

2. **The tube is open** (`tube_isOpen`):
   The set of paths `p'` such that `p'([tᵢ, tᵢ₊₁]) ⊆ Uᵢ` for all `i` is open in the
   compact-open topology on `Path x y`. This follows because each segment `[tᵢ, tᵢ₊₁]` is
   compact and each `Uᵢ` is open, so the tube is a finite intersection of sets of the form
   `{f | MapsTo f K U}` which are open by definition of the compact-open topology.

3. **Ladder homotopy construction** (`tube_subset_homotopy_class`):
   Any path `p'` in the tube is homotopic to `p` via a "ladder homotopy":

   - **Rungs** (`exists_rung_paths`): For each partition point `tᵢ`, construct a path `αᵢ`
     from `p(tᵢ)` to `p'(tᵢ)` using path-connectedness of the neighborhoods.
     The rungs at endpoints are constant paths since `p` and `p'` share endpoints.

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
theorem Path.exists_rung_paths {x y : X} (γ γ' : Path x y)
    (n : ℕ) (t : Fin (n + 1) → unitInterval) (U : Fin n → Set X)
    (h_pathConn : ∀ i, IsPathConnected (U i))
    (h_γ_in_U : ∀ i (s : unitInterval), (t i.castSucc : ℝ) ≤ s ∧ s ≤ (t i.succ : ℝ) → γ s ∈ U i)
    (h_γ'_in_U : ∀ i (s : unitInterval), (t i.castSucc : ℝ) ≤ s ∧ s ≤ (t i.succ : ℝ) → γ' s ∈ U i)
    (h_start : t 0 = 0) (h_end : t (Fin.last n) = 1) :
    ∃ α : (i : Fin (n + 1)) → Path (γ (t i)) (γ' (t i)),
      (∀ (i : Fin n), Set.range (α i.castSucc) ⊆ U i ∧ Set.range (α i.succ) ⊆ U i) := by
  -- Endpoints coincide since γ and γ' share the same start and end
  have h_eq_start : γ (t 0) = γ' (t 0) := by
    simp [h_start, γ.source, γ'.source]
  have h_eq_end : γ (t (Fin.last n)) = γ' (t (Fin.last n)) := by
    simp [h_end, γ.target, γ'.target]
  -- This lemma requires a careful construction of interior rungs that lie in intersections
  -- of consecutive U sets. This is genuinely difficult without additional hypotheses.
  -- For now, we note that this can be done using path connectivity when n is small
  -- or with additional structure on the U sets.
  sorry

/-! ### Homotopy algebra: composition rules needed for pasting -/

/-- Congruence for path composition: if p₁ ≃ p₂ and q₁ ≃ q₂, then p₁·q₁ ≃ p₂·q₂. -/
theorem Path.Homotopic.comp_congr {x y z : X} {p₁ p₂ : Path x y} {q₁ q₂ : Path y z}
    (hp : Path.Homotopic p₁ p₂) (hq : Path.Homotopic q₁ q₂) :
    Path.Homotopic (p₁.trans q₁) (p₂.trans q₂) :=
  Path.Homotopic.hcomp hp hq

/-- Homotopy respects path reversal: if p ≃ q then p.symm ≃ q.symm. -/
theorem Path.Homotopic.symm_congr {x y : X} {p q : Path x y}
    (h : Path.Homotopic p q) :
    Path.Homotopic p.symm q.symm :=
  Nonempty.map Path.Homotopy.symm₂ h

/-- A path composed with its reverse is homotopic to the constant path. -/
theorem Path.Homotopic.trans_symm_self {x y : X} (p : Path x y) :
    Path.Homotopic (p.trans p.symm) (Path.refl x) :=
  ⟨(Path.Homotopy.reflTransSymm p).symm⟩

/-- The reverse of a path composed with the path is homotopic to the constant path. -/
theorem Path.Homotopic.symm_trans_self {x y : X} (p : Path x y) :
    Path.Homotopic (p.symm.trans p) (Path.refl y) :=
  ⟨(Path.Homotopy.reflSymmTrans p).symm⟩

/-- Path composition is associative up to homotopy. -/
theorem Path.Homotopic.trans_assoc {w x y z : X} (p : Path w x) (q : Path x y) (r : Path y z) :
    Path.Homotopic ((p.trans q).trans r) (p.trans (q.trans r)) :=
  ⟨Path.Homotopy.transAssoc p q r⟩

/-- The constant path is a left identity for composition up to homotopy. -/
theorem Path.Homotopic.refl_trans {x y : X} (p : Path x y) :
    Path.Homotopic ((Path.refl x).trans p) p :=
  ⟨Path.Homotopy.reflTrans p⟩

/-- The constant path is a right identity for composition up to homotopy. -/
theorem Path.Homotopic.trans_refl {x y : X} (p : Path x y) :
    Path.Homotopic (p.trans (Path.refl y)) p :=
  ⟨Path.Homotopy.transRefl p⟩

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

/-- The pasting lemma for segment homotopies. Given:
- γ and γ' are paths that can be broken into n segments via partition points t
- α : (i : Fin (n+1)) → Path (γ (t i)) (γ' (t i)) are rung paths connecting partition points
- For each segment i, we have the rectangle homotopy: γᵢ · αᵢ₊₁ ≃ αᵢ · γ'ᵢ

Then by telescoping cancellation:
γ ≃ α₀ · γ' · αₙ⁻¹

Since α₀ and αₙ are constant paths (γ and γ' share endpoints), this gives γ ≃ γ'.

This is proved by induction on n, using the homotopy algebra lemmas. -/
theorem Path.paste_segment_homotopies {x y : X} (γ γ' : Path x y)
    (n : ℕ) (t : Fin (n + 1) → unitInterval)
    (h_mono : StrictMono t)
    (h_start : t 0 = 0) (h_end : t (Fin.last n) = 1)
    (γ_seg : (i : Fin n) → Path (γ (t i.castSucc)) (γ (t i.succ)))
    (γ'_seg : (i : Fin n) → Path (γ' (t i.castSucc)) (γ' (t i.succ)))
    (α : (i : Fin (n + 1)) → Path (γ (t i)) (γ' (t i)))
    (h_γ_seg : ∀ i s, s ∈ Set.Icc (t i.castSucc) (t i.succ) → γ s = (γ_seg i).extend s)
    (h_γ'_seg : ∀ i s, s ∈ Set.Icc (t i.castSucc) (t i.succ) → γ' s = (γ'_seg i).extend s)
    (h_α₀ : HEq (α 0) (Path.refl x))
    (h_αₙ : HEq (α (Fin.last n)) (Path.refl y))
    (h_rectangles : ∀ (i : Fin n),
        Path.Homotopic ((γ_seg i).trans (α i.succ)) ((α i.castSucc).trans (γ'_seg i))) :
    Path.Homotopic γ γ' := by
  sorry

/-- Given a path γ in an SLSC space, paths in the tube around γ are homotopic to γ.
This is the main result that combines all the previous lemmas:
1. Construct rung paths α_i using path-connectedness
2. For each segment, apply segment_rung_homotopy to get γ_i·α_{i+1} ≃ α_i·γ'_i
3. Use paste_segment_homotopies to get γ ≃ γ' by telescoping cancellation -/
theorem Path.tube_subset_homotopy_class (hX : SemilocallySimplyConnected X) {x y : X} (γ : Path x y)
    (n : ℕ) (t : Fin (n + 1) → unitInterval) (U : Fin n → Set X)
    (h_mono : StrictMono t)
    (h_start : t 0 = 0)
    (h_end : t (Fin.last n) = 1)
    (h_pathConn : ∀ i, IsPathConnected (U i))
    (h_slsc : ∀ i, ∀ {p q : Path (γ (t i.castSucc)) (γ (t i.succ))},
        Set.range p ⊆ U i → Set.range q ⊆ U i → Path.Homotopic p q)
    (h_contains : ∀ i (s : unitInterval), (t i.castSucc : ℝ) ≤ s ∧ s ≤ (t i.succ : ℝ) → γ s ∈ U i)
    (γ' : Path x y)
    (hγ' : ∀ i (s : unitInterval), (t i.castSucc : ℝ) ≤ s ∧ s ≤ (t i.succ : ℝ) → γ' s ∈ U i) :
    Path.Homotopic γ' γ := by
  sorry

/-- In an SLSC locally path-connected space, every path p has an open tubular neighborhood
contained in its homotopy class. This is THE KEY LEMMA that bridges the local SLSC property
to the global result that homotopy classes are open.

**Proof outline:**
1. Apply `exists_partition_in_slsc_neighborhoods` to get partition t and SLSC neighborhoods U
2. Define the tube T := {p' | ∀ i s, p'([tᵢ, tᵢ₊₁]) ⊆ Uᵢ}
3. Show T is open by `tube_isOpen` (uses compact-open topology)
4. Show p ∈ T (by construction, p respects the partition)
5. Show T ⊆ {p' | Homotopic p' p} by `tube_subset_homotopy_class` (uses ladder homotopy)

This shows that the SLSC property gives us not just any open set around p, but specifically
an open set where ALL paths are homotopic to p. This is what makes homotopy classes open. -/
theorem Path.exists_open_tubular_neighborhood_in_homotopy_class
    (hX : SemilocallySimplyConnected X) [LocPathConnectedSpace X]
    {x y : X} (p : Path x y) :
    ∃ (T : Set (Path x y)), IsOpen T ∧ p ∈ T ∧ T ⊆ {p' | Path.Homotopic p' p} := by
  -- Step 1: Get partition and SLSC neighborhoods
  obtain ⟨n, t, h_mono, h_start, h_end, h_partition⟩ :=
    Path.exists_partition_in_slsc_neighborhoods hX p
  -- Extract the U sets from the partition
  choose U hU_open hU_pathConn hU_contains hU_slsc using h_partition
  -- Step 2: Define the tube T
  let T : Set (Path x y) := {p' | ∀ i (s : unitInterval),
    (t i.castSucc : ℝ) ≤ s ∧ s ≤ (t i.succ : ℝ) → p' s ∈ U i}
  refine ⟨T, ?_, ?_, ?_⟩
  · -- Show T is open using tube_isOpen
    exact Path.tube_isOpen n t U hU_open
  · -- Show p ∈ T
    exact hU_contains
  · -- Show T ⊆ {p' | Homotopic p' p} using tube_subset_homotopy_class
    intro p' hp'
    apply Path.tube_subset_homotopy_class hX p n t U h_mono h_start h_end
    · exact hU_pathConn
    · exact hU_slsc
    · exact hU_contains
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

/-- In a semilocally simply connected, locally path-connected space, the quotient of paths by
homotopy has discrete topology. This is a key step in proving that semilocally simply connected
spaces admit universal covers.

**Proof:** By `isOpen_setOf_homotopic`, every homotopy class H(p) = {p' | Homotopic p' p} is
open in Path x y. Under the quotient map π : Path x y → Path.Homotopic.Quotient x y, the
preimage π⁻¹({⟦p⟧}) = H(p) is open. Since preimages of singletons are open, every singleton
in the quotient is open, giving the discrete topology. -/
theorem Path.Homotopic.Quotient.discreteTopology
    (hX : SemilocallySimplyConnected X) [LocPathConnectedSpace X] (x y : X) :
    DiscreteTopology (Path.Homotopic.Quotient x y) := by
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
