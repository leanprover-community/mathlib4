/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Order
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Connected.LocPathConnected

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

open CategoryTheory FundamentalGroupoid

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
  sorry

/-- The preimage of a singleton homotopy class under the quotient map is the set of all paths
homotopic to a representative. -/
theorem Path.Homotopic.fiber_eq (x y : X) (p : Path x y) :
    letI : Setoid (Path x y) := Path.Homotopic.setoid x y
    (Quotient.mk' : Path x y → Path.Homotopic.Quotient x y) ⁻¹' {⟦p⟧} =
      {p' : Path x y | Path.Homotopic p' p} := by
  sorry

/-- A singleton in the quotient topology is open if and only if its preimage is open. -/
theorem Path.Homotopic.singleton_isOpen_iff (x y : X) (p : Path x y) :
    letI : Setoid (Path x y) := Path.Homotopic.setoid x y
    IsOpen ({⟦p⟧} : Set (Path.Homotopic.Quotient x y)) ↔
      IsOpen ((Quotient.mk' : Path x y → Path.Homotopic.Quotient x y) ⁻¹' {⟦p⟧}) := by
  sorry

/-- In an SLSC space, given a path γ, there exists a finite partition of [0,1] such that
each segment of γ lies in a path-connected SLSC neighborhood. This uses compactness of the
path's image and the Lebesgue number lemma. -/
theorem Path.exists_partition_in_slsc_neighborhoods (hX : SemilocallySimplyConnected X)
    {x y : X} (γ : Path x y) :
    ∃ (n : ℕ) (t : Fin (n + 1) → unitInterval),
      StrictMono t ∧
      t 0 = 0 ∧
      t (Fin.last n) = 1 ∧
      (∀ i : Fin n, ∃ U : Set X, IsOpen U ∧ IsPathConnected U ∧
        (∀ s : unitInterval, (t i.castSucc : ℝ) ≤ s ∧ s ≤ (t i.succ : ℝ) → γ s ∈ U) ∧
        (∀ {p q : Path (γ (t i.castSucc)) (γ (t i.succ))},
          Set.range p ⊆ U → Set.range q ⊆ U → Path.Homotopic p q)) := by
  sorry

/-- Given a path γ with a partition into SLSC segments, the "tube" of paths that stay in the
same neighborhoods as γ on each segment is an open set in the path space. This follows from
the definition of the compact-open topology on the path space. -/
theorem Path.tube_isOpen (hX : SemilocallySimplyConnected X) {x y : X} (γ : Path x y)
    (n : ℕ) (t : Fin (n + 1) → unitInterval) (U : Fin n → Set X)
    (h_mono : StrictMono t)
    (h_start : t 0 = 0)
    (h_end : t (Fin.last n) = 1)
    (h_open : ∀ i, IsOpen (U i))
    (h_pathConn : ∀ i, IsPathConnected (U i))
    (h_contains : ∀ i (s : unitInterval),
      (t i.castSucc : ℝ) ≤ s ∧ s ≤ (t i.succ : ℝ) → γ s ∈ U i) :
    IsOpen {γ' : Path x y | ∀ i (s : unitInterval),
      (t i.castSucc : ℝ) ≤ s ∧ s ≤ (t i.succ : ℝ) → γ' s ∈ U i} := by
  sorry

/-- In an SLSC neighborhood where loops are nullhomotopic, any two paths with the same
endpoints are homotopic. This is derived by composing one path with the reverse of the other
to form a loop. -/
theorem Path.homotopic_of_loops_nullhomotopic_in_neighborhood {x y : X} (U : Set X)
    (h_loops : ∀ {z : X} (γ : Path z z), z ∈ U → Set.range γ ⊆ U → Path.Homotopic γ (Path.refl z))
    {p q : Path x y} (hp : Set.range p ⊆ U) (hq : Set.range q ⊆ U) :
    Path.Homotopic p q := by
  sorry

/-- An SLSC neighborhood can be chosen to be path-connected (since we can intersect it with
a path-connected neighborhood). -/
theorem exists_pathConnected_slsc_neighborhood (hX : SemilocallySimplyConnected X)
    [LocPathConnectedSpace X] (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPathConnected U ∧
      (∀ {p q : Path x x}, Set.range p ⊆ U → Set.range q ⊆ U → Path.Homotopic p q) := by
  sorry

/-- In a path-connected set U, for any two points a and b in U, there exists a path from a to b
whose range is contained in U. -/
theorem exists_path_in_pathConnected_set {a b : X} (U : Set X) (hU : IsPathConnected U)
    (ha : a ∈ U) (hb : b ∈ U) :
    ∃ p : Path a b, Set.range p ⊆ U := by
  sorry

/-- For paths in the same SLSC neighborhood with the same endpoints, we can show they are
homotopic using the SLSC property applied to paths with same endpoints in U. -/
theorem Path.homotopic_in_slsc_neighborhood {a b : X} (U : Set X)
    (h_slsc : ∀ {x y : X} (p q : Path x y), x ∈ U → y ∈ U →
      Set.range p ⊆ U → Set.range q ⊆ U → Path.Homotopic p q)
    (γ γ' : Path a b)
    (hγ : Set.range γ ⊆ U) (hγ' : Set.range γ' ⊆ U)
    (ha : a ∈ U) (hb : b ∈ U) :
    Path.Homotopic γ γ' := by
  sorry

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
  sorry

/-! ### Construction of "rung" paths for the ladder homotopy -/

/-- Given two paths γ and γ' in a tube with partition points t_i, we can construct connecting
"rung" paths α_i from γ(t_i) to γ'(t_i), where each α_i lies in the appropriate neighborhood.
The rungs at the endpoints (α_0 and α_n) are constant paths since γ and γ' share endpoints. -/
theorem Path.exists_rung_paths {x y : X} (γ γ' : Path x y)
    (n : ℕ) (t : Fin (n + 1) → unitInterval) (U : Fin n → Set X)
    (h_pathConn : ∀ i, IsPathConnected (U i))
    (h_γ_in_U : ∀ i (s : unitInterval), (t i.castSucc : ℝ) ≤ s ∧ s ≤ (t i.succ : ℝ) → γ s ∈ U i)
    (h_γ'_in_U : ∀ i (s : unitInterval), (t i.castSucc : ℝ) ≤ s ∧ s ≤ (t i.succ : ℝ) → γ' s ∈ U i)
    (h_start : t 0 = 0) (h_end : t (Fin.last n) = 1) :
    ∃ α : Fin (n + 1) → Σ (a b : X), Path a b,
      (∀ i, (α i).1 = γ (t i)) ∧
      (∀ i, (α i).2.1 = γ' (t i)) ∧
      α 0 = ⟨x, x, Path.refl x⟩ ∧
      α (Fin.last n) = ⟨y, y, Path.refl y⟩ ∧
      (∀ i : Fin n, Set.range (α i.castSucc).2.2 ⊆ U i ∨ Set.range (α i.succ).2.2 ⊆ U i) := by
  sorry

/-! ### Homotopy algebra: composition rules needed for pasting -/

/-- Congruence for path composition: if p₁ ≃ p₂ and q₁ ≃ q₂, then p₁·q₁ ≃ p₂·q₂. -/
theorem Path.Homotopic.comp_congr {x y z : X} {p₁ p₂ : Path x y} {q₁ q₂ : Path y z}
    (hp : Path.Homotopic p₁ p₂) (hq : Path.Homotopic q₁ q₂) :
    Path.Homotopic (p₁.trans q₁) (p₂.trans q₂) := by
  sorry

/-- Homotopy respects path reversal: if p ≃ q then p.symm ≃ q.symm. -/
theorem Path.Homotopic.symm_congr {x y : X} {p q : Path x y}
    (h : Path.Homotopic p q) :
    Path.Homotopic p.symm q.symm := by
  sorry

/-- A path composed with its reverse is homotopic to the constant path. -/
theorem Path.Homotopic.trans_symm_self {x y : X} (p : Path x y) :
    Path.Homotopic (p.trans p.symm) (Path.refl x) := by
  sorry

/-- The reverse of a path composed with the path is homotopic to the constant path. -/
theorem Path.Homotopic.symm_trans_self {x y : X} (p : Path x y) :
    Path.Homotopic (p.symm.trans p) (Path.refl y) := by
  sorry

/-- Path composition is associative up to homotopy. -/
theorem Path.Homotopic.trans_assoc {w x y z : X} (p : Path w x) (q : Path x y) (r : Path y z) :
    Path.Homotopic ((p.trans q).trans r) (p.trans (q.trans r)) := by
  sorry

/-- The constant path is a left identity for composition up to homotopy. -/
theorem Path.Homotopic.refl_trans {x y : X} (p : Path x y) :
    Path.Homotopic ((Path.refl x).trans p) p := by
  sorry

/-- The constant path is a right identity for composition up to homotopy. -/
theorem Path.Homotopic.trans_refl {x y : X} (p : Path x y) :
    Path.Homotopic (p.trans (Path.refl y)) p := by
  sorry

/-! ### Single segment homotopy: the key step in the ladder construction -/

/-- For a single segment i, the path γ_i · α_{i+1} (along γ then down the next rung) is
homotopic to α_i · γ'_i (down the current rung then along γ'). Both paths lie entirely in
the SLSC neighborhood U_i, and since they share endpoints, the SLSC property implies they
are homotopic. This is the crucial "rectangle" homotopy for each segment. -/
theorem Path.segment_rung_homotopy {a b c d : X} (U : Set X)
    (h_slsc : ∀ {x y : X} (p q : Path x y), x ∈ U → y ∈ U →
      Set.range p ⊆ U → Set.range q ⊆ U → Path.Homotopic p q)
    (h_pathConn : IsPathConnected U)
    (γ : Path a b) (γ' : Path c d) (α_start : Path a c) (α_end : Path b d)
    (hγ : Set.range γ ⊆ U) (hγ' : Set.range γ' ⊆ U)
    (hα_start : Set.range α_start ⊆ U) (hα_end : Set.range α_end ⊆ U)
    (ha : a ∈ U) (hb : b ∈ U) (hc : c ∈ U) (hd : d ∈ U) :
    Path.Homotopic (γ.trans α_end) (α_start.trans γ') := by
  sorry

/-! ### Pasting lemma: telescoping cancellation of rungs -/

/-- The pasting lemma for segment homotopies. Given:
- γ = γ₀ · γ₁ · ... · γₙ₋₁ (path broken into n segments)
- γ' = γ'₀ · γ'₁ · ... · γ'ₙ₋₁ (another path broken into n segments)
- α₀, α₁, ..., αₙ (rung paths connecting partition points)
- For each segment i: γᵢ · α_{i+1} ≃ αᵢ · γ'ᵢ

Then by telescoping cancellation:
γ ≃ α₀ · γ' · αₙ⁻¹

Since α₀ and αₙ are constant paths (γ and γ' share endpoints), this gives γ ≃ γ'.

This is proved by induction on n, using the homotopy algebra lemmas. -/
theorem Path.paste_segment_homotopies {x y : X} (γ γ' : Path x y)
    (n : ℕ) (t : Fin (n + 1) → unitInterval)
    (h_start : t 0 = 0) (h_end : t (Fin.last n) = 1)
    -- We need to express segments and rungs properly, but this captures the idea
    (h_segments : ∀ i : Fin n, True) -- Placeholder for segment homotopy condition
    :
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

/-- In an SLSC space, for any path p, the set of paths homotopic to p is open. -/
theorem Path.isOpen_setOf_homotopic (hX : SemilocallySimplyConnected X) {x y : X} (p : Path x y) :
    IsOpen {p' : Path x y | Path.Homotopic p' p} := by
  sorry

/-- In a semilocally simply connected space, the quotient of paths by homotopy has discrete
topology. This is a key step in proving that semilocally simply connected spaces admit
universal covers. -/
theorem Path.Homotopic.Quotient.discreteTopology (hX : SemilocallySimplyConnected X) (x y : X) :
    DiscreteTopology (Path.Homotopic.Quotient x y) := by
  sorry

end SemilocallySimplyConnected
