/-
Copyright (c) 2026 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Action
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.Tactic.Group

/-!
# Coset graphs (Sabidussi construction)

Given a group `G`, a subgroup `H`, and a *connection set* `D ⊆ G` that is a union of
`(H, H)`-double cosets, is symmetric (`D = D⁻¹`), and is disjoint from `H`, we define the
**coset graph** `Sab(G, H, D)` whose vertices are the left cosets `G ⧸ H` and whose edges
connect `xH` to `yH` whenever `x⁻¹y ∈ D`.

This is Sabidussi's generalization of Cayley graphs: when `H = ⊥`, the coset graph on
`G ⧸ ⊥ ≃ G` recovers the Cayley graph `Cay(G, D)`.

## Main definitions

* `IsConnectionSet H D` — `D` is a union of `(H, H)`-double cosets, closed under inversion,
  and disjoint from `H`
* `SimpleGraph.cosetGraph H D` — the coset graph `Sab(G, H, D)` as a `SimpleGraph (G ⧸ H)`

## Main results

* `SimpleGraph.cosetGraph.adj_mk` — adjacency is characterized by `x⁻¹y ∈ D`
* `SimpleGraph.cosetGraph.graphAction` — `G` acts on the coset graph preserving adjacency
* `SimpleGraph.cosetGraph.isVertexTransitive` — coset graphs are vertex-transitive

## References

* Robin Langer, *Symmetric Graphs and their Quotients*, arXiv:1306.4798, Chapter 2 §2.
* Sabidussi, *Vertex-transitive graphs*, Monatsh. Math. 68 (1964), 426–438.
-/

@[expose] public section

variable {G : Type*} [Group G]

/-- A set `D ⊆ G` is a *connection set* for the subgroup `H` if it is stable under
left and right multiplication by `H` (i.e., a union of `(H,H)`-double cosets),
is closed under inversion, and is disjoint from `H`. -/
structure IsConnectionSet (H : Subgroup G) (D : Set G) : Prop where
  /-- `D` is stable under left and right multiplication by elements of `H`. -/
  double_coset_stable : ∀ d ∈ D, ∀ h₁ ∈ (H : Set G), ∀ h₂ ∈ (H : Set G), h₁ * d * h₂ ∈ D
  /-- `D` is closed under inversion. -/
  inv_mem : ∀ d ∈ D, d⁻¹ ∈ D
  /-- `D` is disjoint from `H`. -/
  disjoint : Disjoint D ↑H

namespace IsConnectionSet

variable {H : Subgroup G} {D : Set G}

theorem one_not_mem (hD : IsConnectionSet H D) : (1 : G) ∉ D :=
  fun h => Set.disjoint_left.mp hD.disjoint h (Subgroup.one_mem H)

end IsConnectionSet

/-- The **coset graph** `Sab(G, H, D)`. Vertices are the left cosets `G ⧸ H`,
and two cosets `xH, yH` are adjacent iff `x⁻¹y ∈ D`.

This is Sabidussi's generalization of Cayley graphs: when `H = ⊥`,
the coset graph on `G ⧸ ⊥ ≃ G` recovers the Cayley graph `Cay(G, D)`. -/
noncomputable def SimpleGraph.cosetGraph (H : Subgroup G) (D : Set G)
    (hD : IsConnectionSet H D) : SimpleGraph (G ⧸ H) where
  Adj q₁ q₂ := Quotient.liftOn₂ q₁ q₂ (fun x y => x⁻¹ * y ∈ D)
    (fun a₁ b₁ a₂ b₂ h₁ h₂ => by
      have ha : a₁⁻¹ * a₂ ∈ (H : Set G) := QuotientGroup.leftRel_apply.mp h₁
      have hb : b₁⁻¹ * b₂ ∈ (H : Set G) := QuotientGroup.leftRel_apply.mp h₂
      apply propext; change a₁⁻¹ * b₁ ∈ D ↔ a₂⁻¹ * b₂ ∈ D; constructor
      · intro h
        have key : a₂⁻¹ * b₂ = (a₂⁻¹ * a₁) * (a₁⁻¹ * b₁) * (b₁⁻¹ * b₂) := by group
        rw [key]
        refine hD.double_coset_stable _ h _ ?_ _ hb
        have : (a₁⁻¹ * a₂)⁻¹ ∈ (H : Set G) := H.inv_mem ha
        rwa [mul_inv_rev, inv_inv] at this
      · intro h
        have key : a₁⁻¹ * b₁ = (a₁⁻¹ * a₂) * (a₂⁻¹ * b₂) * (b₂⁻¹ * b₁) := by group
        rw [key]
        refine hD.double_coset_stable _ h _ ha _ ?_
        have : (b₁⁻¹ * b₂)⁻¹ ∈ (H : Set G) := H.inv_mem hb
        rwa [mul_inv_rev, inv_inv] at this)
  symm := by
    intro q₁ q₂
    refine Quotient.inductionOn₂ q₁ q₂ fun x y => ?_
    simp only [Quotient.liftOn₂_mk]
    intro h
    have hmem := hD.inv_mem _ h
    rwa [mul_inv_rev, inv_inv] at hmem
  loopless := ⟨by
    intro q
    refine Quotient.inductionOn q fun x => ?_
    simp only [Quotient.liftOn₂_mk]
    show ¬(x⁻¹ * x ∈ D)
    rw [inv_mul_cancel]
    exact hD.one_not_mem⟩

namespace SimpleGraph.cosetGraph

variable (H : Subgroup G) (D : Set G) (hD : IsConnectionSet H D)

/-- Adjacency in the coset graph is characterized by membership of `x⁻¹y` in `D`. -/
@[simp]
theorem adj_mk (x y : G) :
    (cosetGraph H D hD).Adj (QuotientGroup.mk x) (QuotientGroup.mk y) ↔ x⁻¹ * y ∈ D :=
  Iff.rfl

/-- The left multiplication action of `G` on `G ⧸ H` preserves coset graph adjacency. -/
instance graphAction : GraphAction G (G ⧸ H) (cosetGraph H D hD) where
  adj_smul g q₁ q₂ := by
    refine Quotient.inductionOn₂ q₁ q₂ fun x y => ?_
    intro h
    change (g * x)⁻¹ * (g * y) ∈ D
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    exact h

/-- Coset graphs are vertex-transitive under the natural action of `G`. -/
instance isVertexTransitive : IsVertexTransitive G (G ⧸ H) (cosetGraph H D hD) where
  pretransitive := MulAction.isPretransitive_quotient G H

end SimpleGraph.cosetGraph

/-! ## Coset projection

When `H ≤ K`, the natural projection `G ⧸ H → G ⧸ K` sends `gH ↦ gK`.
If `D` is a connection set for both `H` and `K`, this projection is a
graph homomorphism: adjacency in `Sab(G, H, D)` implies adjacency in
`Sab(G, K, D)`.

This is the Sabidussi analogue of quotient by a block system: the orbits
of `K` on `G ⧸ H` form a system of blocks of size `[K : H]`, and the
quotient graph is `Sab(G, K, D)`. -/

/-- The natural projection `G ⧸ H → G ⧸ K` when `H ≤ K`. -/
def cosetProjection (H K : Subgroup G) (hle : H ≤ K) :
    G ⧸ H → G ⧸ K :=
  Quotient.map id fun _ _ hab => by
    change (QuotientGroup.leftRel K).r _ _
    have hab' : (QuotientGroup.leftRel H).r _ _ := hab
    rw [QuotientGroup.leftRel_apply] at hab' ⊢
    exact hle hab'

@[simp]
theorem cosetProjection_mk (H K : Subgroup G) (hle : H ≤ K)
    (g : G) : cosetProjection H K hle ⟦g⟧ = ⟦g⟧ :=
  rfl

/-- **Coset projection is a graph homomorphism**: if `H ≤ K` and `D` is a
    connection set for both, then adjacency in `Sab(G, H, D)` implies
    adjacency in `Sab(G, K, D)`.

    The proof is trivial: adjacency is `x⁻¹y ∈ D` in both graphs.
    The subgroup only determines the coset equivalence, not the adjacency test. -/
theorem SimpleGraph.cosetGraph.proj_adj
    {H K : Subgroup G} (hle : H ≤ K) {D : Set G}
    (hDH : IsConnectionSet H D) (hDK : IsConnectionSet K D)
    (q₁ q₂ : G ⧸ H) :
    (cosetGraph H D hDH).Adj q₁ q₂ →
    (cosetGraph K D hDK).Adj (cosetProjection H K hle q₁)
                              (cosetProjection H K hle q₂) :=
  Quotient.inductionOn₂ q₁ q₂ fun _ _ h => h

/-- The coset projection is surjective. -/
theorem cosetProjection_surjective (H K : Subgroup G) (hle : H ≤ K) :
    Function.Surjective (cosetProjection H K hle) :=
  fun q => Quotient.inductionOn q fun g => ⟨⟦g⟧, rfl⟩
