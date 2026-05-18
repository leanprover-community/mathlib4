/-
Copyright (c) 2026 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
module

public import Mathlib.Combinatorics.SimpleGraph.CosetGraph
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Tactic.Group

/-!
# The Sabidussi representation theorem

Every vertex-transitive graph is isomorphic to a coset graph. More precisely,
if `G` acts vertex-transitively on a graph `Γ`, then for any basepoint `v`,
the orbit-stabilizer equivalence `V ≃ G ⧸ stabilizer G v` is a graph
isomorphism from `Γ` to `Sab(G, Gᵥ, D)`, where `D = {g ∈ G : Γ.Adj v (g • v)}`.

## Main definitions

* `connectionSet G Γ v` — the set of group elements moving `v` to a neighbor
* `connectionSet.isConnectionSet` — the connection set satisfies the axioms
* `sabidussiEquiv` — the equivalence `V ≃ G ⧸ stabilizer G v` for transitive actions
* `sabidussiIso` — the graph isomorphism `Γ ≃g cosetGraph (stabilizer G v) D`

## References

* Robin Langer, *Symmetric Graphs and their Quotients*, arXiv:1306.4798, Chapter 2 §2.
* Sabidussi, *Vertex-transitive graphs*, Monatsh. Math. 68 (1964), 426–438.
-/

@[expose] public section

variable {G V : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

/-! ### The connection set -/

/-- The *connection set* of a basepoint `v`: the set of group elements
that move `v` to one of its neighbors. -/
def connectionSet (G : Type*) [Group G] [MulAction G V]
    (Γ : SimpleGraph V) (v : V) : Set G :=
  {g : G | Γ.Adj v (g • v)}

namespace connectionSet

variable [GraphAction G V Γ] (v : V)

omit [GraphAction G V Γ] in
theorem one_not_mem : (1 : G) ∉ connectionSet G Γ v := by
  simp [connectionSet]

theorem inv_mem {g : G} (hg : g ∈ connectionSet G Γ v) :
    g⁻¹ ∈ connectionSet G Γ v := by
  simp only [connectionSet, Set.mem_setOf_eq] at hg ⊢
  have h := Γ.symm hg
  rwa [← GraphAction.adj_smul_iff g⁻¹, inv_smul_smul] at h

theorem double_coset_stable {g : G} (hg : g ∈ connectionSet G Γ v)
    {h₁ : G} (hh₁ : h₁ ∈ MulAction.stabilizer G v)
    {h₂ : G} (hh₂ : h₂ ∈ MulAction.stabilizer G v) :
    h₁ * g * h₂ ∈ connectionSet G Γ v := by
  simp only [connectionSet, Set.mem_setOf_eq] at hg ⊢
  rw [mul_smul, mul_smul, MulAction.mem_stabilizer_iff.mp hh₂]
  have := GraphAction.adj_smul h₁ v (g • v) hg
  rwa [MulAction.mem_stabilizer_iff.mp hh₁] at this

omit [GraphAction G V Γ] in
theorem disjoint_stabilizer :
    Disjoint (connectionSet G Γ v) ↑(MulAction.stabilizer G v) := by
  rw [Set.disjoint_left]
  intro g hg hstab
  simp only [connectionSet, Set.mem_setOf_eq] at hg
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hstab
  rw [hstab] at hg
  exact (Γ.loopless.irrefl v) hg

/-- The connection set forms a valid `IsConnectionSet` for the stabilizer subgroup. -/
theorem isConnectionSet :
    IsConnectionSet (MulAction.stabilizer G v) (connectionSet G Γ v) where
  double_coset_stable _ hd _ hh₁ _ hh₂ := double_coset_stable v hd hh₁ hh₂
  inv_mem _ hd := inv_mem v hd
  disjoint := disjoint_stabilizer v

end connectionSet

/-! ### The orbit-stabilizer equivalence -/

section SabidussiRepresentation

variable [GraphAction G V Γ] [MulAction.IsPretransitive G V] (v : V)

/-- The equivalence `V ≃ G ⧸ stabilizer G v` for a transitive action.

The forward map sends `u` to the coset `gH` where `g • v = u`.
The inverse map sends `⟦g⟧` to `g • v`. -/
noncomputable def sabidussiEquiv : V ≃ G ⧸ MulAction.stabilizer G v where
  toFun u := QuotientGroup.mk (MulAction.exists_smul_eq G v u).choose
  invFun := Quotient.lift (· • v) (by
    intro a b hab
    have hmem : (a⁻¹ * b) • v = v :=
      MulAction.mem_stabilizer_iff.mp (QuotientGroup.leftRel_apply.mp hab)
    calc a • v = a • ((a⁻¹ * b) • v) := by rw [hmem]
      _ = (a * (a⁻¹ * b)) • v := (mul_smul a (a⁻¹ * b) v).symm
      _ = b • v := by rw [mul_inv_cancel_left])
  left_inv u := by
    simp only
    exact (MulAction.exists_smul_eq G v u).choose_spec
  right_inv := by
    intro q
    refine Quotient.inductionOn q fun g => ?_
    simp only [Quotient.lift_mk]
    apply QuotientGroup.eq.mpr
    rw [MulAction.mem_stabilizer_iff, mul_smul]
    set g' := (MulAction.exists_smul_eq G v (g • v)).choose
    have hspec : g' • v = g • v := (MulAction.exists_smul_eq G v (g • v)).choose_spec
    calc g'⁻¹ • (g • v) = g'⁻¹ • (g' • v) := by rw [hspec]
      _ = v := inv_smul_smul g' v

@[simp]
theorem sabidussiEquiv_smul (g : G) :
    sabidussiEquiv v (g • v) = (g : G ⧸ MulAction.stabilizer G v) := by
  simp only [sabidussiEquiv]
  apply QuotientGroup.eq.mpr
  rw [MulAction.mem_stabilizer_iff, mul_smul]
  set g' := (MulAction.exists_smul_eq G v (g • v)).choose
  have hspec : g' • v = g • v := (MulAction.exists_smul_eq G v (g • v)).choose_spec
  calc g'⁻¹ • (g • v) = g'⁻¹ • (g' • v) := by rw [hspec]
    _ = v := inv_smul_smul g' v

@[simp]
theorem sabidussiEquiv_symm_mk (g : G) :
    (sabidussiEquiv v).symm (QuotientGroup.mk g) = g • v := by
  rfl

/-- **Sabidussi's Representation Theorem**: Every vertex-transitive graph is
isomorphic to a coset graph.

The orbit-stabilizer equivalence `V ≃ G ⧸ stabilizer G v` is a graph isomorphism
from `Γ` to `cosetGraph (stabilizer G v) (connectionSet G Γ v)`. -/
noncomputable def sabidussiIso :
    Γ ≃g SimpleGraph.cosetGraph (MulAction.stabilizer G v)
      (connectionSet G Γ v) (connectionSet.isConnectionSet v) where
  toEquiv := sabidussiEquiv v
  map_rel_iff' := by
    intro u w
    set g₁ := (MulAction.exists_smul_eq G v u).choose
    set g₂ := (MulAction.exists_smul_eq G v w).choose
    have hu : g₁ • v = u := (MulAction.exists_smul_eq G v u).choose_spec
    have hw : g₂ • v = w := (MulAction.exists_smul_eq G v w).choose_spec
    change g₁⁻¹ * g₂ ∈ connectionSet G Γ v ↔ Γ.Adj u w
    rw [← hu, ← hw]
    simp only [connectionSet, Set.mem_setOf_eq, mul_smul]
    constructor
    · intro h
      have := (@GraphAction.adj_smul_iff G V _ _ Γ _ g₁⁻¹ (g₁ • v) (g₂ • v)).mp
        (by rwa [inv_smul_smul])
      exact this
    · intro h
      have := (@GraphAction.adj_smul_iff G V _ _ Γ _ g₁⁻¹ (g₁ • v) (g₂ • v)).mpr h
      rwa [inv_smul_smul] at this

end SabidussiRepresentation
