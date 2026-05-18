/-
Copyright (c) 2026 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Symmetric
public import Mathlib.GroupTheory.GroupAction.Blocks

/-!
# Quotient graphs and the Lorimer quotient theorem

The quotient of a symmetric graph `Sab(G, H, HaH)` by a `G`-invariant partition
is again a symmetric graph `Sab(G, K, KaK)` for some overgroup `H ≤ K ≤ G`.

## Main definitions

* `SimpleGraph.quotientGraph` — quotient of a graph by a surjection (partition)
* `cosetQuotientMap` — the natural map `G ⧸ H → G ⧸ K` for `H ≤ K`
* `expandConnectionSet` — the expanded connection set `KDK` for an overgroup `K`

## Main results

* `quotient_cosetGraph_iso` — the quotient of `Sab(G,H,D)` is isomorphic to `Sab(G,K,KDK)`

## References

* Robin Langer, *Symmetric Graphs and their Quotients*, arXiv:1306.4798, Chapter 2 §4.
-/

@[expose] public section

variable {G : Type*} [Group G]

/-! ### Quotient graph construction -/

/-- The **quotient graph** of `Γ` with respect to a surjection `π : V → ι`. -/
def SimpleGraph.quotientGraph {V ι : Type*} (Γ : SimpleGraph V) (π : V → ι) :
    SimpleGraph ι where
  Adj i j := i ≠ j ∧ ∃ u v : V, π u = i ∧ π v = j ∧ Γ.Adj u v
  symm := by
    intro i j ⟨hne, u, v, hui, hvj, hadj⟩
    exact ⟨hne.symm, v, u, hvj, hui, Γ.symm hadj⟩
  loopless := ⟨fun i ⟨hne, _⟩ => hne rfl⟩

/-! ### The coset quotient map -/

/-- The natural map `G ⧸ H → G ⧸ K` for `H ≤ K`, sending `gH ↦ gK`. -/
noncomputable def cosetQuotientMap (H K : Subgroup G) (hHK : H ≤ K) :
    G ⧸ H → G ⧸ K :=
  Quotient.map' id (fun _ _ h => QuotientGroup.leftRel_apply.mpr
    (hHK (QuotientGroup.leftRel_apply.mp h)))

@[simp]
theorem cosetQuotientMap_mk (H K : Subgroup G) (hHK : H ≤ K) (g : G) :
    cosetQuotientMap H K hHK (QuotientGroup.mk g) = QuotientGroup.mk g :=
  rfl

/-! ### Expanded connection set KDK -/

/-- The expanded connection set `KDK` for an overgroup `K`. -/
def expandConnectionSet (K : Subgroup G) (D : Set G) : Set G :=
  {g : G | ∃ k₁ ∈ (K : Set G), ∃ d ∈ D, ∃ k₂ ∈ (K : Set G), g = k₁ * d * k₂}

/-- `KDK` is a valid connection set for `K` when `D ∩ K = ∅`. -/
theorem expandConnectionSet_isConnectionSet (H K : Subgroup G) (D : Set G)
    (hD : IsConnectionSet H D) (hDK : Disjoint D ↑K) :
    IsConnectionSet K (expandConnectionSet K D) where
  double_coset_stable := by
    intro d hd m₁ hm₁ m₂ hm₂
    obtain ⟨k₁, hk₁, e, he, k₂, hk₂, rfl⟩ := hd
    exact ⟨m₁ * k₁, K.mul_mem hm₁ hk₁, e, he, k₂ * m₂, K.mul_mem hk₂ hm₂, by group⟩
  inv_mem := by
    intro d hd
    obtain ⟨k₁, hk₁, e, he, k₂, hk₂, rfl⟩ := hd
    exact ⟨k₂⁻¹, K.inv_mem hk₂, e⁻¹, hD.inv_mem e he, k₁⁻¹, K.inv_mem hk₁, by group⟩
  disjoint := by
    rw [Set.disjoint_left]
    intro g hg hgK
    obtain ⟨k₁, hk₁, d, hd, k₂, hk₂, rfl⟩ := hg
    have : d ∈ (K : Set G) := by
      have := K.mul_mem (K.mul_mem (K.inv_mem hk₁) hgK) (K.inv_mem hk₂)
      convert this using 1; group
    exact Set.disjoint_left.mp hDK hd this

/-! ### The Lorimer quotient theorem -/

/-- **Lorimer's Quotient Theorem**: The quotient of `Sab(G, H, D)` by the overgroup
`K ≥ H` (with `D ∩ K = ∅`) is isomorphic to `Sab(G, K, KDK)`.

The quotient map `G ⧸ H → G ⧸ K` (sending `gH ↦ gK`) induces a graph
isomorphism from the quotient graph to the coset graph with expanded
connection set. -/
noncomputable def quotient_cosetGraph_iso (H K : Subgroup G) (D : Set G)
    (hD : IsConnectionSet H D) (hHK : H ≤ K)
    (hDK : Disjoint D ↑K) :
    SimpleGraph.quotientGraph (SimpleGraph.cosetGraph H D hD) (cosetQuotientMap H K hHK) ≃g
      SimpleGraph.cosetGraph K (expandConnectionSet K D)
        (expandConnectionSet_isConnectionSet H K D hD hDK) where
  toEquiv := Equiv.refl _
  map_rel_iff' := by
    intro q₁ q₂
    refine Quotient.inductionOn₂ q₁ q₂ fun x y => ?_
    simp only [Equiv.refl_apply]
    rw [SimpleGraph.cosetGraph.adj_mk]
    constructor
    · intro ⟨k₁, hk₁, d, hd, k₂, hk₂, heq⟩
      refine ⟨?_, QuotientGroup.mk (x * k₁),
             QuotientGroup.mk (x * k₁ * d), ?_, ?_, ?_⟩
      · intro heq'
        have : d ∈ (K : Set G) := by
          have hK : k₁ * d * k₂ ∈ (K : Set G) := heq ▸ QuotientGroup.eq.mp heq'
          have := K.mul_mem (K.mul_mem (K.inv_mem hk₁) hK) (K.inv_mem hk₂)
          convert this using 1; group
        exact Set.disjoint_left.mp hDK hd this
      · simp only [cosetQuotientMap_mk, QuotientGroup.eq]
        have : (x * k₁)⁻¹ * x = k₁⁻¹ := by group
        rw [this]; exact K.inv_mem hk₁
      · simp only [cosetQuotientMap_mk, QuotientGroup.eq]
        have hy : y = x * (k₁ * d * k₂) := by rw [← heq]; group
        have : (x * k₁ * d)⁻¹ * (x * (k₁ * d * k₂)) = k₂ := by group
        rw [hy, this]; exact hk₂
      · convert hd using 1
        simp [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    · intro ⟨_, u, v, hu, hv, hadj⟩
      revert hu hv hadj
      refine Quotient.inductionOn₂ u v fun x' y' hx' hy' (hadj : x'⁻¹ * y' ∈ D) => ?_
      simp only [cosetQuotientMap_mk] at hx' hy'
      have hxK : x⁻¹ * x' ∈ (K : Set G) := by
        have := K.inv_mem (QuotientGroup.eq.mp hx' : x'⁻¹ * x ∈ K)
        rwa [mul_inv_rev, inv_inv] at this
      have hyK : y'⁻¹ * y ∈ (K : Set G) := QuotientGroup.eq.mp hy'
      exact ⟨x⁻¹ * x', hxK, x'⁻¹ * y', hadj, y'⁻¹ * y, hyK, by group⟩
