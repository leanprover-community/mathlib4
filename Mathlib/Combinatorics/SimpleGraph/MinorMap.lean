/-
Copyright (c) 2024 Google. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Wong
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity

/-!
# Minor maps
-/

/--
A **minor map** on graphs `G` and `H` witnesses that `G` is a minor of `H`, by
mapping each vertex of `G` to the vertices of `H` which are contracted into it.
-/
structure MinorMap {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) where
  /-- The underlying function -/
  toFun : V → Set W
  /-- Each vertex in `G` maps to a connected subgraph in `H` -/
  connected : ∀ v, (H.induce (toFun v)).Connected
  /-- The subgraphs in `H` are disjoint -/
  disjoint : Pairwise (Disjoint on toFun)
  /-- Adjacent vertices in `G` map to neighboring subgraphs in `H` -/
  neighbor : ∀ ⦃v₁ v₂⦄, G.Adj v₁ v₂ → ∃ w₁ ∈ toFun v₁, ∃ w₂ ∈ toFun v₂, H.Adj w₁ w₂

/-- Composition of minor maps. -/
def MinorMap.comp {V₁ V₂ V₃ : Type*}
    {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂} {G₃ : SimpleGraph V₃}
    (M₁₂ : MinorMap G₁ G₂) (M₂₃ : MinorMap G₂ G₃) : MinorMap G₁ G₃ where
  toFun a := ⋃ b ∈ M₁₂.toFun a, M₂₃.toFun b
  connected := by
    intro x₁
    rcases M₁₂.connected x₁ |>.nonempty with ⟨x₂, hx₂⟩
    rcases M₂₃.connected x₂ |>.nonempty with ⟨x₃, hx₃⟩
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    have hx₃' := Set.mem_biUnion hx₂ hx₃
    exists ⟨x₃, hx₃'⟩
    intro ⟨y₃, hy₃'⟩
    rcases Set.mem_iUnion₂.mp hy₃' with ⟨y₂, hy₂, hy₃⟩
    rcases M₁₂.connected x₁ ⟨x₂, hx₂⟩ ⟨y₂, hy₂⟩ with ⟨x₂_to_y₂⟩
    -- Map each vertex in `x₂_to_y₂` to a connected component in `G₃`, using `G₃.neighbor` to bridge
    -- between components.
    let rec loop : (u₂ : V₂) → (hu₂ : u₂ ∈ M₁₂.toFun x₁) → (v₂ : V₂) → (hv₂ : v₂ ∈ M₁₂.toFun x₁)
      → (u₃ : V₃) → (hu₃ : u₃ ∈ M₂₃.toFun u₂) → (v₃ : V₃) → (hv₃ : v₃ ∈ M₂₃.toFun v₂)
      → (G₂.induce (M₁₂.toFun x₁)).Walk ⟨u₂, hu₂⟩ ⟨v₂, hv₂⟩
      → (G₃.induce _).Reachable ⟨u₃, Set.mem_biUnion hu₂ hu₃⟩ ⟨v₃, Set.mem_biUnion hv₂ hv₃⟩
      | u₂, hu₂, _, _, u₃, hu₃, v₃, hv₃, .nil =>
        M₂₃.connected u₂ ⟨u₃, hu₃⟩ ⟨v₃, hv₃⟩
          |>.map (G₃.induceHomOfLE (Set.subset_biUnion_of_mem hu₂) |>.toHom)
      | u₂, hu₂, v₂, hv₂, u₃, hu₃, v₃, hv₃, .cons' _ ⟨w₂, hw₂⟩ _ h p =>
        match M₂₃.neighbor (SimpleGraph.comap_adj.mp h) with
          | ⟨n₃, hn₃, m₃, hm₃, n₃_to_m₃'⟩ =>
            have u₃_to_n₃ :=
              M₂₃.connected u₂ ⟨u₃, hu₃⟩ ⟨n₃, hn₃⟩
                |>.map (G₃.induceHomOfLE (Set.subset_biUnion_of_mem hu₂) |>.toHom)
            have n₃_to_m₃ :=
              @SimpleGraph.Adj.reachable _ (G₃.induce _)
                ⟨n₃, Set.mem_biUnion hu₂ hn₃⟩ ⟨m₃, Set.mem_biUnion hw₂ hm₃⟩
                (SimpleGraph.comap_adj.mp n₃_to_m₃')
            have m₃_to_v₃ := loop w₂ hw₂ v₂ hv₂ m₃ hm₃ v₃ hv₃ p
            u₃_to_n₃ |>.trans n₃_to_m₃ |>.trans m₃_to_v₃
    exact loop x₂ hx₂ y₂ hy₂ x₃ hx₃ y₃ hy₃ x₂_to_y₂
  disjoint := by
    intro x₁ y₁ h₁
    rw [Function.onFun_apply, Set.disjoint_iUnion₂_left]
    intro x₂ hx₂
    rw [Set.disjoint_iUnion₂_right]
    intro y₂ hy₂
    apply M₂₃.disjoint
    exact M₁₂.disjoint h₁ |>.ne_of_mem hx₂ hy₂
  neighbor := by
    intro x₁ y₁ h₁
    have ⟨x₂, hx₂, y₂, hy₂, h₂⟩ := M₁₂.neighbor h₁
    have ⟨x₃, hx₃, y₃, hy₃, h₃⟩ := M₂₃.neighbor h₂
    exact ⟨x₃, Set.mem_biUnion hx₂ hx₃, y₃, Set.mem_biUnion hy₂ hy₃, h₃⟩

section

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- An injective homomorphism gives rise to a minor map. -/
def MinorMap.ofHom (f : G →g H) (hf : Function.Injective ⇑f) : MinorMap G H where
  toFun v := {f v}
  connected x := SimpleGraph.induce_singleton_eq_top H (f x) ▸ SimpleGraph.top_connected
  disjoint _ _ h := Set.disjoint_singleton.mpr (hf.ne h)
  neighbor x y hG := ⟨f x, rfl, f y, rfl, f.map_adj hG⟩

/-- Vertex deletion creates a minor. -/
def MinorMap.ofEmbedding (f : G ↪g H) : MinorMap G H :=
  MinorMap.ofHom f.toHom f.injective

end section

/-- Edge deletion creates a minor. -/
def MinorMap.ofLE {V : Type*} {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂) : MinorMap G₁ G₂ :=
  MinorMap.ofHom (SimpleGraph.Hom.ofLE h) Function.injective_id

/-- A graph is a minor of itself. -/
def MinorMap.id {V : Type*} (G : SimpleGraph V) : MinorMap G G := MinorMap.ofLE le_rfl
