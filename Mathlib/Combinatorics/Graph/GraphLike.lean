/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.GraphLike.Basic
public import Mathlib.Combinatorics.Graph.Basic

/-!
In this file we make `Graph` an instance of `GraphLike`.
-/

public section

variable {α β γ : Type*} {G : Graph α β}

namespace Graph

class IsDart (G : Graph α β) (γ : outParam Type*) where
  dartSet : Set γ
  edge : γ → β
  symm : γ → γ
  symm_invol : ∀ ⦃d⦄, symm (symm d) = d
  symm_irrefl : ∀ ⦃d⦄, symm d ≠ d
  symm_mem : ∀ ⦃d⦄, d ∈ dartSet → symm d ∈ dartSet
  edge_of_symm : ∀ ⦃d₁ d₂⦄, edge d₁ = edge d₂ ↔ d₁ = d₂ ∨ d₁ = symm d₂
  basePt : γ → α
  isLink : ∀ ⦃d⦄, d ∈ dartSet → G.IsLink (edge d) (basePt d) (basePt (symm d))
  surj : ∀ ⦃e⦄, e ∈ G.edgeSet → ∃ d ∈ dartSet, e = edge d

instance [IsDart G γ] : GraphLike α γ G where
  verts := V(G)
  darts := IsDart.dartSet G
  fst := IsDart.basePt G
  snd := (IsDart.basePt G <| IsDart.symm G ·)
  fst_mem_of_darts hd := (IsDart.isLink hd).left_mem
  snd_mem_of_darts hd := (IsDart.isLink hd).right_mem
  Adj u v := G.Adj u v
  exists_darts_iff_adj {u v : α} := by
    refine ⟨?_, fun ⟨e, he⟩ => ?_⟩
    · rintro ⟨d, hd, rfl, rfl⟩
      exact (IsDart.isLink hd).adj
    obtain ⟨d, hd, rfl, rfl⟩ := IsDart.surj he.edge_mem
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := he.eq_and_eq_or_eq_and_eq <| IsDart.isLink hd
    · use d, hd
    exact ⟨IsDart.symm G d, IsDart.symm_mem hd, by simp [IsDart.symm_invol]⟩

end Graph
