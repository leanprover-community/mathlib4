/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.GraphLike.Symm
public import Mathlib.Combinatorics.Graph.Basic

/-!
In this file we make `Graph` an instance of `GraphLike`.
-/

public section

variable {α β γ : Type*} {G : Graph α β}

namespace Graph

class HasDart (G : Graph α β) (γ : outParam Type*) where
  /-- The set of darts of a graph. -/
  dartSet : Set γ
  /-- The opposite dart, provided by fixed-point-free involution. -/
  symm : γ → γ
  symm_invol : ∀ ⦃d⦄, symm (symm d) = d
  symm_ne : ∀ ⦃d⦄, symm d ≠ d
  symm_mem : ∀ ⦃d⦄, d ∈ dartSet → symm d ∈ dartSet
  /-- The edge of a dart. -/
  edge : γ → β
  edge_eq_edge_iff : ∀ ⦃d₁ d₂⦄, edge d₁ = edge d₂ ↔ d₁ = d₂ ∨ d₁ = symm d₂
  edge_surj : ∀ ⦃e⦄, e ∈ G.edgeSet → ∃ d ∈ dartSet, e = edge d
  /-- The base point of a dart. -/
  basePt : γ → α
  isLink : ∀ ⦃d⦄, d ∈ dartSet → G.IsLink (edge d) (basePt d) (basePt (symm d))

attribute [simp] HasDart.symm_invol

@[simp]
lemma HasDart.symm_mem_dartSet_iff [HasDart G γ] {d : γ} :
    HasDart.symm G d ∈ HasDart.dartSet G ↔ d ∈ HasDart.dartSet G :=
  ⟨fun h ↦ symm_invol (G := G) (d := d) ▸ symm_mem (d := symm G d) h, symm_mem (d := d)⟩

instance [HasDart G γ] : SymmGraphLike α γ G where
  verts := V(G)
  darts := HasDart.dartSet G
  fst := HasDart.basePt G
  snd := (HasDart.basePt G <| HasDart.symm G ·)
  fst_mem_of_darts d hd := (HasDart.isLink hd).left_mem
  snd_mem_of_darts d hd := (HasDart.isLink hd).right_mem
  symm := HasDart.symm G
  symm_invol := HasDart.symm_invol
  symm_ne d hd := HasDart.symm_ne (d := d)
  symm_fst d := by simp
  symm_snd d := by simp
  symm_mem_darts_iff d := HasDart.symm_mem_dartSet_iff
  Adj u v := G.Adj u v
  exists_darts_iff_adj {u v : α} := by
    refine ⟨?_, fun ⟨e, he⟩ => ?_⟩
    · rintro ⟨d, hd, rfl, rfl⟩
      exact (HasDart.isLink hd).adj
    obtain ⟨d, hd, rfl, rfl⟩ := HasDart.edge_surj he.edge_mem
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := he.eq_and_eq_or_eq_and_eq <| HasDart.isLink hd
    · use d, hd
    exact ⟨HasDart.symm G d, HasDart.symm_mem hd, by simp [HasDart.symm_invol]⟩

end Graph
