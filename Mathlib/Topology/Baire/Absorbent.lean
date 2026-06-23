/-
Copyright (c) 2026 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
module

public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Bornology.Absorbs

/-!
# Absorbent sets in Baire spaces

In a Baire space acted on by a group with zero `G₀` with countably generated and
nontrivial `cobounded` filter, a closed absorbent set has nonempty interior.
-/

public section

open Set Filter Bornology
open scoped Pointwise Topology

variable {G₀ E : Type*} [GroupWithZero G₀] [Bornology G₀] [TopologicalSpace E]
  [MulAction G₀ E] [ContinuousConstSMul G₀ E]

/-- In a (nonempty) Baire space, a closed absorbent set has nonempty interior, provided the
`cobounded` filter of the acting group with zero is countably generated and nontrivial (`NeBot`).

The dilations `a n • s` along a sequence `a n` drawn from a countable basis of `cobounded G₀` cover
the space, so by Baire one of them — and hence `s` itself, via the homeomorphism `a n • ·` — has
nonempty interior. -/
theorem Absorbent.interior_nonempty [BaireSpace E] [Nonempty E]
    [(cobounded G₀).IsCountablyGenerated] [NeBot (cobounded G₀)]
    {s : Set E} (hs : Absorbent G₀ s) (hc : IsClosed s) : (interior s).Nonempty := by
  obtain ⟨B, hB⟩ := (cobounded G₀).exists_antitone_basis
  -- Choose nonzero representatives `a n ∈ B n`.
  have hmem (n : ℕ) : (B n ∩ {a : G₀ | a ≠ 0}).Nonempty :=
    Filter.nonempty_of_mem (inter_mem (hB.mem_of_mem trivial)
      (eventually_ne_cobounded 0))
  choose a ha using hmem
  -- The dilations `a n • s` cover the whole space.
  have key : ∀ x : E, ∃ n, x ∈ a n • s := fun x => by
    have hx : ∀ᶠ c in cobounded G₀, x ∈ c • s := by
      simpa [Absorbs, singleton_subset_iff] using hs x
    obtain ⟨n, -, hn⟩ := hB.toHasBasis.mem_iff.mp hx
    exact ⟨n, hn (ha n).1⟩
  have hcover : ⋃ n, closure (a n • s) = univ :=
    eq_univ_of_forall fun x ↦ mem_iUnion.mpr <| (key x).imp fun n hn ↦ subset_closure hn
  -- By Baire some dilation has nonempty interior; transfer back through the homeomorphism.
  obtain ⟨n, hn_int⟩ := nonempty_interior_of_iUnion_of_closed (fun n ↦ isClosed_closure) hcover
  rw [(hc.smul_of_ne_zero (ha n).2).closure_eq, interior_smul₀ (ha n).2] at hn_int
  exact smul_set_nonempty.mp hn_int
