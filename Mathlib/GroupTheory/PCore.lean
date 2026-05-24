/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.GroupTheory.Sylow

/-!
# The `p`-core of a group

For a group `G` and a natural number `p`, the **`p`-core** `O_p(G)` is the
largest normal `p`-subgroup of `G`. We define it as the supremum of all
normal `p`-subgroups, prove that it is normal, and prove that it is itself
a `p`-group (no finiteness hypothesis needed: the family of normal
`p`-subgroups is directed under `≤`).

## Main definitions

* `Subgroup.pCore p G` : the `p`-core of `G`, classically denoted `O_p(G)`.

## Main results

* `Subgroup.pCore_normal` (instance) : `pCore p G` is normal in `G`.
* `Subgroup.isPGroup_pCore` : `pCore p G` is itself a `p`-group.
* `Subgroup.le_pCore` : every normal `p`-subgroup of `G` is contained in
  `pCore p G`.
* `Subgroup.mem_pCore_iff` : an element lies in `pCore p G` iff it lies in
  some normal `p`-subgroup.
* `Subgroup.pCore_eq_bot_iff` : `pCore p G = ⊥` iff `G` has no non-trivial
  normal `p`-subgroup.
* `Subgroup.pCore_eq_top` : if `G` is itself a `p`-group, `pCore p G = ⊤`.
* `Subgroup.pCore_eq_iInf_sylow` : for finite `G` and prime `p`, the
  `p`-core equals the intersection of all Sylow `p`-subgroups.

## Terminology

The notation `O_p(G)` for the `p`-core is classical; in code we use the
descriptive name `pCore`.

## TODO

* Behaviour of `pCore` under group homomorphisms.
* Interaction with `IsSolvable` and the upper Fitting series.
-/

@[expose] public section

namespace Subgroup

open scoped Pointwise

variable {G : Type*} [Group G] {p : ℕ}

/-- The **`p`-core** `O_p(G)` of a group `G`: the supremum of all normal
`p`-subgroups. By `isPGroup_pCore` this is itself a `p`-group, and so is
the largest normal `p`-subgroup of `G`.

We define it via an `iSup` over the subtype of normal `p`-subgroups,
which makes `Subgroup.iSup_induction` directly applicable. -/
def pCore (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  ⨆ N : {N : Subgroup G // N.Normal ∧ IsPGroup p N}, (N : Subgroup G)

/-- The subtype of normal `p`-subgroups is nonempty (it contains `⊥`). -/
instance : Nonempty {N : Subgroup G // N.Normal ∧ IsPGroup p N} :=
  ⟨⟨⊥, inferInstance, IsPGroup.of_bot⟩⟩

/-- Every normal `p`-subgroup of `G` is contained in the `p`-core. -/
theorem le_pCore {N : Subgroup G} (hN_normal : N.Normal) (hN_pGroup : IsPGroup p N) :
    N ≤ pCore p G :=
  le_iSup (fun N : {N : Subgroup G // N.Normal ∧ IsPGroup p N} => (N : Subgroup G))
    ⟨N, hN_normal, hN_pGroup⟩

/-- The `p`-core is normal in `G`. -/
instance pCore_normal : (pCore p G).Normal :=
  normal_iSup_normal fun N => N.2.1

/-- The indexing family of normal `p`-subgroups is directed under `≤`:
for any two normal `p`-subgroups, their join is again a normal
`p`-subgroup. -/
theorem directed_normal_isPGroup :
    Directed (· ≤ ·)
      (fun N : {N : Subgroup G // N.Normal ∧ IsPGroup p N} => (N : Subgroup G)) := by
  rintro ⟨N₁, h₁N, h₁P⟩ ⟨N₂, h₂N, h₂P⟩
  haveI := h₁N
  haveI := h₂N
  exact ⟨⟨N₁ ⊔ N₂, sup_normal N₁ N₂, h₁P.to_sup_of_normal_left h₂P⟩,
    le_sup_left, le_sup_right⟩

/-- The `p`-core is itself a `p`-group. Since the family of normal
`p`-subgroups is directed under `≤`, every element of the supremum
already lies in one of them. -/
theorem isPGroup_pCore : IsPGroup p (pCore p G) := by
  intro ⟨x, hx⟩
  obtain ⟨N, hxN⟩ := (mem_iSup_of_directed directed_normal_isPGroup).mp hx
  obtain ⟨k, hk⟩ := N.2.2 ⟨x, hxN⟩
  refine ⟨k, ?_⟩
  ext
  simpa using Subtype.ext_iff.mp hk

/-- Characterisation of membership in the `p`-core: an element lies in
`pCore p G` iff it lies in some normal `p`-subgroup of `G`. -/
theorem mem_pCore_iff {x : G} :
    x ∈ pCore p G ↔ ∃ N : Subgroup G, N.Normal ∧ IsPGroup p N ∧ x ∈ N := by
  rw [pCore, mem_iSup_of_directed directed_normal_isPGroup]
  exact ⟨fun ⟨N, hxN⟩ => ⟨N, N.2.1, N.2.2, hxN⟩,
    fun ⟨N, hN, hP, hxN⟩ => ⟨⟨N, hN, hP⟩, hxN⟩⟩

/-- The `p`-core is trivial iff `G` has no non-trivial normal `p`-subgroup. -/
theorem pCore_eq_bot_iff :
    pCore p G = ⊥ ↔ ∀ N : Subgroup G, N.Normal → IsPGroup p N → N = ⊥ := by
  refine ⟨fun h N hN hP => le_bot_iff.mp (h ▸ le_pCore hN hP), fun h => ?_⟩
  rw [eq_bot_iff_forall]
  intro x hx
  obtain ⟨N, hN, hP, hxN⟩ := mem_pCore_iff.mp hx
  simpa [h N hN hP] using hxN

/-- If `G` itself is a `p`-group, then `pCore p G = ⊤`. -/
theorem pCore_eq_top (h : IsPGroup p (⊤ : Subgroup G)) : pCore p G = ⊤ :=
  eq_top_iff.2 (le_pCore inferInstance h)

/-- The `p`-core is contained in every Sylow `p`-subgroup. -/
theorem pCore_le_sylow [Fact p.Prime] [Finite G] (P : Sylow p G) : pCore p G ≤ P := by
  have hpg : IsPGroup p (pCore p G) := isPGroup_pCore
  obtain ⟨P₀, hP₀⟩ := hpg.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P₀ P
  rw [Sylow.coe_subgroup_smul, ← pCore_normal.conj_smul_eq_self g]
  exact smul_le_smul_left (MulAut.conj g) hP₀

/-- The intersection of all Sylow `p`-subgroups is normal: conjugation
permutes the Sylow `p`-subgroups, so the intersection is fixed. -/
theorem normal_iInf_sylow [Fact p.Prime] [Finite G] :
    (⨅ P : Sylow p G, (P : Subgroup G)).Normal where
  conj_mem n hn g := by
    simp only [mem_iInf] at hn ⊢
    intro P
    have h := hn (g⁻¹ • P)
    rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at h
    simpa using h

/-- The intersection of all Sylow `p`-subgroups is a `p`-group, being
contained in any single Sylow `p`-subgroup. -/
theorem isPGroup_iInf_sylow [Fact p.Prime] :
    IsPGroup p ↥(⨅ P : Sylow p G, (P : Subgroup G)) :=
  (Classical.arbitrary (Sylow p G)).2.to_le (iInf_le _ _)

/-- For a finite group `G` and a prime `p`, the `p`-core equals the
intersection of all Sylow `p`-subgroups. -/
theorem pCore_eq_iInf_sylow [Fact p.Prime] [Finite G] :
    pCore p G = ⨅ P : Sylow p G, (P : Subgroup G) :=
  le_antisymm (le_iInf pCore_le_sylow) (le_pCore normal_iInf_sylow isPGroup_iInf_sylow)

end Subgroup
