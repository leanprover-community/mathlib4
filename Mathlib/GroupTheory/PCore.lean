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
* `Subgroup.normal_le_pCore` : for `N` normal in `G`, `N ≤ pCore p G`
  iff `N` is a `p`-group.
* `Subgroup.mem_pCore_iff` : an element lies in `pCore p G` iff it lies in
  some normal `p`-subgroup.
* `Subgroup.pCore_eq_bot_iff` : `pCore p G = ⊥` iff `G` has no non-trivial
  normal `p`-subgroup.
* `Subgroup.pCore_eq_top_iff` : `pCore p G = ⊤` iff `G` is itself a `p`-group.
* `Subgroup.pCore_eq_iInf_sylow` : for finite `G` and prime `p`, the
  `p`-core equals the intersection of all Sylow `p`-subgroups.
* `Subgroup.map_pCore_le_pCore` (surjective `f`) and
  `Subgroup.comap_pCore_le_pCore` (`p`-group kernel) describe how the
  `p`-core behaves under group homomorphisms;
  `Subgroup.comap_pCore_eq_pCore` gives the equality when both
  conditions hold, and `MulEquiv.map_pCore` is the isomorphism case.

## Terminology

The notation `O_p(G)` for the `p`-core is classical; in code we use the
descriptive name `pCore`.

## TODO

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
theorem directed_pCore :
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
  obtain ⟨N, hxN⟩ := (mem_iSup_of_directed directed_pCore).mp hx
  obtain ⟨k, hk⟩ := N.2.2 ⟨x, hxN⟩
  refine ⟨k, ?_⟩
  ext
  simpa using Subtype.ext_iff.mp hk

/-- For a normal subgroup `N` of `G`, containment in the `p`-core is
characterised by being a `p`-group. -/
theorem normal_le_pCore {N : Subgroup G} [hN : N.Normal] :
    N ≤ pCore p G ↔ IsPGroup p N :=
  ⟨fun h => isPGroup_pCore.to_le h, le_pCore hN⟩

/-- Characterisation of membership in the `p`-core: an element lies in
`pCore p G` iff it lies in some normal `p`-subgroup of `G`. -/
theorem mem_pCore_iff {x : G} :
    x ∈ pCore p G ↔ ∃ N : Subgroup G, N.Normal ∧ IsPGroup p N ∧ x ∈ N := by
  rw [pCore, mem_iSup_of_directed directed_pCore]
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

/-- `pCore p G = ⊤` iff the whole group `G` is a `p`-group. -/
theorem pCore_eq_top_iff : pCore p G = ⊤ ↔ IsPGroup p (⊤ : Subgroup G) :=
  ⟨fun h => isPGroup_pCore.to_le (h ▸ le_rfl), fun h => eq_top_iff.2 (le_pCore inferInstance h)⟩

/-- If `G` itself is a `p`-group, then `pCore p G = ⊤`. -/
theorem pCore_eq_top (h : IsPGroup p (⊤ : Subgroup G)) : pCore p G = ⊤ :=
  pCore_eq_top_iff.2 h

/-- The `p`-core is contained in every Sylow `p`-subgroup. The argument
needs no finiteness or primality: `P ⊔ pCore p G` is a `p`-subgroup
(as the join of a `p`-subgroup with a normal `p`-subgroup), so by
maximality of `P` it equals `P`. -/
theorem pCore_le_sylow (P : Sylow p G) : pCore p G ≤ P := by
  have hpsup : IsPGroup p ((P : Subgroup G) ⊔ pCore p G : Subgroup G) :=
    P.2.to_sup_of_normal_right isPGroup_pCore
  have heq : (P : Subgroup G) ⊔ pCore p G = P := P.3 hpsup le_sup_left
  exact le_sup_right.trans heq.le

/-- The intersection of all Sylow `p`-subgroups is normal: conjugation
permutes the Sylow `p`-subgroups, so the intersection is fixed. -/
theorem normal_iInf_sylow : (⨅ P : Sylow p G, (P : Subgroup G)).Normal where
  conj_mem n hn g := by
    simp only [mem_iInf] at hn ⊢
    intro P
    have h := hn (g⁻¹ • P)
    rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at h
    simpa using h

/-- The intersection of all Sylow `p`-subgroups is a `p`-group, being
contained in any single Sylow `p`-subgroup. -/
theorem isPGroup_iInf_sylow : IsPGroup p ↥(⨅ P : Sylow p G, (P : Subgroup G)) :=
  (Classical.arbitrary (Sylow p G)).2.to_le (iInf_le _ _)

/-- The `p`-core equals the intersection of all Sylow `p`-subgroups.
This holds for arbitrary groups and arbitrary `p`: each Sylow contains
`pCore p G` by maximality, and the intersection of Sylows is itself a
normal `p`-subgroup hence contained in `pCore p G`. -/
theorem pCore_eq_iInf_sylow : pCore p G = ⨅ P : Sylow p G, (P : Subgroup G) :=
  le_antisymm (le_iInf pCore_le_sylow) (le_pCore normal_iInf_sylow isPGroup_iInf_sylow)

section Hom

variable {H : Type*} [Group H]

/-- A surjective group homomorphism sends the `p`-core into the `p`-core. -/
theorem map_pCore_le_pCore {f : G →* H} (hf : Function.Surjective f) :
    (pCore p G).map f ≤ pCore p H :=
  le_pCore (pCore_normal.map f hf) (isPGroup_pCore.map f)

/-- A surjective group homomorphism pulls back the `p`-core to a subgroup
containing the source's `p`-core. (Equivalent to `map_pCore_le_pCore`
by the `map`/`comap` adjunction.) -/
theorem pCore_le_comap_pCore {f : G →* H} (hf : Function.Surjective f) :
    pCore p G ≤ (pCore p H).comap f :=
  map_le_iff_le_comap.mp (map_pCore_le_pCore hf)

/-- If the kernel of `f : G →* H` is a `p`-group, then the preimage of the
`p`-core of `H` is contained in the `p`-core of `G`. -/
theorem comap_pCore_le_pCore {f : G →* H} (hker : IsPGroup p f.ker) :
    (pCore p H).comap f ≤ pCore p G :=
  le_pCore (pCore_normal.comap f) (isPGroup_pCore.comap_of_ker_isPGroup f hker)

/-- If `f : G →* H` is surjective with `p`-group kernel, then the `p`-core
of `G` is the preimage of the `p`-core of `H`. -/
theorem comap_pCore_eq_pCore {f : G →* H} (hf : Function.Surjective f) (hker : IsPGroup p f.ker) :
    (pCore p H).comap f = pCore p G :=
  le_antisymm (comap_pCore_le_pCore hker) (pCore_le_comap_pCore hf)

/-- A group isomorphism preserves the `p`-core. -/
theorem _root_.MulEquiv.map_pCore (e : G ≃* H) :
    (pCore p G).map e.toMonoidHom = pCore p H := by
  rw [map_equiv_eq_comap_symm']
  exact comap_pCore_eq_pCore e.symm.surjective (IsPGroup.ker_isPGroup_of_injective e.symm.injective)

end Hom

end Subgroup
