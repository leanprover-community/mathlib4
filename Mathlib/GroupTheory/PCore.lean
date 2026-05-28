/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.GroupTheory.Sylow

/-!
# The `p`-core of a subgroup

For a subgroup `H` of a group `G` and a natural number `p`, the **`p`-core**
`O_p(H)` is the largest normal `p`-subgroup of `H`. We define it as the
supremum of all normal `p`-subgroups of `H`, prove that it is normal in `H`,
and prove that it is itself a `p`-group (no finiteness hypothesis needed:
the family of normal `p`-subgroups is directed under `≤`).

Following the convention used for `Sylow p H`, the `p`-core of a subgroup
`H : Subgroup G` is itself a `Subgroup H`, not a `Subgroup G`. For the
classical `O_p(G)`, take `pCore p (⊤ : Subgroup G)`; the universal property
and Sylow alignment then specialise to give the textbook statements.

## Main definitions

* `Subgroup.pCore p H` : the `p`-core of `H`, classically denoted `O_p(H)`,
  as a `Subgroup H`.

## Main results

* `Subgroup.pCore_normal` (instance), `Subgroup.pCore_characteristic` (instance),
  `Subgroup.isPGroup_pCore`: `pCore p H` is a characteristic `p`-subgroup of `H`,
  with no finiteness hypothesis.
* `Subgroup.normal_le_pCore`: for `N` normal in `H`, `N ≤ pCore p H ↔ IsPGroup p N`,
  the universal property.
* `Subgroup.pCore_eq_iInf_sylow`: `pCore p H = ⨅ P : Sylow p H, (P : Subgroup H)`.
* `Subgroup.map_pCore_le_pCore`, `Subgroup.map_pCore_eq_pCore`,
  `Subgroup.comap_pCore_eq_pCore`, and `MulEquiv.map_pCore` describe the behaviour
  of `pCore` under group homomorphisms, using `MonoidHom.subgroupMap` and
  `MonoidHom.subgroupComap` as the natural restrictions.

## TODO

* Interaction with `IsSolvable` and the upper Fitting series.
-/

public section

namespace Subgroup

open scoped Pointwise

variable {G : Type*} [Group G] {p : ℕ} {H : Subgroup G}

/-- The **`p`-core** `O_p(H)` of a subgroup `H` of `G`: the supremum of all
normal `p`-subgroups of `H`, as a `Subgroup H`. By `isPGroup_pCore` this is
itself a `p`-group, and so is the largest normal `p`-subgroup of `H`.

We define it via an `iSup` over the subtype of normal `p`-subgroups,
which makes `Subgroup.iSup_induction` directly applicable. -/
@[expose] def pCore (p : ℕ) (H : Subgroup G) : Subgroup H :=
  ⨆ N : {N : Subgroup H // N.Normal ∧ IsPGroup p N}, (N : Subgroup H)

/-- The subtype of normal `p`-subgroups of `H` is nonempty (it contains `⊥`). -/
private instance : Nonempty {N : Subgroup H // N.Normal ∧ IsPGroup p N} :=
  ⟨⟨⊥, inferInstance, IsPGroup.of_bot⟩⟩

/-- Every normal `p`-subgroup of `H` is contained in the `p`-core. -/
theorem le_pCore {N : Subgroup H} (hN_normal : N.Normal) (hN_pGroup : IsPGroup p N) :
    N ≤ pCore p H :=
  le_iSup (fun N : {N : Subgroup H // N.Normal ∧ IsPGroup p N} => (N : Subgroup H))
    ⟨N, hN_normal, hN_pGroup⟩

/-- The `p`-core is normal in `H`. -/
instance pCore_normal : (pCore p H).Normal :=
  normal_iSup_normal fun N => N.2.1

/-- The indexing family of normal `p`-subgroups is directed under `≤`:
for any two normal `p`-subgroups, their join is again a normal
`p`-subgroup. -/
theorem directed_pCore :
    Directed (· ≤ ·)
      (fun N : {N : Subgroup H // N.Normal ∧ IsPGroup p N} => (N : Subgroup H)) := by
  rintro ⟨N₁, h₁N, h₁P⟩ ⟨N₂, h₂N, h₂P⟩
  haveI := h₁N
  haveI := h₂N
  exact ⟨⟨N₁ ⊔ N₂, sup_normal N₁ N₂, h₁P.to_sup_of_normal_left h₂P⟩,
    le_sup_left, le_sup_right⟩

/-- The `p`-core is itself a `p`-group. Since the family of normal
`p`-subgroups is directed under `≤`, every element of the supremum
already lies in one of them. -/
theorem isPGroup_pCore : IsPGroup p (pCore p H) := by
  intro ⟨x, hx⟩
  obtain ⟨N, hxN⟩ := (mem_iSup_of_directed directed_pCore).mp hx
  obtain ⟨k, hk⟩ := N.2.2 ⟨x, hxN⟩
  refine ⟨k, ?_⟩
  apply Subtype.ext
  simpa using Subtype.ext_iff.mp hk

/-- The `p`-core is characteristic in `H`: any automorphism of `H` permutes
the family of normal `p`-subgroups, so it fixes their supremum. -/
instance pCore_characteristic : (pCore p H).Characteristic :=
  characteristic_iff_comap_le.mpr fun ϕ => le_pCore (pCore_normal.comap ϕ.toMonoidHom)
    (isPGroup_pCore.comap_of_injective ϕ.toMonoidHom ϕ.injective)

/-- For a normal subgroup `N` of `H`, containment in the `p`-core is
characterised by being a `p`-group. -/
theorem normal_le_pCore {N : Subgroup H} [hN : N.Normal] :
    N ≤ pCore p H ↔ IsPGroup p N :=
  ⟨fun h => isPGroup_pCore.to_le h, le_pCore hN⟩

/-- Characterisation of membership in the `p`-core: an element lies in
`pCore p H` iff it lies in some normal `p`-subgroup of `H`. -/
theorem mem_pCore_iff {x : H} :
    x ∈ pCore p H ↔ ∃ N : Subgroup H, N.Normal ∧ IsPGroup p N ∧ x ∈ N := by
  rw [pCore, mem_iSup_of_directed directed_pCore]
  exact ⟨fun ⟨N, hxN⟩ => ⟨N, N.2.1, N.2.2, hxN⟩,
    fun ⟨N, hN, hP, hxN⟩ => ⟨⟨N, hN, hP⟩, hxN⟩⟩

/-- The `p`-core is trivial iff `H` has no non-trivial normal `p`-subgroup. -/
theorem pCore_eq_bot_iff :
    pCore p H = ⊥ ↔ ∀ N : Subgroup H, N.Normal → IsPGroup p N → N = ⊥ := by
  refine ⟨fun h N hN hP => le_bot_iff.mp (h ▸ le_pCore hN hP), fun h => ?_⟩
  rw [eq_bot_iff_forall]
  intro x hx
  obtain ⟨N, hN, hP, hxN⟩ := mem_pCore_iff.mp hx
  simpa [h N hN hP] using hxN

/-- `pCore p H = ⊤` iff `H` is a `p`-group. -/
theorem pCore_eq_top_iff : pCore p H = ⊤ ↔ IsPGroup p H :=
  ⟨fun h => (isPGroup_pCore.to_le h.ge).of_equiv topEquiv,
   fun h => eq_top_iff.2 (le_pCore inferInstance (h.of_equiv topEquiv.symm))⟩

/-- If `H` is a `p`-group, then `pCore p H = ⊤`. -/
theorem pCore_eq_top (h : IsPGroup p H) : pCore p H = ⊤ :=
  pCore_eq_top_iff.2 h

/-- The `0`-core is the whole subgroup: every group is a `0`-group, since
`g ^ 0 ^ 1 = g ^ 0 = 1`. -/
@[simp]
theorem pCore_zero : pCore 0 H = ⊤ :=
  pCore_eq_top fun _ => ⟨1, by simp⟩

/-- The `1`-core is trivial: a `1`-group is necessarily the trivial group,
since `g ^ 1 ^ k = g ^ 1 = g`. -/
@[simp]
theorem pCore_one : pCore 1 H = ⊥ := by
  rw [eq_bot_iff_forall]
  intro x hx
  obtain ⟨k, hk⟩ := isPGroup_pCore ⟨x, hx⟩
  rw [one_pow, pow_one] at hk
  exact congrArg Subtype.val hk

/-- The `p`-core is contained in every Sylow `p`-subgroup. The argument
needs no finiteness or primality: `P ⊔ pCore p H` is a `p`-subgroup
(as the join of a `p`-subgroup with a normal `p`-subgroup), so by
maximality of `P` it equals `P`. -/
theorem pCore_le_sylow (P : Sylow p H) : pCore p H ≤ P := by
  have hpsup : IsPGroup p ((P : Subgroup H) ⊔ pCore p H : Subgroup H) :=
    P.2.to_sup_of_normal_right isPGroup_pCore
  have heq : (P : Subgroup H) ⊔ pCore p H = P := P.3 hpsup le_sup_left
  exact le_sup_right.trans heq.le

/-- The intersection of all Sylow `p`-subgroups of `H` is normal in `H`:
conjugation permutes the Sylow `p`-subgroups, so the intersection is fixed. -/
theorem normal_iInf_sylow : (⨅ P : Sylow p H, (P : Subgroup H)).Normal where
  conj_mem n hn g := by
    simp only [mem_iInf] at hn ⊢
    intro P
    have h := hn (g⁻¹ • P)
    rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at h
    simpa using h

/-- The intersection of all Sylow `p`-subgroups of `H` is a `p`-group,
being contained in any single Sylow `p`-subgroup. -/
theorem isPGroup_iInf_sylow : IsPGroup p ↥(⨅ P : Sylow p H, (P : Subgroup H)) :=
  (Classical.arbitrary (Sylow p H)).2.to_le (iInf_le _ _)

/-- The `p`-core equals the intersection of all Sylow `p`-subgroups of `H`.
This holds for arbitrary `H` and arbitrary `p`: each Sylow contains
`pCore p H` by maximality, and the intersection of Sylows is itself a
normal `p`-subgroup hence contained in `pCore p H`. -/
theorem pCore_eq_iInf_sylow : pCore p H = ⨅ P : Sylow p H, (P : Subgroup H) :=
  le_antisymm (le_iInf pCore_le_sylow) (le_pCore normal_iInf_sylow isPGroup_iInf_sylow)

/-- A normal Sylow `p`-subgroup of `H` coincides with the `p`-core: it is a normal
`p`-subgroup hence below `pCore p H`, and `pCore p H` is below every Sylow. -/
theorem sylow_eq_pCore_of_normal (P : Sylow p H) [(P : Subgroup H).Normal] :
    (P : Subgroup H) = pCore p H :=
  le_antisymm (le_pCore inferInstance P.2) (pCore_le_sylow P)

/-- A Sylow `p`-subgroup of `H` equals the `p`-core iff it is normal. -/
theorem pCore_eq_sylow_iff_normal (P : Sylow p H) :
    pCore p H = (P : Subgroup H) ↔ (P : Subgroup H).Normal := by
  refine ⟨fun h => h ▸ pCore_normal, fun h => ?_⟩
  haveI := h
  exact (sylow_eq_pCore_of_normal P).symm

section Hom

variable {G' : Type*} [Group G']

/-- A group homomorphism sends the `p`-core of `H` into the `p`-core of `H.map f`,
via the (always surjective) restriction `f.subgroupMap H : H →* H.map f`. -/
theorem map_pCore_le_pCore (f : G →* G') (H : Subgroup G) :
    (pCore p H).map (f.subgroupMap H) ≤ pCore p (H.map f) :=
  le_pCore (pCore_normal.map _ (f.subgroupMap_surjective H)) (isPGroup_pCore.map _)

/-- Adjoint form of `map_pCore_le_pCore`. -/
theorem pCore_le_comap_pCore (f : G →* G') (H : Subgroup G) :
    pCore p H ≤ (pCore p (H.map f)).comap (f.subgroupMap H) :=
  map_le_iff_le_comap.mp (map_pCore_le_pCore f H)

/-- If the restriction `f.subgroupMap H : H →* H.map f` has `p`-group kernel, then
its image of `pCore p H` is exactly `pCore p (H.map f)`. The hypothesis is implied
by `IsPGroup p f.ker` (via `ker_subgroupMap`), but only the restricted kernel matters. -/
theorem map_pCore_eq_pCore (f : G →* G') (H : Subgroup G)
    (hker : IsPGroup p (f.subgroupMap H).ker) :
    (pCore p H).map (f.subgroupMap H) = pCore p (H.map f) := by
  refine le_antisymm (map_pCore_le_pCore f H) ?_
  conv_lhs => rw [← Subgroup.map_comap_eq_self_of_surjective (f.subgroupMap_surjective H)
    (pCore p (H.map f))]
  exact Subgroup.map_mono <| le_pCore (pCore_normal.comap _)
    (isPGroup_pCore.comap_of_ker_isPGroup _ hker)

/-- If the restriction `f.subgroupComap H' : H'.comap f →* H'` has `p`-group kernel,
then the preimage of `pCore p H'` is contained in `pCore p (H'.comap f)`. The hypothesis
is implied by `IsPGroup p f.ker` (via `ker_subgroupComap`). -/
theorem comap_pCore_le_pCore (f : G →* G') (H' : Subgroup G')
    (hker : IsPGroup p (f.subgroupComap H').ker) :
    (pCore p H').comap (f.subgroupComap H') ≤ pCore p (H'.comap f) :=
  le_pCore (pCore_normal.comap _) (isPGroup_pCore.comap_of_ker_isPGroup _ hker)

/-- If the restriction `f.subgroupComap H' : H'.comap f →* H'` is surjective with
`p`-group kernel, then the `p`-core of `H'.comap f` is the preimage of `pCore p H'`.
Surjectivity of the restriction is equivalent to `H' ≤ f.range`. -/
theorem comap_pCore_eq_pCore (f : G →* G') (H' : Subgroup G')
    (hf : Function.Surjective (f.subgroupComap H'))
    (hker : IsPGroup p (f.subgroupComap H').ker) :
    (pCore p H').comap (f.subgroupComap H') = pCore p (H'.comap f) := by
  refine le_antisymm (comap_pCore_le_pCore f H' hker) ?_
  rw [← map_le_iff_le_comap]
  exact le_pCore (pCore_normal.map _ hf) (isPGroup_pCore.map _)

/-- A group isomorphism `e : G ≃* G'` preserves the `p`-core of a subgroup `H`,
via the restricted isomorphism `e.subgroupMap H : H ≃* H.map (e : G →* G')`. -/
theorem _root_.MulEquiv.map_pCore (e : G ≃* G') (H : Subgroup G) :
    (pCore p H).map (e.subgroupMap H).toMonoidHom = pCore p (H.map (e : G →* G')) :=
  map_pCore_eq_pCore (e : G →* G') H
    (IsPGroup.ker_isPGroup_of_injective (e.subgroupMap H).injective)

end Hom

end Subgroup
