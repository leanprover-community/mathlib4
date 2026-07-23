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

The `p`-core of a subgroup `H : Subgroup G` is returned as a `Subgroup G`
(lying inside `H`, see `pCore_le`), so that it composes directly with other
ambient-group constructions without inserting `.map H.subtype`. For the
classical `O_p(G)`, take `pCore p (⊤ : Subgroup G)`.

Because `pCore p H` is a `Subgroup G` that is only normal **in `H`** (not in
`G` in general), its normality and characteristicity are stated for the
relative subgroup `(pCore p H).subgroupOf H`, not for `pCore p H` itself.

## Main definitions

* `Subgroup.pCore p H` : the `p`-core of `H`, classically denoted `O_p(H)`,
  as a `Subgroup G` contained in `H`.

## Main results

* `Subgroup.pCore_le`: `pCore p H ≤ H`.
* `Subgroup.isPGroup_pCore`: the ambient subgroup `pCore p H` is a `p`-group, with no
  finiteness hypothesis.
* `Subgroup.pCore_subgroupOf_normal` (instance), `Subgroup.pCore_subgroupOf_characteristic`
  (instance): inside `H`, the `p`-core is normal and characteristic.
* `Subgroup.le_pCore`, `Subgroup.le_pCore_of_le`: a normal `p`-subgroup of `H` (embedded into
  `G`) is contained in the `p`-core — the universal property.
* `Subgroup.pCore_eq_iInf_sylow`: `pCore p H = (⨅ P : Sylow p H, (P : Subgroup H)).map H.subtype`.
* `Subgroup.map_pCore_le_pCore`, `Subgroup.map_pCore_eq_pCore`,
  `Subgroup.comap_pCore_le_pCore`, `Subgroup.comap_pCore_eq_pCore`, and `MulEquiv.map_pCore`
  describe the behaviour of `pCore` under group homomorphisms.

## TODO

* Interaction with `IsSolvable` and the upper Fitting series.
-/

public section

namespace Subgroup

open scoped Pointwise

variable {G : Type*} [Group G] {p : ℕ} {H : Subgroup G}

/-- The **`p`-core** `O_p(H)` of a subgroup `H` of `G`: the supremum of all
normal `p`-subgroups of `H`, embedded back into `G` via `H.subtype`. It is a
`Subgroup G` contained in `H` (see `pCore_le`); by `isPGroup_pCore` it is a
`p`-group, and so the largest normal `p`-subgroup of `H`.

We define it via an `iSup` over the subtype of normal `p`-subgroups, which makes
`Subgroup.iSup_induction` directly applicable after `pCore_subgroupOf`. -/
def pCore (p : ℕ) (H : Subgroup G) : Subgroup G :=
  ⨆ N : {N : Subgroup H // N.Normal ∧ IsPGroup p N}, (N : Subgroup H).map H.subtype

/-- The `p`-core as a supremum of the normal `p`-subgroups of `H`, embedded into `G`. -/
theorem pCore_eq_iSup :
    pCore p H =
      ⨆ N : {N : Subgroup H // N.Normal ∧ IsPGroup p N}, (N : Subgroup H).map H.subtype := by
  rw [pCore]

/-- The subtype of normal `p`-subgroups of `H` is nonempty (it contains `⊥`). -/
private instance : Nonempty {N : Subgroup H // N.Normal ∧ IsPGroup p N} :=
  ⟨⟨⊥, inferInstance, IsPGroup.of_bot⟩⟩

/-- The `p`-core of `H` is contained in `H`. -/
theorem pCore_le : pCore p H ≤ H :=
  iSup_le fun _ => map_subtype_le _

/-- The `p`-core of the trivial subgroup is trivial. -/
@[simp]
theorem pCore_bot : pCore p (⊥ : Subgroup G) = ⊥ :=
  le_bot_iff.mp pCore_le

/-- Computed inside `H`, the `p`-core is the supremum of all normal
`p`-subgroups of `H`. -/
theorem pCore_subgroupOf :
    (pCore p H).subgroupOf H =
      ⨆ N : {N : Subgroup H // N.Normal ∧ IsPGroup p N}, (N : Subgroup H) := by
  rw [pCore, ← Subgroup.map_iSup]
  exact comap_map_eq_self_of_injective H.subtype_injective _

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

/-- A normal `p`-subgroup `N` of `H` is contained in the `p`-core, computed
inside `H`. -/
theorem le_pCore_subgroupOf {N : Subgroup H} (hN_normal : N.Normal) (hN_pGroup : IsPGroup p N) :
    N ≤ (pCore p H).subgroupOf H := by
  rw [pCore_subgroupOf]
  exact le_iSup (fun N : {N : Subgroup H // N.Normal ∧ IsPGroup p N} => (N : Subgroup H))
    ⟨N, hN_normal, hN_pGroup⟩

/-- The universal property: a normal `p`-subgroup of `H`, embedded into `G`,
is contained in the `p`-core. -/
theorem le_pCore {N : Subgroup H} (hN_normal : N.Normal) (hN_pGroup : IsPGroup p N) :
    N.map H.subtype ≤ pCore p H :=
  le_iSup (fun N : {N : Subgroup H // N.Normal ∧ IsPGroup p N} => (N : Subgroup H).map H.subtype)
    ⟨N, hN_normal, hN_pGroup⟩

/-- The `p`-core, computed inside `H`, is a `p`-group. -/
theorem isPGroup_pCore_subgroupOf : IsPGroup p ((pCore p H).subgroupOf H) := by
  rw [pCore_subgroupOf]
  haveI : ∀ N : {N : Subgroup H // N.Normal ∧ IsPGroup p N}, ((N : Subgroup H)).Normal :=
    fun N => N.2.1
  exact Sylow.iSup_of_normal _ fun N => N.2.2

/-- The `p`-core is itself a `p`-group. Since every normal `p`-subgroup of `H`
is contained in a Sylow `p`-subgroup, their supremum is a `p`-group
(`Sylow.iSup_of_normal`). -/
theorem isPGroup_pCore : IsPGroup p (pCore p H) := by
  rw [pCore, ← Subgroup.map_iSup]
  haveI : ∀ N : {N : Subgroup H // N.Normal ∧ IsPGroup p N}, ((N : Subgroup H)).Normal :=
    fun N => N.2.1
  exact (Sylow.iSup_of_normal _ fun N => N.2.2).map H.subtype

/-- The `p`-core is normal in `H`. -/
instance pCore_subgroupOf_normal : ((pCore p H).subgroupOf H).Normal := by
  rw [pCore_subgroupOf]
  haveI : ∀ N : {N : Subgroup H // N.Normal ∧ IsPGroup p N}, ((N : Subgroup H)).Normal :=
    fun N => N.2.1
  exact Subgroup.iSup_normal _

/-- The `p`-core is characteristic in `H`: any automorphism of `H` permutes
the family of normal `p`-subgroups, so it fixes their supremum. -/
instance pCore_subgroupOf_characteristic : ((pCore p H).subgroupOf H).Characteristic :=
  characteristic_iff_comap_le.mpr fun ϕ =>
    le_pCore_subgroupOf (pCore_subgroupOf_normal.comap ϕ.toMonoidHom)
      (isPGroup_pCore_subgroupOf.comap_of_injective ϕ.toMonoidHom ϕ.injective)

/-- The universal property, inside `H`: a normal subgroup `N` of `H` is contained in the
`p`-core iff it is a `p`-group. -/
theorem le_pCore_subgroupOf_iff {N : Subgroup H} [hN : N.Normal] :
    N ≤ (pCore p H).subgroupOf H ↔ IsPGroup p N :=
  ⟨fun h => isPGroup_pCore_subgroupOf.to_le h, le_pCore_subgroupOf hN⟩

/-- For a normal subgroup `N` of `H`, containment of its image in the `p`-core
is characterised by being a `p`-group. -/
theorem map_subtype_le_pCore_iff {N : Subgroup H} [N.Normal] :
    N.map H.subtype ≤ pCore p H ↔ IsPGroup p N := by
  rw [map_le_iff_le_comap]; exact le_pCore_subgroupOf_iff

/-- Characterisation of membership in the `p`-core: an element of `H` lies in
`pCore p H` iff it lies in some normal `p`-subgroup of `H`. -/
theorem mem_pCore_subgroupOf_iff {x : H} :
    x ∈ (pCore p H).subgroupOf H ↔ ∃ N : Subgroup H, N.Normal ∧ IsPGroup p N ∧ x ∈ N := by
  rw [pCore_subgroupOf, mem_iSup_of_directed directed_pCore]
  exact ⟨fun ⟨N, hxN⟩ => ⟨N, N.2.1, N.2.2, hxN⟩,
    fun ⟨N, hN, hP, hxN⟩ => ⟨⟨N, hN, hP⟩, hxN⟩⟩

/-- Characterisation of membership in the `p`-core as an ambient subgroup: `x : G` lies in
`pCore p H` iff it lies in (the image of) some normal `p`-subgroup of `H`. -/
theorem mem_pCore_iff {x : G} :
    x ∈ pCore p H ↔ ∃ N : Subgroup H, N.Normal ∧ IsPGroup p N ∧ x ∈ N.map H.subtype := by
  rw [pCore_eq_iSup, mem_iSup_of_directed fun a b =>
    (directed_pCore a b).imp fun _ h => ⟨map_mono h.1, map_mono h.2⟩]
  exact ⟨fun ⟨N, hxN⟩ => ⟨N, N.2.1, N.2.2, hxN⟩,
    fun ⟨N, hN, hP, hxN⟩ => ⟨⟨N, hN, hP⟩, hxN⟩⟩

/-- The `p`-core is trivial iff `H` has no non-trivial normal `p`-subgroup. -/
theorem pCore_eq_bot_iff :
    pCore p H = ⊥ ↔ ∀ N : Subgroup H, N.Normal → IsPGroup p N → N = ⊥ := by
  have key : pCore p H = ⊥ ↔ (pCore p H).subgroupOf H = ⊥ :=
    ⟨fun h => by rw [h, bot_subgroupOf],
     fun h => by rw [← map_subgroupOf_eq_of_le (pCore_le (H := H)), h, map_bot]⟩
  rw [key, pCore_subgroupOf]
  refine ⟨fun h N hN hP => le_bot_iff.mp (h ▸ le_iSup
    (fun N : {N : Subgroup H // N.Normal ∧ IsPGroup p N} => (N : Subgroup H)) ⟨N, hN, hP⟩),
    fun h => ?_⟩
  rw [eq_bot_iff_forall]
  intro x hx
  obtain ⟨N, hxN⟩ := (mem_iSup_of_directed directed_pCore).mp hx
  simpa [h N N.2.1 N.2.2] using hxN

/-- `(⊤ : Subgroup H)` embeds onto `H`. -/
private theorem top_map_subtype : (⊤ : Subgroup H).map H.subtype = H := by
  have h := map_subgroupOf_eq_of_le (le_refl H)
  rwa [subgroupOf_self] at h

/-- `pCore p H = H` iff `H` is a `p`-group. -/
theorem pCore_eq_self_iff : pCore p H = H ↔ IsPGroup p H := by
  refine ⟨fun h => h ▸ isPGroup_pCore, fun h => le_antisymm pCore_le ?_⟩
  have h := le_pCore (N := (⊤ : Subgroup H)) inferInstance (h.of_equiv topEquiv.symm)
  rwa [top_map_subtype] at h

/-- If `H` is a `p`-group, then `pCore p H = H`. -/
theorem pCore_eq_self (h : IsPGroup p H) : pCore p H = H :=
  pCore_eq_self_iff.2 h

/-- The `0`-core is the whole subgroup: every group is a `0`-group. -/
@[simp]
theorem pCore_zero : pCore 0 H = H :=
  pCore_eq_self fun _ => ⟨1, by simp⟩

/-- The `1`-core is trivial. -/
@[simp]
theorem pCore_one : pCore 1 H = ⊥ := by
  rw [eq_bot_iff_forall]
  intro x hx
  obtain ⟨k, hk⟩ := isPGroup_pCore ⟨x, hx⟩
  rw [one_pow, pow_one] at hk
  exact congrArg Subtype.val hk

/-- The `p`-core, computed inside `H`, is contained in every Sylow `p`-subgroup. -/
theorem pCore_subgroupOf_le_sylow (P : Sylow p H) : (pCore p H).subgroupOf H ≤ P := by
  have hpsup : IsPGroup p ((P : Subgroup H) ⊔ (pCore p H).subgroupOf H : Subgroup H) :=
    P.2.to_sup_of_normal_right isPGroup_pCore_subgroupOf
  have heq : (P : Subgroup H) ⊔ (pCore p H).subgroupOf H = P := P.3 hpsup le_sup_left
  exact le_sup_right.trans heq.le

/-- The `p`-core is contained in every Sylow `p`-subgroup (embedded into `G`). -/
theorem pCore_le_sylow (P : Sylow p H) : pCore p H ≤ (P : Subgroup H).map H.subtype := by
  rw [← map_subgroupOf_eq_of_le (pCore_le (H := H))]
  exact map_mono (pCore_subgroupOf_le_sylow P)

/-- The intersection of all Sylow `p`-subgroups of `H` is normal in `H`. -/
theorem normal_iInf_sylow : (⨅ P : Sylow p H, (P : Subgroup H)).Normal where
  conj_mem n hn g := by
    simp only [mem_iInf] at hn ⊢
    intro P
    have h := hn (g⁻¹ • P)
    rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at h
    simpa using h

/-- The intersection of all Sylow `p`-subgroups of `H` is a `p`-group. -/
theorem isPGroup_iInf_sylow : IsPGroup p ↥(⨅ P : Sylow p H, (P : Subgroup H)) :=
  (Classical.arbitrary (Sylow p H)).2.to_le (iInf_le _ _)

/-- Computed inside `H`, the `p`-core equals the intersection of all Sylow
`p`-subgroups of `H`. -/
theorem pCore_subgroupOf_eq_iInf_sylow :
    (pCore p H).subgroupOf H = ⨅ P : Sylow p H, (P : Subgroup H) :=
  le_antisymm (le_iInf pCore_subgroupOf_le_sylow)
    (le_pCore_subgroupOf normal_iInf_sylow isPGroup_iInf_sylow)

/-- The `p`-core equals the intersection of all Sylow `p`-subgroups of `H`,
embedded into `G`. -/
theorem pCore_eq_iInf_sylow :
    pCore p H = (⨅ P : Sylow p H, (P : Subgroup H)).map H.subtype := by
  rw [← pCore_subgroupOf_eq_iInf_sylow, map_subgroupOf_eq_of_le pCore_le]

/-- A normal Sylow `p`-subgroup of `H` coincides with the `p`-core inside `H`. -/
theorem sylow_eq_pCore_subgroupOf_of_normal (P : Sylow p H) [(P : Subgroup H).Normal] :
    (P : Subgroup H) = (pCore p H).subgroupOf H :=
  le_antisymm (le_pCore_subgroupOf inferInstance P.2) (pCore_subgroupOf_le_sylow P)

/-- A Sylow `p`-subgroup of `H` equals the `p`-core (inside `H`) iff it is normal. -/
theorem pCore_subgroupOf_eq_sylow_iff_normal (P : Sylow p H) :
    (pCore p H).subgroupOf H = (P : Subgroup H) ↔ (P : Subgroup H).Normal := by
  refine ⟨fun h => h ▸ pCore_subgroupOf_normal, fun h => ?_⟩
  haveI := h
  exact (sylow_eq_pCore_subgroupOf_of_normal P).symm

/-- The universal property, stated for an ambient-group subgroup: a `p`-subgroup `N ≤ H`
that is normal in `H` is contained in the `p`-core. -/
theorem le_pCore_of_le {N : Subgroup G} (hle : N ≤ H) (hnorm : (N.subgroupOf H).Normal)
    (hp : IsPGroup p N) : N ≤ pCore p H := by
  rw [← map_subgroupOf_eq_of_le hle]
  exact le_pCore hnorm (hp.of_equiv (subgroupOfEquivOfLe hle).symm)

section Hom

variable {G' : Type*} [Group G']

/-- A group homomorphism sends the `p`-core of `H` into the `p`-core of `H.map f`. -/
theorem map_pCore_le_pCore (f : G →* G') : (pCore p H).map f ≤ pCore p (H.map f) := by
  rw [pCore, Subgroup.map_iSup]
  refine iSup_le fun N => ?_
  rw [Subgroup.map_map,
    show f.comp H.subtype = (H.map f).subtype.comp (f.subgroupMap H) from rfl,
    ← Subgroup.map_map]
  exact le_pCore (N.2.1.map _ (f.subgroupMap_surjective H)) (N.2.2.map _)

/-- Adjoint form of `map_pCore_le_pCore`. -/
theorem pCore_le_comap_pCore (f : G →* G') :
    pCore p H ≤ (pCore p (H.map f)).comap f :=
  map_le_iff_le_comap.mp (map_pCore_le_pCore f)

/-- A group isomorphism `e : G ≃* G'` carries the `p`-core of `H` to the `p`-core of its image. -/
theorem _root_.MulEquiv.map_pCore (e : G ≃* G') :
    (pCore p H).map (e : G →* G') = pCore p (H.map (e : G →* G')) := by
  have he : (e.symm : G' →* G).comp (e : G →* G') = MonoidHom.id G :=
    MonoidHom.ext e.symm_apply_apply
  have he' : (e : G →* G').comp (e.symm : G' →* G) = MonoidHom.id G' :=
    MonoidHom.ext e.apply_symm_apply
  refine le_antisymm (map_pCore_le_pCore _) ?_
  have h := map_pCore_le_pCore (p := p) (e.symm : G' →* G) (H := H.map (e : G →* G'))
  rw [Subgroup.map_map, he, Subgroup.map_id] at h
  calc pCore p (H.map (e : G →* G'))
      = ((pCore p (H.map (e : G →* G'))).map (e.symm : G' →* G)).map (e : G →* G') := by
        rw [Subgroup.map_map, he', Subgroup.map_id]
    _ ≤ (pCore p H).map (e : G →* G') := map_mono h

/-- If the restriction `f.subgroupMap H` has `p`-group kernel, then `f` maps the `p`-core of `H`
exactly onto the `p`-core of `H.map f`. The hypothesis is implied by `IsPGroup p f.ker`. -/
theorem map_pCore_eq_pCore (f : G →* G') (hker : IsPGroup p (f.subgroupMap H).ker) :
    (pCore p H).map f = pCore p (H.map f) := by
  refine le_antisymm (map_pCore_le_pCore f) ?_
  rw [← map_subgroupOf_eq_of_le (pCore_le : pCore p (H.map f) ≤ H.map f),
    ← map_subgroupOf_eq_of_le (map_mono pCore_le : (pCore p H).map f ≤ H.map f),
    ← subgroupOf_map_subgroupMap f pCore_le]
  refine map_mono ?_
  conv_lhs => rw [← Subgroup.map_comap_eq_self_of_surjective (f.subgroupMap_surjective H)
    ((pCore p (H.map f)).subgroupOf (H.map f))]
  exact map_mono <| le_pCore_subgroupOf (pCore_subgroupOf_normal.comap _)
    (isPGroup_pCore_subgroupOf.comap_of_ker_isPGroup _ hker)

/-- If `f` has `p`-group kernel, then `f` maps the `p`-core of `H` exactly onto the `p`-core of
`H.map f`. This is the convenient form of `map_pCore_eq_pCore`. -/
theorem map_pCore_eq_pCore_of_ker_isPGroup (f : G →* G') (hker : IsPGroup p f.ker) :
    (pCore p H).map f = pCore p (H.map f) :=
  map_pCore_eq_pCore f <| by
    rw [ker_subgroupMap]; exact hker.comap_of_injective H.subtype H.subtype_injective

/-- If `f` has `p`-group kernel, the preimage of the `p`-core of `H'` is contained in the
`p`-core of `H'.comap f`. -/
theorem comap_pCore_le_pCore (f : G →* G') (H' : Subgroup G') (hker : IsPGroup p f.ker) :
    (pCore p H').comap f ≤ pCore p (H'.comap f) := by
  refine le_pCore_of_le (comap_mono pCore_le) ?_ (isPGroup_pCore.comap_of_ker_isPGroup f hker)
  rw [← subgroupOf_comap_subgroupComap]
  exact pCore_subgroupOf_normal.comap _

/-- If `H' ≤ f.range` and `f` has `p`-group kernel, the preimage of the `p`-core of `H'` is exactly
the `p`-core of `H'.comap f`. -/
theorem comap_pCore_eq_pCore (f : G →* G') (H' : Subgroup G') (hf : H' ≤ f.range)
    (hker : IsPGroup p f.ker) :
    (pCore p H').comap f = pCore p (H'.comap f) := by
  refine le_antisymm (comap_pCore_le_pCore f H' hker) ?_
  rw [← map_le_iff_le_comap]
  calc (pCore p (H'.comap f)).map f
      ≤ pCore p ((H'.comap f).map f) := map_pCore_le_pCore f
    _ = pCore p H' := by rw [map_comap_eq_self hf]

end Hom

end Subgroup
