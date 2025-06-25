/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Data.Finite.Card
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer
import Mathlib.Tactic.Group
/-!
# SubMulActions on complements of invariant subsets

- We define `SubMulAction` of an invariant subset in various contexts,
especially stabilizers and fixing subgroups : `SubMulAction_of_compl`,
`SubMulAction_of_stabilizer`, `SubMulAction_of_fixingSubgroup`.

- We define equivariant maps that relate various of these `SubMulAction`s
and permit to manipulate them in a relatively smooth way:

  * `SubMulAction.ofFixingSubgroupEmpty_equivariantMap`:
  the identity map, when the set is the empty set.

  * `SubMulAction.fixingSubgroupInsertEquiv M a s` : the
  multiplicative equivalence between `fixingSubgroup M (insert a s)``
  and `fixingSubgroup (stablizer M a) s`

  * `SubMulAction.ofFixingSubgroup_insert_map` : the equivariant
  map between `SubMulAction.ofFixingSubgroup M (insert a s)`
  and `SubMulAction.ofFixingSubgroup (stablizer M a) s`.

  * `SubMulAction.fixingSubgroupEquivFixingSubgroup`:
  the multiplicative equivalence between `SubMulAction.fixingSubgroup M s`
  and `SubMulAction.fixingSubgroup M t` induced by `g : M`
  such that `g • t = s`.

  * `SubMulAction.conjMap_ofFixingSubgroup`:
  the equivariant map between `SubMulAction.ofFixingSubgroup M t`
  and `SubMulAction.ofFIxingSubgroup M s`
  induced by `g : M` such that `g • t = s`.

  * `SubMulAction.ofFixingSubgroup_of_inclusion`:
  the identity from `SubMulAction.ofFixingSubgroup M s`
  to `SubMulAction.ofFixingSubgroup M t`, when `t ⊆ s`,
  as an equivariant map.

  * `SubMulAction.ofFixingSubgroup_of_singleton`:
  the identity map from `SubMulAction.ofStablizer M a`
  to `SubMulAction.ofFixingSubgroup M {a}`.

  * `SubMulAction.ofFixingSubgroup_of_eq`:
  the identity from `SubMulAction.ofFixingSubgroup M s`
  to `SubMulAction.ofFixingSubgroup M t`, when `s = t`,
  as an equivariant map.

  * `SubMulAction.ofFixingSubgroup.append`: appends
  an enumeration of `ofFixingSubgroup M s` at the end
  of an enumeration of `s`, as an equivariant map.

-/

open scoped Pointwise

open MulAction Function

namespace SubMulAction

variable (M : Type*) {α : Type*} [Group M] [MulAction M α] (s : Set α)

/-- The `SubMulAction` of `fixingSubgroup M s` on the complement of `s`. -/
@[to_additive "The `SubAddAction` of `fixingAddSubgroup M s` on the complement of `s`."]
def ofFixingSubgroup : SubMulAction (fixingSubgroup M s) α where
  carrier := sᶜ
  smul_mem' := fun ⟨c, hc⟩ x ↦ by
    rw [← Subgroup.inv_mem_iff] at hc
    simp only [Set.mem_compl_iff, not_imp_not]
    intro hcx
    rwa [← one_smul M x, ← inv_mul_cancel c, mul_smul, (mem_fixingSubgroup_iff M).mp hc (c • x) hcx]

@[to_additive (attr := simp)]
theorem ofFixingSubgroup_carrier :
    (ofFixingSubgroup M s).carrier = sᶜ := rfl

variable {s}

@[to_additive]
theorem mem_ofFixingSubgroup_iff {x : α} :
    x ∈ ofFixingSubgroup M s ↔ x ∉ s :=
  Iff.rfl

variable {M}

@[to_additive]
theorem not_mem_of_mem_ofFixingSubgroup (x : ofFixingSubgroup M s) :
    ↑x ∉ s := x.prop

variable (M s) in
/-- The identity map of the `SubMulAction` of the `fixingSubgroup`
into the ambient set, as an equivariant map. -/
@[to_additive
"The identity map of the `SubAddAction` of the `fixingAddSubgroup`
into the ambient set, as an equivariant map."]
def ofFixingSubgroup_equivariantMap :
    ofFixingSubgroup M s →ₑ[(fixingSubgroup M s).subtype] α where
  toFun x := x
  map_smul' _ _ := rfl

@[to_additive]
theorem ofFixingSubgroup_equivariantMap_injective :
    Injective (ofFixingSubgroup_equivariantMap M s) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  simpa [Subtype.mk.injEq] using hxy

section Comparisons

variable (M α)

section Empty

@[to_additive]
theorem ofFixingSubgroupEmpty_equivariantMap_bijective :
    Bijective (ofFixingSubgroup_equivariantMap M (∅ : Set α)) := by
  refine ⟨ofFixingSubgroup_equivariantMap_injective, fun x ↦ ?_⟩
  exact ⟨⟨x, (mem_ofFixingSubgroup_iff M).mp (Set.notMem_empty x)⟩, rfl⟩

@[to_additive]
theorem of_fixingSubgroupEmpty_mapScalars_surjective :
    Surjective (fixingSubgroup M (∅ : Set α)).subtype := fun g ↦ by
  suffices g ∈ fixingSubgroup M (∅ : Set α) by
    exact ⟨⟨g, this⟩, rfl⟩
  simp [mem_fixingSubgroup_iff]

end Empty

section FixingSubgroupInsert

variable {α}

variable {M} in
@[to_additive]
theorem mem_fixingSubgroup_insert_iff {a : α} {s : Set α} {m : M} :
    m ∈ fixingSubgroup M (insert a s) ↔ m • a = a ∧ m ∈ fixingSubgroup M s := by
  simp [mem_fixingSubgroup_iff]

variable {M} in
@[to_additive]
theorem fixingSubgroup_of_insert (a : α) (s : Set (ofStabilizer M a)) :
    fixingSubgroup M (insert a ((fun x ↦ x.val) '' s)) =
      (fixingSubgroup (↥(stabilizer M a)) s).map (stabilizer M a).subtype := by
  ext m
  simp [mem_fixingSubgroup_iff, mem_ofStabilizer_iff, subgroup_smul_def, and_comm]

variable {M} in
@[to_additive]
theorem mem_ofFixingSubgroup_insert_iff {a : α} {s : Set (ofStabilizer M a)} {x : α} :
    x ∈ ofFixingSubgroup M (insert a ((fun x ↦ x.val) '' s)) ↔
      ∃ (hx : x ∈ ofStabilizer M a),
        (⟨x, hx⟩ : ofStabilizer M a) ∈ ofFixingSubgroup (stabilizer M a) s := by
  simp_rw [mem_ofFixingSubgroup_iff, mem_ofStabilizer_iff]
  aesop

/-- The natural group isomorphism between fixing subgroups. -/
@[to_additive "The natural additive group isomorphism between fixing additive subgroups."]
def fixingSubgroupInsertEquiv (a : α) (s : Set (ofStabilizer M a)) :
    fixingSubgroup M (insert a (Subtype.val '' s)) ≃* fixingSubgroup (stabilizer M a) s where
  toFun m := ⟨⟨(m : M), (mem_fixingSubgroup_iff M).mp m.prop a (Set.mem_insert _ _)⟩,
      fun ⟨x, hx⟩ => by
        simp only [← SetLike.coe_eq_coe]
        refine (mem_fixingSubgroup_iff M).mp m.prop _ (Set.mem_insert_of_mem a ?_)
        exact ⟨⟨x, (SubMulAction.mem_ofStabilizer_iff  M a).mp x.prop⟩, hx, rfl⟩⟩
  map_mul' _ _ := by simp [← Subtype.coe_inj]
  invFun m := ⟨m, by simp [fixingSubgroup_of_insert]⟩
  left_inv _ := by simp
  right_inv _ := by simp

/-- The identity map of fixing subgroup of stabilizer
into the fixing subgroup of the extended set, as an equivariant map. -/
@[to_additive "The identity map of fixing additive subgroup of stabilizer
into the fixing additive subgroup of the extended set, as an equivariant map."]
def ofFixingSubgroup_insert_map (a : α) (s : Set (ofStabilizer M a)) :
    ofFixingSubgroup M (insert a (Subtype.val '' s))
      →ₑ[fixingSubgroupInsertEquiv M a s] (ofFixingSubgroup (stabilizer M a) s) where
  toFun x := by
    choose hx hx' using (mem_ofFixingSubgroup_insert_iff.mp x.prop)
    exact ⟨_, hx'⟩
  map_smul' _ _ := rfl

variable {M} in
@[to_additive (attr := simp)]
theorem ofFixingSubgroup_insert_map_apply {a : α} {s : Set (ofStabilizer M a)}
    {x : α} (hx : x ∈ ofFixingSubgroup M (insert a (Subtype.val '' s))) :
    (ofFixingSubgroup_insert_map M a s) ⟨x, hx⟩ = x :=
  rfl

@[to_additive]
theorem ofFixingSubgroup_insert_map_bijective (a : α) (s : Set (ofStabilizer M a)) :
    Bijective (ofFixingSubgroup_insert_map M a s) := by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    simpa only [← Subtype.coe_inj, ofFixingSubgroup_insert_map_apply] using h
  · rintro ⟨⟨x, hx1⟩, hx2⟩
    exact ⟨⟨x, mem_ofFixingSubgroup_insert_iff.mpr ⟨hx1, hx2⟩⟩, rfl⟩

end FixingSubgroupInsert

section FixingSubgroupConj

variable {s t : Set α} {g : M}

@[to_additive]
theorem _root_.Set.conj_mem_fixingSubgroup (hg : g • t = s) {k : M} (hk : k ∈ fixingSubgroup M t) :
    MulAut.conj g k ∈ fixingSubgroup M s := by
  simp only [mem_fixingSubgroup_iff] at hk ⊢
  intro y hy
  rw [MulAut.conj_apply, eq_comm, mul_smul, mul_smul, ← inv_smul_eq_iff, eq_comm]
  apply hk
  rw [← Set.mem_smul_set_iff_inv_smul_mem, hg]
  exact hy

@[to_additive]
theorem fixingSubgroup_map_conj_eq (hg : g • t = s) :
    (fixingSubgroup M t).map (MulAut.conj g).toMonoidHom = fixingSubgroup M s :=  by
  ext k
  simp only [MulEquiv.toMonoidHom_eq_coe, Subgroup.mem_map, MonoidHom.coe_coe]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact Set.conj_mem_fixingSubgroup _ _ hg hn
  · intro hk
    use MulAut.conj g⁻¹ k
    constructor
    · apply Set.conj_mem_fixingSubgroup _ _ _ hk
      rw [inv_smul_eq_iff, hg]
    · simp [MulAut.conj]; group

variable (g s) in
/-- The `fixingSubgroup` of `g • s` is the conjugate of the `fixingSubgroup` of `s` by `g`. -/
@[to_additive "The `fixingAddSubgroup` of `g +ᵥ s` is the conjugate
of the `fixingAddSubgroup` of `s` by `g`."]
theorem fixingSubgroup_smul_eq_fixingSubgroup_map_conj :
    fixingSubgroup M (g • s) = (fixingSubgroup M s).map (MulAut.conj g).toMonoidHom :=
  (fixingSubgroup_map_conj_eq _ _ rfl).symm

/-- The equivalence of `fixingSubgroup M t` with `fixingSubgroup M s`
  when `s` is a translate of `t`. -/
@[to_additive
"The equivalence of `fixingSubgroup M t` with `fixingSubgroup M s`
  when `s` is a translate of `t`."]
def fixingSubgroupEquivFixingSubgroup (hg : g • t = s) :
    fixingSubgroup M t ≃* fixingSubgroup M s :=
  ((MulAut.conj g).subgroupMap (fixingSubgroup M t)).trans
    (MulEquiv.subgroupCongr (fixingSubgroup_map_conj_eq _ _ hg))

@[to_additive (attr := simp)]
theorem fixingSubgroupEquivFixingSubgroup_coe_apply (hg : g • t = s) (x : fixingSubgroup M t) :
    (fixingSubgroupEquivFixingSubgroup M α hg x : M) = MulAut.conj g x := rfl

/-- Conjugation induces an equivariant map between the `SubMulAction` of
the fixing subgroup of a subset and that of a translate. -/
@[to_additive
"Conjugation induces an equivariant map between the `SubAddAction` of
the fixing subgroup of a subset and that of a translate."]
def conjMap_ofFixingSubgroup (hg : g • t = s) :
    ofFixingSubgroup M t →ₑ[fixingSubgroupEquivFixingSubgroup M α hg] ofFixingSubgroup M s where
  toFun := fun ⟨x, hx⟩ =>
    ⟨g • x, by
      intro hgxt; apply hx
      rw [← hg] at hgxt
      exact Set.smul_mem_smul_set_iff.mp hgxt⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => by
    simp [← SetLike.coe_eq_coe, subgroup_smul_def, subgroup_smul_def,
      MulAut.conj_apply, mul_smul, inv_smul_smul]

@[to_additive (attr := simp)]
theorem conjMap_ofFixingSubgroup_coe_apply {hg : g • t = s} (x : ofFixingSubgroup M t) :
    conjMap_ofFixingSubgroup _ _ hg x = g • (x : α) := rfl

@[to_additive]
theorem conjMap_ofFixingSubgroup_bijective {s t : Set α} {g : M} (hst : g • s = t) :
    Bijective (conjMap_ofFixingSubgroup M α hst) := by
  constructor
  · rintro  x y hxy
    simpa [← SetLike.coe_eq_coe] using hxy
  · rintro ⟨x, hx⟩
    rw [eq_comm, ← inv_smul_eq_iff] at hst
    use (SubMulAction.conjMap_ofFixingSubgroup _ _ hst) ⟨x, hx⟩
    simp [← SetLike.coe_eq_coe]

end FixingSubgroupConj

/-- The identity between the iterated `SubMulAction`
  of the `fixingSubgroup` and the `SubMulAction` of the `fixingSubgroup`
  of the union, as an equivariant map. -/
@[to_additive "The identity between the iterated `SubAddAction`
  of the `fixingAddSubgroup` and the `SubAddAction` of the `fixingAddSubgroup`
  of the union, as an equivariant map."]
def map_ofFixingSubgroupUnion (s t : Set α) :
    let ψ : fixingSubgroup M (s ∪ t) →
      fixingSubgroup (fixingSubgroup M s) (Subtype.val ⁻¹' t : Set (ofFixingSubgroup M s)) :=
      fun m ↦ ⟨⟨m, by
        let hm := m.prop
        simp only [fixingSubgroup_union, Subgroup.mem_inf] at hm
        exact hm.left⟩, by
      let hm := m.prop
      simp only [fixingSubgroup_union, Subgroup.mem_inf] at hm
      rintro ⟨⟨x, hx⟩, hx'⟩
      simp only [Set.mem_preimage] at hx'
      simp only [← SetLike.coe_eq_coe, Subtype.coe_mk, SubMulAction.val_smul_of_tower]
      exact hm.right ⟨x, hx'⟩⟩
    ofFixingSubgroup M (s ∪ t) →ₑ[ψ]
      ofFixingSubgroup (fixingSubgroup M s) (Subtype.val ⁻¹' t : Set (ofFixingSubgroup M s)) where
  toFun x :=
    ⟨⟨x, fun hx => x.prop (Set.mem_union_left t hx)⟩,
        fun hx => x.prop (by
          apply Set.mem_union_right s
          simpa only [Set.mem_preimage, Subtype.coe_mk] using hx)⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => by
    rw [← SetLike.coe_eq_coe, ← SetLike.coe_eq_coe]
    rfl

@[to_additive]
theorem map_ofFixingSubgroupUnion_def (s t : Set α)
    (x : SubMulAction.ofFixingSubgroup M (s ∪ t)) :
    ((SubMulAction.map_ofFixingSubgroupUnion M _ s t) x : α) = x :=
  rfl

@[to_additive]
theorem map_ofFixingSubgroupUnion_bijective (s t : Set α) :
    Bijective (map_ofFixingSubgroupUnion M _ s t) := by
  constructor
  · intro a b h
    simpa only [← SetLike.coe_eq_coe] using h
  · rintro ⟨⟨a, ha⟩, ha'⟩
    suffices a ∈ ofFixingSubgroup M (s ∪ t) by
      exact ⟨⟨a, this⟩,  rfl⟩
    intro hy
    rcases (Set.mem_union a s t).mp hy with h | h
    · exact ha h
    · apply ha'
      simpa only [Set.mem_preimage]

/-- The equivariant map on `SubMulAction.ofFixingSubgroup` given a set inclusion. -/
@[to_additive
"The equivariant map on `SubAddAction.ofFixingAddSubgroup` given a set inclusion."]
def ofFixingSubgroup_of_inclusion {s t : Set α} (hst : t ⊆ s) :
    ofFixingSubgroup M s
      →ₑ[Subgroup.inclusion (fixingSubgroup_antitone M α hst)]
        ofFixingSubgroup M t where
  toFun y := ⟨y.val, fun h => y.prop (hst h)⟩
  map_smul' _ _ := rfl

@[to_additive]
lemma ofFixingSubgroup_of_inclusion_injective {s t : Set α} (hst : t ⊆ s) :
    Injective (ofFixingSubgroup_of_inclusion M _ hst) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  rw [← SetLike.coe_eq_coe] at hxy ⊢
  exact hxy

/-- The equivariant map between `SubMulAction.ofStabilizer M a`
and `ofFixingSubgroup M {a}`. -/
@[to_additive "The equivariant map between `SubAddAction.ofStabilizer M a`
and `ofFixingAddSubgroup M {a}`."]
def ofFixingSubgroup_of_singleton (a : α) :
    let φ : fixingSubgroup M ({a} : Set α) → stabilizer M a := fun ⟨m, hm⟩ =>
      ⟨m, ((mem_fixingSubgroup_iff M).mp hm) a (Set.mem_singleton a)⟩
    ofFixingSubgroup M ({a} : Set α) →ₑ[φ] ofStabilizer M a where
  toFun x := ⟨x, by simp⟩
  map_smul' _ _ := rfl

@[to_additive]
theorem ofFixingSubgroup_of_singleton_bijective (a : α) :
    Bijective (ofFixingSubgroup_of_singleton M _ a) :=
  ⟨fun _ _ ↦ id, fun x ↦ ⟨x, rfl⟩⟩

/-- The identity between the `SubMulAction`s of `fixingSubgroup`s
of equal sets, as an equivariant map. -/
@[to_additive "The identity between the `SubAddAction`s of `fixingAddSubgroup`s
of equal sets, as an equivariant map."]
def ofFixingSubgroup_of_eq {s t : Set α} (hst : s = t) :
    let φ : fixingSubgroup M s ≃* fixingSubgroup M t :=
      MulEquiv.subgroupCongr (congrArg₂ _ rfl hst)
    ofFixingSubgroup M s →ₑ[φ] ofFixingSubgroup M t where
  toFun := fun ⟨x, hx⟩ => ⟨x, by rw [← hst]; exact hx⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => rfl

@[to_additive (attr := simp)]
theorem ofFixingSubgroup_of_eq_apply {s t : Set α} (hst : s = t)
    (x : ofFixingSubgroup M s) :
    ((ofFixingSubgroup_of_eq M _ hst x) : α) = x := rfl

@[to_additive]
theorem ofFixingSubgroup_of_eq_bijective {s t : Set α} (hst : s = t) :
    Bijective (ofFixingSubgroup_of_eq M _ hst) :=
  ⟨fun _ _ hxy ↦ by simpa [← SetLike.coe_eq_coe] using hxy,
    fun ⟨x, hxt⟩ ↦ ⟨⟨x, by rwa [hst]⟩, by simp [← SetLike.coe_eq_coe]⟩⟩

end Comparisons

section Construction

open Function.Embedding Fin.Embedding

/-- Append `Fin m ↪ ofFixingSubgroup M s` at the end of an enumeration of `s`. -/
@[to_additive
"Append `Fin m ↪ ofFixingSubgroup M s` at the end of an enumeration of `s`."]
noncomputable def ofFixingSubgroup.append
    {n : ℕ} {s : Set α} [Finite s] (x : Fin n ↪ ofFixingSubgroup M s) :
    Fin (s.ncard + n) ↪ α := by
  have : Nonempty (Fin (s.ncard) ≃ s) :=
    Finite.card_eq.mp (by simp [Set.Nat.card_coe_set_eq])
  let y := (Classical.choice this).toEmbedding
  apply Fin.Embedding.append (x := y.trans (subtype _)) (y := x.trans (subtype _))
  rw [Set.disjoint_iff_forall_ne]
  rintro _ ⟨j, rfl⟩ _ ⟨i, rfl⟩ H
  apply (x i).prop
  simp only [trans_apply, Function.Embedding.subtype_apply, ne_eq] at H
  simpa [H] using Subtype.coe_prop (y j)

@[to_additive]
theorem ofFixingSubgroup.append_left {n : ℕ} {s : Set α} [Finite s]
    (x : Fin n ↪ ofFixingSubgroup M s) (i : Fin s.ncard) :
    let Hs : Nonempty (Fin (s.ncard) ≃ s) :=
      Finite.card_eq.mp (by simp [Set.Nat.card_coe_set_eq])
    ofFixingSubgroup.append x (Fin.castAdd n i) = (Classical.choice Hs) i := by
  simp [ofFixingSubgroup.append]

@[to_additive]
theorem ofFixingSubgroup.append_right {n : ℕ} {s : Set α} [Finite s]
    (x : Fin n ↪ ofFixingSubgroup M s) (i : Fin n) :
    ofFixingSubgroup.append x (Fin.natAdd s.ncard i) = x i := by
  simp [ofFixingSubgroup.append]

end Construction

end SubMulAction
