/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer
public import Mathlib.GroupTheory.GroupAction.Primitive

import all Mathlib.Algebra.Group.End -- TODO: needed for `to_additive`
public import Mathlib.Data.Finite.Card
public import Mathlib.Tactic.Choose
import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Set.Disjoint
import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Group
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# SubMulActions on complements of invariant subsets

Given a `MulAction` of `G` on `α` and `s : Set α`,

- `SubMulAction.ofFixingSubgroup` is the action
  of `FixingSubgroup G s` on the complement `sᶜ` of `s`.

- We define equivariant maps that relate various of these `SubMulAction`s
  and permit to manipulate them in a relatively smooth way:

  * `SubMulAction.ofFixingSubgroup_equivariantMap`:
    the identity map from `sᶜ` to `α`, as an equivariant map
    relative to the injection of `FixingSubgroup G s` into `G`.

  * `SubMulAction.fixingSubgroupInsertEquiv M a s`: the
    multiplicative equivalence between `fixingSubgroup M (insert a s)`
    and `fixingSubgroup (stabilizer M a) s`

  * `SubMulAction.ofFixingSubgroup_insert_map`: the equivariant
    map between `SubMulAction.ofFixingSubgroup M (Set.insert a s)`
    and `SubMulAction.ofFixingSubgroup (MulAction.stabilizer M a) s`.

  * `SubMulAction.fixingSubgroupEquivFixingSubgroup`:
    the multiplicative equivalence between `SubMulAction.ofFixingSubgroup M s`
    and `SubMulAction.ofFixingSubgroup M t` induced by `g : M`
    such that `g • t = s`.

  * `SubMulAction.conjMap_ofFixingSubgroup`:
    the equivariant map between `SubMulAction.ofFixingSubgroup M t`
    and `SubMulAction.ofFixingSubgroup M s`
    induced by `g : M` such that `g • t = s`.

  * `SubMulAction.ofFixingSubgroup_of_inclusion`:
    the identity from `SubMulAction.ofFixingSubgroup M s`
    to `SubMulAction.ofFixingSubgroup M t`, when `t ⊆ s`,
    as an equivariant map.

  * `SubMulAction.ofFixingSubgroup_of_singleton`:
    the identity map from `SubMulAction.ofStabilizer M a`
    to `SubMulAction.ofFixingSubgroup M {a}`.

  * `SubMulAction.ofFixingSubgroup_of_eq`:
    the identity from `SubMulAction.ofFixingSubgroup M s`
    to `SubMulAction.ofFixingSubgroup M t`, when `s = t`,
    as an equivariant map.

  * `SubMulAction.ofFixingSubgroup.append`: appends
    an enumeration of `ofFixingSubgroup M s` at the end
    of an enumeration of `s`, as an equivariant map.

-/

@[expose] public section

open scoped Pointwise

open MulAction Function

namespace SubMulAction

variable (M : Type*) {α : Type*} [Group M] [MulAction M α] (s : Set α)

/-- The `SubMulAction` of `fixingSubgroup M s` on the complement of `s`. -/
@[to_additive /-- The `SubAddAction` of `fixingAddSubgroup M s` on the complement of `s`. -/]
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

@[to_additive]
theorem disjoint_val_image {t : Set (ofFixingSubgroup M s)} :
    Disjoint s (Subtype.val '' t) := by
  rw [Set.disjoint_iff]
  rintro a ⟨hbs, ⟨b, _, rfl⟩⟩; exact (b.prop hbs).elim

variable (M s) in
/-- The identity map of the `SubMulAction` of the `fixingSubgroup`
into the ambient set, as an equivariant map. -/
@[to_additive
/-- The identity map of the `SubAddAction` of the `fixingAddSubgroup`
into the ambient set, as an equivariant map. -/]
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

section Empty

@[to_additive]
theorem ofFixingSubgroupEmpty_equivariantMap_bijective :
    Bijective (ofFixingSubgroup_equivariantMap M (∅ : Set α)) := by
  refine ⟨ofFixingSubgroup_equivariantMap_injective, fun x ↦ ?_⟩
  exact ⟨⟨x, (mem_ofFixingSubgroup_iff M).mp (Set.notMem_empty x)⟩, rfl⟩

@[to_additive]
theorem of_fixingSubgroupEmpty_mapScalars_surjective :
    Surjective (fixingSubgroup M (∅ : Set α)).subtype :=
  fun g ↦ ⟨⟨g, by simp⟩, rfl⟩

end Empty

section FixingSubgroupInsert

@[to_additive]
theorem mem_fixingSubgroup_insert_iff {a : α} {s : Set α} {m : M} :
    m ∈ fixingSubgroup M (insert a s) ↔ m • a = a ∧ m ∈ fixingSubgroup M s := by
  simp [mem_fixingSubgroup_iff]

@[to_additive]
theorem fixingSubgroup_of_insert (a : α) (s : Set (ofStabilizer M a)) :
    fixingSubgroup M (insert a ((fun x ↦ x.val) '' s)) =
      (fixingSubgroup (↥(stabilizer M a)) s).map (stabilizer M a).subtype := by
  ext m
  simp [mem_fixingSubgroup_iff, mem_ofStabilizer_iff, subgroup_smul_def, and_comm]

@[to_additive]
theorem mem_ofFixingSubgroup_insert_iff {a : α} {s : Set (ofStabilizer M a)} {x : α} :
    x ∈ ofFixingSubgroup M (insert a ((fun x ↦ x.val) '' s)) ↔
      ∃ (hx : x ∈ ofStabilizer M a),
        (⟨x, hx⟩ : ofStabilizer M a) ∈ ofFixingSubgroup (stabilizer M a) s := by
  grind [mem_ofFixingSubgroup_iff, mem_ofStabilizer_iff]

/-- The natural group isomorphism between fixing subgroups. -/
@[to_additive /-- The natural additive group isomorphism between fixing additive subgroups. -/]
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
@[to_additive /-- The identity map of fixing additive subgroup of stabilizer
into the fixing additive subgroup of the extended set, as an equivariant map. -/]
def ofFixingSubgroup_insert_map (a : α) (s : Set (ofStabilizer M a)) :
    ofFixingSubgroup M (insert a (Subtype.val '' s))
      →ₑ[fixingSubgroupInsertEquiv a s]
        ofFixingSubgroup (stabilizer M a) s where
  toFun x := by
    choose hx hx' using (mem_ofFixingSubgroup_insert_iff.mp x.prop)
    exact ⟨_, hx'⟩
  map_smul' _ _ := rfl

@[to_additive (attr := simp)]
theorem ofFixingSubgroup_insert_map_apply {a : α} {s : Set (ofStabilizer M a)}
    {x : α} (hx : x ∈ ofFixingSubgroup M (insert a (Subtype.val '' s))) :
    (ofFixingSubgroup_insert_map a s) ⟨x, hx⟩ = x :=
  rfl

@[to_additive]
theorem ofFixingSubgroup_insert_map_bijective {a : α} {s : Set (ofStabilizer M a)} :
    Bijective (ofFixingSubgroup_insert_map a s) := by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    simpa only [← Subtype.coe_inj, ofFixingSubgroup_insert_map_apply] using h
  · rintro ⟨⟨x, hx1⟩, hx2⟩
    exact ⟨⟨x, mem_ofFixingSubgroup_insert_iff.mpr ⟨hx1, hx2⟩⟩, rfl⟩

end FixingSubgroupInsert

section FixingSubgroupConj

variable {s t : Set α} {g : M}

/-
FIXME: The use of `to_additive` in this section is a horrible mess.
It requires translating `MulAut.instGroup` to `AddAut.instAddGroup` instead of `AddAut.instGroup`,
and `MulAut.conj` shouldn't be able to translate to `AddAut.conj`, but somehow it works out.
-/
attribute [to_additive] MulAut.instGroup

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
    (fixingSubgroup M t).map (MulAut.conj g).toMonoidHom = fixingSubgroup M s := by
  ext k
  simp only [MulEquiv.toMonoidHom_eq_coe, Subgroup.mem_map, MonoidHom.coe_coe]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact Set.conj_mem_fixingSubgroup hg hn
  · intro hk
    use MulAut.conj g⁻¹ k
    constructor
    · apply Set.conj_mem_fixingSubgroup _ hk
      rw [inv_smul_eq_iff, hg]
    · simp [MulAut.conj]; group

variable (g s) in
/-- The `fixingSubgroup` of `g • s` is the conjugate of the `fixingSubgroup` of `s` by `g`. -/
@[to_additive /-- The `fixingAddSubgroup` of `g +ᵥ s` is the conjugate
of the `fixingAddSubgroup` of `s` by `g`. -/]
theorem fixingSubgroup_smul_eq_fixingSubgroup_map_conj :
    fixingSubgroup M (g • s) = (fixingSubgroup M s).map (MulAut.conj g).toMonoidHom :=
  (fixingSubgroup_map_conj_eq rfl).symm

/-- The equivalence of `fixingSubgroup M t` with `fixingSubgroup M s`
  when `s` is a translate of `t`. -/
@[to_additive
/-- The equivalence of `fixingSubgroup M t` with `fixingSubgroup M s`
  when `s` is a translate of `t`. -/]
def fixingSubgroupEquivFixingSubgroup (hg : g • t = s) :
    fixingSubgroup M t ≃* fixingSubgroup M s :=
  ((MulAut.conj g).subgroupMap (fixingSubgroup M t)).trans
    (MulEquiv.subgroupCongr (fixingSubgroup_map_conj_eq hg))

@[to_additive (attr := simp)]
theorem fixingSubgroupEquivFixingSubgroup_coe_apply (hg : g • t = s) (x : fixingSubgroup M t) :
    (fixingSubgroupEquivFixingSubgroup hg x : M) = MulAut.conj g x := rfl

/-- Conjugation induces an equivariant map between the `SubMulAction` of
the fixing subgroup of a subset and that of a translate. -/
@[to_additive
/-- Conjugation induces an equivariant map between the `SubAddAction` of
the fixing subgroup of a subset and that of a translate. -/]
def conjMap_ofFixingSubgroup (hg : g • t = s) :
    ofFixingSubgroup M t →ₑ[fixingSubgroupEquivFixingSubgroup hg] ofFixingSubgroup M s where
  toFun := fun ⟨x, hx⟩ =>
    ⟨g • x, by
      intro hgxt; apply hx
      rw [← hg] at hgxt
      exact Set.smul_mem_smul_set_iff.mp hgxt⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => by
    simp only [← SetLike.coe_eq_coe, subgroup_smul_def,
      SetLike.val_smul,
      fixingSubgroupEquivFixingSubgroup_coe_apply,
      MulAut.conj_apply, mul_smul, inv_smul_smul]

@[to_additive (attr := simp)]
theorem conjMap_ofFixingSubgroup_coe_apply {hg : g • t = s} (x : ofFixingSubgroup M t) :
    conjMap_ofFixingSubgroup hg x = g • (x : α) := rfl

@[to_additive]
theorem conjMap_ofFixingSubgroup_bijective {s t : Set α} {g : M} {hst : g • s = t} :
    Bijective (conjMap_ofFixingSubgroup hst) := by
  constructor
  · rintro x y hxy
    simpa [← SetLike.coe_eq_coe] using hxy
  · rintro ⟨x, hx⟩
    rw [eq_comm, ← inv_smul_eq_iff] at hst
    use (SubMulAction.conjMap_ofFixingSubgroup hst) ⟨x, hx⟩
    simp [← SetLike.coe_eq_coe]

end FixingSubgroupConj

variable {s t : Set α}

@[to_additive]
lemma mem_fixingSubgroup_union_iff {g : M} :
    g ∈ fixingSubgroup M (s ∪ t) ↔ g ∈ fixingSubgroup M s ∧ g ∈ fixingSubgroup M t := by
  simp [fixingSubgroup_union, Subgroup.mem_inf]

/-- The group morphism from `fixingSubgroup` of a union to the iterated `fixingSubgroup`. -/
@[to_additive
/-- The additive group morphism from `fixingAddSubgroup` of a union
to the iterated `fixingAddSubgroup`. -/]
def fixingSubgroup_union_to_fixingSubgroup_of_fixingSubgroup :
    fixingSubgroup M (s ∪ t) →*
      fixingSubgroup (fixingSubgroup M s) (Subtype.val ⁻¹' t : Set (ofFixingSubgroup M s)) where
  toFun m := ⟨⟨m, (mem_fixingSubgroup_union_iff.mp m.prop).1⟩, by
      rintro ⟨⟨x, hx⟩, hx'⟩
      simp only [Set.mem_preimage] at hx'
      simp only [← SetLike.coe_eq_coe, SubMulAction.val_smul_of_tower]
      exact (mem_fixingSubgroup_union_iff.mp m.prop).2 ⟨x, hx'⟩⟩
  map_one' := by simp
  map_mul' _ _ := by simp

variable (M s t) in
/-- The identity between the iterated `SubMulAction`
  of the `fixingSubgroup` and the `SubMulAction` of the `fixingSubgroup`
  of the union, as an equivariant map. -/
@[to_additive /-- The identity between the iterated `SubAddAction`
  of the `fixingAddSubgroup` and the `SubAddAction` of the `fixingAddSubgroup`
  of the union, as an equivariant map. -/]
def map_ofFixingSubgroupUnion :
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
      simp only [← SetLike.coe_eq_coe, SubMulAction.val_smul_of_tower]
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
    exact subgroup_smul_def ⟨m, hm⟩ x

@[to_additive]
theorem map_ofFixingSubgroupUnion_def (x : SubMulAction.ofFixingSubgroup M (s ∪ t)) :
    ((SubMulAction.map_ofFixingSubgroupUnion M s t) x : α) = x :=
  rfl

@[to_additive]
theorem map_ofFixingSubgroupUnion_bijective :
    Bijective (map_ofFixingSubgroupUnion M s t) := by
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

variable (M) in
/-- The equivariant map on `SubMulAction.ofFixingSubgroup` given a set inclusion. -/
@[to_additive
/-- The equivariant map on `SubAddAction.ofFixingAddSubgroup` given a set inclusion. -/]
def ofFixingSubgroup_of_inclusion (hst : t ⊆ s) :
    ofFixingSubgroup M s
      →ₑ[Subgroup.inclusion (fixingSubgroup_antitone M α hst)]
        ofFixingSubgroup M t where
  toFun y := ⟨y.val, fun h => y.prop (hst h)⟩
  map_smul' _ _ := rfl

@[to_additive]
lemma ofFixingSubgroup_of_inclusion_injective {hst : t ⊆ s} :
    Injective (ofFixingSubgroup_of_inclusion M hst) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  rw [← SetLike.coe_eq_coe] at hxy ⊢
  exact hxy

variable (M) in
/-- The equivariant map between `SubMulAction.ofStabilizer M a`
and `ofFixingSubgroup M {a}`. -/
@[to_additive /-- The equivariant map between `SubAddAction.ofStabilizer M a`
and `ofFixingAddSubgroup M {a}`. -/]
def ofFixingSubgroup_of_singleton (a : α) :
    let φ : fixingSubgroup M ({a} : Set α) → stabilizer M a := fun ⟨m, hm⟩ =>
      ⟨m, ((mem_fixingSubgroup_iff M).mp hm) a (Set.mem_singleton a)⟩
    ofFixingSubgroup M ({a} : Set α) →ₑ[φ] ofStabilizer M a where
  toFun x := ⟨x, by simp⟩
  map_smul' _ _ := rfl

@[to_additive]
theorem ofFixingSubgroup_of_singleton_bijective {a : α} :
    Bijective (ofFixingSubgroup_of_singleton M a) :=
  ⟨fun _ _ ↦ id, fun x ↦ ⟨x, rfl⟩⟩

variable (M) in
/-- The identity between the `SubMulAction`s of `fixingSubgroup`s
of equal sets, as an equivariant map. -/
@[to_additive /-- The identity between the `SubAddAction`s of `fixingAddSubgroup`s
of equal sets, as an equivariant map. -/]
def ofFixingSubgroup_of_eq (hst : s = t) :
    let φ : fixingSubgroup M s ≃* fixingSubgroup M t :=
      MulEquiv.subgroupCongr (congrArg₂ _ rfl hst)
    ofFixingSubgroup M s →ₑ[φ] ofFixingSubgroup M t where
  toFun := fun ⟨x, hx⟩ => ⟨x, by rw [← hst]; exact hx⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => rfl

@[to_additive (attr := simp)]
theorem ofFixingSubgroup_of_eq_apply {hst : s = t}
    (x : ofFixingSubgroup M s) :
    ((ofFixingSubgroup_of_eq M hst x) : α) = x := rfl

@[to_additive]
theorem ofFixingSubgroup_of_eq_bijective {hst : s = t} :
    Bijective (ofFixingSubgroup_of_eq M hst) :=
  ⟨fun _ _ hxy ↦ by simpa [← SetLike.coe_eq_coe] using hxy,
    fun ⟨x, hxt⟩ ↦ ⟨⟨x, by rwa [hst]⟩, by simp [← SetLike.coe_eq_coe]⟩⟩

end Comparisons

section Construction

open Function.Embedding Fin.Embedding

/-- Append `Fin m ↪ ofFixingSubgroup M s` at the end of an enumeration of `s`. -/
@[to_additive
/-- Append `Fin m ↪ ofFixingSubgroup M s` at the end of an enumeration of `s`. -/]
noncomputable def ofFixingSubgroup.append
    {n : ℕ} [Finite s] (x : Fin n ↪ ofFixingSubgroup M s) :
    Fin (s.ncard + n) ↪ α := by
  have : Nonempty (Fin (s.ncard) ≃ s) :=
    Finite.card_eq.mp (by simp [Nat.card_coe_set_eq])
  let y := (Classical.choice this).toEmbedding
  apply Fin.Embedding.append (x := y.trans (subtype _)) (y := x.trans (subtype _))
  rw [Set.disjoint_iff_forall_ne]
  rintro _ ⟨j, rfl⟩ _ ⟨i, rfl⟩ H
  apply (x i).prop
  simp only [trans_apply, Function.Embedding.subtype_apply] at H
  simpa [H] using Subtype.coe_prop (y j)

@[to_additive]
theorem ofFixingSubgroup.append_left {n : ℕ} [Finite s]
    (x : Fin n ↪ ofFixingSubgroup M s) (i : Fin s.ncard) :
    let Hs : Nonempty (Fin (s.ncard) ≃ s) :=
      Finite.card_eq.mp (by simp [Nat.card_coe_set_eq])
    ofFixingSubgroup.append x (Fin.castAdd n i) = (Classical.choice Hs) i := by
  simp [ofFixingSubgroup.append]

@[to_additive]
theorem ofFixingSubgroup.append_right {n : ℕ} [Finite s]
    (x : Fin n ↪ ofFixingSubgroup M s) (i : Fin n) :
    ofFixingSubgroup.append x (Fin.natAdd s.ncard i) = x i := by
  simp [ofFixingSubgroup.append]

end Construction

section TwoCriteria

open MulAction

/-- A pretransitivity criterion. -/
theorem IsPretransitive.isPretransitive_ofFixingSubgroup_inter
    (hs : IsPretransitive (fixingSubgroup M s) (ofFixingSubgroup M s))
    {g : M} (ha : s ∪ g • s ≠ ⊤) :
    IsPretransitive (fixingSubgroup M (s ∩ g • s)) (ofFixingSubgroup M (s ∩ g • s)) := by
  rw [Ne, Set.top_eq_univ, ← Set.compl_empty_iff, ← Ne, ← Set.nonempty_iff_ne_empty] at ha
  obtain ⟨a, ha⟩ := ha
  rw [Set.compl_union] at ha
  have ha' : a ∈ (s ∩ g • s)ᶜ := by
    rw [Set.compl_inter]
    exact Set.mem_union_left _ ha.1
  rw [MulAction.isPretransitive_iff_base (⟨a, ha'⟩ : ofFixingSubgroup M (s ∩ g • s))]
  rintro ⟨x, hx⟩
  rw [mem_ofFixingSubgroup_iff, Set.mem_inter_iff, not_and_or] at hx
  rcases hx with hx | hx
  · obtain ⟨⟨k, hk⟩, hkax⟩ := hs.exists_smul_eq ⟨a, ha.1⟩ ⟨x, hx⟩
    use ⟨k, fun ⟨y, hy⟩ ↦ hk ⟨y, hy.1⟩⟩
    rwa [Subtype.ext_iff] at hkax ⊢
  · have hg'x : g⁻¹ • x ∈ ofFixingSubgroup M s := mt Set.mem_smul_set_iff_inv_smul_mem.mpr hx
    have hg'a : g⁻¹ • a ∈ ofFixingSubgroup M s := mt Set.mem_smul_set_iff_inv_smul_mem.mpr ha.2
    obtain ⟨⟨k, hk⟩, hkax⟩ := hs.exists_smul_eq ⟨g⁻¹ • a, hg'a⟩ ⟨g⁻¹ • x, hg'x⟩
    use ⟨g * k * g⁻¹, ?_⟩
    · simp only [← SetLike.coe_eq_coe] at hkax ⊢
      rwa [SetLike.val_smul, Subgroup.mk_smul, eq_inv_smul_iff, smul_smul, smul_smul] at hkax
    · rw [mem_fixingSubgroup_iff] at hk ⊢
      intro y hy
      rw [mul_smul, mul_smul, smul_eq_iff_eq_inv_smul g]
      exact hk _ (Set.mem_smul_set_iff_inv_smul_mem.mp hy.2)

/-- A primitivity criterion -/
theorem IsPreprimitive.isPreprimitive_ofFixingSubgroup_inter
    [Finite α]
    (hs : IsPreprimitive (fixingSubgroup M s) (ofFixingSubgroup M s))
    {g : M} (ha : s ∪ g • s ≠ ⊤) :
    IsPreprimitive (fixingSubgroup M (s ∩ g • s)) (ofFixingSubgroup M (s ∩ g • s)) := by
  have := IsPretransitive.isPretransitive_ofFixingSubgroup_inter hs.toIsPretransitive ha
  apply IsPreprimitive.of_card_lt (f := ofFixingSubgroup_of_inclusion M Set.inter_subset_left)
  rw [show Nat.card (ofFixingSubgroup M (s ∩ g • s)) = (s ∩ g • s)ᶜ.ncard from
    Nat.card_coe_set_eq _, Set.ncard_range_of_injective ofFixingSubgroup_of_inclusion_injective,
    show Nat.card (ofFixingSubgroup M s) = sᶜ.ncard from Nat.card_coe_set_eq _, Set.compl_inter]
  refine (Set.ncard_union_lt sᶜ.toFinite (g • s)ᶜ.toFinite ?_).trans_le ?_
  · rwa [Set.disjoint_compl_right_iff_subset, Set.compl_subset_iff_union]
  · rw [← Set.smul_set_compl, Set.ncard_smul_set, two_mul]

end TwoCriteria

end SubMulAction

section Pointwise

open MulAction Set

variable (G : Type*) [Group G] {α : Type*} [MulAction G α]

@[to_additive]
theorem MulAction.fixingSubgroup_le_stabilizer (s : Set α) :
    fixingSubgroup G s ≤ stabilizer G s := by
  intro k hk
  rw [mem_stabilizer_iff]
  conv_rhs => rw [← Set.image_id s]
  apply Set.image_congr
  simpa only [mem_fixingSubgroup_iff, id] using hk

end Pointwise
