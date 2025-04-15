/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer
import Mathlib.GroupTheory.GroupAction.FixingSubgroup


/-!
# Sub_mul_actions on complements of invariant subsets

- We define sub_mul_action of an invariant subset in various contexts,
especially stabilizers and fixing subgroups : `sub_mul_action_of_compl`,
`sub_mul_action_of_stabilizer`, `sub_mul_action_of_fixing_subgroup`.

- We define equivariant maps that relate various of these sub_mul_actions
and permit to manipulate them in a relatively smooth way.
-/

open scoped Pointwise

open MulAction

namespace SubMulAction

variable (M : Type*) [Group M] {α : Type*} [MulAction M α]

/-- The SubMulAction of `fixingSubgroup M s` on the complement of `s` -/
def ofFixingSubgroup (s : Set α) : SubMulAction (fixingSubgroup M s) α where
  carrier := sᶜ
  smul_mem' := fun ⟨c, hc⟩ x ↦ by
    rw [← Subgroup.inv_mem_iff] at hc
    simp only [Set.mem_compl_iff, not_imp_not]
    intro hcx
    rwa [← one_smul M x, ← inv_mul_cancel c, mul_smul, (mem_fixingSubgroup_iff M).mp hc (c • x) hcx]

theorem ofFixingSubgroup_carrier {s : Set α} :
    (ofFixingSubgroup M s).carrier = sᶜ := rfl

theorem mem_ofFixingSubgroup_iff {s : Set α} {x : α} :
    x ∈ ofFixingSubgroup M s ↔ x ∉ s :=
  Iff.rfl

variable {M}

theorem not_mem_of_mem_ofFixingSubgroup {s : Set α}
  (x : ofFixingSubgroup M s) : ↑x ∉ s := x.prop

section Comparisons

variable (M α)

section Empty

/-- The identity map of the sub_mul_action of the fixing_subgroup
of the empty set into the ambient set, as an equivariant map -/
def ofFixingSubgroupEmpty_equivariantMap :
    ofFixingSubgroup M (∅ : Set α) →ₑ[(fixingSubgroup M (∅ : Set α)).subtype] α where
  toFun x := x
  map_smul' _ _ := rfl

theorem ofFixingSubgroupEmpty_equivariantMap_bijective :
    Function.Bijective (ofFixingSubgroupEmpty_equivariantMap M α) := by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp [Subtype.mk_eq_mk]; exact hxy
  · exact fun x ↦ ⟨⟨x, (mem_ofFixingSubgroup_iff M).mp (Set.not_mem_empty x)⟩, rfl⟩

theorem of_fixingSubgroupEmpty_mapScalars_surjective :
    Function.Surjective (fixingSubgroup M (∅ : Set α)).subtype := fun g ↦ by
  suffices g ∈ fixingSubgroup M (∅ : Set α) by
    exact ⟨⟨g, this⟩, rfl⟩
  simp [mem_fixingSubgroup_iff]

end Empty


section FixingSubgroupInsert

variable {α}

variable {M} in
theorem mem_fixingSubgroup_insert_iff {a : α} {s : Set α} {m : M} :
    m ∈ fixingSubgroup M (insert a s) ↔ m • a = a ∧ m ∈ fixingSubgroup M s := by
  simp [mem_fixingSubgroup_iff]

variable {M} in
theorem fixingSubgroup_of_insert (a : α) (s : Set (ofStabilizer M a)) :
    fixingSubgroup M (insert a ((fun x ↦ x.val) '' s)) =
      (fixingSubgroup (↥(stabilizer M a)) s).map (stabilizer M a).subtype := by
  ext m
  simp [mem_fixingSubgroup_iff, mem_ofStabilizer_iff, and_comm]

variable {M} in
theorem mem_ofFixingSubgroup_insert_iff {a : α} {s : Set (ofStabilizer M a)} {x : α} :
    x ∈ ofFixingSubgroup M (insert a ((fun x ↦ x.val) '' s)) ↔
      ∃ (hx : x ∈ ofStabilizer M a),
        (⟨x, hx⟩ : ofStabilizer M a) ∈ ofFixingSubgroup (stabilizer M a) s := by
  simp_rw [mem_ofFixingSubgroup_iff, mem_ofStabilizer_iff]
  aesop

/-- The natural group morphism between fixing subgroups -/
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
into the fixing subgroup of the extended set, as an equivariant map -/
def ofFixingSubgroup_insert_map (a : α) (s : Set (ofStabilizer M a)) :
    ofFixingSubgroup M (insert a (Subtype.val '' s))
      →ₑ[fixingSubgroupInsertEquiv M a s] (ofFixingSubgroup (stabilizer M a) s) where
  toFun x := by
    choose hx hx' using (mem_ofFixingSubgroup_insert_iff.mp x.prop)
    exact ⟨_, hx'⟩
  map_smul' _ _ := rfl

variable {M} in
@[simp]
theorem ofFixingSubgroup_insert_map_apply {a : α} {s : Set (ofStabilizer M a)}
    {x : α} (hx : x ∈ ofFixingSubgroup M (insert a (Subtype.val '' s))) :
    ↑((ofFixingSubgroup_insert_map M a s) ⟨x, hx⟩) = x :=
  rfl

theorem ofFixingSubgroup_insert_map_bijective
    (a : α) (s : Set (ofStabilizer M a)) :
    Function.Bijective (ofFixingSubgroup_insert_map M a s) := by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    simpa only [← Subtype.coe_inj, ofFixingSubgroup_insert_map_apply] using h
  · rintro ⟨⟨x, hx1⟩, hx2⟩
    exact ⟨⟨x, mem_ofFixingSubgroup_insert_iff.mpr ⟨hx1, hx2⟩⟩, rfl⟩

end FixingSubgroupInsert

section FixingSubgroupConj

variable {s t : Set α} {g : M}

theorem _root_.Set.conj_mem_fixingSubgroup (hg : g • t = s)
    {k : M} (hk : k ∈ fixingSubgroup M t) :
    MulAut.conj g k ∈ fixingSubgroup M s := by
  simp only [mem_fixingSubgroup_iff] at hk ⊢
  intro y hy
  rw [MulAut.conj_apply, eq_comm, mul_smul, mul_smul, ← inv_smul_eq_iff, eq_comm]
  apply hk
  rw [← Set.mem_smul_set_iff_inv_smul_mem, hg]
  exact hy

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
/-- If the fixing_subgroup of `s` is `G`, then the fixing_subgroup of `g • s` is `gGg⁻¹`. -/
theorem fixingSubgroup_smul_eq_fixingSubgroup_map_conj :
    fixingSubgroup M (g • s) = (fixingSubgroup M s).map (MulAut.conj g).toMonoidHom :=
  (fixingSubgroup_map_conj_eq _ _ rfl).symm

/-- The equivalence of `fixingSubgroup M t` with `fixingSubgroup M s`
  when `t` is a translate of `g` -/
def fixingSubgroupEquivFixingSubgroup (hg : g • t = s) :
    fixingSubgroup M t ≃* fixingSubgroup M s :=
  ((MulAut.conj g).subgroupMap (fixingSubgroup M t)).trans
    (MulEquiv.subgroupCongr (fixingSubgroup_map_conj_eq _ _ hg))

/-- Conjugation induces an equivariant map between the sub_mul_action of
the fixing subgroup of a subset and that of a translate -/
def conjMap_ofFixingSubgroup (hg : g • t = s) :
    ofFixingSubgroup M t →ₑ[fixingSubgroupEquivFixingSubgroup M α hg] ofFixingSubgroup M s where
  toFun := fun ⟨x, hx⟩ =>
    ⟨g • x, by
      intro hgxt; apply hx
      rw [← hg] at hgxt
      exact Set.smul_mem_smul_set_iff.mp hgxt⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => by
    rw [← SetLike.coe_eq_coe]
    change g • m • x = MulAut.conj g m • g • x
    simp only [MulAut.conj_apply, mul_smul, inv_smul_smul]

@[simp]
theorem conjMap_ofFixingSubgroup_apply {hg : g • t = s} (x : ofFixingSubgroup M t) :
    ↑(conjMap_ofFixingSubgroup _ _ hg x) = g • (x : α) := rfl

theorem conjMap_ofFixingSubgroup_bijective {s t : Set α} {g : M} (hst : g • s = t) :
    Function.Bijective (conjMap_ofFixingSubgroup M α hst) := by
  constructor
  · rintro  x y hxy
    simpa [← SetLike.coe_eq_coe] using hxy
  · rintro ⟨x, hx⟩
    rw [eq_comm, ← inv_smul_eq_iff] at hst
    use (SubMulAction.conjMap_ofFixingSubgroup _ _ hst) ⟨x, hx⟩
    simp [← SetLike.coe_eq_coe]

end FixingSubgroupConj

/-- The identity between the iterated sub_mul_action
  of the fixing_subgroups and the sub_mul_action of the fixing_subgroup
  of the union, as an equivariant map -/
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

theorem map_ofFixingSubgroupUnion_def (s t : Set α)
    (x : SubMulAction.ofFixingSubgroup M (s ∪ t)) :
    ((SubMulAction.map_ofFixingSubgroupUnion M _ s t) x : α) = x :=
  rfl

theorem map_ofFixingSubgroupUnion_bijective (s t : Set α) :
    Function.Bijective (map_ofFixingSubgroupUnion M _ s t) := by
  constructor
  · intro a b h
    simp only [← SetLike.coe_eq_coe] at h ⊢
    exact h
  · rintro ⟨⟨a, ha⟩, ha'⟩
    suffices a ∈ ofFixingSubgroup M (s ∪ t) by
      exact ⟨⟨a, this⟩,  rfl⟩
    intro hy
    rcases (Set.mem_union a s t).mp hy with h | h
    · exact ha h
    · apply ha'
      simp only [Set.mem_preimage]
      exact h

/-- The equivariant map on `SUbMulAction.ofFixingSubgroup` given a set inclusion -/
def ofFixingSubgroup_of_inclusion {s t : Set α} (hst : t ⊆ s) :
    ofFixingSubgroup M s
      →ₑ[Subgroup.inclusion (fixingSubgroup_antitone M α hst)]
        ofFixingSubgroup M t where
  toFun y := ⟨y.val, fun h => y.prop (hst h)⟩
  map_smul' _ _ := rfl

lemma ofFixingSubgroup_of_inclusion_injective {s t : Set α} (hst : t ⊆ s) :
    Function.Injective (ofFixingSubgroup_of_inclusion M _ hst) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  rw [← SetLike.coe_eq_coe] at hxy ⊢
  exact hxy

/-- The equivariant map between `SubMulAction.ofStabilizer M a`
and `ofFixingSubgroup M {a}` -/
def ofFixingSubgroup_of_singleton (a : α) :
    let φ : fixingSubgroup M ({a} : Set α) → stabilizer M a := fun ⟨m, hm⟩ =>
      ⟨m, ((mem_fixingSubgroup_iff M).mp hm) a (Set.mem_singleton a)⟩
    ofFixingSubgroup M ({a} : Set α) →ₑ[φ] ofStabilizer M a where
  toFun x := ⟨x, by simp⟩
  map_smul' _ _ := rfl

theorem ofFixingSubgroup_of_singleton_bijective (a : α) :
    Function.Bijective (ofFixingSubgroup_of_singleton M _ a) :=
  ⟨fun _ _ ↦ id, fun x ↦ ⟨x, rfl⟩⟩

/-- The identity between the `SubMulAction`s of `fixingSubgroup`s
of equal sets, as an equivariant map -/
def ofFixingSubgroup_of_eq {s t : Set α} (hst : s = t) :
    let φ : fixingSubgroup M s ≃* fixingSubgroup M t :=
      MulEquiv.subgroupCongr (congrArg₂ _ rfl hst)
    ofFixingSubgroup M s →ₑ[φ] ofFixingSubgroup M t where
  toFun := fun ⟨x, hx⟩ => ⟨x, by rw [← hst]; exact hx⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => rfl

@[simp]
theorem ofFixingSubgroup_of_eq_apply {s t : Set α} (hst : s = t)
    (x : ofFixingSubgroup M s) :
    ((ofFixingSubgroup_of_eq M _ hst x) : α) = x := rfl

theorem ofFixingSubgroup_of_eq_bijective {s t : Set α} (hst : s = t) :
    Function.Bijective (ofFixingSubgroup_of_eq M _ hst) :=
  ⟨fun _ _ hxy ↦ by simpa [← SetLike.coe_eq_coe] using hxy,
    fun ⟨x, hxt⟩ ↦ ⟨⟨x, by rwa [hst]⟩, by simp [← SetLike.coe_eq_coe]⟩⟩

end Comparisons

section Transitivity

open Function.Embedding Fin.Embedding

/-- Append `Fin m ↪ ofFixingSubgroup M s` at the end of an enumeration of `s` -/
noncomputable def ofFixingSubgroup.merge
    {m n : ℕ} {s : Set α} [Finite s] (hmn : s.ncard + m = n)
    (x : Fin m ↪ ofFixingSubgroup M s) : Fin n ↪ α :=
  Fin.Embedding.merge hmn
    ((Finite.equivFinOfCardEq rfl).symm.toEmbedding.trans (subtype s.Mem))
    (x.trans (subtype _)) (by
      rw [Set.disjoint_iff_forall_ne]
      rintro a hs b hx h
      simp only [Set.mem_range, trans_apply, Equiv.coe_toEmbedding,
        Function.Embedding.subtype_apply] at hs hx
      obtain ⟨i, rfl⟩ := hs
      obtain ⟨j, rfl⟩ := hx
      apply (x j).prop
      rw [← h]
      exact Subtype.coe_prop ((Finite.equivFinOfCardEq rfl).symm i))

theorem ofFixingSubgroup.merge_apply₁
    {m n : ℕ} {s : Set α} [Finite s] (hmn : s.ncard + m = n)
    (x : Fin m ↪ ofFixingSubgroup M s) (i : Fin n) (hi : i.val < s.ncard) :
    ofFixingSubgroup.merge hmn x i = (Finite.equivFinOfCardEq rfl).symm ⟨i.val, hi⟩ := by
  simp [merge, Fin.Embedding.merge_apply, trans_apply, Equiv.coe_toEmbedding,
    Function.Embedding.subtype_apply, dif_pos hi]
  rfl

theorem ofFixingSubgroup.merge_apply₂
    {m n : ℕ} {s : Set α} [Finite s] (hmn : s.ncard + m = n)
    (x : Fin m ↪ ofFixingSubgroup M s) (i : Fin n) (hi : s.ncard ≤ i.val ) :
    ofFixingSubgroup.merge hmn x i = x ⟨i.val - s.ncard,
      Nat.sub_lt_left_of_lt_add hi (by simp [hmn, i.prop])⟩ := by
  rw [← not_lt] at hi
  simp only [merge, Fin.Embedding.merge_apply, trans_apply, Equiv.coe_toEmbedding,
    Function.Embedding.subtype_apply, dif_neg hi]

/-
noncomputable def ofFixingSubgroup.merge'
    {m n : ℕ} {s : Set α} [Finite s] (hmn : m + s.ncard = n)
    (x : Fin m ↪ ofFixingSubgroup M s) : Fin n ↪ α :=
  Fin.Embedding.merge hmn
    (x.trans (subtype _))
    ((Finite.equivFinOfCardEq rfl).symm.toEmbedding.trans (subtype s.Mem))
    (by
      rw [Set.disjoint_iff_forall_ne]
      rintro a hs b hx h
      simp only [Set.mem_range, trans_apply, Equiv.coe_toEmbedding,
        Function.Embedding.subtype_apply] at hs hx
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, rfl⟩ := hs
      apply (x j).prop
      rw [h]
      exact Subtype.coe_prop ((Finite.equivFinOfCardEq rfl).symm i))

theorem ofFixingSubgroup.merge'_apply₁
    {m n : ℕ} {s : Set α} [Finite s] (hmn : m + s.ncard = n)
    (x : Fin m ↪ ofFixingSubgroup M s) (i : Fin n) (hi : i.val < m) :
    ofFixingSubgroup.merge' hmn x i = x ⟨i.val, hi⟩ := by
  simp only [merge', Fin.Embedding.merge_apply, trans_apply,
    Function.Embedding.subtype_apply, Equiv.coe_toEmbedding, dif_pos hi]

theorem ofFixingSubgroup.merge'_apply₂
    {m n : ℕ} {s : Set α} [Finite s] (hmn : m + s.ncard = n)
    (x : Fin m ↪ ofFixingSubgroup M s) (i : Fin n) (hi : m ≤ i.val) :
    ofFixingSubgroup.merge' hmn x i =
      (Finite.equivFinOfCardEq (α := s) rfl).symm ⟨i.val - m,
        by simp [Nat.sub_lt_iff_lt_add hi, Set.Nat.card_coe_set_eq, hmn]⟩ := by
  rw [← not_lt] at hi
  simp only [merge', Fin.Embedding.merge_apply, trans_apply,
    Function.Embedding.subtype_apply, Equiv.coe_toEmbedding, dif_neg hi]
  congr
-/

/-- The fixator of a subset of cardinal d in a k-transitive action
acts (k-d) transitively on the remaining -/
theorem ofFixingSubgroup.isMultiplyPretransitive {m n : ℕ} [IsMultiplyPretransitive M α n]
    (s : Set α) [Finite s] (hmn : s.ncard + m = n) :
    IsMultiplyPretransitive (fixingSubgroup M s) (ofFixingSubgroup M s) m where
  exists_smul_eq x y := by
    set x' := ofFixingSubgroup.merge hmn x with hx'
    set y' := ofFixingSubgroup.merge hmn y with hy'
    obtain ⟨g, hg⟩ := exists_smul_eq M x' y'
    suffices g ∈ fixingSubgroup M s by
      use ⟨g, this⟩
      ext i
      have hi : s.ncard + i < n := by
        rw [← hmn]
        exact Nat.add_lt_add_left i.prop s.ncard
      simp only [smul_apply, SetLike.val_smul, Subgroup.mk_smul]
      rw [DFunLike.ext_iff] at hg
      specialize hg ⟨_, hi⟩
      simp only [smul_apply] at hg
      simpa [smul_apply, hx', hy',
        ofFixingSubgroup.merge_apply₂ hmn _ ⟨_, hi⟩ (Nat.le_add_right s.ncard ↑i)] using hg
    simp [DFunLike.ext_iff, smul_apply, hx', hy'] at hg
    intro a
    set i := (Finite.equivFinOfCardEq rfl) a
    have hi : i.val < n := lt_of_lt_of_le i.prop (by simp [← hmn, Set.Nat.card_coe_set_eq])
    specialize hg ⟨i.val, hi⟩
    simpa [ofFixingSubgroup.merge_apply₁ hmn _ ⟨i.val, hi⟩ (by
        simpa [Set.Nat.card_coe_set_eq] using i.prop),
      Fin.eta, i] using hg

/-- The fixator of a subset of cardinal d in a k-transitive action
acts (k-d) transitively on the remaining -/
theorem ofFixingSubgroup.isMultiplyPretransitive' {m n : ℕ} [IsMultiplyPretransitive M α n]
    (s : Set α) [Finite s] (hmn : s.ncard + m ≤ n) (hn : (n : ENat) ≤ ENat.card α) :
    IsMultiplyPretransitive (fixingSubgroup M s) (SubMulAction.ofFixingSubgroup M s) m :=
  letI : IsMultiplyPretransitive M α (s.ncard + m) := isMultiplyPretransitive_of_le' hmn hn
  isMultiplyPretransitive s rfl

end Transitivity

end SubMulAction


