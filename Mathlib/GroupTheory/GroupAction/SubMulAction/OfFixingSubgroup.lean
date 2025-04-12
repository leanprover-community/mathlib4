/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer


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

theorem mem_fixingSubgroup_insert_iff {a : α} {s : Set α} {m : M} :
    m ∈ fixingSubgroup M (insert a s) ↔ m • a = a ∧ m ∈ fixingSubgroup M s := by
  simp [mem_fixingSubgroup_iff]

theorem fixingSubgroup_of_insert (a : α) (s : Set (ofStabilizer M a)) :
    fixingSubgroup M (insert a ((fun x ↦ x.val) '' s)) =
      (fixingSubgroup (↥(stabilizer M a)) s).map (stabilizer M a).subtype := by
  ext m
  simp only [Subgroup.mem_map, mem_fixingSubgroup_iff]
  constructor
  · intro hm
    use ⟨m, mem_stabilizer_iff.mpr (hm _ (Set.mem_insert a _))⟩
    simp only [Subgroup.coe_subtype, and_true, mem_fixingSubgroup_iff]
    rintro ⟨y, hy⟩ hy'
    simp only [SetLike.mk_smul_mk, Subtype.mk.injEq]
    exact hm y (Set.mem_insert_of_mem a ⟨⟨y, hy⟩, ⟨hy', rfl⟩⟩)
  · rintro ⟨⟨n, hn'⟩, hn, rfl⟩
    simp only [Subgroup.coe_subtype, SetLike.mem_coe, mem_fixingSubgroup_iff] at hn ⊢
    intro x hx
    rw [Set.mem_insert_iff] at hx
    rcases hx with hx | hx
    · simpa [hx] using hn'
    · simp only [Set.mem_image] at hx
      rcases hx with ⟨y, hy, rfl⟩
      conv_rhs => rw [← hn y hy, SubMulAction.val_smul, subgroup_smul_def]

variable (M α) in
/-- The identity map of the sub_mul_action of the fixing_subgroup
of the empty set into the ambient set, as an equivariant map -/
def ofFixingSubgroupEmpty_equivariantMap :
    ofFixingSubgroup M (∅ : Set α) →ₑ[(fixingSubgroup M (∅ : Set α)).subtype] α where
  toFun x := x
  map_smul' _ _ := rfl

variable (α) in
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

section FixingSubgroupInsert

/-- The natural group morphism between fixing subgroups -/
def fixingSubgroupMap_insert (a : α) (s : Set (ofStabilizer M a)) :
    fixingSubgroup M (insert a (Subtype.val '' s)) →* fixingSubgroup (stabilizer M a) s where
  toFun m := ⟨⟨(m : M), (mem_fixingSubgroup_iff M).mp m.prop a (Set.mem_insert _ _)⟩,
      fun ⟨x, hx⟩ => by
        simp only [← SetLike.coe_eq_coe]
        refine (mem_fixingSubgroup_iff M).mp m.prop _ (Set.mem_insert_of_mem a ?_)
        exact ⟨⟨x, (SubMulAction.mem_ofStabilizer_iff  M a).mp x.prop⟩, hx, rfl⟩⟩
  map_one' := by simp
  map_mul' _ _ := by simp [← Subtype.coe_inj]

theorem fixingSubgroupMap_insert_bijective (a : α) (s : Set (ofStabilizer M a)) :
    Function.Bijective (fixingSubgroupMap_insert a s) := by
  constructor
  · rintro _ _ hmn
    simpa [← SetLike.coe_eq_coe] using hmn
  · rintro ⟨⟨m, hm⟩, hm'⟩
    refine ⟨⟨m, ?_⟩, rfl⟩
    rw [mem_fixingSubgroup_iff]
    intro x hx
    rcases Set.mem_insert_iff.mp hx with ⟨rfl⟩ | ⟨y, hy, rfl⟩
    · exact mem_stabilizer_iff.mp hm
    · rw [mem_fixingSubgroup_iff] at hm'
      simpa [← SetLike.coe_eq_coe] using hm' y hy

/-- The identity map of fixing subgroup of stabilizer
into the fixing subgroup of the extended set, as an equivariant map -/
def equivariantMap_ofFixingSubgroup_to_ofStabilizer (a : α) (s : Set (ofStabilizer M a)) :
    ofFixingSubgroup M (insert a (Subtype.val '' s))
      →ₑ[fixingSubgroupMap_insert a s] (ofFixingSubgroup (stabilizer M a) s) where
  toFun x := ⟨⟨x, fun h ↦ (mem_ofFixingSubgroup_iff M).mp x.prop (by
      rw [h]
      apply Set.mem_insert)⟩,
    fun h ↦ (mem_ofFixingSubgroup_iff M).mp x.prop <|
      Set.mem_insert_of_mem _ ⟨⟨(x : α), _⟩, ⟨h, rfl⟩⟩⟩
  map_smul' _ _ := rfl

@[simp]
theorem equivariantMap_ofFixingSubgroup_to_ofStabilizer_coe {a : α} {s : Set (ofStabilizer M a)}
    {x : α} (hx : x ∈ ofFixingSubgroup M (insert a (Subtype.val '' s))) :
    ↑((equivariantMap_ofFixingSubgroup_to_ofStabilizer a s) ⟨x, hx⟩) = x :=
  rfl

theorem equivariantMap_ofFixingSubgroup_to_ofStabilizer_bijective
    (a : α) (s : Set (ofStabilizer M a)) :
    Function.Bijective (equivariantMap_ofFixingSubgroup_to_ofStabilizer a s) := by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    simp only [Subtype.mk_eq_mk]
    rw [← equivariantMap_ofFixingSubgroup_to_ofStabilizer_coe hx,
      ← equivariantMap_ofFixingSubgroup_to_ofStabilizer_coe hy, h]
  · rintro ⟨⟨x, hx1⟩, hx2⟩
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [mem_ofFixingSubgroup_iff]
    intro h
    rcases Set.mem_insert_iff.mp h with  h' | h'
    · exact (mem_ofStabilizer_iff _ _).mp hx1 h'
    · obtain ⟨x1, hx1', rfl⟩ := h'
      exact (mem_ofFixingSubgroup_iff _).mp hx2 hx1'

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
    exact Set.conj_mem_fixingSubgroup hg hn
  · intro hk
    use MulAut.conj g⁻¹ k
    constructor
    · apply Set.conj_mem_fixingSubgroup _ hk
      ext; simp [← hg]
    · simp [MulAut.conj]; group

variable (g s) in
/-- If the fixing_subgroup of `s` is `G`, then the fixing_subgroup of `g • s` is `gGg⁻¹`. -/
theorem fixingSubgroup_smul_eq_fixingSubgroup_map_conj :
    fixingSubgroup M (g • s) = (fixingSubgroup M s).map (MulAut.conj g).toMonoidHom :=
  (fixingSubgroup_map_conj_eq rfl).symm

def fixingSubgroupEquivFixingSubgroup (hg : g • t = s) :
    fixingSubgroup M t ≃* fixingSubgroup M s :=
  ((MulAut.conj g).subgroupMap (fixingSubgroup M t)).trans
    (MulEquiv.subgroupCongr (fixingSubgroup_map_conj_eq hg))

/-- Conjugation induces an equivariant map between the sub_mul_action of
the fixing subgroup of a subset and that of a translate -/
def conjMap_ofFixingSubgroup (hg : g • t = s) :
    ofFixingSubgroup M t →ₑ[fixingSubgroupEquivFixingSubgroup hg] ofFixingSubgroup M s where
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
    ↑(conjMap_ofFixingSubgroup hg x) = g • (x : α) := rfl

theorem conjMap_ofFixingSubgroup_bijective {s t : Set α} {g : M} (hst : g • s = t) :
    Function.Bijective (conjMap_ofFixingSubgroup hst) := by
  constructor
  · rintro  _ _ hxy
    simpa [← SetLike.coe_eq_coe] using hxy
  · rintro ⟨x, hx⟩
    rw [eq_comm, ← inv_smul_eq_iff] at hst
    use (SubMulAction.conjMap_ofFixingSubgroup hst) ⟨x, hx⟩
    simp [← SetLike.coe_eq_coe]

end FixingSubgroupConj

variable (M) in
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
    ((SubMulAction.map_ofFixingSubgroupUnion M s t) x : α) = x :=
  rfl

theorem map_ofFixingSubgroupUnion_bijective (s t : Set α) :
    Function.Bijective (map_ofFixingSubgroupUnion M s t) := by
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

variable (M) in
/-- The equivariant map on sub_mul_action.of_fixing_subgroup given a set inclusion -/
def ofFixingSubgroup_of_inclusion {s t : Set α} (hst : t ⊆ s) :
    ofFixingSubgroup M s
      →ₑ[Subgroup.inclusion (fixingSubgroup_antitone M α hst)]
        ofFixingSubgroup M t where
  toFun y := ⟨y.val, fun h => y.prop (hst h)⟩
  map_smul' _ _ := rfl

lemma ofFixingSubgroup_of_inclusion_injective {s t : Set α} (hst : t ⊆ s) :
    Function.Injective (ofFixingSubgroup_of_inclusion M hst) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  rw [← SetLike.coe_eq_coe] at hxy ⊢
  exact hxy

variable (M) in
/-- The equivariant map between sub_mul_action.of_stabilizer
  and .of_fixing_subgroup of the singleton -/
def ofFixingSubgroup_of_singleton (a : α) :
    let φ : fixingSubgroup M ({a} : Set α) → stabilizer M a := fun ⟨m, hm⟩ =>
      ⟨m, ((mem_fixingSubgroup_iff M).mp hm) a (Set.mem_singleton a)⟩
    ofFixingSubgroup M ({a} : Set α) →ₑ[φ] ofStabilizer M a where
  toFun x := ⟨x, by simp⟩
  map_smul' _ _ := rfl

theorem ofFixingSubgroup_of_singleton_bijective (a : α) :
    Function.Bijective (ofFixingSubgroup_of_singleton M a) :=
  ⟨fun _ _ ↦ id, fun x ↦ ⟨x, rfl⟩⟩

variable (M) in
/-- The identity between the sub_mul_action of fixing_subgroups
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
    ((ofFixingSubgroup_of_eq M hst x) : α) = x := rfl

theorem ofFixingSubgroup_of_eq_bijective {s t : Set α} (hst : s = t) :
    Function.Bijective (ofFixingSubgroup_of_eq M hst) :=
  ⟨fun _ _ hxy ↦ by simpa [← SetLike.coe_eq_coe] using hxy,
    fun ⟨x, hxt⟩ ↦ ⟨⟨x, by rwa [hst]⟩, by simp [← SetLike.coe_eq_coe]⟩⟩

end SubMulAction


