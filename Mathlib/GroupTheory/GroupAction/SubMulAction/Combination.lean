/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.MaximalSubgroups

/-! # Combinations

Combinations in a type are finite subsets of given cardinality.
This file provides some API for handling them, especially in the context of a group action.

* `Set.powersetCard α n` is the set of all `Finset α` with cardinality `n`.
  The name is chosen in relation with `Finset.powersetCard` which corresponds to
  the analogous structure for subsets of given cardinality of a given `Finset`, as a `Finset`.

* `Set.powersetCard.card` proves that the `Nat.card`-cardinality
  of this set is equal to `(Nat.card α).choose n`.

* `Set.powersetCard.subMulAction`:
  When a group `G` acts on `α`, the `SubMulAction` of `G` on `powersetCard α n`.

This induces a `MulAction G (powersetCard α n)` instance. Then:

* `Set.powerSetCard.mulActionHom_of_embedding`:
  the equivariant map from `Fin n ↪ α` to `powersetCard α n`.

* `Set.powersetCard.isPretransitive_of_isMultiplyPretransitive`
  shows the pretransitivity of that action if the action of `G` on `α` is `n`-pretransitive.

* `Set.powersetCard.isPretransitive` shows that `Equiv.Perm α`
  acts pretransitively on `powersetCard α n`, for all `n`.

* `Set.powersetCard.compl`: Given an equality `m + n = Fintype.card α`,
  the complement of an `n`-combination, as an `m`-combination.
  This map is an equivariant map with respect to a group action on `α`.

* `Set.powersetCard.mulActionHom_singleton`:
  The obvious map from `α` to `powersetCard α 1`, as an equivariant map.

-/

@[expose] public section

variable (G : Type*) [Group G] (α : Type*) [MulAction G α]

/-- The type of combinations of `n` elements of a type `α`.

See also `Finset.powersetCard`. -/
def Set.powersetCard (n : ℕ) := {s : Finset α | s.card = n}

variable {α} {n : ℕ} {s t : Set.powersetCard α n}

namespace Set.powersetCard

open scoped Pointwise

open MulAction Finset Set Equiv Equiv.Perm

@[simp]
theorem mem_iff {s : Finset α} :
    s ∈ powersetCard α n ↔ s.card = n := by
  rw [powersetCard, Set.mem_setOf_eq]

instance : SetLike (powersetCard α n) α := SetLike.instSubtype

instance : PartialOrder (Set.powersetCard α n) := .ofSetLike (Set.powersetCard α n) α

@[simp]
theorem coe_coe {s : powersetCard α n} :
    ((s : Finset α) : Set α) = s := rfl

theorem mem_coe_iff {s : Set.powersetCard α n} {a : α} : a ∈ (s : Finset α) ↔ a ∈ s := .rfl

theorem card_eq (s : Set.powersetCard α n) : (s : Finset α).card = n :=
  s.prop

theorem ncard_eq (s : Set.powersetCard α n) : (s : Set α).ncard = n := by
  rw [← coe_coe, Set.ncard_coe_finset, s.prop]

theorem coe_nonempty_iff {s : Set.powersetCard α n} :
    (s : Set α).Nonempty ↔ 1 ≤ n := by
  rw [← Set.powersetCard.coe_coe, Finset.coe_nonempty, ← one_le_card, s.prop]

theorem coe_nontrivial_iff {s : Set.powersetCard α n} :
    (s : Set α).Nontrivial ↔ 1 < n := by
  rw [← coe_coe, Finset.nontrivial_coe, ← one_lt_card_iff_nontrivial, card_eq]

theorem eq_iff_subset : s = t ↔ (s : Finset α) ⊆ (t : Finset α) := by
  rw [Finset.subset_iff_eq_of_card_le (t.prop.trans_le s.prop.ge), Subtype.ext_iff]

theorem exists_mem_notMem (hn : 1 ≤ n) (hα : n < ENat.card α) {a b : α} (hab : a ≠ b) :
    ∃ s : powersetCard α n, a ∈ s ∧ b ∉ s := by
  have ha' : n ≤ Set.encard {b}ᶜ := by
    rwa [← (Set.encard_add_encard_compl {b}).trans (Set.encard_univ α), Set.encard_singleton,
      add_comm, ENat.lt_add_one_iff' (ENat.coe_ne_top n)] at hα
  obtain ⟨s, has, has', hs⟩ :=
    Set.exists_superset_subset_encard_eq (s := {a}) (by simp [Ne.symm hab]) (by simpa) ha'
  have : Set.Finite s := Set.finite_of_encard_eq_coe hs
  exact ⟨⟨Set.Finite.toFinset this, by
    rwa [mem_iff, ← ENat.coe_inj, ← this.encard_eq_coe_toFinset_card]⟩,
      by simpa using has, by simpa using has'⟩

section

variable [DecidableEq α]

variable (α n) in
/-- `Set.powersetCard α n` as a `SubMulAction` of `Finset α`. -/
@[to_additive /--`Set.powersetCard α n` as a `SubAddAction` of `Finsetα`.-/]
def subMulAction : SubMulAction G (Finset α) where
  carrier := Set.powersetCard α n
  smul_mem' g s := (Finset.card_smul_finset g s).trans

@[to_additive]
instance : MulAction G (Set.powersetCard α n) :=
  (subMulAction G α n).mulAction

variable {G}

@[to_additive (attr := simp)]
theorem coe_smul {n : ℕ} {g : G} {s : powersetCard α n} :
    ((g • s : powersetCard α n) : Finset α) = g • s :=
  SubMulAction.val_smul (p := subMulAction G α n) g s

@[to_additive addAction_stabilizer_coe]
theorem stabilizer_coe {n : ℕ} (s : powersetCard α n) :
    stabilizer G s = stabilizer G (s : Set α) := by
  ext g
  simp [mem_stabilizer_iff, ← Subtype.coe_inj, ← Finset.coe_inj]

theorem addAction_faithful {G : Type*} [AddGroup G] [AddAction G α] {n : ℕ}
    (hn : 1 ≤ n) (hα : n < ENat.card α) {g : G} :
    AddAction.toPerm g = (1 : Perm (powersetCard α n)) ↔ AddAction.toPerm g = (1 : Perm α) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · contrapose h with h
    have : ∃ a, (g +ᵥ a : α) ≠ a := by simpa [Equiv.ext_iff] using h
    obtain ⟨a, ha⟩ := this
    obtain ⟨s, has, has'⟩ := exists_mem_notMem hn hα (Ne.symm ha)
    rw [Equiv.ext_iff, not_forall]
    use s
    contrapose! has'
    simp only [AddAction.toPerm_apply, coe_one, id_eq] at has'
    rw [← has']
    simpa [← mem_coe_iff]
  · simp only [Equiv.ext_iff, AddAction.toPerm_apply] at h ⊢
    simp [Subtype.ext_iff, Finset.ext_iff, mem_vadd_finset, h]

/-- If an additive group `G` acts faithfully on `α`,
then it acts faithfully on `powersetCard α n`,
provided `1 ≤ n < ENat.card α`. -/
theorem faithfulVAdd {G : Type*} [AddGroup G] [AddAction G α] {n : ℕ}
    (hn : 1 ≤ n) (hα : n < ENat.card α) [FaithfulVAdd G α] :
    FaithfulVAdd G (powersetCard α n) := by
  rw [faithfulVAdd_iff]
  intro g hg
  apply AddAction.toPerm_injective (α := G) (β := α)
  rw [AddAction.toPerm_zero, ← addAction_faithful hn hα]
  exact Perm.ext_iff.mpr hg

theorem mulAction_faithful (hn : 1 ≤ n) (hα : n < ENat.card α) {g : G} :
    MulAction.toPerm g = (1 : Perm (powersetCard α n)) ↔ MulAction.toPerm g = (1 : Perm α) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · contrapose h with h
    have : ∃ a, (g • a : α) ≠ a := by simpa [Equiv.ext_iff] using h
    obtain ⟨a, ha⟩ := this
    obtain ⟨s, has, has'⟩ := exists_mem_notMem hn hα (Ne.symm ha)
    rw [Equiv.ext_iff, not_forall]
    use s
    contrapose! has'
    simp only [MulAction.toPerm_apply, coe_one, id_eq] at has'
    rw [← has']
    simpa only [coe_smul, smul_mem_smul_finset_iff, ← mem_coe_iff]
  · simp only [Equiv.ext_iff, MulAction.toPerm_apply] at h ⊢
    simp [Subtype.ext_iff, Finset.ext_iff, mem_smul_finset, h]

/-- If a group `G` acts faithfully on `α`, then
it acts faithfull on `powersetCard α n` provided `1 ≤ n < ENat.card α`. -/
theorem faithfulSMul (hn : 1 ≤ n) (hα : n < ENat.card α) [FaithfulSMul G α] :
    FaithfulSMul G (powersetCard α n) := by
  rw [faithfulSMul_iff]
  intro g hg
  apply MulAction.toPerm_injective (α := G) (β := α)
  rw [MulAction.toPerm_one, ← mulAction_faithful hn hα]
  exact Perm.ext_iff.mpr hg

attribute [to_additive existing] faithfulSMul

variable (α G)

variable (n) in
/-- The equivariant map from embeddings of `Fin n` (aka arrangement) to combinations. -/
@[to_additive /-- The equivariant map from embeddings of `Fin n`
  (aka arrangements) to combinations. -/]
def mulActionHom_of_embedding : (Fin n ↪ α) →[G] powersetCard α n where
  toFun f := ⟨Finset.univ.map f, by rw [mem_iff, Finset.card_map, Finset.card_fin]⟩
  map_smul' g f := by
    rw [← Subtype.coe_inj, Subtype.coe_mk, coe_smul,
      f.smul_def, Finset.smul_finset_def,
      ← Finset.map_map, Finset.map_eq_image]
    simp [toPerm]

@[to_additive]
theorem coe_mulActionHom_of_embedding (f : Fin n ↪ α) :
    ↑((mulActionHom_of_embedding G α n).toFun f) = Finset.univ.map f :=
  rfl

@[to_additive]
theorem mulActionHom_of_embedding_surjective :
    Function.Surjective (mulActionHom_of_embedding G α n) := by
  intro ⟨s, hs⟩
  obtain ⟨f : Fin n ↪ α, hf⟩ :=
    Function.Embedding.exists_of_card_eq_finset (by rw [hs, Fintype.card_fin])
  exact ⟨f, Subtype.ext hf⟩

end

variable (α n)

theorem coe_finset [Fintype α] :
    powersetCard α n = Finset.powersetCard n (Finset.univ : Finset α) := by
  ext; simp

instance [Finite α] : Finite (powersetCard α n) := by
  have : Fintype α := Fintype.ofFinite α
  simpa [coe_finset] using Subtype.finite

protected theorem card :
    Nat.card (powersetCard α n) = (Nat.card α).choose n := by
  classical
  cases fintypeOrInfinite α
  · simp [coe_finset]
  · rcases n with _ | n
    · simp [powersetCard]
    · rcases finite_or_infinite (powersetCard α (n + 1)) with hc | hc
      · refine (Infinite.false (α := (powersetCard α (n + 1) → powersetCard α (n + 1))) ?_).elim
        have : FaithfulSMul (Perm α) (powersetCard α (n + 1)) :=
          faithfulSMul (Nat.le_add_left 1 n) (by simp)
        exact (Infinite.false (α := (powersetCard α (n + 1) → powersetCard α (n + 1)))
          (Infinite.of_injective _ (smul_left_injective' (M := Perm α)))).elim
      · simp

variable {α n}

/-- If `0 < n < ENat.card α`, then `powersetCard α n` is nontrivial. -/
theorem nontrivial (h1 : 0 < n) (h2 : n < ENat.card α) :
    Nontrivial (powersetCard α n) := by
  classical
  have h : Nontrivial α :=
    (ENat.one_lt_card_iff_nontrivial α).mp (lt_of_le_of_lt (Nat.one_le_cast.mpr h1) h2)
  have : FaithfulSMul (Perm α) (powersetCard α n) := faithfulSMul h1 h2
  have h := (smul_left_injective' (M := Perm α) (α := powersetCard α n)).nontrivial
  contrapose! h
  infer_instance

/-- A variant of `Set.powersetCard.nontrivial` that uses `Nat.card`. -/
theorem nontrivial' (h1 : 0 < n) (h2 : n < Nat.card α) :
    Nontrivial (powersetCard α n) := by
  have : Finite α := Nat.finite_of_card_ne_zero (ne_zero_of_lt h2)
  apply nontrivial h1
  simp [ENat.card_eq_coe_natCard α, h2]

theorem eq_empty_iff [Finite α] :
    powersetCard α n = ∅ ↔ Nat.card α < n := by
  rw [← Set.ncard_eq_zero, ← _root_.Nat.card_coe_set_eq, powersetCard.card, Nat.choose_eq_zero_iff]

theorem nontrivial_iff [Finite α] :
    Nontrivial (powersetCard α n) ↔ 0 < n ∧ n < Nat.card α := by
  rw [← Finite.one_lt_card_iff_nontrivial, powersetCard.card, Nat.one_lt_iff_ne_zero_and_ne_one,
    ne_eq, Nat.choose_eq_zero_iff, ne_eq, Nat.choose_eq_one_iff]
  grind

variable (α) in
theorem infinite (h : 0 < n) [Infinite α] : Infinite (powersetCard α n) := by
  apply Or.resolve_left
  · rwa [← Nat.card_eq_zero, powersetCard.card,
      Nat.card_eq_zero_of_infinite, Nat.choose_eq_zero_iff]
  · suffices Nontrivial (powersetCard α n) by
      exact not_isEmpty_of_nonempty ↑(powersetCard α n)
    apply nontrivial h
    simp

variable [DecidableEq α]

@[to_additive isPretransitive_of_isMultiplyPretransitive']
theorem isPretransitive_of_isMultiplyPretransitive (h : IsMultiplyPretransitive G α n) :
    IsPretransitive G (powersetCard α n) :=
  IsPretransitive.of_surjective_map (mulActionHom_of_embedding_surjective G α) h

theorem isPretransitive : IsPretransitive (Perm α) (powersetCard α n) :=
  isPretransitive_of_isMultiplyPretransitive _ (isMultiplyPretransitive α n)

section

variable (α)

variable [Fintype α] {m : ℕ} (hm : m + n = Fintype.card α)
include hm

/-- The complement of a combination, as an equivariant map. -/
def compl : powersetCard α n →[G] powersetCard α m where
  toFun s := ⟨(sᶜ : Finset α), by
      rw [mem_iff, Finset.card_compl]
      have := mem_iff.mp s.2
      omega⟩
  map_smul' g s := by ext; simp [← Finset.inv_smul_mem_iff]

variable {hm} in
theorem coe_compl {s : powersetCard α n} :
    (compl G α hm s : Finset α) = (s : Finset α)ᶜ :=
  rfl

variable {hm} in
theorem mem_compl {s : powersetCard α n} {a : α} :
    a ∈ compl G α hm s ↔ a ∉ s :=
  Finset.mem_compl

theorem compl_compl :
    (compl G α <| (n.add_comm m).trans hm).comp (compl G α hm) = .id G := by
  ext s a
  change a ∈ (compl G α _).comp (compl G α hm) s ↔ a ∈ s
  simp [MulActionHom.comp_apply, mem_compl]

theorem compl_bijective :
    Function.Bijective (compl G α hm) :=
  Function.bijective_iff_has_inverse.mpr ⟨compl G α ((n.add_comm m).trans hm),
    DFunLike.ext_iff.mp (compl_compl G α hm), DFunLike.ext_iff.mp (compl_compl G α _)⟩

end

variable (α)

/-- The obvious map from a type to its 1-combinations, as an equivariant map. -/
@[to_additive /-- The obvious map from a type to its 1-combinations, as an equivariant map. -/]
def mulActionHom_singleton : α →[G] powersetCard α 1 where
  toFun x := ⟨{x}, Finset.card_singleton x⟩
  map_smul' _ _ := rfl

@[to_additive]
theorem mulActionHom_singleton_bijective :
    Function.Bijective (mulActionHom_singleton G α) := by
  refine ⟨fun a b h ↦ Finset.singleton_injective congr($h.1), fun ⟨s, hs⟩ ↦ ?_⟩
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs
  exact ⟨a, rfl⟩

variable {α}

/-- The action of `Equiv.Perm α` on `Set.powersetCard α n` is preprimitive
provided `1 ≤ n < Nat.card α` and `Nat.card α ≠ 2 * n`.

This is a consequence that the stabilizer of such a combination
is a maximal subgroup. -/
theorem isPreprimitive_perm {n : ℕ} (h_one_le : 1 ≤ n) (hn : n < Nat.card α)
    (hα : Nat.card α ≠ 2 * n) :
    IsPreprimitive (Perm α) (powersetCard α n) := by
  -- The finiteness of `α` follows from the assumptions of the theorem.
  have : Finite α := Nat.finite_of_card_ne_zero (Nat.ne_zero_of_lt hn)
  have : Fintype α := Fintype.ofFinite α
  -- The action is pretransitive.
  have : IsPretransitive (Perm α) (powersetCard α n) := powersetCard.isPretransitive
  -- The type on which the group acts is nontrivial.
  have : Nontrivial (powersetCard α n) := powersetCard.nontrivial' h_one_le hn
  obtain ⟨s⟩ := this.to_nonempty
  -- It remains to prove that stabilizer of some point is maximal.
  rw [← isCoatom_stabilizer_iff_preprimitive _ s]
  -- The stabilizer of a combination is the stabilizer of the underlying set.
  rw [stabilizer_coe]
  -- We conclude by `Equiv.Perm.isCoatom_stabilizer`
  apply isCoatom_stabilizer
  -- `s` is nonempty because `n ≠ 0`.
  · rwa [powersetCard.coe_nonempty_iff]
  -- `sᶜ` is nonempty because `n < Nat.card α`.
  · rw [Set.nonempty_compl, ne_eq, Set.eq_univ_iff_ncard, ncard_eq]
    exact hn.ne
  -- `Nat.card α ≠ 2 * s.ncard` because `Nat.card α ≠ 2 * s`.
  · rwa [ncard_eq]

/-- If `3 ≤ Nat.card α`, then `alternatingGroup α` acts transitively on `Set.powersetCard α n`.

If `Nat.card α ≤ 2`, then `alternatinGroup α` is trivial, and
the result only holds in the trivial case where `powersetCard α n` is a subsingleton,
that is, when `n = 0` or `Nat.card α ≤ n`. -/
theorem isPretransitive_alternatingGroup [Fintype α] (hα : 3 ≤ Nat.card α) :
    IsPretransitive (alternatingGroup α) (powersetCard α n) := by
  wlog! hn : 2 * n ≤ Nat.card α
  · have : IsPretransitive (alternatingGroup α) (powersetCard α (Nat.card α - n)) := by
      apply this hα
      grind
    by_cases hn' : n ≤ Nat.card α
    · apply IsPretransitive.of_surjective_map
        (compl_bijective (alternatingGroup α) α _).surjective this
      aesop
    · suffices Subsingleton (powersetCard α n) by infer_instance
      rw [not_le] at hn'
      rw [← Finite.card_le_one_iff_subsingleton, powersetCard.card,
        Nat.choose_eq_zero_iff.mpr hn']
      simp
  apply isPretransitive_of_isMultiplyPretransitive
  rcases eq_or_ne n 0 with rfl | hn0
  · infer_instance
  rcases eq_or_ne n 1 with rfl | hn1
  · rw [is_one_pretransitive_iff]
    exact alternatingGroup.isPretransitive_of_three_le_card α hα
  have := alternatingGroup.isMultiplyPretransitive α
  apply isMultiplyPretransitive_of_le (n := Nat.card α - 2) <;> grind

/-- The action of `alternatingGroup α` on `Set.powersetCard α n` is preprimitive
provided `1 ≤ n < Nat.card α` and `Nat.card α ≠ 2 * n`. -/
theorem isPreprimitive_alternatingGroup [Fintype α] {n : ℕ}
    (h_three_le : 3 ≤ n) (hn : n < Nat.card α) (hα : Nat.card α ≠ 2 * n) :
    IsPreprimitive (alternatingGroup α) (powersetCard α n) := by
  have : IsPretransitive (alternatingGroup α) (powersetCard α n) :=
    isPretransitive_alternatingGroup (le_trans h_three_le hn.le)
  have : Nontrivial (powersetCard α n) := nontrivial (by positivity) (by simpa using hn)
  obtain ⟨s⟩ := this.to_nonempty
  rw [← isCoatom_stabilizer_iff_preprimitive _ s, stabilizer_coe]
  apply alternatingGroup.isCoatom_stabilizer
  · rw [powersetCard.coe_nonempty_iff]
    exact le_trans (by norm_num) h_three_le
  · simp only [Set.nonempty_compl, ne_eq, Set.eq_univ_iff_ncard, ncard_eq]
    exact ne_of_lt hn
  · simpa only [ncard_eq]

end Set.powersetCard
