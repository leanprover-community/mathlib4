/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

module

public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.GroupAction.Embedding
public import Mathlib.GroupTheory.GroupAction.Basic

/-! # Combinations

Combinations in a type are finite subsets of given cardinality.
This file provides some API for handling them, especially in the context of a group action.

* `Nat.Combination α n` is the set of all `Finset α` with cardinality `n`.

* `Nat.Combination.card` proves that the `Nat.card`-cardinality
of this set is equal to `(Nat.card α).choose n`.

* `Nat.Combination.subMulAction`:
When a group `G` acts on `α`, the `SubMulAction` of `G` on `n.Combination α`.

This induces a `MulAction G (n.Combination α)` instance. Then:

* `EmbeddingToCombination.map`: the equivariant map from `Fin n ↪ α` to `n.Combination α`.

* `Nat.Combination.isPretransitive_of_isMultiplyPretransitive`
shows the pretransitivity of that action if the action of `G` on `α` is `n`-pretransitive.

* `Nat.Combination.isPretransitive` shows that `Equiv.Perm α`
acts pretransitively on `n.Combination α`, for all `n`.

* `Nat.Combination.compl`: Given an equality `m + n = Fintype.card α`,
the complement of an `n`-combination, as an `m`-combination.
This map is an equivariant map with respect to a group action on `α`.

* `Nat.toCombination_one_equivariant`:
The obvious map from `α` to `1.Combination α`, as an equivariant map.

-/

@[expose] public section

variable (G : Type*) [Group G] (α : Type*) [MulAction G α]

/-- The type of combinations of `n` elements of a type `α` -/
def Nat.Combination (n : ℕ) := {s : Finset α | s.card = n}

variable {α} {n : ℕ} {s t : n.Combination α}

namespace Nat.Combination

open scoped Pointwise

open MulAction Finset

@[simp]
theorem mem_iff {s : Finset α} :
    s ∈ n.Combination α ↔ s.card = n := by
  rw [Combination, Set.mem_setOf_eq]

instance : SetLike (n.Combination α) α := SetLike.instSubtype

@[simp]
theorem coe_coe {s : n.Combination α} :
    ((s : Finset α) : Set α) = s := rfl

theorem mem_coe_iff {s : Nat.Combination α n} {a : α} : a ∈ (s : Finset α) ↔ a ∈ s := .rfl

theorem eq_iff_subset : s = t ↔ (s : Finset α) ⊆ (t : Finset α) := by
  rw [Finset.subset_iff_eq_of_card_le (t.prop.trans_le s.prop.ge), Subtype.ext_iff]

theorem exists_mem_notMem (hn : 1 ≤ n) (hα : n < ENat.card α) {a b : α} (hab : a ≠ b) :
    ∃ s : n.Combination α, a ∈ s ∧ b ∉ s := by
  have ha' : n ≤ Set.encard {b}ᶜ := by
    rwa [← (Set.encard_add_encard_compl {b}).trans (Set.encard_univ α), Set.encard_singleton,
      add_comm, ENat.lt_add_one_iff' (ENat.coe_ne_top n)] at hα
  obtain ⟨s, has, has', hs⟩ :=
    Set.exists_superset_subset_encard_eq (s := {a}) (by simp [Ne.symm hab]) (by simpa) ha'
  have : Set.Finite s := Set.finite_of_encard_eq_coe hs
  exact ⟨⟨Set.Finite.toFinset this, by
    rwa [mem_iff, ← ENat.coe_inj, ← this.encard_eq_coe_toFinset_card]⟩,
      by simpa using has, by simpa using has'⟩

variable (α n) in
/-- `Nat.Combination α n` as a `SubMulAction` of `Finset α`. -/
@[to_additive /--`Nat.Combination α n` as a `SubAddAction` of `Finsetα`.-/]
def subMulAction [DecidableEq α] : SubMulAction G (Finset α) where
  carrier := n.Combination α
  smul_mem' g s := (Finset.card_smul_finset g s).trans

@[to_additive]
instance [DecidableEq α] : MulAction G (n.Combination α) :=
  (subMulAction G α n).mulAction

variable {G}

@[to_additive (attr := simp)]
theorem coe_smul [DecidableEq α] {n : ℕ} {g : G} {s : n.Combination α} :
    ((g • s : n.Combination α) : Finset α) = g • s :=
  SubMulAction.val_smul (p := subMulAction G α n) g s

theorem addAction_faithful {G : Type*} [AddGroup G] {α : Type*} [AddAction G α] {n : ℕ}
    [DecidableEq α] (hn : 1 ≤ n) (hα : n < ENat.card α) {g : G} :
    AddAction.toPerm g = (1 : Equiv.Perm (n.Combination α))
      ↔ AddAction.toPerm g = (1 : Equiv.Perm α) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · contrapose h with h
    have : ∃ a, (g +ᵥ a : α) ≠ a := by simpa [Equiv.ext_iff] using h
    obtain ⟨a, ha⟩ := this
    obtain ⟨s, has, has'⟩ := exists_mem_notMem hn hα (Ne.symm ha)
    rw [Equiv.ext_iff, not_forall]
    use s
    contrapose! has'
    simp only [AddAction.toPerm_apply, Equiv.Perm.coe_one, id_eq] at has'
    rw [← has']
    simpa [← mem_coe_iff]
  · simp only [Equiv.ext_iff, AddAction.toPerm_apply] at h ⊢
    simp [Subtype.ext_iff, Finset.ext_iff, mem_vadd_finset, h]

/-- If an additive group `G` acts faithfully on `α`,
then it acts faithfully on `n.Combination α`,
provided `1 ≤ n < ENat.card α`. -/
theorem faithfulVAdd {G : Type*} [AddGroup G] {α : Type*} [AddAction G α] {n : ℕ}
    [DecidableEq α] (hn : 1 ≤ n) (hα : n < ENat.card α) [FaithfulVAdd G α] :
    FaithfulVAdd G (n.Combination α) := by
  rw [faithfulVAdd_iff]
  intro g hg
  apply AddAction.toPerm_injective (α := G) (β := α)
  rw [AddAction.toPerm_zero, ← addAction_faithful hn hα]
  exact Equiv.Perm.ext_iff.mpr hg

theorem mulAction_faithful {G : Type*} [Group G] {α : Type*} [MulAction G α] {n : ℕ}
    [DecidableEq α] (hn : 1 ≤ n) (hα : n < ENat.card α) {g : G} :
    MulAction.toPerm g = (1 : Equiv.Perm (n.Combination α))
      ↔ MulAction.toPerm g = (1 : Equiv.Perm α) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · contrapose h with h
    have : ∃ a, (g • a : α) ≠ a := by simpa [Equiv.ext_iff] using h
    obtain ⟨a, ha⟩ := this
    obtain ⟨s, has, has'⟩ := exists_mem_notMem hn hα (Ne.symm ha)
    rw [Equiv.ext_iff, not_forall]
    use s
    contrapose! has'
    simp only [MulAction.toPerm_apply, Equiv.Perm.coe_one, id_eq] at has'
    rw [← has']
    simpa only [coe_smul, smul_mem_smul_finset_iff, ← mem_coe_iff]
  · simp only [Equiv.ext_iff, MulAction.toPerm_apply] at h ⊢
    simp [Subtype.ext_iff, Finset.ext_iff, mem_smul_finset, h]

/-- If a group `G` acts faithfully on `α`,
then it acts faithfull on `n.Combination α`,
provided `1 ≤ n < ENat.card α`. -/
theorem faithfulSMul [DecidableEq α] (hn : 1 ≤ n) (hα : n < ENat.card α) [FaithfulSMul G α] :
    FaithfulSMul G (n.Combination α) := by
  rw [faithfulSMul_iff]
  intro g hg
  apply MulAction.toPerm_injective (α := G) (β := α)
  rw [MulAction.toPerm_one, ← mulAction_faithful hn hα]
  exact Equiv.Perm.ext_iff.mpr hg

attribute [to_additive existing] faithfulSMul

variable (α G)

variable (n) in
/-- The equivariant map from embeddings of `Fin n` (aka arrangement) to combinations. -/
@[to_additive /-- The equivariant map from embeddings of `Fin n`
  (aka arrangements) to combinations. -/]
def mulActionHom_of_embedding [DecidableEq α] :
    (Fin n ↪ α) →[G] n.Combination α where
  toFun f := ⟨Finset.univ.map f, by rw [mem_iff, Finset.card_map, Finset.card_fin]⟩
  map_smul' g f := by
    rw [← Subtype.coe_inj, Subtype.coe_mk, coe_smul,
      f.smul_def, Finset.smul_finset_def,
      ← Finset.map_map, Finset.map_eq_image]
    simp [toPerm]

@[to_additive]
theorem coe_mulActionHom_of_embedding [DecidableEq α] (f : Fin n ↪ α) :
    ↑((mulActionHom_of_embedding G α n).toFun f) = Finset.univ.map f :=
  rfl

@[to_additive]
theorem mulActionHom_of_embedding_surjective [DecidableEq α] :
    Function.Surjective (mulActionHom_of_embedding G α n) := by
  intro ⟨s, hs⟩
  obtain ⟨f : Fin n ↪ α, hf⟩ :=
    Function.Embedding.exists_of_card_eq_finset (by rw [hs, Fintype.card_fin])
  exact ⟨f, Subtype.ext hf⟩

protected theorem card :
    Nat.card (n.Combination α) = (Nat.card α).choose n := by
  classical
  cases fintypeOrInfinite α
  · suffices n.Combination α = Finset.powersetCard n (Finset.univ : Finset α) by
      simp [this]
    ext; simp
  · rcases n with _ | n
    · simp [Combination]
    · rcases finite_or_infinite (Combination α (n + 1)) with hc | hc
      · refine (Infinite.false (α := (Combination α (n + 1) → Combination α (n + 1))) ?_).elim
        have : FaithfulSMul (Equiv.Perm α) (Combination α (n + 1)) :=
          Nat.Combination.faithfulSMul (le_add_left 1 n) (by simp)
        exact (Infinite.false (α := (Combination α (n + 1) → Combination α (n + 1)))
          (Infinite.of_injective _ (smul_left_injective' (M := Equiv.Perm α)))).elim
      · simp

variable {α} in
/-- If `0 < n < ENat.card α`, then `n.Combination α` is nontrivial. -/
theorem nontrivial (h1 : 0 < n) (h2 : n < ENat.card α) :
    Nontrivial (n.Combination α) := by
  classical
  have h : Nontrivial α :=
    (ENat.one_lt_card_iff_nontrivial α).mp (lt_of_le_of_lt (one_le_cast.mpr h1) h2)
  have : FaithfulSMul (Equiv.Perm α) (Combination α n) := Nat.Combination.faithfulSMul h1 h2
  have h := (smul_left_injective' (M := Equiv.Perm α) (α := Combination α n)).nontrivial
  contrapose! h
  infer_instance

variable {α} in
/-- A variant of `Nat.Combination.nontrivial` that uses `Nat.card`. -/
theorem nontrivial' (h1 : 0 < n) (h2 : n < Nat.card α) :
    Nontrivial (n.Combination α) := by
  have : Finite α := finite_of_card_ne_zero (ne_zero_of_lt h2)
  apply nontrivial h1
  simp [ENat.card_eq_coe_natCard α, h2]

section

variable [DecidableEq α]

@[to_additive isPretransitive_of_isMultiplyPretransitive']
theorem isPretransitive_of_isMultiplyPretransitive (h : IsMultiplyPretransitive G α n) :
    IsPretransitive G (n.Combination α) :=
  IsPretransitive.of_surjective_map (mulActionHom_of_embedding_surjective G α) h

theorem isPretransitive : IsPretransitive (Equiv.Perm α) (n.Combination α) :=
  isPretransitive_of_isMultiplyPretransitive _ _
    (Equiv.Perm.isMultiplyPretransitive α n)

end

section

variable [DecidableEq α] [Fintype α] {m : ℕ} (hm : m + n = Fintype.card α)
include hm

/-- The complement of a combination, as an equivariant map. -/
def compl : n.Combination α →[G] m.Combination α where
  toFun s := ⟨(sᶜ : Finset α), by
      rw [mem_iff, Finset.card_compl]
      have := mem_iff.mp s.2
      omega⟩
  map_smul' g s := by ext; simp [← Finset.inv_smul_mem_iff]

variable {hm} in
theorem coe_compl {s : n.Combination α} :
    (compl G α hm s : Finset α) = (s : Finset α)ᶜ :=
  rfl

variable {hm} in
theorem mem_compl {s : n.Combination α} {a : α} :
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

/-- The obvious map from a type to its 1-combinations, as an equivariant map. -/
@[to_additive /-- The obvious map from a type to its 1-combinations, as an equivariant map. -/]
def mulActionHom_singleton [DecidableEq α] :
    α →[G] Nat.Combination α 1 where
  toFun x := ⟨{x}, Finset.card_singleton x⟩
  map_smul' _ _ := rfl

@[to_additive]
theorem mulActionHom_singleton_bijective [DecidableEq α] :
    Function.Bijective (mulActionHom_singleton G α) := by
  refine ⟨fun a b h ↦ Finset.singleton_injective congr($h.1), fun ⟨s, hs⟩ ↦ ?_⟩
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs
  exact ⟨a, rfl⟩

end Nat.Combination
