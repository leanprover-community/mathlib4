/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.GroupAction.Embedding
import Mathlib.GroupTheory.GroupAction.Basic

/-! # Combinations

Combinations in a type are finite subsets of given cardinality.
This file provides some API for handling them, especially in the context of a group action.

* `Nat.Combination α n` is the set of all `Finset α` with cardinality `n`.

* `Nat.Combination.card` proves that the `Nat.Card`-cardinality
of this set is equal to `(Nat.card α).choose n`.

* `Nat.Combination.subMulAction`:
When a group `G` acts on `α`, the `SubMulAction` of `G` on `n.Combination α`.

This induces a `MulAction G (n.Combination α)` instance. Then:

* `EmbeddingToCombination.map`: the equivariant map from `Fin n ↪ α` to `n.Combination α`.

* `Nat.Combination.isPretransitive_of_IsMultiplyPretransitive`
shows the pretransitivity of that action if the action of `G` on `α` is `n`-pretransitive.

* `Nat.Combination.isPretransitive` shows that `Equiv.Perm α`
acts pretransitively on `n.Combination α`, for all `n`.

* `Nat.Combination.compl`: Given an equality `m + n = Fintype.card α`,
the complement of an `n`-combination, as an `m`-combination.
This map is an equivariant map with respect to a group action on `α`.

* `Nat.toCombination_one_equivariant`:
The obvious map from `α` to `1.Combination α`, as an equivariant map.

-/

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

-- TODO : Update once there is a `SetLike` for `Finset` (PR  #28241)
instance : SetLike (n.Combination α) α where
  coe s := s
  coe_injective' s t h := SetCoe.ext (by simpa using h)

@[simp]
theorem coe_coe {s : n.Combination α} :
    ((s : Finset α) : Set α) = s := rfl

theorem mem_coe_iff {s : Nat.Combination α n} {a : α} : a ∈ (s : Finset α) ↔ a ∈ s := .rfl

theorem eq_iff_subset : s = t ↔ (s : Finset α) ⊆ (t : Finset α) := by
  rw [Finset.subset_iff_eq_of_card_le (t.prop.trans_le s.prop.ge), Subtype.ext_iff]

theorem exists_mem_notMem (hn : 1 ≤ n) (hα : n < ENat.card α) {a b : α} (hab : a ≠ b) :
    ∃ s : n.Combination α, a ∈ s ∧ b ∉ s := by
  have ha' : n ≤ Set.encard {b}ᶜ := by
    rw [← not_lt, ← ENat.add_lt_add_iff_left (k := 1) _, not_lt]
    rwa [← Set.encard_singleton b, Set.encard_add_encard_compl,
      Set.encard_singleton, Set.encard_univ, add_comm,
      ENat.add_one_le_iff]
    all_goals { exact ENat.coe_ne_top _}
  obtain ⟨s, has, has', hs⟩ :=
    Set.exists_superset_subset_encard_eq (s := {a}) (by simp [Ne.symm hab]) (by simpa) ha'
  simp only [Set.singleton_subset_iff, Set.subset_compl_singleton_iff] at has has'
  letI : Set.Finite s := Set.finite_of_encard_eq_coe hs
  use ⟨Set.Finite.toFinset this, by
      rw [mem_iff, ←ENat.coe_inj, ← hs, this.encard_eq_coe_toFinset_card]⟩
  simp [← mem_coe_iff, has, has']

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
    ((g • s : n.Combination α) : Finset α) = (g • s) :=
  SubMulAction.val_smul (p := subMulAction G α n) g s

@[to_additive]
theorem smul_ne_iff_exists_mem_notMem_smul [DecidableEq α] {s t : n.Combination α} {g : G} :
    g • s ≠ t ↔ ∃ a ∈ (s : Finset α), a ∉ g⁻¹ • (t : Finset α) := by
  rw [← Finset.not_subset, not_iff_not, ← coe_smul, ← eq_iff_subset]
  exact smul_eq_iff_eq_inv_smul g

theorem addAction_faithful {G : Type*} [AddGroup G] {α : Type*} [AddAction G α] {n : ℕ}
    [DecidableEq α] (hn : 1 ≤ n) (hα : n < ENat.card α)
    {g : G} (hg : (AddAction.toPerm g : Equiv.Perm α) ≠ 1) :
    ∃ s : n.Combination α, g +ᵥ s ≠ s := by
  have : ∃ (a : α), (g +ᵥ a : α) ≠ a := by
    by_contra! h
    apply hg
    ext a
    simpa only using h a
  obtain ⟨a, ha⟩ := this
  obtain ⟨s, has, has'⟩ := exists_mem_notMem hn hα (Ne.symm ha)
  use s
  intro h
  apply has'
  rwa [← h, ← mem_coe_iff, coe_vadd, vadd_mem_vadd_finset_iff, mem_coe_iff]

theorem faithfulVAdd {G : Type*} [AddGroup G] {α : Type*} [AddAction G α] {n : ℕ}
    [DecidableEq α] (hn : 1 ≤ n) (hα : n < ENat.card α)
    [FaithfulVAdd G α] :
    FaithfulVAdd G (n.Combination α) := ⟨fun {g₁ g₂} h ↦ by
  simp only [vadd_eq_iff_eq_neg_vadd, vadd_vadd] at h
  rw [← neg_inj, ← sub_eq_zero, sub_neg_eq_add]
  set g := -g₁ + g₂
  by_contra! h'
  have hg : (AddAction.toPerm g : Equiv.Perm α) ≠ 1 := by
    intro K
    simp only [Equiv.Perm.ext_iff, Equiv.Perm.coe_one, id_eq] at K
    apply h'
    apply FaithfulVAdd.eq_of_vadd_eq_vadd (P := α)
    simpa using K
  obtain ⟨s, hs⟩ := addAction_faithful hn hα hg
  apply hs
  rw [← h]⟩

theorem mulAction_faithful [DecidableEq α] (hn : 1 ≤ n) (hα : n < ENat.card α)
    {g : G} (hg : (MulAction.toPerm g : Equiv.Perm α) ≠ 1) :
    ∃ s : n.Combination α, g • s ≠ s := by
  have : ∃ (a : α), (g • a : α) ≠ a := by
    by_contra! h
    apply hg
    ext a
    simpa only using h a
  obtain ⟨a, ha⟩ := this
  obtain ⟨s, has, has'⟩ := exists_mem_notMem hn hα (Ne.symm ha)
  use s
  intro h
  apply has'
  rwa [← h, ← mem_coe_iff, coe_smul, smul_mem_smul_finset_iff, mem_coe_iff]

theorem faithfulSMul [DecidableEq α] (hn : 1 ≤ n) (hα : n < ENat.card α)
    [FaithfulSMul G α] :
    FaithfulSMul G (n.Combination α) := ⟨fun {g₁ g₂} h ↦ by
  simp only [smul_eq_iff_eq_inv_smul, smul_smul] at h
  rw [← inv_inj, ← div_eq_one, div_inv_eq_mul]
  set g := g₁⁻¹ * g₂
  by_contra! h'
  have hg : (MulAction.toPerm g : Equiv.Perm α) ≠ 1 := by
    intro K
    simp only [Equiv.Perm.ext_iff, Equiv.Perm.coe_one, id_eq] at K
    apply h'
    apply FaithfulSMul.eq_of_smul_eq_smul (α := α)
    simpa using K
  obtain ⟨s, hs⟩ := mulAction_faithful hn hα hg
  apply hs
  rw [← h]⟩

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
    simp only [id]
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

protected theorem card [Finite α] :
    Nat.card (n.Combination α) = (Nat.card α).choose n := by
  have := Fintype.ofFinite α
  suffices n.Combination α = Finset.powersetCard n (Finset.univ : Finset α) by
    simp [this]
  ext; simp

variable {α} in
theorem _root_.ENat.nontrivial_combination (h1 : 0 < n) (h2 : n < ENat.card α) :
    Nontrivial (n.Combination α) := by
  obtain ⟨t, ht⟩ := Cardinal.exists_finset_le_card α (n + 1)
    (by rwa [← Cardinal.natCast_le_toENat_iff, cast_add,
      cast_one, ENat.add_one_le_iff (ENat.coe_ne_top n)])
  obtain ⟨s, hst, hsn⟩ := t.exists_subset_card_eq ht
  have : ∃ f : Fin (n + 1) ↪ α, Finset.univ.map f = s := by
    apply Function.Embedding.exists_of_card_eq_finset
    simp [hsn]
  obtain ⟨f, hf⟩ := this
  rw [nontrivial_iff]
  let j := Fin.castSuccEmb.trans f
  use ⟨Finset.univ.map ((Fin.castLEEmb n.le_succ).trans f), by simp⟩
  use ⟨Finset.univ.map ((Fin.succAboveEmb 0).trans f), by simp⟩
  simp only [ne_eq, Subtype.mk.injEq]
  intro h
  suffices f 0 ∉ Finset.univ.map ((Fin.succAboveEmb 0).trans f) by
    apply this
    rw [← h, mem_map]
    use ⟨0, h1⟩
    simp
  simp

theorem _root_.Nat.nontrivial_combination (h1 : 0 < n) (h2 : n < Nat.card α) :
    Nontrivial (n.Combination α) := by
  apply ENat.nontrivial_combination h1
  suffices ENat.card α = Nat.card α by
    simp [this, h2]
  refine (ENat.toNat_eq_iff ?_).mp rfl
  exact Nat.ne_zero_of_lt h2

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
    (compl G α <| n.add_comm m ▸ hm).comp (compl G α hm) = .id G := by
  ext s a
  change a ∈ (compl G α _).comp (compl G α hm) s ↔ a ∈ s
  simp [MulActionHom.comp_apply, mem_compl]

theorem compl_bijective :
    Function.Bijective (compl G α hm) :=
  let e : _ ≃ _ := ⟨compl G α hm, compl G α (n.add_comm m ▸ hm),
    fun _ ↦ congr($(compl_compl G α _) _), fun _ ↦ congr($(compl_compl G α _) _)⟩
  e.bijective

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
