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

variable (G : Type*) [Group G] {α : Type*} [MulAction G α]

open scoped Pointwise

open MulAction

variable (α) in
/-- The type of combinations of `n` elements of a type `α` -/
def Nat.Combination (n : ℕ) := {s : Finset α | s.card = n}

variable {n : ℕ} {s t : n.Combination α}

@[simp]
theorem Nat.Combination.mem_iff {s : Finset α} :
    s ∈ n.Combination α ↔ s.card = n := by
  unfold Combination
  simp only [Set.mem_setOf_eq]

theorem Nat.Combination.ext_iff :
    s = t ↔ (s : Finset α) = (t : Finset α) := Subtype.ext_iff

instance : SetLike (n.Combination α) α where
  coe s := s
  coe_injective' s t h := by
    rwa [Subtype.ext_iff, ← Finset.coe_inj]

@[simp]
theorem Nat.Combination.coe_coe {s : n.Combination α} :
    ((s : Finset α) : Set α) = s := rfl

theorem Nat.Combination.mem_coe_iff {s : Nat.Combination α n} {a : α} :
    a ∈ (s : Finset α) ↔ a ∈ s:= by
  rw [← SetLike.mem_coe, ← Finset.mem_coe, Nat.Combination.coe_coe]

@[ext]
theorem Nat.Combination.ext :
    (s : Finset α) = (t : Finset α) → s = t := Subtype.ext

theorem Nat.Combination.eq_iff_subset :
    s = t ↔ (s : Finset α) ⊆ (t : Finset α) := by
  constructor
  · intro h
    rw [h]
  · intro h
    rw [← Subtype.coe_inj]
    apply Finset.eq_of_subset_of_card_le h
    rw [s.prop, t.prop]

variable (α n) in
/-- `Nat.Combination α n` as a `SubMulAction` of `Finset α`. -/
def Nat.Combination.subMulAction [DecidableEq α] :
    SubMulAction G (Finset α) where
  carrier := n.Combination α
  smul_mem' g s hs := by
    rw [Nat.Combination.mem_iff] at hs ⊢
    rw [← hs]
    rw [Finset.card_smul_finset]

instance Nat.Combination.mulAction [DecidableEq α] :
    MulAction G (n.Combination α) :=
  (Nat.Combination.subMulAction G α n).mulAction

variable {G}

-- Why does `Nat.Combination.mulAction_apply` doesn't work?
@[simp]
theorem Nat.Combination.coe_smul [DecidableEq α]
    {n : ℕ} {g : G} {s : n.Combination α} :
    ((g • s : n.Combination α) : Finset α) = (g • s) :=
  rfl

@[simp]
theorem Nat.Combination.smul_coe [DecidableEq α]
    {n : ℕ} {g : G} {s : Finset α} {hs : s ∈ n.Combination α} :
    (g • ⟨s, hs⟩ : n.Combination α) = g • s := by
  rw [Nat.Combination.coe_smul]

theorem Nat.combination.smul_ne_iff_hasMem_not_mem [DecidableEq α] {s t : n.Combination α} {g : G} :
    g • s ≠ t ↔ ∃ a  ∈ (s : Finset α), a ∉ g⁻¹ • (t : Finset α) := by
  rw [← Finset.not_subset, not_iff_not, ← Combination.coe_smul, ← Nat.Combination.eq_iff_subset]
  exact smul_eq_iff_eq_inv_smul g

theorem Nat.Combination.mulAction_faithful
    [DecidableEq α] (hn : 1 ≤ n) (hα : n < ENat.card α)
    {g : G} (hg : (MulAction.toPerm g : Equiv.Perm α) ≠ 1) :
    ∃ s : n.Combination α, g • s ≠ s := by
  classical
  have : ∃ (a : α), (g • a : α) ≠ a := by
    by_contra! h
    apply hg
    ext a
    simpa only using h a
  obtain ⟨a, ha⟩ := this
  suffices ∃ (s : Set α), s.encard = n ∧ a ∈ s ∧ g • a ∉ s by
    obtain ⟨s, hs, has, has'⟩ := this
    have : Set.Finite s := Set.finite_of_encard_eq_coe hs
    use ⟨Set.Finite.toFinset this, by
      rw [Nat.Combination.mem_iff, ←ENat.coe_inj, ← hs, this.encard_eq_coe_toFinset_card]⟩
    rw [ne_eq, Nat.Combination.ext_iff, coe_smul]
    simp only [← Finset.coe_inj, Set.Finite.coe_toFinset, Finset.coe_smul_finset]
    intro h
    apply has'
    rw [← h]
    exact Set.smul_mem_smul_set has
  have : ({a} : Set α) ⊆ {g • a}ᶜ := by
    simp only [Set.subset_compl_singleton_iff, Set.mem_singleton_iff]
    exact ha
  have hα' : n ≤ Set.encard ({g • a}ᶜ) := by
    rw [← not_lt, ← ENat.add_lt_add_iff_left (k := 1) _, not_lt]
    rwa [← Set.encard_singleton (g • a), Set.encard_add_encard_compl,
      Set.encard_singleton, Set.encard_univ, add_comm,
      ENat.add_one_le_iff]
    all_goals { exact ENat.coe_ne_top _}
  obtain ⟨s, has, has', hs⟩ :=
    Set.exists_superset_subset_encard_eq this
      (by rwa [Set.encard_singleton, ← Nat.cast_one, Nat.cast_le])
      hα'
  use s, hs
  simp only [Set.singleton_subset_iff, Set.subset_compl_singleton_iff] at has has'
  exact ⟨has, has'⟩

variable (α G)

variable (n) in
/-- The equivariant map from embeddings of `Fin n` (aka arrangement) to combinations. -/
def EmbeddingToCombination.map [DecidableEq α] :
    (Fin n ↪ α) →[G] n.Combination α where
  toFun := fun f : Fin n ↪ α =>
    ⟨Finset.univ.map f, by rw [Nat.Combination.mem_iff, Finset.card_map, Finset.card_fin]⟩
  map_smul' g f := by
    simp only [id]
    rw [← Subtype.coe_inj, Subtype.coe_mk, Nat.Combination.coe_smul,
      Function.Embedding.smul_def, Finset.smul_finset_def,
      ← Finset.map_map, Finset.map_eq_image]
    simp [toPerm]

theorem EmbeddingToCombination.map_def [DecidableEq α] (f : Fin n ↪ α) :
    ↑((EmbeddingToCombination.map G α n).toFun f) = Finset.univ.map f :=
  rfl

lemma Finset.exists_fin_enum (s : Finset α) (hsn : s.card = n) :
    ∃ f : Fin n ↪ α, Finset.univ.map f = s := by
  obtain ⟨m, ⟨e⟩⟩ := (finite_iff_exists_equiv_fin (α := s)).mp
    (Finite.of_fintype { x // x ∈ s })
  have h : m = n := by
    rwa [← Fintype.card_fin m, ← Fintype.card_congr e,
      Fintype.card_coe]
  use (e.trans (finCongr h)).symm.toEmbedding.trans
    (Function.Embedding.subtype _)
  simp [← Finset.map_map, attach_map_val]

theorem EmbeddingToFinset.map_surjective [DecidableEq α] :
    Function.Surjective (EmbeddingToCombination.map G α n) := by
  rintro ⟨s, hs⟩
  rw [Nat.Combination.mem_iff] at hs
  obtain ⟨f, hf⟩ := s.exists_fin_enum α hs
  use { toFun := f, inj' := f.injective }
  simpa only [Function.Embedding.mk_coe, Nat.Combination.ext_iff]

theorem Nat.Combination.card [Finite α] :
    Nat.card (n.Combination α) = (Nat.card α).choose n := by
  have : Fintype α := Fintype.ofFinite α
  suffices n.Combination α = Finset.powersetCard n (Finset.univ : Finset α) by
    simp [this]
  ext s
  simp

theorem Nat.Combination_nontrivial (h1 : 0 < n) (h2 : n < Nat.card α) :
    Nontrivial (n.Combination α) := by
  classical
  have : 0 < Nat.card α := lt_trans h1 h2
  have _ : Finite α := (Nat.card_pos_iff.mp this).2
  have : 0 < Nat.card (Combination α n) := by
    rw [Nat.Combination.card]
    exact Nat.choose_pos (le_of_lt h2)
  have _ : Finite ↑(Combination α n) := (Nat.card_pos_iff.mp this).2
  rw [← Finite.one_lt_card_iff_nontrivial,
    Nat.Combination.card]
  rw [← not_le]
  intro H
  rw [le_one_iff_eq_zero_or_eq_one] at H
  rcases H with H | H
  · rw [Nat.choose_eq_zero_iff] at H
    exact lt_irrefl _ (lt_trans H h2)
  · rw [Nat.choose_eq_one_iff] at H
    rcases H with ⟨rfl⟩ | ⟨rfl⟩ <;>
      exact lt_irrefl _ (by assumption)

theorem Nat.Combination.isPretransitive_of_IsMultiplyPretransitive [DecidableEq α]
    (h : IsMultiplyPretransitive G α n) :
    IsPretransitive G (n.Combination α) :=
  IsPretransitive.of_surjective_map (EmbeddingToFinset.map_surjective G α) h

theorem Nat.Combination.isPretransitive [DecidableEq α] :
    IsPretransitive (Equiv.Perm α) (n.Combination α) :=
  Nat.Combination.isPretransitive_of_IsMultiplyPretransitive _ _
    (Equiv.Perm.isMultiplyPretransitive α n)

/-- The complement of a combination, as an equivariant map. -/
def Nat.Combination.compl [DecidableEq α] [Fintype α]
    {m : ℕ} (hm : m + n = Fintype.card α) :
    n.Combination α →[G] m.Combination α where
  toFun := fun ⟨s, hs⟩ =>
    ⟨(sᶜ : Finset α), by
      change sᶜ.card = m; change s.card = n at hs
      rw [Finset.card_compl, hs, Nat.sub_eq_iff_eq_add _, hm]
      rw [← hm]; apply Nat.le_add_left⟩
  map_smul' := fun g ⟨s, hs⟩ => by
    apply Subtype.coe_injective
    ext
    simp [← Finset.inv_smul_mem_iff]

theorem Nat.Combination.coe_compl [DecidableEq α] [Fintype α]
    {m : ℕ} {hm : m + n = Fintype.card α} {s : n.Combination α} :
    (Nat.Combination.compl G α hm s : Finset α) = (s : Finset α)ᶜ :=
  rfl

theorem Nat.Combination.mem_compl [DecidableEq α] [Fintype α]
    {m : ℕ} {hm : m + n = Fintype.card α} {s : n.Combination α} {a : α} :
    a ∈ Nat.Combination.compl G α hm s ↔ a ∉ s :=
  Finset.mem_compl

theorem Nat.Combination.compl_compl
    [DecidableEq α] [Fintype α] {m : ℕ}
    (hm : m + n = Fintype.card α) :
    let hm' : n + m = Fintype.card α := (Nat.add_comm _ _) ▸ hm
    (Nat.Combination.compl G α hm').comp (Nat.Combination.compl G α hm) = MulActionHom.id G := by
  intro hm'
  ext s a
  change a ∈ (compl G α hm').comp (compl G α hm) s ↔ a ∈ s
  simp [MulActionHom.comp_apply, mem_compl]

theorem Nat.Combination.compl_bijective
    [DecidableEq α] [Fintype α] {m : ℕ} (hm : m + n = Fintype.card α) :
    Function.Bijective (Nat.Combination.compl G α hm) := by
  have hm' := Nat.add_comm _ _ ▸ hm
  constructor
  · intro s t h
    have := congrArg (Nat.Combination.compl G α hm') h
    simpa [← MulActionHom.comp_apply, Nat.Combination.compl_compl] using this
  · intro s
    use (Nat.Combination.compl G α hm') s
    simp [← MulActionHom.comp_apply, Nat.Combination.compl_compl]

/-- The obvious map from a type to its 1-combinations, as an equivariant map. -/
def Nat.toCombination_one_equivariant [DecidableEq α] :
    α →[G] Nat.Combination α 1 where
  toFun := fun x => ⟨{x}, Finset.card_singleton x⟩
  map_smul' _ _ := rfl

theorem Nat.toCombination_one_equivariant_bijective [DecidableEq α] :
    Function.Bijective (Nat.toCombination_one_equivariant G α) := by
  constructor
  · intro a b h
    simp only [toCombination_one_equivariant, Nat.Combination.ext_iff] at h
    apply Finset.singleton_injective
    exact h
  · rintro ⟨s, hs⟩
    simp [Nat.Combination.mem_iff, Finset.card_eq_one] at hs
    obtain ⟨a, ha⟩ := hs
    use a
    simp only [toCombination_one_equivariant, ha]
    rfl

