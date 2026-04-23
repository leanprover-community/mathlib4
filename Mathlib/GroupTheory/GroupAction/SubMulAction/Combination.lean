/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

module

public import Mathlib.Data.Set.PowersetCard
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.GroupTheory.Perm.MaximalSubgroups
import Mathlib.GroupTheory.SpecificGroups.Alternating.MaximalSubgroups
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToAdditive

/-! # Combinations

Combinations in a type are finite subsets of given cardinality.
This file provides some API for handling them in the context of a group action.

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

namespace Set.powersetCard

open scoped Pointwise

open MulAction Finset Set Equiv Equiv.Perm

variable (G : Type*) [Group G] {α : Type*} [MulAction G α]
  {n : ℕ} {s t : Set.powersetCard α n}

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
  inferInstanceAs <| MulAction G (subMulAction G α n)

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
    contrapose has'
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
    contrapose has'
    simp only [MulAction.toPerm_apply, coe_one, id_eq] at has'
    rw [← has']
    simpa only [coe_smul, smul_mem_smul_finset_iff, ← mem_coe_iff]
  · simp only [Equiv.ext_iff, MulAction.toPerm_apply] at h ⊢
    simp [Subtype.ext_iff, Finset.ext_iff, mem_smul_finset, h]

/-- If a group `G` acts faithfully on `α`, then
it acts faithfully on `powersetCard α n` provided `1 ≤ n < ENat.card α`. -/
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
  toFun := ofFinEmb n α
  map_smul' g f := by
    rw [← Subtype.coe_inj, coe_smul, f.smul_def, val_ofFinEmb, val_ofFinEmb,
      Finset.smul_finset_def, ← Finset.map_map, Finset.map_eq_image]
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

variable [DecidableEq α]

@[to_additive isPretransitive_of_isMultiplyPretransitive']
theorem isPretransitive_of_isMultiplyPretransitive (h : IsMultiplyPretransitive G α n) :
    IsPretransitive G (powersetCard α n) :=
  IsPretransitive.of_surjective_map (mulActionHom_of_embedding_surjective G α) h

theorem isPretransitive : IsPretransitive (Perm α) (powersetCard α n) :=
  isPretransitive_of_isMultiplyPretransitive _ (isMultiplyPretransitive α n)

section compl

variable (α)

variable [Fintype α] {m : ℕ} (hm : m + n = Fintype.card α)
include hm

/-- The complement of a combination, as an equivariant map. -/
def mulActionHom_compl : powersetCard α n →[G] powersetCard α m where
  toFun := compl hm
  map_smul' g s := by ext; simp [← Finset.inv_smul_mem_iff]

variable {hm} in
theorem coe_mulActionHom_compl {s : powersetCard α n} :
    (mulActionHom_compl G α hm s : Finset α) = (s : Finset α)ᶜ :=
  rfl

variable {hm} in
theorem mem_mulActionHom_compl {s : powersetCard α n} {a : α} :
    a ∈ mulActionHom_compl G α hm s ↔ a ∉ s :=
  Finset.mem_compl

theorem mulActionHom_compl_mulActionHom_compl :
    (mulActionHom_compl G α <| (n.add_comm m).trans hm).comp
    (mulActionHom_compl G α hm) = .id G := by
  ext s a
  change a ∈ (mulActionHom_compl G α _).comp (mulActionHom_compl G α hm) s ↔ a ∈ s
  simp [MulActionHom.comp_apply, mem_mulActionHom_compl]

theorem mulActionHom_compl_bijective :
    Function.Bijective (mulActionHom_compl G α hm) :=
  Function.bijective_iff_has_inverse.mpr ⟨mulActionHom_compl G α ((n.add_comm m).trans hm),
    DFunLike.ext_iff.mp (mulActionHom_compl_mulActionHom_compl G α hm),
    DFunLike.ext_iff.mp (mulActionHom_compl_mulActionHom_compl G α _)⟩

end compl

variable (α)

/-- The obvious map from a type to its 1-combinations, as an equivariant map. -/
@[to_additive /-- The obvious map from a type to its 1-combinations, as an equivariant map. -/]
noncomputable def mulActionHom_singleton : α →[G] powersetCard α 1 where
  toFun := ofSingleton
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

set_option backward.isDefEq.respectTransparency false in
/-- If `3 ≤ Nat.card α`, then `alternatingGroup α` acts transitively on `Set.powersetCard α n`.

If `Nat.card α ≤ 2`, then `alternatingGroup α` is trivial, and
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
        (mulActionHom_compl_bijective (alternatingGroup α) α _).surjective this
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

set_option backward.isDefEq.respectTransparency false in
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
