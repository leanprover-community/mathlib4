/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.Tactic.Group
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finite.Card

/-!
# Sub_mul_actions on complements of invariant subsets

- We define sub_mul_action of an invariant subset in various contexts,
especially stabilizers and fixing subgroups : `sub_mul_action_of_compl`,
`sub_mul_action_of_stabilizer`, `sub_mul_action_of_fixing_subgroup`.

- We define equivariant maps that relate various of these sub_mul_actions
and permit to manipulate them in a relatively smooth way.
-/

open scoped Pointwise

open MulAction Function.Embedding

namespace SubMulAction

variable (M : Type*) [Group M] {α : Type*} [MulAction M α]

/-- Action of stabilizer of a point on the complement -/
def ofStabilizer (a : α) : SubMulAction (stabilizer M a) α where
  carrier := {a}ᶜ
  smul_mem' g x := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [not_imp_not]
    rw [smul_eq_iff_eq_inv_smul]
    intro hgx
    apply symm
    rw [hgx, ← smul_eq_iff_eq_inv_smul]
    exact g.prop

theorem ofStabilizer_carrier (a : α) : (ofStabilizer M a).carrier = {a}ᶜ :=
  rfl

theorem mem_ofStabilizer_iff (a : α) {x : α} : x ∈ ofStabilizer M a ↔ x ≠ a :=
  Iff.rfl

theorem neq_of_mem_ofStabilizer (a : α) {x : (ofStabilizer M a)} : ↑x ≠ a :=
  x.prop

lemma Enat_card_ofStabilizer_eq_add_one (a : α) :
    ENat.card (ofStabilizer M a) + 1 = ENat.card α := by
  unfold ENat.card
  rw [← Cardinal.mk_sum_compl {a}, map_add, add_comm, eq_comm]
  congr
  simp

lemma nat_card_of_Stabilizer_eq [Finite α] (a : α) :
    Nat.card (ofStabilizer M a) = Nat.card α - 1 := by
  unfold Nat.card
  rw [← Cardinal.mk_sum_compl {a},
    Cardinal.toNat_add Cardinal.mk_lt_aleph0 Cardinal.mk_lt_aleph0]
  simp only [Cardinal.mk_fintype, Fintype.card_unique, Nat.cast_one, map_one, add_tsub_cancel_left]
  congr

variable {a b : α} {g : M} (hg : g • b = a)
variable {M}

/-- Conjugation induces an equivariant map between the SubMulAction of
the stabilizer of a point and that of its translate -/
def ofStabilizer.conjMap :
    ofStabilizer M a →ₑ[stabilizerEquivStabilizer hg] ofStabilizer M b where
  toFun := fun ⟨x, hx⟩ =>
    ⟨g⁻¹ • x, fun hy ↦ by
      simp only [Set.mem_singleton_iff, inv_smul_eq_iff, hg] at hy
      exact hx hy⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => by
    rw [← SetLike.coe_eq_coe]
    simp [SubMulAction.val_smul_of_tower, subgroup_smul_def,
       stabilizerEquivStabilizer_apply, ← smul_assoc, MulAut.conj_apply]

def ofStabilizer.conjMap_apply (x : ofStabilizer M a) :
    (conjMap hg x : α) = g⁻¹ • x := rfl

theorem ofStabilizer.conjMap_bijective :
    Function.Bijective (conjMap hg) := by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [Subtype.mk_eq_mk]
    apply (MulAction.injective g⁻¹)
    rwa [← SetLike.coe_eq_coe, conjMap_apply] at hxy
  · rintro ⟨x, hx⟩
    use (ofStabilizer.conjMap (inv_smul_eq_iff.mpr hg.symm)) ⟨x, hx⟩
    simp [← SetLike.coe_eq_coe, conjMap_apply]

section Transitivity

def ofStabilizer.append {n : ℕ} (x : Fin n ↪ ofStabilizer M a) :
    Fin n.succ ↪ α := by
  let j : ofStabilizer M a ↪ α := {
    toFun := fun u => id u
    inj' := fun x y hxy => by simpa using hxy }
  apply Fin.Embedding.append (x.trans j) (a := a)
  simp [Set.mem_range, trans_apply, not_exists, j]
  exact fun i ↦ (x i).prop

theorem ofStabilizer.append_apply {n : ℕ} (x : Fin n ↪ ofStabilizer M a)
    {i : Fin n.succ} (hi : i.val < n) :
    append x i = (x ⟨i, hi⟩ : α) := by
  simp [append, Fin.Embedding.append, Fin.Embedding.merge, dif_pos hi]

theorem ofStabilizer.append_apply_last {n : ℕ} (x : Fin n ↪ ofStabilizer M a) :
    append x (Fin.last n) = a := by
  simp [append, Fin.Embedding.append, Fin.Embedding.merge, dif_neg]

/- lemma exists_extends_with_last_eq
    (a : α) {n : ℕ} (x : Fin n ↪ SubMulAction.ofStabilizer M a) :
    let j : SubMulAction.ofStabilizer M a ↪ α :=
      { toFun := fun u => id u
        inj' := fun x y hxy => by simpa using hxy }
    ∃ x' : Fin n.succ ↪ α,
      (Fin.castLEEmb (Nat.le_succ n)).trans x' = x.trans j ∧
        x' ⟨n, Nat.lt_succ_self n⟩ = a := by
  intro j

  refine may_extend_with (x.trans (subtype _)) a ?_
  rintro ⟨u, hu⟩
  simp only [toFun_eq_coe, trans_apply, Function.Embedding.coe_subtype] at hu
  apply SubMulAction.neq_of_mem_ofStabilizer M a
  exact hu -/


example : ofStabilizer M a ↪ α := Function.Embedding.subtype _

variable (M) in
lemma exists_smul_of_last_eq [IsPretransitive M α]
    {n : ℕ} (a : α) (x : Fin n.succ ↪ α) :
    ∃ (g : M) (y : Fin n ↪ SubMulAction.ofStabilizer M a),
      (Fin.castLEEmb (Nat.le_succ n)).trans (g • x) =
          trans y (subtype _) ∧ g • x (Fin.last n) = a := by
  obtain ⟨g, hgx⟩ := exists_smul_eq M (x (Fin.last n)) a
  exact ⟨g, {
    toFun i := ⟨g • x i, by
      simp only [Nat.succ_eq_add_one, Fin.coe_eq_castSucc, mem_ofStabilizer_iff, ← hgx, ne_eq,
        smul_left_cancel_iff, EmbeddingLike.apply_eq_iff_eq]
      exact Fin.ne_of_lt i.prop⟩
    inj' i j := by
      simp only [Fin.coe_eq_castSucc, Subtype.mk.injEq, smul_left_cancel_iff,
        EmbeddingLike.apply_eq_iff_eq, Fin.castSucc_inj, imp_self] },
    by ext i; simp; rfl, hgx⟩

/-- Multiple transitivity of a pretransitive action
  is equivalent to one less transitivity of stabilizer of a point
  (Wielandt, th. 9.1, 1st part) -/
theorem ofStabilizer.isMultiplyPretransitive' [IsPretransitive M α] {n : ℕ} :
    IsMultiplyPretransitive M α n.succ ↔
      ∀ a : α, IsMultiplyPretransitive (stabilizer M a) (SubMulAction.ofStabilizer M a) n := by
  constructor
  · -- if the action is n.succ-multiply transitive,
    -- then the action of sub_mul_action_of_stabilizer is n-multiply transitive
    intro hn a -- ; let hn_eq := hn.exists_smul_eq
    apply IsPretransitive.mk
    intro x y
    obtain ⟨g, hgxy⟩ := exists_smul_eq M (append x) (append y)
    have hg : g ∈ stabilizer M a := by
      rw [mem_stabilizer_iff]
      nth_rewrite 1 [← append_apply_last x, ← Function.Embedding.smul_apply,
        hgxy, append_apply_last y]
      rfl
    use ⟨g, hg⟩
    ext ⟨i, hi⟩
    simp only [Function.Embedding.smul_apply, SubMulAction.val_smul_of_tower]
    simp only [subgroup_smul_def]
    rw [← append_apply x (i := ⟨i, Nat.lt_succ_of_lt hi⟩),
      ← Function.Embedding.smul_apply, hgxy, append_apply y]
  · -- if the action of sub_mul_action.of_stabilizer is n-multiply transitive,
    -- then the action is n.succ-multiply transitive.
    intro hn
    /- have aux_fun : ∀ (a : α) (x : Fin n.succ ↪ α),
        ∃ (g : M) (x1 : Fin n ↪ ↥(SubMulAction.ofStabilizer M a)),
          (Fin.castLEEmb (Nat.le_succ n)).toEmbedding.trans (g • x) =
              Function.Embedding.trans x1 (subtype _) ∧
                g • x ⟨n, Nat.lt_succ_self n⟩ = a := by
      intro a x
      obtain ⟨g, hgx⟩ := hα'eq (x ⟨n, Nat.lt_succ_self n⟩) a
      use g
      have zgx : ∀ (i : Fin n), g • x (Fin.castSucc i) ∈ SubMulAction.ofStabilizer M a := by
        rintro ⟨i, hi⟩
        rw [mem_SubMulAction.ofStabilizer_iff]
        rw [← hgx]
        simp only [Fin.castSucc_mk, ne_eq, smul_left_cancel_iff, EmbeddingLike.apply_eq_iff_eq, Fin.mk.injEq]
        exact Nat.ne_of_lt hi
      use {
        toFun := fun i => ⟨g • x i, (by
          simp
          exact zgx i)⟩
        inj' := fun i j ↦ by
          simp only [Fin.coe_eq_castSucc, Subtype.mk.injEq, smul_left_cancel_iff,
            EmbeddingLike.apply_eq_iff_eq, Fin.castSucc_inj, imp_self] }
      constructor
      · ext i
        simp
        rfl
      · exact hgx -/
    apply IsPretransitive.mk
    intro x
    -- gx • x = x1 :: a
    let a := x (Fin.last n)
    obtain ⟨gx, x1, hgx, hga⟩ := exists_smul_of_last_eq M a x
    intro y
    -- gy • y = y1 :: a
    obtain ⟨gy, y1, hgy, hgb⟩ := exists_smul_of_last_eq M a y
    -- g • x1 = y1,
    obtain ⟨g, hg⟩ := (hn a).exists_smul_eq x1 y1
    use gy⁻¹ * g * gx
    ext ⟨i, hi⟩
    simp only [mul_smul, smul_apply]
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi' | hi'
    · rw [Function.Embedding.ext_iff] at hgx hgy hg
      specialize hgx ⟨i, hi'⟩; specialize hgy ⟨i, hi'⟩; specialize hg ⟨i, hi'⟩
      simp only [Nat.succ_eq_add_one, trans_apply, Fin.castLEEmb_apply, Fin.castLE_mk, smul_apply,
        coe_subtype] at hgx hgy hg
      -- simp [hgx, inv_smul_eq_iff, hgy, ← hg]
      rw [hgx, mul_smul, inv_smul_eq_iff, hgy, ← hg]; rfl
    · simp only [hi']
      -- dsimp [Fin.last] at  hga hgb
      rw [hga, mul_smul, inv_smul_eq_iff, hgb]
      rw [← mem_stabilizer_iff]; exact SetLike.coe_mem g

/-- Multiple transitivity of a pretransitive action
  is equivalent to one less transitivity of stabilizer of a point
  (Wielandt, th. 9.1, 1st part)-/
theorem stabilizer.isMultiplyPretransitive (hα' : IsPretransitive M α) {n : ℕ}
    {a : α} :-- (hα0 : ↑n ≤ #α) /- (hα : card_ge α n.succ) -/  :
    IsMultiplyPretransitive M α n.succ ↔
      IsMultiplyPretransitive (stabilizer M a) (SubMulAction.ofStabilizer M a) n :=
  by
  -- let hα'eq := hα'.exists_smul_eq
  constructor
  · -- if the action is n.succ-multiply transitive,
    -- then the action of sub_mul_action_of_stabilizer is n-multiply transitive
    intro hn; let hn_eq := hn.exists_smul_eq
    apply IsPretransitive.mk
    /- let j : SubMulAction.ofStabilizer M a ↪ α :=
      { toFun := fun u => id u
        inj' := fun x y hxy => by simpa using hxy }
    have :
      ∀ x : Fin n ↪ SubMulAction.ofStabilizer M a,
        ∃ x' : Fin n.succ ↪ α,
          (Fin.castLEEmb (Nat.le_succ n)).toEmbedding.trans x' = x.trans j ∧
            x' ⟨n, Nat.lt_succ_self n⟩ = a :=
      by
      intro x
      refine may_extend_with (x.trans (subtype _)) a _
      rintro ⟨u, hu⟩
      simp only [toFun_eq_coe, trans_apply, Function.Embedding.coe_subtype] at hu
      apply (SubMulAction.ofStabilizer_neq M a)
      exact hu -/
    intro x y
    obtain ⟨x', hx', hx'a⟩ := exists_extends_with_last_eq M a x
    obtain ⟨y', hy', hy'a⟩ := exists_extends_with_last_eq M a y
    obtain ⟨g, hg'⟩ := hn_eq x' y'
    have hg : g ∈ stabilizer M a := by
      rw [mem_stabilizer_iff]
      conv_lhs => rw [← hx'a]
      rw [← hy'a, ← hg', smul_apply]
    use ⟨g, hg⟩
    ext ⟨i, hi⟩
    simp only [smul_apply, SubMulAction.val_smul_of_tower]
    rw [Function.Embedding.ext_iff] at hx' hy'
    specialize hx' ⟨i, hi⟩; specialize hy' ⟨i, hi⟩
    simp only [trans_apply, RelEmbedding.coe_toEmbedding, Fin.castLE_mk, id, coeFn_mk] at hx' hy'
    rw [← hx', ← hy', ← hg']; rfl
  · -- if the action of sub_mul_action.of_stabilizer is n-multiply transitive,
    -- then the action is n.succ-multiply transitive.
    intro hn
    apply IsPretransitive.mk
    intro x
    -- obtain gx : gx • x = x1 :: a
    obtain ⟨gx, x1, hgx, hga⟩ := exists_smul_of_last_eq M a x
    intro y
    -- obtain gy : gy • y = y1 :: a
    obtain ⟨gy, y1, hgy, hgb⟩ := exists_smul_of_last_eq M a y
    -- g • x1 = y1,
    let hna_eq := hn.exists_smul_eq
    obtain ⟨g, hg⟩ := hna_eq x1 y1
    use gy⁻¹ * g * gx
    ext ⟨i, hi⟩
    rw [mul_smul]; simp only [smul_apply]
    cases' lt_or_eq_of_le (le_of_lt_succ hi) with hi' hi'
    · rw [Function.Embedding.ext_iff] at hgx hgy hg
      specialize hgx ⟨i, hi'⟩; specialize hgy ⟨i, hi'⟩; specialize hg ⟨i, hi'⟩
      simp only [trans_apply, RelEmbedding.coe_toEmbedding, Fin.castLE_mk, smul_apply,
        Function.Embedding.coe_subtype] at hgx hgy hg
      dsimp only [Fin.castLEEmb_apply, Fin.castLE_mk] at hgx hgy
      rw [hgx, mul_smul, inv_smul_eq_iff, hgy, ← hg]; rfl
    · simp only [hi']
      dsimp only [Fin.last] at hga hgb
      rw [hga, mul_smul, inv_smul_eq_iff, hgb]
      rw [← mem_stabilizer_iff]; exact SetLike.coe_mem g

end SubMulAction


