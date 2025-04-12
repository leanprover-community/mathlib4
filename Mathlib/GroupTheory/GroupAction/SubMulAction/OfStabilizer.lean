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

/-! # The SubMulAction of the stabilizer of a point on the complement of that point

When a group `G` acts on a type `α`, the stabilizer of a point `a : α`
acts naturally on the complement of that point.

Such actions (and similar ones for other sets than singletons)
are useful to study the multiple transitivity of the group `G`,
since `n`-transitivity of `G` on `α` is equivalent to `n - 1`-transitivity
of `stabilizer G a` on the complement of `a`.

We define equivariant maps that relate various of these sub_mul_actions
and permit to manipulate them in a relatively smooth way.

* `SubMulAction.ofStabilizer a` : the action of `stabilizer G a` on `{a}ᶜ`

* `SubMulAction.Enat_card_ofStabilizer_eq_add_one`, `SubMulAction.nat_card_ofStabilizer_eq`
compute the cardinality of the `carrier` of that action.

Consider `a b : α` and `g : G` such that `hg : g • b = a`.

* `SubMulAction.conjMap hg` is the equivariant map
from `SubMulAction.ofStabilizer G a` to `SubMulAction.ofStabilizer G b`.

* `SubMulAction.ofStabilizer.isPretransitive_iff_conj hg` shows
that this actions are equivalently pretransitive or

* `SubMulAction.ofStabilizer.isMultiplyPretransitive_iff_conj hg` shows
that this actions are equivalently `n`-pretransitive for all `n : ℕ`.

* `SubMulAction.ofStabilizer.append` : given `x : Fin n ↪ ofStabilizer G a`,
append `a` to obtain `y : Fin n.succ ↪ α`

* `SubMulAction.ofStabilizer.isMultiplyPretransitive_iff` : is the action of `G` on `α`
is pretransitive, then it is `n.succ` pretransitive if and only if
the action of `stabilizer G a` on `ofStabilizer G a` is `n`-pretransitive.

-/

open scoped Pointwise

open MulAction Function.Embedding

namespace SubMulAction

variable (G : Type*) [Group G] {α : Type*} [MulAction G α]

/-- Action of stabilizer of a point on the complement -/
def ofStabilizer (a : α) : SubMulAction (stabilizer G a) α where
  carrier := {a}ᶜ
  smul_mem' g x := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [not_imp_not]
    rw [smul_eq_iff_eq_inv_smul]
    intro hgx
    apply symm
    rw [hgx, ← smul_eq_iff_eq_inv_smul]
    exact g.prop

theorem ofStabilizer_carrier (a : α) : (ofStabilizer G a).carrier = {a}ᶜ :=
  rfl

theorem mem_ofStabilizer_iff (a : α) {x : α} : x ∈ ofStabilizer G a ↔ x ≠ a :=
  Iff.rfl

theorem neq_of_mem_ofStabilizer (a : α) {x : (ofStabilizer G a)} : ↑x ≠ a :=
  x.prop

lemma Enat_card_ofStabilizer_eq_add_one (a : α) :
    ENat.card (ofStabilizer G a) + 1 = ENat.card α := by
  unfold ENat.card
  rw [← Cardinal.mk_sum_compl {a}, map_add, add_comm, eq_comm]
  congr
  simp

lemma nat_card_ofStabilizer_eq [Finite α] (a : α) :
    Nat.card (ofStabilizer G a) = Nat.card α - 1 := by
  unfold Nat.card
  rw [← Cardinal.mk_sum_compl {a},
    Cardinal.toNat_add Cardinal.mk_lt_aleph0 Cardinal.mk_lt_aleph0]
  simp only [Cardinal.mk_fintype, Fintype.card_unique, Nat.cast_one, map_one, add_tsub_cancel_left]
  congr

variable {a b : α} {g : G} (hg : g • b = a)
variable {G}

/-- Conjugation induces an equivariant map between the SubMulAction of
the stabilizer of a point and that of its translate -/
def ofStabilizer.conjMap :
    ofStabilizer G a →ₑ[stabilizerEquivStabilizer hg] ofStabilizer G b where
  toFun := fun ⟨x, hx⟩ =>
    ⟨g⁻¹ • x, fun hy ↦ by
      simp only [Set.mem_singleton_iff, inv_smul_eq_iff, hg] at hy
      exact hx hy⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => by
    rw [← SetLike.coe_eq_coe]
    simp [SubMulAction.val_smul_of_tower, subgroup_smul_def,
       stabilizerEquivStabilizer_apply, ← smul_assoc, MulAut.conj_apply]

theorem ofStabilizer.conjMap_apply (x : ofStabilizer G a) :
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

/-- Append `a` to `x : Fin n ↪ ofStabilizer G a`  to get an element of `Fin n.succ ↪ α`. -/
def ofStabilizer.append {n : ℕ} (x : Fin n ↪ ofStabilizer G a) :
    Fin n.succ ↪ α := by
  let j : ofStabilizer G a ↪ α := {
    toFun := fun u => id u
    inj' := fun x y hxy => by simpa using hxy }
  apply Fin.Embedding.append (x.trans j) (a := a)
  simp [Set.mem_range, trans_apply, not_exists, j]
  exact fun i ↦ (x i).prop

theorem ofStabilizer.append_apply {n : ℕ} (x : Fin n ↪ ofStabilizer G a)
    {i : Fin n.succ} (hi : i.val < n) :
    append x i = (x ⟨i, hi⟩ : α) := by
  simp [append, Fin.Embedding.append, Fin.Embedding.merge, dif_pos hi]

theorem ofStabilizer.append_apply_last {n : ℕ} (x : Fin n ↪ ofStabilizer G a) :
    append x (Fin.last n) = a := by
  simp [append, Fin.Embedding.append, Fin.Embedding.merge, dif_neg]

variable (G) in
lemma exists_smul_of_last_eq [IsPretransitive G α] {n : ℕ} (a : α) (x : Fin n.succ ↪ α) :
    ∃ (g : G) (y : Fin n ↪ ofStabilizer G a),
      Fin.castSuccEmb.trans (g • x) = trans y (subtype _) ∧
        g • x (Fin.last n) = a := by
  obtain ⟨g, hgx⟩ := exists_smul_eq G (x (Fin.last n)) a
  exact ⟨g,
    (Fin.castSuccEmb.trans (g • x)).codRestrict (ofStabilizer G a)
      (fun i ↦ by
        simp only [trans_apply, Fin.castSuccEmb_apply, smul_apply,
          SetLike.mem_coe, mem_ofStabilizer_iff, ← hgx, ne_eq, smul_left_cancel_iff,
          EmbeddingLike.apply_eq_iff_eq]
        refine Fin.lt_last_iff_ne_last.mp i.prop),
    by ext; simp; rfl,
    hgx⟩

theorem ofStabilizer.isPretransitive_iff_of_conj {a b : α} {g : G} (hg : g • b = a) :
    IsPretransitive (stabilizer G a) (ofStabilizer G a) ↔
      IsPretransitive (stabilizer G b) (ofStabilizer G b) :=
  isPretransitive_congr (MulEquiv.surjective _) (ofStabilizer.conjMap_bijective hg)

theorem ofStabilizer.isPretransitive_iff [IsPretransitive G α] {a b : α} :
    IsPretransitive (stabilizer G a) (ofStabilizer G a) ↔
      IsPretransitive (stabilizer G b) (ofStabilizer G b) := by
  obtain ⟨g, hg⟩ := exists_smul_eq G b a
  exact isPretransitive_congr (MulEquiv.surjective _) (ofStabilizer.conjMap_bijective hg)

theorem ofStabilizer.isMultiplyPretransitive_iff_of_conj
    {n : ℕ} {a b : α} {g : G} (hg : g • b = a) :
    IsMultiplyPretransitive (stabilizer G a) (ofStabilizer G a) n ↔
      IsMultiplyPretransitive (stabilizer G b) (ofStabilizer G b) n :=
  IsPretransitive.of_embedding_congr (MulEquiv.surjective _) (ofStabilizer.conjMap_bijective hg)

theorem ofStabilizer.isMultiplyPretransitive_iff [IsPretransitive G α] {n : ℕ} {a b : α} :
    IsMultiplyPretransitive (stabilizer G a) (ofStabilizer G a) n ↔
      IsMultiplyPretransitive (stabilizer G b) (ofStabilizer G b) n := by
  obtain ⟨g, hg⟩ := exists_smul_eq G b a
  exact IsPretransitive.of_embedding_congr (MulEquiv.surjective _)
    (ofStabilizer.conjMap_bijective hg)

/-- Multiple transitivity of a pretransitive action
  is equivalent to one less transitivity of stabilizer of a point
  (Wielandt, th. 9.1, 1st part) -/
theorem ofStabilizer.isMultiplyPretransitive [IsPretransitive G α] {n : ℕ} {a : α} :
    IsMultiplyPretransitive G α n.succ ↔
      IsMultiplyPretransitive (stabilizer G a) (SubMulAction.ofStabilizer G a) n := by
  constructor
  · exact fun hn ↦ {
      exists_smul_eq x y := by
        obtain ⟨g, hgxy⟩ := exists_smul_eq G (append x) (append y)
        have hg : g ∈ stabilizer G a := by
          rw [mem_stabilizer_iff]
          nth_rewrite 1 [← append_apply_last x, ← Function.Embedding.smul_apply,
            hgxy, append_apply_last y]
          rfl
        use ⟨g, hg⟩
        ext ⟨i, hi⟩
        simp only [Function.Embedding.smul_apply, SubMulAction.val_smul_of_tower]
        simp only [subgroup_smul_def]
        rw [← append_apply x (i := ⟨i, Nat.lt_succ_of_lt hi⟩),
          ← Function.Embedding.smul_apply, hgxy, append_apply y] }
  · exact fun hn ↦ {
      exists_smul_eq x y := by
        -- gx • x = x1 :: a
        obtain ⟨gx, x1, hgx, hga⟩ := exists_smul_of_last_eq G a x
        -- gy • y = y1 :: a
        obtain ⟨gy, y1, hgy, hgb⟩ := exists_smul_of_last_eq G a y
        -- g • x1 = y1,
        obtain ⟨g, hg⟩ := hn.exists_smul_eq x1 y1
        use gy⁻¹ * g * gx
        ext i
        simp only [mul_smul, smul_apply]
        rcases Fin.eq_castSucc_or_eq_last i with hi | hi
        · rw [Function.Embedding.ext_iff] at hgx hgy hg
          obtain ⟨j, hj⟩ := hi
          have : i = Fin.castSuccEmb j := by rw [hj]; rfl
          specialize hgx j; specialize hgy j; specialize hg j
          simp only [Nat.succ_eq_add_one, trans_apply, ← this, smul_apply] at hgx hgy
          rw [← Subtype.coe_inj] at hg
          rwa [inv_smul_eq_iff, hgy, hgx]
        · rw [hi, hga, inv_smul_eq_iff, hgb, g.prop] }

end SubMulAction


