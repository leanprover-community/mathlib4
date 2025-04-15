/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.GroupTheory.GroupAction.Basic
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

/-- Action of the stabilizer of a point on the complement -/
@[to_additive "Action of the stabilizer of a point on the complement"]
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

@[to_additive]
theorem ofStabilizer_carrier (a : α) : (ofStabilizer G a).carrier = {a}ᶜ :=
  rfl

@[to_additive]
theorem mem_ofStabilizer_iff (a : α) {x : α} : x ∈ ofStabilizer G a ↔ x ≠ a :=
  Iff.rfl

@[to_additive]
theorem neq_of_mem_ofStabilizer (a : α) {x : (ofStabilizer G a)} : ↑x ≠ a :=
  x.prop

@[to_additive]
lemma Enat_card_ofStabilizer_eq_add_one (a : α) :
    ENat.card (ofStabilizer G a) + 1 = ENat.card α := by
  unfold ENat.card
  rw [← Cardinal.mk_sum_compl {a}, map_add, add_comm, eq_comm]
  congr
  simp

@[to_additive]
lemma nat_card_ofStabilizer_eq [Finite α] (a : α) :
    Nat.card (ofStabilizer G a) = Nat.card α - 1 := by
  unfold Nat.card
  rw [← Cardinal.mk_sum_compl {a},
    Cardinal.toNat_add Cardinal.mk_lt_aleph0 Cardinal.mk_lt_aleph0]
  simp only [Cardinal.mk_fintype, Fintype.card_unique, Nat.cast_one, map_one, add_tsub_cancel_left]
  congr

variable {G}

/-- Conjugation induces an equivariant map between the SubAddAction of
the stabilizer of a point and that of its translate -/
def _root_.SubAddAction.ofStabilizer.conjMap {G : Type*} [AddGroup G] {α : Type*} [AddAction G α]
    {g : G} {a b : α} (hg : b = g +ᵥ a) :
    AddActionHom (AddAction.stabilizerEquivStabilizer hg).symm
      (SubAddAction.ofStabilizer G a) (SubAddAction.ofStabilizer G b) where
  toFun x := ⟨g +ᵥ x.val, fun hy ↦ x.prop (by simpa [hg] using hy)⟩
  map_vadd' := fun ⟨k, hk⟩ x ↦ by
    simp [← SetLike.coe_eq_coe, AddAction.stabilizerEquivStabilizer, ← vadd_assoc]

/-- Conjugation induces an equivariant map between the SubMulAction of
the stabilizer of a point and that of its translate -/
@[to_additive existing]
def ofStabilizer.conjMap {g : G} {a b : α} (hg : b = g • a) :
    MulActionHom (stabilizerEquivStabilizer hg).symm (ofStabilizer G a) (ofStabilizer G b) where
    -- stabilizerEquivStabilizer hg] ofStabilizer G a where
  toFun x := ⟨g • x.val, fun hy ↦ x.prop (by simpa [hg] using hy)⟩
  map_smul' := fun ⟨k, hk⟩ ↦ by
    simp [← SetLike.coe_eq_coe, stabilizerEquivStabilizer, ← smul_assoc]

variable {g  h k: G} {a b c: α}
variable (hg : b = g • a) (hh : c = h • b) (hk : c = k • a)

@[to_additive]
theorem ofStabilizer.conjMap_apply (x : ofStabilizer G a) :
    (conjMap hg x : α) = g • x := rfl

theorem _root_.AddAction.stabilizerEquivStabilizer_compTriple
    {G : Type*} [AddGroup G] {α : Type*} [AddAction G α]
    {g h k : G} {a b c : α} {hg : b = g +ᵥ a} {hh : c = h +ᵥ b} {hk : c = k +ᵥ a} (H : k = h + g) :
    CompTriple (AddAction.stabilizerEquivStabilizer hg).symm
      (AddAction.stabilizerEquivStabilizer hh).symm
      (AddAction.stabilizerEquivStabilizer hk).symm where
  comp_eq := by
    ext
    simp [AddAction.stabilizerEquivStabilizer, H, AddAut.inv_def, AddAut.conj, ← add_assoc]

variable {hg hh hk} in
@[to_additive existing]
theorem _root_.MulAction.stabilizerEquivStabilizer_compTriple (H : k = h * g) :
    CompTriple (stabilizerEquivStabilizer hg).symm
      (stabilizerEquivStabilizer hh).symm
      (stabilizerEquivStabilizer hk).symm where
  comp_eq := by
    ext
    simp [stabilizerEquivStabilizer, H, MulAut.inv_def, MulAut.conj, ← mul_assoc]

variable {hg hh hk} in
@[to_additive]
theorem ofStabilizer.conjMap_comp_apply (H : k = h * g) (x : ofStabilizer G a) :
    conjMap hh (conjMap hg x) = conjMap hk x := by
  simp [← Subtype.coe_inj, conjMap_apply, H, mul_smul]

@[to_additive]
theorem ofStabilizer.conjMap_comp_inv_apply (x : ofStabilizer G a) :
    (conjMap (eq_inv_smul_iff.mpr hg.symm)) (conjMap hg x) = x := by
  simp [← Subtype.coe_inj, conjMap_apply]

@[to_additive]
theorem ofStabilizer.inv_conjMap_comp_apply (x : ofStabilizer G b) :
    conjMap hg (conjMap (eq_inv_smul_iff.mpr hg.symm) x) = x := by
  simp [← Subtype.coe_inj, conjMap_apply]

@[to_additive]
theorem ofStabilizer.conjMap_comp (H : k = h * g) :
    (conjMap hh).comp (conjMap hg) (κ := stabilizerEquivStabilizer_compTriple H) = conjMap hk := by
  ext x
  simp only [MulActionHom.comp_apply, SetLike.coe_eq_coe]
  exact conjMap_comp_apply H x

@[to_additive]
theorem ofStabilizer.conjMap_bijective : Function.Bijective (conjMap hg) := by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [Subtype.mk_eq_mk]
    apply (MulAction.injective g)
    rwa [← SetLike.coe_eq_coe, conjMap_apply] at hxy
  · intro x
    refine ⟨conjMap _ x, inv_conjMap_comp_apply _ x⟩

/-- Append `a` to `x : Fin n ↪ ofStabilizer G a`  to get an element of `Fin n.succ ↪ α` -/
@[to_additive
  "Append `a` to `x : Fin n ↪ ofStabilizer G a`  to get an element of `Fin n.succ ↪ α`"]
def ofStabilizer.append {n : ℕ} (x : Fin n ↪ ofStabilizer G a) :
    Fin n.succ ↪ α := by
  let j : ofStabilizer G a ↪ α := {
    toFun := fun u => id u
    inj' := fun x y hxy => by simpa using hxy }
  apply Fin.Embedding.append (x.trans j) (a := a)
  simp [Set.mem_range, trans_apply, not_exists, j]
  exact fun i ↦ (x i).prop

@[to_additive]
theorem ofStabilizer.append_apply_of_lt {n : ℕ} (x : Fin n ↪ ofStabilizer G a)
    {i : Fin n.succ} (hi : i.val < n) :
    append x i = (x ⟨i, hi⟩ : α) := by
  simp [append, Fin.Embedding.append_apply_of_lt hi]

@[to_additive]
theorem ofStabilizer.append_apply_last {n : ℕ} (x : Fin n ↪ ofStabilizer G a) :
    append x (Fin.last n) = a := by
  simp [append, Fin.Embedding.append_apply_last]

variable (G) in
@[to_additive]
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

@[to_additive]
theorem ofStabilizer.isPretransitive_iff_of_conj {a b : α} {g : G} (hg : b = g • a) :
  IsPretransitive (stabilizer G a) (ofStabilizer G a) ↔
    IsPretransitive (stabilizer G b) (ofStabilizer G b) :=
  isPretransitive_congr (MulEquiv.surjective _) (ofStabilizer.conjMap_bijective hg)

@[to_additive]
theorem ofStabilizer.isPretransitive_iff [IsPretransitive G α] {a b : α} :
    IsPretransitive (stabilizer G a) (ofStabilizer G a) ↔
      IsPretransitive (stabilizer G b) (ofStabilizer G b) :=
  let ⟨_, hg⟩ := exists_smul_eq G a b
  isPretransitive_iff_of_conj hg.symm

@[to_additive]
theorem ofStabilizer.isMultiplyPretransitive_iff_of_conj
    {n : ℕ} {a b : α} {g : G} (hg : b = g • a) :
    IsMultiplyPretransitive (stabilizer G a) (ofStabilizer G a) n ↔
      IsMultiplyPretransitive (stabilizer G b) (ofStabilizer G b) n :=
  IsPretransitive.of_embedding_congr (MulEquiv.surjective _) (ofStabilizer.conjMap_bijective hg)

@[to_additive]
theorem ofStabilizer.isMultiplyPretransitive_iff [IsPretransitive G α] {n : ℕ} {a b : α} :
    IsMultiplyPretransitive (stabilizer G a) (ofStabilizer G a) n ↔
      IsMultiplyPretransitive (stabilizer G b) (ofStabilizer G b) n :=
  let ⟨_, hg⟩ := exists_smul_eq G a b
  isMultiplyPretransitive_iff_of_conj hg.symm

/-- Multiple transitivity of a pretransitive action
  is equivalent to one less transitivity of stabilizer of a point
  (Wielandt, th. 9.1, 1st part) -/
@[to_additive
  "Multiple transitivity of a pretransitive action
  is equivalent to one less transitivity of stabilizer of a point
  (Wielandt, th. 9.1, 1st part)"]
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
        rw [← append_apply_of_lt x (i := ⟨i, Nat.lt_succ_of_lt hi⟩),
          ← Function.Embedding.smul_apply, hgxy, append_apply_of_lt y] }
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


