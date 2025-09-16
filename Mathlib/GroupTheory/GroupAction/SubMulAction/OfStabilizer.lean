/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Embedding
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fin.Tuple.Embedding

/-! # The SubMulAction of the stabilizer of a point on the complement of that point

When a group `G` acts on a type `α`, the stabilizer of a point `a : α`
acts naturally on the complement of that point.

Such actions (as the similar one for the fixator of a set acting on the complement
of that set, defined in `Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup`)
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

/-- Action of the stabilizer of a point on the complement. -/
@[to_additive /-- Action of the stabilizer of a point on the complement. -/]
def ofStabilizer (a : α) : SubMulAction (stabilizer G a) α where
  carrier := {a}ᶜ
  smul_mem' g x := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [not_imp_not, smul_eq_iff_eq_inv_smul]
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
theorem notMem_val_image {a : α} (t : Set (ofStabilizer G a)) :
    a ∉ Subtype.val '' t := by
  rintro ⟨b, hb⟩
  exact b.prop (by simp [hb])

@[to_additive]
theorem neq_of_mem_ofStabilizer (a : α) {x : ofStabilizer G a} : ↑x ≠ a :=
  x.prop

@[to_additive]
lemma Enat_card_ofStabilizer_eq_add_one (a : α) :
    ENat.card (ofStabilizer G a) + 1 = ENat.card α := by
  dsimp only [ENat.card]
  rw [← Cardinal.mk_sum_compl {a}, map_add, add_comm, eq_comm]
  congr
  simp

@[to_additive]
lemma nat_card_ofStabilizer_eq [Finite α] (a : α) :
    Nat.card (ofStabilizer G a) = Nat.card α - 1 := by
  dsimp only [Nat.card]
  rw [← Cardinal.mk_sum_compl {a},
    Cardinal.toNat_add Cardinal.mk_lt_aleph0 Cardinal.mk_lt_aleph0]
  simp only [Cardinal.mk_fintype, Fintype.card_unique, Nat.cast_one, map_one, add_tsub_cancel_left]
  congr

variable {G}

/-- Conjugation induces an equivariant map between the SubAddAction of
the stabilizer of a point and that of its translate. -/
def _root_.SubAddAction.ofStabilizer.conjMap {G : Type*} [AddGroup G] {α : Type*} [AddAction G α]
    {g : G} {a b : α} (hg : b = g +ᵥ a) :
    AddActionHom (AddAction.stabilizerEquivStabilizer hg)
      (SubAddAction.ofStabilizer G a) (SubAddAction.ofStabilizer G b) where
  toFun x := ⟨g +ᵥ x.val, fun hy ↦ x.prop (by simpa [hg] using hy)⟩
  map_vadd' := fun ⟨k, hk⟩ x ↦ by
    simp [← SetLike.coe_eq_coe, AddAction.addSubgroup_vadd_def,
      AddAction.stabilizerEquivStabilizer_apply, ← vadd_assoc]

/-- Conjugation induces an equivariant map between the SubMulAction of
the stabilizer of a point and that of its translate. -/
@[to_additive existing]
def ofStabilizer.conjMap {g : G} {a b : α} (hg : b = g • a) :
    MulActionHom (stabilizerEquivStabilizer hg) (ofStabilizer G a) (ofStabilizer G b) where
  toFun x := ⟨g • x.val, fun hy ↦ x.prop (by simpa [hg] using hy)⟩
  map_smul' := fun ⟨k, hk⟩ ↦ by
    simp [← SetLike.coe_eq_coe, subgroup_smul_def, stabilizerEquivStabilizer, ← smul_assoc]

variable {g h k : G} {a b c : α}
variable (hg : b = g • a) (hh : c = h • b) (hk : c = k • a)

@[to_additive]
theorem ofStabilizer.conjMap_apply (x : ofStabilizer G a) :
    (conjMap hg x : α) = g • x := rfl

theorem _root_.AddAction.stabilizerEquivStabilizer_compTriple
    {G : Type*} [AddGroup G] {α : Type*} [AddAction G α]
    {g h k : G} {a b c : α} {hg : b = g +ᵥ a} {hh : c = h +ᵥ b} {hk : c = k +ᵥ a} (H : k = h + g) :
    CompTriple (AddAction.stabilizerEquivStabilizer hg)
      (AddAction.stabilizerEquivStabilizer hh) (AddAction.stabilizerEquivStabilizer hk) where
  comp_eq := by
    ext
    simp [AddAction.stabilizerEquivStabilizer, H, AddAut.conj, ← add_assoc]

variable {hg hh hk} in
@[to_additive existing]
theorem _root_.MulAction.stabilizerEquivStabilizer_compTriple (H : k = h * g) :
    CompTriple (stabilizerEquivStabilizer hg)
      (stabilizerEquivStabilizer hh) (stabilizerEquivStabilizer hk) where
  comp_eq := by
    ext
    simp [stabilizerEquivStabilizer, H, MulAut.conj, ← mul_assoc]

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
  simpa using conjMap_comp_apply H x

@[to_additive]
theorem ofStabilizer.conjMap_bijective : Function.Bijective (conjMap hg) := by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [Subtype.mk_eq_mk]
    apply (MulAction.injective g)
    rwa [← SetLike.coe_eq_coe, conjMap_apply] at hxy
  · intro x
    exact ⟨conjMap _ x, inv_conjMap_comp_apply _ x⟩

/-- Append `a` to `x : Fin n ↪ ofStabilizer G a`  to get an element of `Fin n.succ ↪ α`. -/
@[to_additive
  /-- Append `a` to `x : Fin n ↪ ofStabilizer G a`  to get an element of `Fin n.succ ↪ α`. -/]
def ofStabilizer.snoc {n : ℕ} (x : Fin n ↪ ofStabilizer G a) :
    Fin n.succ ↪ α :=
  Fin.Embedding.snoc (x.trans (subtype _)) (a := a) (by
    simp [Set.mem_range, trans_apply, not_exists]
    exact fun i ↦ (x i).prop)

@[to_additive]
theorem ofStabilizer.snoc_castSucc {n : ℕ} (x : Fin n ↪ ofStabilizer G a) (i : Fin n) :
    snoc x i.castSucc = x i := by
  simp [snoc]

@[to_additive]
theorem ofStabilizer.snoc_last {n : ℕ} (x : Fin n ↪ ofStabilizer G a) :
    snoc x (Fin.last n) = a := by
  simp [snoc]

variable (G) in
@[to_additive]
lemma exists_smul_of_last_eq [IsPretransitive G α] {n : ℕ} (a : α) (x : Fin n.succ ↪ α) :
    ∃ (g : G) (y : Fin n ↪ ofStabilizer G a), g • x = ofStabilizer.snoc y := by
  obtain ⟨g, hgx⟩ := exists_smul_eq G (x (Fin.last n)) a
  have H : ∀ i, Fin.Embedding.init (g • x) i ∈ ofStabilizer G a := fun i ↦ by
    simp only [mem_ofStabilizer_iff,
      Nat.succ_eq_add_one, ← hgx, ← smul_apply, ne_eq]
    suffices Fin.Embedding.init (g • x) i = (g • x) i.castSucc by
      simp [this]
    simp [Fin.Embedding.init, Fin.init_def]
  use g, (Fin.Embedding.init (g • x)).codRestrict (ofStabilizer G a) H
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | ⟨rfl⟩
  · simpa [ofStabilizer.snoc] using
      Subtype.eq_iff.mp <| Function.Embedding.codRestrict_apply _ _ H i
  · simpa only [smul_apply, ofStabilizer.snoc, Fin.Embedding.snoc_last]

end SubMulAction
