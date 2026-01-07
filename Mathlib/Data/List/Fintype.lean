/-
Copyright (c) 2025 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module
public import Mathlib.Data.FinEnum
public import Mathlib.Logic.Equiv.Fin.Basic
/-!
# List coercion to type

This module defines a `CoeSort` instance for lists and gives it a `Fintype` instance.
It also defines `Multiset.toEnumFinset`, which is another way to enumerate the elements of
a multiset. These coercions and definitions make it easier to sum over multisets using existing
`Finset` theory.

## Main definitions

* A coercion from `m : Multiset α` to a `Type*`. Each `x : m` has two components.
  The first, `x.1`, can be obtained via the coercion `↑x : α`,
  and it yields the underlying element of the multiset.
  The second, `x.2`, is a term of `Fin (m.count x)`,
  and its function is to ensure each term appears with the correct multiplicity.
  Note that this coercion requires `DecidableEq α` due to the definition using `Multiset.count`.
* `Multiset.toEnumFinset` is a `Finset` version of this.
* `Multiset.coeEmbedding` is the embedding `m ↪ α × ℕ`, whose first component is the coercion
  and whose second component enumerates elements with multiplicity.
* `Multiset.ofIdxEquiv` is the equivalence `m ≃ m.toEnumFinset`.

## Tags

list enumeration
-/

@[expose] public section

universe u v

variable {α : Type u} {β : Type v} {l : List α}

namespace List

@[irreducible, coe] def ToType : List α → Type := (Fin <| ·.length)

instance coeSortType : CoeSort (List α) Type := ⟨ToType⟩

unseal ToType in
@[irreducible] def equivFin {l : List α} : ↥l ≃ Fin (l.length) where
  toFun := id
  invFun := id

def ToType.idx : l → Fin (l.length) := equivFin
def ofFin : Fin (l.length) → l := equivFin.symm

@[simp, grind =] theorem coe_equivFin : ⇑(equivFin (l := l)) = ToType.idx := rfl
@[simp, grind =] theorem coe_equivFin_symm : ⇑(equivFin (l := l)).symm = ofFin := rfl

@[simp, grind =] theorem idx_ofFin (i : Fin (l.length)) : (ofFin i).idx = i :=
  equivFin.apply_symm_apply _
@[simp, grind =] theorem ofFin_idx (x : l) : ofFin x.idx = x := equivFin.symm_apply_apply _
theorem equivFin_ofFin (i : Fin (l.length)) : equivFin (ofFin i) = i := idx_ofFin i

@[simp, grind =] theorem equivFin_apply {x : l} : equivFin x = x.idx := rfl
@[simp, grind =] theorem equivFin_symm_apply {i : Fin (l.length)} : equivFin.symm i = ofFin i := rfl

@[simp, grind =] theorem ofFin_inj {i j : Fin (l.length)} : ofFin i = ofFin j ↔ i = j :=
  equivFin.symm.injective.eq_iff
@[simp, grind =] theorem ToType.idx_inj {x y : l} : x.idx = y.idx ↔ x = y :=
  equivFin.injective.eq_iff

@[ext, grind ext] protected theorem ToType.ext {x y : l} (h : x.idx = y.idx) : x = y :=
  equivFin.injective h

@[coe] def ToType.coe (x : l) : α := l[x.idx.val]

instance : CoeOut l α := ⟨ToType.coe⟩

@[simp, grind =] theorem ToType.getElem_val_idx (x : l) : l[x.idx.val] = x := rfl
@[simp, grind =] theorem coe_ofFin (i : Fin (l.length)) : ofFin i = l[i] :=
  (ofFin i).getElem_val_idx.symm.trans (by grind)

@[simp, grind .] theorem ToType.coe_mem {x : l} : ↑x ∈ l := getElem_mem _

@[cases_eliminator, elab_as_elim]
def ToType.ofFinCases {motive : l → Sort v} (ofFin : ∀ i, motive (ofFin i)) (x : l) : motive x :=
  ofFin_idx x ▸ ofFin (x.idx)

@[simp, grind =]
theorem ofFinCases_ofFin {motive : l → Sort v} (ofFin : ∀ i, motive (ofFin i))
    {i : Fin (l.length)} : (l.ofFin i).ofFinCases (motive := motive) ofFin = (ofFin i) := by
  grind [ToType.ofFinCases]


instance : DecidableEq l := equivFin.decidableEq

instance : FinEnum l where
  card := l.length
  equiv := equivFin

@[simp] theorem finEnum_card : FinEnum.card l = l.length := rfl

@[simp] theorem fintype_card : Fintype.card l = l.length := FinEnum.card_eq_fintypeCard.symm

instance : IsEmpty ([] : List α) := (equivFin.trans <| finCongr length_nil).isEmpty
instance {a : α} : Unique [a] := (equivFin.trans <| finCongr length_singleton).unique

instance [NeZero (l.length)] : Inhabited l := equivFin.inhabited

@[simp] theorem default_eq [NeZero (l.length)] : (default : l) = ofFin 0 := rfl

@[grind =] theorem coe_default [NeZero (l.length)] :
    (default : l) = l[0]'(Nat.pos_of_neZero _) := coe_ofFin 0

instance [l.length.AtLeastTwo] : Nontrivial l := equivFin.nontrivial

theorem subsingleton_iff_length_le_one : Subsingleton l ↔ l.length ≤ 1 := by
  rw [equivFin.subsingleton_congr, Fin.subsingleton_iff_le_one]

theorem nontrivial_iff_two_le_length : Nontrivial l ↔ 2 ≤ l.length := by
  rw [equivFin.nontrivial_congr, Fin.nontrivial_iff_two_le]

def nilEquiv : ([] : List α) ≃ Empty := equivFin.trans finZeroEquiv

instance {a : α} {l : List α} : NeZero ((a :: l).length) := ⟨Nat.succ_ne_zero _⟩

@[simps]
def consEmbedding (a : α) : l ↪ a :: l where
  toFun x := ofFin x.idx.succ
  inj' x := by simp
