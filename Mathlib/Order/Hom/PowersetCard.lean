/-
Copyright (c) 2026 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/
module

public import Mathlib.Data.Set.PowersetCard
public import Mathlib.Data.Finset.Sort
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite sets of an ordered type

This file defines the isomorphism between ordered embeddings into a linearly ordered type and
the finite sets of that type.

## Definitions

* `ofFinEmbEquiv` is the equivalence between `Fin n ↪o I` and `Set.powersetCard I n` when `I` is
  a linearly ordered type.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open Finset Function Set

namespace Set.powersetCard

section order

variable {n : ℕ} {I : Type*} [LinearOrder I]

/-- The isomorphism of `OrderEmbedding`s from `Fin n` into `I` with `Set.powersetCard I n`
when `I` is linearly ordered. -/
def ofFinEmbEquiv : (Fin n ↪o I) ≃ powersetCard I n where
  toFun f := ofFinEmb n I f.toEmbedding
  invFun s := Finset.orderEmbOfFin s.val s.prop
  left_inv f := by symm; apply Finset.orderEmbOfFin_unique'; simp
  right_inv s := by ext; simp

lemma ofFinEmbEquiv_apply (f : Fin n ↪o I) :
    ofFinEmbEquiv f = ofFinEmb n I f.toEmbedding :=
  rfl

lemma ofFinEmbEquiv_symm_apply (s : powersetCard I n) :
    ofFinEmbEquiv.symm s = Finset.orderEmbOfFin s.val s.prop := rfl

@[simp]
lemma mem_ofFinEmbEquiv_iff_mem_range (f : Fin n ↪o I) (i : I) :
    i ∈ ofFinEmbEquiv f ↔ i ∈ range f := by
  simp [ofFinEmbEquiv_apply]

lemma mem_range_ofFinEmbEquiv_symm_iff_mem (s : powersetCard I n) (i : I) :
    i ∈ range (ofFinEmbEquiv.symm s) ↔ i ∈ s := by
  simp [ofFinEmbEquiv_symm_apply]

/-- The natural enumeration of the elements of linearly-ordered type. -/
@[simps!] def orderIsoOfFin {n : ℕ} {I : Type*} [LinearOrder I] (s : powersetCard I n) :
    Fin n ≃o s.val :=
  s.val.orderIsoOfFin s.prop

/-- The permutation of `Fin (m + n)` corresponding to adjoining a `Finset` of card `m`
to a `Finset` of card `n` and sorting the resulting set. In other words, given `s₁ < s₂ < ⋯ < sₘ`
and `t₁ < t₂ < ⋯ < tₙ` (disjoint) this is the permutation obtained by sorting
`s₁, s₂, …, sₘ, t₁, t₂, …, tₙ`. -/
def permOfDisjoint {m n : ℕ} {I : Type*} [LinearOrder I]
    {s : powersetCard I m} {t : powersetCard I n} (h : Disjoint s.val t.val) :
    Equiv.Perm (Fin (m + n)) :=
  letI e₁ : Fin (m + n) ≃ Fin m ⊕ Fin n := finSumFinEquiv.symm
  letI e₂ : Fin m ⊕ Fin n ≃ s.val ⊕ t.val := (orderIsoOfFin s).sumCongr (orderIsoOfFin t)
  letI e₃ : s.val ⊕ t.val ≃ disjUnion h := Equiv.Finset.disjUnionEquiv _ _ h
  letI e₄ : disjUnion h ≃o Fin (m + n) := (orderIsoOfFin (disjUnion h)).symm
  e₁.trans <| e₂.trans <| e₃.trans <| e₄

end order

end Set.powersetCard
