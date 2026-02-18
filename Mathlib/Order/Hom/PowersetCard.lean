/-
Copyright (c) 2026 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/
module

public import Mathlib.Data.Set.PowersetCard
public import Mathlib.Data.Finset.Sort

/-!
# Finite sets of an ordered type

This file defines the isomorphism between ordered embeddings into a linearly ordered type and
the finite sets of that type.

## Definitions

* `ofFinEmbEquiv` is the equivalence between `Fin n ↪o I` and `Set.powersetCard I n` when `I` is
  a linearly ordered type.

-/

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

end order

end Set.powersetCard
