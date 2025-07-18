/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Logic.Function.Defs

/-!
# Propositional typeclasses on several maps

This file contains typeclasses that are used in the definition of
equivariant maps in the spirit what was initially developed
by Frédéric Dupuis and Heather Macbeth for linear maps.

* `CompTriple φ ψ χ`, which expresses that `ψ.comp φ = χ`
* `CompTriple.IsId φ`, which expresses that `φ = id`

TODO :
* align with RingHomCompTriple

-/

section CompTriple

/-- Class of composing triples -/
class CompTriple {M N P : Type*} (φ : M → N) (ψ : N → P) (χ : outParam (M → P)) : Prop where
  /-- The maps form a commuting triangle -/
  comp_eq : ψ.comp φ = χ

attribute [simp] CompTriple.comp_eq

namespace CompTriple

/-- Class of Id maps -/
class IsId {M : Type*} (σ : M → M) : Prop where
  eq_id : σ = id

instance {M : Type*} : IsId (@id M) where
  eq_id := rfl

instance instComp_id {N P : Type*} {φ : N → N} [IsId φ] {ψ : N → P} :
    CompTriple φ ψ ψ where
  comp_eq := by simp only [IsId.eq_id, Function.comp_id]

instance instId_comp {M N : Type*} {φ : M → N} {ψ : N → N} [IsId ψ] :
    CompTriple φ ψ φ where
  comp_eq := by simp only [IsId.eq_id, Function.id_comp]

/-- `φ`, `ψ` and `ψ ∘ φ` for` a `CompTriple` -/
theorem comp {M N P : Type*}
    {φ : M → N} {ψ : N → P} :
    CompTriple φ ψ (ψ.comp φ) where
  comp_eq := rfl

lemma comp_inv {M N : Type*} {φ : M → N} {ψ : N → M}
    (h : Function.RightInverse φ ψ) {χ : M → M} [IsId χ] :
    CompTriple φ ψ χ where
  comp_eq := by simp only [IsId.eq_id, h.id]

lemma comp_apply {M N P : Type*}
    {φ : M → N} {ψ : N → P} {χ : M → P} (h : CompTriple φ ψ χ) (x : M) :
    ψ (φ x) = χ x := by
  rw [← h.comp_eq, Function.comp_apply]

end CompTriple

end CompTriple
