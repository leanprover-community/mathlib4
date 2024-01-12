/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Logic.Function.Basic


/-!
# Propositional typeclasses on several monoid homs

This file contains typeclasses used in the definition of (semi)linear maps:

TODO :
* align with RingHomCompTriple

-/

section CompTriple

/-- Class of composing triples -/
class CompTriple  {M N P : Type*} (φ : M → N) (ψ : N → P) (χ : outParam (M → P)) : Prop where
  /-- The maps form a commuting triangle -/
  comp_eq : ψ.comp φ = χ

attribute [simp] CompTriple.comp_eq

namespace CompTriple

/-- Class of Id maps -/
class isId {M : Type*} (σ : M → M) : Prop where
  eq_id : σ = id

instance {M : Type*} : isId (@id M) where
  eq_id := rfl

lemma comp_id {N P : Type*} {φ : N → N} [isId φ] {ψ : N → P} :
    CompTriple φ ψ ψ := {
  comp_eq := by simp only [isId.eq_id, Function.comp.right_id]}

lemma id_comp {M N : Type*} {φ : M → N} {ψ : N → N} [isId ψ] :
    CompTriple φ ψ φ := {
  comp_eq := by simp only [isId.eq_id, Function.comp.left_id]}

lemma comp {M N P : Type*}
    {φ : M → N} {ψ : N → P} :
  CompTriple φ ψ  (ψ.comp φ) := {comp_eq := rfl}

lemma comp_inv {M N : Type*} {φ : M → N} {ψ : N → M}
    (h : Function.RightInverse φ ψ) {χ : M → M} [isId χ] :
    CompTriple φ ψ χ := {
  comp_eq := by simp only [isId.eq_id, h.id] }

lemma apply {M N P : Type*}
    {φ : M → N} {ψ : N → P} {χ : M → P} (h : CompTriple φ ψ χ) (x : M) :
  ψ (φ x) = χ x := by
  rw [← h.comp_eq, Function.comp_apply]

end CompTriple
