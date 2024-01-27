/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/


import Mathlib.Logic.Function.CompTypeclasses
import Mathlib.Algebra.Group.Hom.Defs

/-!
# Propositional typeclasses on several monoid homs

This file contains typeclasses used in the definition of (semi)linear maps:

TODO :
* align with RingHomCompTriple
* probably rename MonoidHom.CompTriple as MonoidHomCompTriple
(or, on the opposite, rename RingHomCompTriple as RingHom.CompTriple)
* does one need AddHom.CompTriple ?

-/


section MonoidHomCompTriple

namespace MonoidHom

/-- Class of composing triples -/
class CompTriple  {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]
  (φ : M →* N) (ψ : N →* P) (χ : outParam (M →* P)) : Prop where
  /-- The maps form a commuting triangle -/
  comp_eq : ψ.comp φ = χ

attribute [simp] CompTriple.comp_eq

namespace CompTriple

variable {M' : Type*} [Monoid M']
variable {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]

/-- Class of Id maps -/
class isId (σ : M →* M) : Prop where
  eq_id : σ = MonoidHom.id M

instance {M : Type*} [Monoid M] : isId (MonoidHom.id M) where
  eq_id := rfl

instance {σ : M →* M} [isId σ] : CompTriple.isId σ := {
  eq_id := by simp only [isId.eq_id, MonoidHom.coe_mk, OneHom.coe_mk] }

instance {φ : M →* N} {ψ : N  →* P} {χ : M →* P} [κ : CompTriple φ ψ χ] :
    _root_.CompTriple φ ψ χ := {
  comp_eq := by rw [← MonoidHom.coe_comp, κ.comp_eq] }

lemma comp {φ : M →* N} {ψ : N →* P} :
    CompTriple φ ψ (ψ.comp φ) := {comp_eq := rfl}


lemma comp_id {N P : Type*} [Monoid N] [Monoid P]
    {φ : N →* N} [isId φ] {ψ : N →* P} :
    CompTriple φ ψ ψ := {
  comp_eq := by simp only [isId.eq_id, MonoidHom.comp_id] }

lemma id_comp {M N : Type*} [Monoid M] [Monoid N]
    {φ : M →* N} {ψ : N →* N} [isId ψ] :
    CompTriple φ ψ φ := {
  comp_eq := by simp only [isId.eq_id, MonoidHom.id_comp] }

lemma comp_inv {φ : M →* N} {ψ : N →* M} (h : Function.RightInverse φ ψ)
    {χ : M →* M} [isId χ] :
    CompTriple φ ψ χ := {
  comp_eq := by
    simp only [isId.eq_id, ← DFunLike.coe_fn_eq, coe_comp, h.id, coe_mk, OneHom.coe_mk] }

lemma apply
    {φ : M →* N} {ψ : N →* P} {χ : M →* P} (h : CompTriple φ ψ χ) (x : M) :
  ψ (φ x) = χ x := by
  rw [← h.comp_eq, MonoidHom.comp_apply]

@[simp]
theorem comp_assoc {Q : Type*} [Monoid Q]
    {φ₁ : M →* N} {φ₂ : N →* P} {φ₁₂ : M →* P}
    (κ : CompTriple φ₁ φ₂ φ₁₂)
    {φ₃ : P →* Q} {φ₂₃ : N →* Q} (κ' : CompTriple φ₂ φ₃ φ₂₃)
    {φ₁₂₃ : M →* Q} :
    CompTriple φ₁ φ₂₃ φ₁₂₃ ↔ CompTriple φ₁₂ φ₃ φ₁₂₃ := by
  constructor
  all_goals {
    rintro ⟨h⟩
    exact ⟨ by simp only [← κ.comp_eq, ← h, ← κ'.comp_eq]; rfl ⟩ }

end MonoidHom.CompTriple
