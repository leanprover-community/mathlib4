/-
Copyright (c) 2025 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Subrepresentations

This file defines subrepresentations of a monoid representation.

-/

@[expose] public section

open Pointwise
open scoped MonoidAlgebra

variable {A G W M : Type*} [CommRing A] [Monoid G] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G W} [AddCommMonoid M] [Module A[G] M]

variable (ρ) in
/-- A subrepresentation of `G` of the `A`-module `W` is a submodule of `W`
which is stable under the `G`-action.
-/
structure Subrepresentation where
  /-- A subrepresentation is a submodule. -/
  toSubmodule : Submodule A W
  apply_mem_toSubmodule (g : G) ⦃v : W⦄ : v ∈ toSubmodule → ρ g v ∈ toSubmodule

namespace Subrepresentation

lemma toSubmodule_injective :
    Function.Injective (toSubmodule : Subrepresentation ρ → Submodule A W) := by
  rintro ⟨_,_⟩
  congr!

instance : SetLike (Subrepresentation ρ) W where
  coe ρ' := ρ'.toSubmodule
  coe_injective' := SetLike.coe_injective.comp toSubmodule_injective

/-- A subrepresentation is a representation. -/
def toRepresentation (ρ' : Subrepresentation ρ) : Representation A G ρ'.toSubmodule where
  toFun g := (ρ g).restrict (ρ'.apply_mem_toSubmodule g)
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

instance : Max (Subrepresentation ρ) where
  max ρ₁ ρ₂ := .mk (ρ₁.toSubmodule ⊔ ρ₂.toSubmodule) <| by
      simp only [Submodule.forall_mem_sup, map_add]
      intro g x₁ hx₁ x₂ hx₂
      exact Submodule.mem_sup.mpr
        ⟨ρ g x₁, ρ₁.apply_mem_toSubmodule g hx₁, ρ g x₂, ρ₂.apply_mem_toSubmodule g hx₂, rfl⟩

instance : Min (Subrepresentation ρ) where
  min ρ₁ ρ₂ := .mk (ρ₁.toSubmodule ⊓ ρ₂.toSubmodule) <| by
      simp only [Submodule.mem_inf, and_imp]
      rintro g x hx₁ hx₂
      exact ⟨ρ₁.apply_mem_toSubmodule g hx₁, ρ₂.apply_mem_toSubmodule g hx₂⟩


@[simp, norm_cast]
lemma coe_sup (ρ₁ ρ₂ : Subrepresentation ρ) : ↑(ρ₁ ⊔ ρ₂) = (ρ₁ : Set W) + (ρ₂ : Set W) :=
  Submodule.coe_sup ρ₁.toSubmodule ρ₂.toSubmodule

@[simp, norm_cast]
lemma coe_inf (ρ₁ ρ₂ : Subrepresentation ρ) : ↑(ρ₁ ⊓ ρ₂) = (ρ₁ ∩ ρ₂ : Set W) := rfl

@[simp]
lemma toSubmodule_sup (ρ₁ ρ₂ : Subrepresentation ρ) :
  (ρ₁ ⊔ ρ₂).toSubmodule = ρ₁.toSubmodule ⊔ ρ₂.toSubmodule := rfl

@[simp]
lemma toSubmodule_inf (ρ₁ ρ₂ : Subrepresentation ρ) :
  (ρ₁ ⊓ ρ₂).toSubmodule = ρ₁.toSubmodule ⊓ ρ₂.toSubmodule := rfl

instance : Lattice (Subrepresentation ρ) :=
  toSubmodule_injective.lattice _ toSubmodule_sup toSubmodule_inf

instance : BoundedOrder (Subrepresentation ρ) where
  top := ⟨⊤, by simp⟩
  le_top _ _ := by simp
  bot := ⟨⊥, by simp⟩
  bot_le _ _ := by simp +contextual

end Subrepresentation
