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
This file defines subrepresentations of a monoid representation.

-/

@[expose] public section

open Pointwise
open scoped MonoidAlgebra

universe u

variable {A : Type u} [CommRing A]

variable {G : Type u} [Monoid G]

variable {W : Type u} [AddCommMonoid W] [Module A W]

variable {ρ : Representation A G W}

variable {M : Type u} [AddCommMonoid M] [Module A[G] M]

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

/-- A subrepresentation of `ρ` can be thought of as an `A[G]` submodule of `ρ.asModule`.
-/
def asSubmodule (σ : Subrepresentation ρ) : Submodule A[G] ρ.asModule where
  carrier := σ.toSubmodule.carrier
  add_mem' := σ.toSubmodule.add_mem'
  zero_mem' := σ.toSubmodule.zero_mem'
  smul_mem' := by
    intro c v hv
    induction c using MonoidAlgebra.induction_linear with
      | zero => rw [zero_smul]; exact σ.toSubmodule.zero_mem'
      | add x y hx hy => rw [add_smul]; exact σ.toSubmodule.add_mem' hx hy
      | single g a =>
        rw [Representation.single_smul]
        exact σ.toSubmodule.smul_mem' a (σ.apply_mem_toSubmodule g hv)

/-- A subrepresentation of `ofModule M` can be thought of as an `A[G]` submodule of `M`.
-/
def asSubmodule' (σ : Subrepresentation (Representation.ofModule (k := A) (G := G) M)) :
    Submodule A[G] M where
  carrier := σ.toSubmodule.carrier
  add_mem' := σ.toSubmodule.add_mem'
  zero_mem' := σ.toSubmodule.zero_mem'
  smul_mem' := by
    intro c m hm
    induction c using MonoidAlgebra.induction_linear with
      | zero => rw [zero_smul]; exact σ.toSubmodule.zero_mem'
      | add x y hx hy => rw [add_smul]; exact σ.toSubmodule.add_mem' hx hy
      | single g a =>
        have h := σ.apply_mem_toSubmodule g hm
        dsimp [Representation.ofModule, RestrictScalars.lsmul] at h
        have : MonoidAlgebra.single g a • m =
            (algebraMap A A[G]) a • MonoidAlgebra.single g (1 : A) • m := by
          simp only [MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self, RingHom.coe_id,
            Function.comp_apply, id_eq, smul_smul, MonoidAlgebra.single_mul_single, one_mul,
            mul_one]
        rw [this]
        exact σ.toSubmodule.smul_mem' ((algebraMap A A) a) h

/-- A submodule of an `A[G]`-module `M` can be thought of as a subrepresentation of `ofModule M`.
-/
def ofSubmodule (N : Submodule A[G] M) :
    Subrepresentation (Representation.ofModule (k := A) (G := G) M) where
  toSubmodule :={
    carrier := N.carrier
    add_mem' := N.add_mem'
    zero_mem' := N.zero_mem'
    smul_mem' := fun a m hm => N.smul_mem' (algebraMap A A[G] a) hm
  }
  apply_mem_toSubmodule := by
    intro g v hv
    change v ∈ N at hv
    change ((Representation.ofModule M) g) v ∈ N
    dsimp [Representation.ofModule, RestrictScalars.lsmul]
    exact Submodule.smul_of_tower_mem N (MonoidAlgebra.single g 1) hv

/-- An `A[G]`-submodule of `ρ.asModule` can be thought of as a subrepresentation of `ρ`.
-/
def ofSubmodule' (N : Submodule A[G] ρ.asModule) : Subrepresentation ρ where
  toSubmodule := {
    carrier := N.carrier
    add_mem' := N.add_mem'
    zero_mem' := N.zero_mem'
    smul_mem' := by
      intro a w hw
      simpa using (N.smul_mem (algebraMap A A[G] a) hw)
  }
  apply_mem_toSubmodule := by
    intro g w hw
    change w ∈ N at hw
    change (ρ g) w ∈ N
    letI _ : Module A[G] W := by exact ρ.instModuleMonoidAlgebraAsModule
    have h : (MonoidAlgebra.single g (1 : A)) • w ∈ N :=
      Submodule.smul_of_tower_mem N _ hw
    rw [Representation.single_smul, one_smul] at h
    exact h

/-- An order-preserving equivalence between subrepresentations of `ρ` and submodules of
`ρ.asModule`. -/
def subrepresentationSubmoduleOrderIso : Subrepresentation ρ ≃o Submodule A[G] ρ.asModule where
  toFun := asSubmodule
  invFun := ofSubmodule'
  left_inv := by
    dsimp [Function.LeftInverse]
    intro σ
    rfl
  right_inv := by
    dsimp [Function.RightInverse, Function.LeftInverse]
    intro N
    rfl
  map_rel_iff' := by
    intro σ τ
    rfl

/-- An order-preserving equivalence between `A[G]`-submodules of an `A[G]`-module M and
subrepresentations of `ρ`. -/
def submoduleSubrepresentationOrderIso : Submodule A[G] M ≃o
    Subrepresentation (Representation.ofModule (k := A) (G := G) M) where
  toFun := ofSubmodule
  invFun := asSubmodule'
  left_inv := by
    dsimp [Function.LeftInverse]
    intro N
    rfl
  right_inv := by
    dsimp [Function.RightInverse, Function.LeftInverse]
    intro σ
    rfl
  map_rel_iff' := by
    intro N K
    rfl

end Subrepresentation
