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

/-- A subrepresentation of `ρ` can be thought of as an `A[G]` submodule of `ρ.asModule`.
-/
def asSubmodule (σ : Subrepresentation ρ) : Submodule A[G] ρ.asModule where
  __ := σ.toSubmodule
  smul_mem' c v hv := by
    induction c using MonoidAlgebra.induction_linear with
    | zero => simp [zero_smul]
    | add x y hx hy => rw [add_smul]; exact σ.toSubmodule.add_mem' hx hy
    | single g a =>
      rw [Representation.single_smul]
      exact σ.toSubmodule.smul_mem' a (σ.apply_mem_toSubmodule g hv)

@[simp]
lemma mem_asSubmodule_iff {σ : Subrepresentation ρ} {v : W} : v ∈ asSubmodule σ ↔ v ∈ σ := by rfl

/-- A subrepresentation of `ofModule M` can be thought of as an `A[G]` submodule of `M`.
-/
def asSubmodule' (σ : Subrepresentation (Representation.ofModule (k := A) (G := G) M)) :
    Submodule A[G] M where
  __ := σ.toSubmodule
  smul_mem' c m hm := by
    induction c using MonoidAlgebra.induction_linear with
    | zero => rw [zero_smul]; exact σ.toSubmodule.zero_mem'
    | add x y hx hy => rw [add_smul]; exact σ.toSubmodule.add_mem' hx hy
    | single g a =>
      rw [← mul_one a, ← smul_eq_mul, ← MonoidAlgebra.smul_single, Algebra.smul_def, mul_smul]
      exact σ.toSubmodule.smul_mem' ((algebraMap A A) a) <| by
        simpa [Representation.ofModule, RestrictScalars.lsmul] using σ.apply_mem_toSubmodule g hm

@[simp]
lemma mem_asSubmodule'_iff {σ : Subrepresentation (Representation.ofModule (k := A) (G := G) M)}
    {m : M} : m ∈ asSubmodule' σ ↔ m ∈ σ := by rfl

/-- A submodule of an `A[G]`-module `M` can be thought of as a subrepresentation of `ofModule M`.
-/
def ofSubmodule (N : Submodule A[G] M) :
    Subrepresentation (Representation.ofModule (k := A) (G := G) M) where
  toSubmodule := {N with
    smul_mem' a m hm := N.smul_mem' (algebraMap A A[G] a) hm}
  apply_mem_toSubmodule g v hv := by
    simpa [Representation.ofModule, RestrictScalars.lsmul] using
      Submodule.smul_of_tower_mem N (MonoidAlgebra.single g 1) hv

@[simp]
lemma mem_ofSubmodule_iff {N : Submodule A[G] M} {m : M} : m ∈ ofSubmodule N ↔ m ∈ N := by rfl

/-- An `A[G]`-submodule of `ρ.asModule` can be thought of as a subrepresentation of `ρ`.
-/
def ofSubmodule' (N : Submodule A[G] ρ.asModule) : Subrepresentation ρ where
  toSubmodule := {N with
    smul_mem' a w hw := by simpa using (N.smul_mem (algebraMap A A[G] a) hw)}
  apply_mem_toSubmodule g w hw := by
    letI _ : Module A[G] W := ρ.instModuleMonoidAlgebraAsModule
    have h : (MonoidAlgebra.single g (1 : A)) • w ∈ N :=
      Submodule.smul_of_tower_mem N _ hw
    rw [Representation.single_smul, one_smul] at h
    exact h

@[simp]
lemma mem_ofSubmodule'_iff {N : Submodule A[G] ρ.asModule} {w : W} : w ∈ ofSubmodule' N ↔ w ∈ N :=
  by rfl

/-- An order-preserving equivalence between subrepresentations of `ρ` and submodules of
`ρ.asModule`. -/
@[simps]
def subrepresentationSubmoduleOrderIso : Subrepresentation ρ ≃o Submodule A[G] ρ.asModule where
  toFun := asSubmodule
  invFun := ofSubmodule'
  left_inv σ := rfl
  right_inv N := rfl
  map_rel_iff' := by rfl

/-- An order-preserving equivalence between `A[G]`-submodules of an `A[G]`-module M and
subrepresentations of `ρ`. -/
@[simps]
def submoduleSubrepresentationOrderIso : Submodule A[G] M ≃o
    Subrepresentation (Representation.ofModule (k := A) (G := G) M) where
  toFun := ofSubmodule
  invFun := asSubmodule'
  left_inv N := rfl
  right_inv σ := rfl
  map_rel_iff' := by rfl

end Subrepresentation
