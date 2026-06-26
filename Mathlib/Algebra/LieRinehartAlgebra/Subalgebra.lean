/-
Copyright (c) 2026 Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonid Ryvkin
-/

module

public import Mathlib.Algebra.LieRinehartAlgebra.Defs

/-!
# Lie-Rinehart subalgebras

This file defines Lie-Rinehart subalgebras of a Lie-Rinehart algebra and provides basic related
definitions and results.

## Main definitions/ statements:

* `LieRinehartSubalgebra` as an `A`-submodule of `L` stable under the Lie bracket. (This is also
applicable to Lie-Rinehart rings and more generally any `A`-module with a Lie ring structure).

* A Lie-Rinehart subalgebra of a Lie-Rinehart ring is a Lie-Rinehart ring

* A Lie-Rinehart subalgebra of a Lie-Rinehart algebra is a Lie-Rinehart algebra over the same ring.

-/

public section

open scoped LieRinehartAlgebra

variable (A L : Type*) [CommRing A] [LieRing L] [Module A L]

/-- A Lie-Rinehart subalgebra of a Lie-Rinehart algebra `(R A L)` is an `A`-submodule of `L`, which
is stable under the Lie bracket. (This can be defined independently of `R` and most
Lie-Rinehart algebra axioms). -/
structure LieRinehartSubalgebra extends Submodule A L where
  lie_mem' {a b} : a ∈ carrier → b ∈ carrier → ⁅a, b⁆ ∈ carrier

instance : Zero (LieRinehartSubalgebra A L) :=
  ⟨⟨0, fun {x y hx _hy} ↦ by simp [(Submodule.mem_bot A).mp hx]⟩⟩

instance : Inhabited (LieRinehartSubalgebra A L) :=
  ⟨0⟩

namespace LieRinehartSubalgebra

instance : SetLike (LieRinehartSubalgebra A L) L where
  coe L' := L'.carrier
  coe_injective L' L'' h := by
    rcases L'
    rcases L''
    congr
    exact SetLike.coe_injective h

instance : PartialOrder (LieRinehartSubalgebra A L) := .ofSetLike (LieRinehartSubalgebra A L) L

instance : AddSubgroupClass (LieRinehartSubalgebra A L) L where
  add_mem := Submodule.add_mem _
  zero_mem L' := L'.zero_mem'
  neg_mem {L'} x hx := show -x ∈ L'.toSubmodule from neg_mem hx

instance : SMulMemClass (LieRinehartSubalgebra A L) A L where
  smul_mem {s} := SMulMemClass.smul_mem (s := s.toSubmodule)

/-- A Lie-Rinehart subalgebra forms a Lie ring. -/
instance lieRing (L' : LieRinehartSubalgebra A L) : LieRing L' where
  bracket x y := ⟨⁅x.val, y.val⁆, L'.lie_mem' x.property y.property⟩
  lie_add x y z := by aesop
  add_lie x y z := by aesop
  lie_self x := by aesop
  leibniz_lie x y z := by aesop

variable {A L}
variable (L' : LieRinehartSubalgebra A L)

protected theorem zero_mem : (0 : L) ∈ L' :=
  zero_mem L'

protected theorem add_mem {x y : L} : x ∈ L' → y ∈ L' → (x + y : L) ∈ L' :=
  add_mem

protected theorem sub_mem {x y : L} : x ∈ L' → y ∈ L' → (x - y : L) ∈ L' :=
  sub_mem

protected theorem smul_mem (t : A) {x : L} (h : x ∈ L') : t • x ∈ L' :=
  SMulMemClass.smul_mem _ h

theorem lie_mem {x y : L} (hx : x ∈ L') (hy : y ∈ L') : (⁅x, y⁆ : L) ∈ L' :=
  L'.lie_mem' hx hy

theorem mem_carrier {x : L} : x ∈ L'.carrier ↔ x ∈ (L' : Set L) :=
  Iff.rfl

theorem mem_mk_iff (S : Set L) (h₁ h₂ h₃ h₄) {x : L} :
    x ∈ (⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩, h₄⟩ : LieRinehartSubalgebra A L) ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem mem_toSubmodule {x : L} : x ∈ L'.toSubmodule ↔ x ∈ L' :=
  Iff.rfl

@[simp]
theorem mem_mk_iff' (p : Submodule A L) (h) {x : L} :
    x ∈ (⟨p, h⟩ : LieRinehartSubalgebra A L) ↔ x ∈ p :=
  Iff.rfl

theorem mem_coe {x : L} : x ∈ (L' : Set L) ↔ x ∈ L' :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_bracket (x y : L') : (↑⁅x, y⁆ : L) = ⁅(↑x : L), ↑y⁆ :=
  rfl

theorem ext_iff (x y : L') : x = y ↔ (x : L) = y := Subtype.ext_iff

theorem coe_zero_iff_zero (x : L') : (x : L) = 0 ↔ x = 0 := (ext_iff L' x 0).symm

@[ext]
theorem ext (L₁' L₂' : LieRinehartSubalgebra A L) (h : ∀ x, x ∈ L₁' ↔ x ∈ L₂') : L₁' = L₂' :=
  SetLike.ext h

theorem ext_iff' (L₁' L₂' : LieRinehartSubalgebra A L) : L₁' = L₂' ↔ ∀ x, x ∈ L₁' ↔ x ∈ L₂' :=
  SetLike.ext_iff

@[simp]
theorem mk_coe (S : Set L) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩, h₄⟩ : LieRinehartSubalgebra A L) : Set L) = S :=
  rfl

theorem toSubmodule_mk (p : Submodule A L) (h) :
    ({ p with lie_mem' := h } : LieRinehartSubalgebra A L).toSubmodule = p := rfl

theorem coe_injective : Function.Injective ((↑) : LieRinehartSubalgebra A L → Set L) :=
  SetLike.coe_injective

@[norm_cast]
theorem coe_set_eq (L₁' L₂' : LieRinehartSubalgebra A L) : (L₁' : Set L) = L₂' ↔ L₁' = L₂' :=
  SetLike.coe_set_eq

theorem toSubmodule_injective : Function.Injective (toSubmodule (A := A) (L := L)) := by
  intro L₁' L₂' h
  rw [SetLike.ext'_iff] at h
  rw [← coe_set_eq]
  exact h

theorem coe_toSubmodule : (L'.toSubmodule : Set L) = L' :=
  rfl

section LieModule

variable {M : Type*} [AddCommGroup M] [LieRingModule L M]

instance : Bracket L' M where
  bracket x m := ⁅(x : L), m⁆

@[simp]
theorem coe_bracket_of_module (x : L') (m : M) : ⁅x, m⁆ = ⁅(x : L), m⁆ :=
  rfl

instance : IsLieTower L' L M where
  leibniz_lie x y m := leibniz_lie x.val y m

/-- Given a Lie-Rinehart algebra `L` containing a LieRinehart subalgebra `L' ⊆ L`, together with a
Lie ring module `M` of `L`, we may regard `M` as a Lie ring module of `L'` by restriction. -/
instance lieRingModule : LieRingModule L' M where
  add_lie x y m := add_lie (x : L) y m
  lie_add x y m := lie_add (x : L) y m
  leibniz_lie x y m := leibniz_lie x (y : L) m

end LieModule

variable [LieRingModule L A] [LieRinehartRing A L]

/-- A Lie-Rinehart subalgebra of a Lie-Rinehart ring forms a new Lie-Rinehart ring. -/
instance : LieRinehartRing A L' where
  lie_smul_eq_mul' a b x := LieRinehartRing.lie_smul_eq_mul a b (x : L)
  leibniz_mul_right' x a b := LieRinehartRing.leibniz_mul_right (x : L) a b
  leibniz_smul_right' _ _ _ := by simp [ext_iff]

variable (R : Type*) [CommRing R] [Algebra R A] [LieAlgebra R L] [LieRinehartAlgebra R A L]

/-- A Lie-Rinehart subalgebra of a Lie-Rinehart algebra forms a Lie algebra. -/
instance lieAlgebra : LieAlgebra R L' where
  lie_smul := by aesop

/-- Converts a Lie-Rinehart subalgebra to the corresponding Lie subalgebra. -/
@[expose] def toLieSubalgebra : LieSubalgebra R L where
  toSubmodule := L'.toSubmodule.restrictScalars R
  lie_mem' := L'.lie_mem'

theorem toLieSubalgebra_injective : Function.Injective (fun L' =>
    L'.toLieSubalgebra R : LieRinehartSubalgebra A L → LieSubalgebra R L) :=  fun L₁' L₂' h ↦ by
  rw [SetLike.ext'_iff] at h
  rw [← coe_set_eq]
  exact h

@[simp]
theorem toLieSubalgebra_inj (L₁' L₂' : LieRinehartSubalgebra A L) :
    (L₁'.toLieSubalgebra R) = (L₂'.toLieSubalgebra R) ↔ L₁' = L₂' :=
  (toLieSubalgebra_injective R).eq_iff

theorem coe_toLieSubalgebra : ((L'.toLieSubalgebra R) : Set L) = L' := rfl

section LieModule

variable {M : Type*} [AddCommGroup M] [LieRingModule L M] [Module R M]

/-- Given a Lie-Rinehart algebra  `L` containing a LieRinehart subalgebra `L' ⊆ L`, together with a
 Lie module `M` of `L`, we may regard `M` as a Lie module of `L'` by restriction. -/
instance lieModule [LieModule R L M] : LieModule R L' M where
  smul_lie t x m := by
    rw [coe_bracket_of_module, Submodule.coe_smul_of_tower, smul_lie, coe_bracket_of_module]
  lie_smul t x m := by simp only [coe_bracket_of_module, lie_smul]

end LieModule

/-- A Lie-Rinehart subalgebra forms a new Lie-Rinehart algebra. -/
instance : LieRinehartAlgebra R A L' where

/-- The embedding of a Lie-Rinehart subalgebra into the ambient space as a morphism of
Lie-Rinehart algebras. -/
@[expose] def incl : L' →ₗ⁅(AlgHom.id R A)⁆ L where
  __ := L'.toSubmodule.subtype.restrictScalars R
  map_lie' {x y} := coe_bracket L' x y
  map_smul_apply' a x := L'.toSubmodule.subtype.map_smul a x
  apply_lie' a x := AlgHom.id_apply ⁅x, a⁆

@[simp]
theorem coe_incl : ⇑(L'.incl R) = ((↑) : L' → L) := rfl

end LieRinehartSubalgebra
