/-
Copyright (c) 2026 Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonid Ryvkin
-/
module

public import Mathlib.Algebra.LieRinehartAlgebra.Subalgebra

/-!
# Lie-Rinehart ideals

/-- A strict Lie-Rinehart Ideal of a Lie-Rinehart algebra `(R A L)` is an `A`-submodule of `L`,
which is a Lie ideal with respect to the Lie bracket and whose action on `A` is trivial.
(This can be defined independently of `R` and most Lie-Rinehart algebra axioms). -/

## Main definitions/ statements:

* `StrictLieRinehartIdeal` as an `A`-submodule of `L` forming an ideal  under the Lie bracket, and
acting trivially on `A.

* The inverse image of an ideal under a Lie-Rinehart algebra homomorphism over
`f: L₁→ₗ⁅(AlgHom.id R A)⁆ L₂` is a Lie-Rinehart ideal. In particular the kernel of such an `f`
is an ideal.

## Remark on strictness:

The strict notion corresponds to ideals which realize kernels of Lie Rinehart homomorphisms over
the identity algebra map of `A`. We use the word strict, because more flexible notions of ideals
exists:
https://www.uni-math.gwdg.de/mjotz/JotzLean18c.pdf
https://arxiv.org/pdf/1706.07084

-/

@[expose] public section

/-- A strict Lie-Rinehart Ideal of a Lie-Rinehart ring `(A L)` is an `A`-submodule of `L`,
which is a Lie ideal with respect to the Lie bracket and acts trivially on `A`. -/
structure StrictLieRinehartIdeal (A L : Type*) [CommRing A] [LieRing L] [Module A L]
    [LieRingModule L A] extends Submodule A L where
  ideal' {l l'} : l ∈ carrier → ⁅l, l'⁆ ∈ carrier
  isotropic (l : L) (a : A) : l ∈ carrier → ⁅l, a⁆ = 0

namespace StrictLieRinehartIdeal

/-- Forgetting that a Lie-Rinehart-ideal is also a Lie ideal.
-/
add_decl_doc StrictLieRinehartIdeal.toSubmodule

variable {A L} [CommRing A] [LieRing L] [Module A L] [LieRingModule L A]

instance : SetLike (StrictLieRinehartIdeal A L) L where
  coe s := s.carrier
  coe_injective s s' h := by
    rcases s
    rcases s'
    congr
    exact SetLike.coe_injective h

instance : PartialOrder (StrictLieRinehartIdeal A L) := .ofSetLike (StrictLieRinehartIdeal A L) L

instance : AddSubgroupClass (StrictLieRinehartIdeal A L) L where
  add_mem {s} := s.add_mem
  zero_mem {s} := s.zero_mem
  neg_mem {s} := s.neg_mem

instance : SMulMemClass (StrictLieRinehartIdeal A L) A L where
  smul_mem {s} := s.smul_mem'

instance : Zero (StrictLieRinehartIdeal A L) :=
  ⟨⟨0, @fun x y hx ↦ by
    rw [(Submodule.mem_bot A).1 hx, zero_lie]
    exact Submodule.zero_mem 0, by
      intro l a h; aesop⟩⟩

instance : Inhabited (StrictLieRinehartIdeal A L) := ⟨0⟩

/-- A Lie-Rinehart ideal forms a Lie ring. -/
instance lieRing {s : StrictLieRinehartIdeal A L} : LieRing s where
  bracket x y := ⟨⁅x.val, y.val⁆, s.ideal' x.property⟩
  lie_add x y z := by aesop
  add_lie x y z := by aesop
  lie_self x := by aesop
  leibniz_lie x y z := by aesop

@[simp]
lemma coe_bracket {s : StrictLieRinehartIdeal A L} (x y : s) : ⁅x, y⁆ = ⁅(x : L), (y : L)⁆ := rfl

theorem mem_carrier {s : StrictLieRinehartIdeal A L} {x : L} : x ∈ s.carrier ↔ x ∈ (s : Set L) :=
  Iff.rfl

@[ext]
theorem ext {s t : StrictLieRinehartIdeal A L} (h : ∀ x : L, x ∈ s ↔ x ∈ t) : s = t :=
  SetLike.ext h

@[simp]
lemma coe_mk (s : Submodule A L) (h₁) (h₂) : ((⟨s, h₁, h₂⟩ :
    StrictLieRinehartIdeal A L) : Set L) = s := rfl

@[simp]
theorem mem_toSubmodule {s : StrictLieRinehartIdeal A L} {x} : x ∈ s.toSubmodule ↔ x ∈ s := Iff.rfl

@[simp]
theorem coe_toSubmodule (s : StrictLieRinehartIdeal A L) : (s.toSubmodule : Set L) = s := rfl

theorem toSubmodule_injective :
    Function.Injective (toSubmodule : StrictLieRinehartIdeal A L → Submodule A L) := fun S T h =>
  ext fun x => by rw [← mem_toSubmodule, ← mem_toSubmodule, h]

theorem toSubmodule_inj {s t : StrictLieRinehartIdeal A L} : s.toSubmodule = t.toSubmodule ↔ s = t
  := toSubmodule_injective.eq_iff

theorem toSubmodule_le_iff {s t : StrictLieRinehartIdeal A L} :
    s.toSubmodule ≤ t.toSubmodule ↔ s ≤ t :=
  Iff.rfl

section LieModule

variable {s : StrictLieRinehartIdeal A L} {M : Type*} [AddCommGroup M] [LieRingModule L M]

instance : Bracket s M where
  bracket x m := ⁅(x : L), m⁆

@[simp]
theorem coe_bracket_of_module (x : s) (m : M) : ⁅x, m⁆ = ⁅(x : L), m⁆ :=
  rfl

instance : IsLieTower s L M where
  leibniz_lie x y m := leibniz_lie x.val y m

/-- Given a Lie-Rinehart algebra `L` containing a LieRinehart ideal `s ⊆ L`, together with a
Lie ring module `M` of `L`, we may regard `M` as a Lie ring module of `s` by restriction. -/
instance lieRingModule : LieRingModule s M where
  add_lie x y m := add_lie (x : L) y m
  lie_add x y m := lie_add (x : L) y m
  leibniz_lie x y m := leibniz_lie x (y : L) m

end LieModule

variable [LieRinehartRing A L]

/-- A Lie-Rinehart ideal of a Lie-Rinehart ring forms a new Lie-Rinehart ring. -/
instance {s : StrictLieRinehartIdeal A L} : LieRinehartRing A s where
  lie_smul_eq_mul' a b x := LieRinehartRing.lie_smul_eq_mul a b (x : L)
  leibniz_mul_right' x a b := LieRinehartRing.leibniz_mul_right (x : L) a b
  leibniz_smul_right' x y a := by ext; exact LieRinehartRing.leibniz_smul_right (x : L) y a

variable {R : Type*} [CommRing R] [Algebra R A] [LieAlgebra R L] [LieRinehartAlgebra R A L]

/-- A Lie-Rinehart ideal forms a Lie algebra. -/
instance lieAlgebra {s : StrictLieRinehartIdeal A L} : LieAlgebra R s where
  lie_smul _ _ _ := by ext; apply lie_smul

variable (R) in
/-- Converts a Lie-Rinehart ideal to the corresponding Lie ideal. -/
def toLieIdeal {s : StrictLieRinehartIdeal A L} : LieIdeal R L where
  toSubmodule := s.toSubmodule.restrictScalars R
  lie_mem {x y} hy := by
    rw [←lie_skew]
    refine neg_mem ?_
    exact s.ideal' hy

theorem toLieIdeal_injective : Function.Injective (fun s =>
    s.toLieIdeal R : StrictLieRinehartIdeal A L → LieIdeal R L) := fun s₁ s₂ h ↦ by
  rw [SetLike.ext_iff] at h; ext x; exact h x

@[simp]
theorem toLieIdeal_inj (s t : StrictLieRinehartIdeal A L) :
    (s.toLieIdeal R) = (t.toLieIdeal R) ↔ s = t := toLieIdeal_injective.eq_iff

theorem coe_toLieIdeal {s : StrictLieRinehartIdeal A L} : ((s.toLieIdeal R) : Set L) = s := rfl

section LieModule

variable {M : Type*} [AddCommGroup M] [LieRingModule L M] [Module R M] [LieModule R L M]

/-- Given a Lie-Rinehart algebra  `L` containing a LieRinehart subalgebra `s ⊆ L`, together with a
 Lie module `M` of `L`, we may regard `M` as a Lie module of `s` by restriction. -/
instance lieModule {s : StrictLieRinehartIdeal A L} : LieModule R s M where
  smul_lie t x m := by
    rw [coe_bracket_of_module, Submodule.coe_smul_of_tower, smul_lie, coe_bracket_of_module]
  lie_smul t x m := by simp only [coe_bracket_of_module, lie_smul]

end LieModule

/-- A Lie-Rinehart ideal forms a new Lie-Rinehart algebra. -/
instance {s : StrictLieRinehartIdeal A L} : LieRinehartAlgebra R A s where

open scoped LieRinehartAlgebra

variable (R) in
/-- The embedding of a Lie-Rinehart ideal into the ambient space as a morphism of
Lie-Rinehart algebras. -/
def incl {s : StrictLieRinehartIdeal A L} : s →ₗ⁅(AlgHom.id R A)⁆ L where
  __ := s.toSubmodule.subtype.restrictScalars R
  map_lie' {x y} := by simp
  map_smul_apply' a x := s.toSubmodule.subtype.map_smul a x
  apply_lie' a x := AlgHom.id_apply ⁅x, a⁆

@[simp]
theorem coe_incl {s : StrictLieRinehartIdeal A L} : ⇑(s.incl R) = ((↑) : s → L) := rfl

variable {L₁ L₂ : Type*} [LieRing L₁] [Module A L₁] [LieRingModule L₁ A] [LieAlgebra R L₁]
  [LieRing L₂] [Module A L₂] [LieRingModule L₂ A] [LieAlgebra R L₂]

/-- The preimage of a strict Lie-Rinehart ideal under a homomorphism `f` (which lies over the
identity of `A`) is a strict Lie-Rinehart ideal. -/
def comap (f : L₁→ₗ⁅(AlgHom.id R A)⁆ L₂) (s₂ : StrictLieRinehartIdeal A L₂) :
    StrictLieRinehartIdeal A L₁ := {
  s₂.toSubmodule.comap (f.toLinearMap') with
  ideal' {x y} h := by
    change f.toLinearMap' ⁅x, y⁆ ∈ s₂
    rw [LieRinehartAlgebra.Hom.toLinearMap'_apply, LieHom.map_lie]
    change f.toLinearMap' x ∈ s₂ at h
    rw [LieRinehartAlgebra.Hom.toLinearMap'_apply] at h
    exact s₂.ideal' h
  isotropic x a h := by
    change f.toLinearMap' x ∈ s₂ at h
    rw [LieRinehartAlgebra.Hom.toLinearMap'_apply,] at h
    have h2 := f.apply_lie' a x
    simp only [AlgHom.coe_id, id_eq] at h2
    rw [h2]
    exact s₂.isotropic (f x) a h }

end StrictLieRinehartIdeal

namespace LieRinehartAlgebra

namespace Hom

variable {R A L₁ L₂ : Type*} [CommRing R] [CommRing A] [Algebra R A] [LieRing L₁] [Module A L₁]
  [LieRingModule L₁ A] [LieAlgebra R L₁] [LieRing L₂] [Module A L₂] [LieRingModule L₂ A]
  [LieAlgebra R L₂] (f : L₁→ₗ⁅(AlgHom.id R A)⁆ L₂)

/-- The kernel of a Lie-Rinehart homomorphism `f` (which lies over the
identity of `A`) is a strict Lie-Rinehart ideal. -/
def ker : StrictLieRinehartIdeal A L₁ := StrictLieRinehartIdeal.comap f 0

@[simp]
theorem mem_ker {l : L₁} : l ∈ f.ker ↔ f l = 0 := Iff.rfl

end Hom

end LieRinehartAlgebra

end
