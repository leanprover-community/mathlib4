
/-
Copyright (c) 2026 Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonid Ryvkin
-/
module

public import Mathlib.Algebra.LieRinehartAlgebra.StrictIdeal

/-!
# Quotients of Lie-Rinehart algebras by strict Lie-Rinehart ideals

Given a Lie-Rinehart algebra `(R A L)` and an ideal `s ⊆ L`, the quotient `L ⧸ s` inherits the
structure of a Lie-Rinehart algebra.
-/

@[expose] public section

universe u v

namespace StrictLieRinehartIdeal

variable {A : Type u} {L : Type v} [CommRing A] [LieRing L] [Module A L] [LieRingModule L A]

instance : HasQuotient L (StrictLieRinehartIdeal A L) := ⟨fun s => L ⧸ s.toSubmodule⟩

namespace Quotient

variable {s : StrictLieRinehartIdeal A L}

instance : AddCommGroup (L ⧸ s) := Submodule.Quotient.addCommGroup _

instance : Module A (L ⧸ s) := Submodule.Quotient.module _


/-- Map associating to an element in a Lie-Rinehart algebra `L`, an element in the quotient
`L ⧸ s`, where s is a strict Lie-Rinehart ideal. -/
abbrev mk : L → L ⧸ s := Submodule.Quotient.mk

@[simp]
theorem mk_eq_zero' {l : L} : mk (s := s) l = 0 ↔ l ∈ s :=
  Submodule.Quotient.mk_eq_zero s.toSubmodule

theorem is_quotient_mk (l : L) : Quotient.mk'' l = (mk l : L ⧸ s) := rfl

instance : LieRing (L ⧸ s) where
  bracket x y :=
    Quotient.liftOn₂' x y (fun x' y' => mk ⁅x', y'⁆) (by
      intros a₁ a₂ b₁ b₂ ha hb
      rw [Submodule.quotientRel_def, mem_toSubmodule] at ha hb
      apply (Submodule.Quotient.eq s.toSubmodule).2
      rw [mem_toSubmodule]
      have h : ⁅a₁, a₂⁆ - ⁅b₁, b₂⁆ = ⁅a₁ - b₁, a₂⁆ + ⁅b₁, a₂ - b₂⁆ := by simp
      rw [h]
      refine add_mem ?_ ?_
      · exact s.ideal' ha
      · rw [← neg_mem_iff, lie_skew]; exact s.ideal' hb)
  add_lie := by rintro ⟨x⟩ ⟨y⟩ ⟨z⟩; exact congrArg mk (add_lie x y z)
  lie_add := by rintro ⟨x⟩ ⟨y⟩ ⟨z⟩; exact congrArg mk (lie_add x y z)
  lie_self := by rintro ⟨x⟩; exact congrArg mk (lie_self x)
  leibniz_lie := by rintro ⟨x⟩ ⟨y⟩ ⟨z⟩; exact congrArg mk (leibniz_lie x y z)

@[simp]
theorem mk_bracket (x y : L) : mk ⁅x, y⁆ = ⁅(mk x : L ⧸ s), (mk y : L ⧸ s)⁆ := rfl

instance : Bracket (L ⧸ s) A where
  bracket x a := Quotient.liftOn' x (fun x' => ⁅x', a⁆) (by
    intros l l' h
    rw [Submodule.quotientRel_def, mem_toSubmodule] at h
    rw [← sub_eq_zero, ←sub_lie]
    exact s.isotropic (l - l') a h)

@[simp]
theorem mk_bracket' (x : L) (a : A) : ⁅x, a⁆ = ⁅(mk x : L ⧸ s), a⁆ := rfl

instance : LieRingModule (L ⧸ s) A where
  add_lie := by rintro ⟨x⟩ ⟨y⟩ a; exact (add_lie x y a)
  lie_add := by rintro ⟨x⟩ a b; exact (lie_add x a b)
  leibniz_lie := by rintro ⟨x⟩ ⟨y⟩ a; exact (leibniz_lie x y a)

instance [LieRinehartRing A L] : LieRinehartRing A (L ⧸ s) where
  lie_smul_eq_mul' := by rintro a b ⟨x⟩; exact (LieRinehartRing.lie_smul_eq_mul a b x)
  leibniz_mul_right' := by rintro ⟨x⟩ a b; exact (LieRinehartRing.leibniz_mul_right x a b)
  leibniz_smul_right' := by
    rintro ⟨x⟩ ⟨y⟩ a
    exact congrArg mk (LieRinehartRing.leibniz_smul_right x y a)

variable {R : Type*} [CommRing R] [Algebra R A] [LieAlgebra R L] [LieRinehartRing A L]
  [LieRinehartAlgebra R A L]

instance : LieAlgebra R (L ⧸ s) where
  smul r l := Quotient.liftOn' l (fun l' => mk (r • l')) (by
    intros a b h
    rw [Submodule.quotientRel_def, mem_toSubmodule] at h
    apply (Submodule.Quotient.eq s.toSubmodule).2
    rw [mem_toSubmodule, ← smul_sub]
    exact (s.restrictScalars R).smul_mem r h)
  mul_smul := by rintro r₁ r₂ ⟨x⟩; exact congrArg mk (mul_smul r₁ r₂ x)
  one_smul := by rintro ⟨x⟩; exact congrArg mk (one_smul R x)
  smul_zero r := congrArg mk (smul_zero r)
  smul_add := by rintro r ⟨x⟩ ⟨y⟩; exact congrArg mk (smul_add r x y)
  add_smul := by rintro r₁ r₂ ⟨x⟩; exact congrArg mk (add_smul r₁ r₂ x)
  zero_smul := by rintro ⟨x⟩; exact congrArg mk (zero_smul R x)
  lie_smul := by rintro r ⟨x⟩ ⟨y⟩; exact congrArg mk (lie_smul r x y)

variable (s R) in
open LieRinehartAlgebra in
/-- `StrictLieRinehartIdeal.Quotient.mk` as a Lie-Rinehart homomorphism. -/
def mk' : L →ₗ⁅(AlgHom.id R A)⁆ L ⧸ s :=
  { (s.toSubmodule.restrictScalars R).mkQ with
    toFun := mk -- this can be removed, but then it stops being 'a constructor application', not
                -- sure if we want that
    map_lie'  {_ _} := rfl
    map_smul_apply' _ _ := rfl
    apply_lie' _ _ := rfl }

@[simp]
lemma mk'_apply {l : L} : mk' s R l = mk l := rfl

@[simp]
theorem surjective_mk' : Function.Surjective (mk' s R) := Quot.mk_surjective

theorem mk_eq_zero {l : L} : mk' s R l = 0 ↔ l ∈ s := Submodule.Quotient.mk_eq_zero s.toSubmodule

@[simp]
theorem mk'_ker : (mk' s R).ker = s := by ext l; simp

end Quotient
end StrictLieRinehartIdeal

end
