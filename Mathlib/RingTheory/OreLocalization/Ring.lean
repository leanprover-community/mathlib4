/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Kevin Klinge, Andrew Yang
-/

import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.OreLocalization.Basic

#align_import ring_theory.ore_localization.basic from "leanprover-community/mathlib"@"861a26926586cd46ff80264d121cdb6fa0e35cc1"

/-!

# Module and Ring instances of Ore Localizations

The `Monoid` and `DistribMulAction` instances and additive versions are provided in
`RingTheory/OreLocalization/Basic.lean`.

-/

universe u

namespace OreLocalization

section Module

variable {R : Type*} [Semiring R] {S : Submonoid R} [OreSet S]
variable {X : Type*} [AddCommMonoid X] [Module R X]

protected theorem zero_smul (x : X[S⁻¹]) : (0 : R[S⁻¹]) • x = 0 := by
  induction' x using OreLocalization.ind with r s
  rw [OreLocalization.zero_def, oreDiv_smul_char 0 r 1 s 0 1 (by simp)]; simp

protected theorem add_smul (y z : R[S⁻¹]) (x : X[S⁻¹]) :
    (y + z) • x = y • x + z • x := by
  induction' x using OreLocalization.ind with r₁ s₁
  induction' y using OreLocalization.ind with r₂ s₂
  induction' z using OreLocalization.ind with r₃ s₃
  rcases oreDivAddChar' r₂ r₃ s₂ s₃ with ⟨ra, sa, ha, q⟩
  rw [q]
  clear q
  rw [OreLocalization.expand' r₂ s₂ sa]
  rcases oreDivSMulChar' (sa • r₂) r₁ (sa * s₂) s₁ with ⟨rb, sb, hb, q⟩
  rw [q]
  clear q
  have hs₃rasb : sb * ra * s₃ ∈ S := by
    rw [mul_assoc, ← ha]
    norm_cast
    apply SetLike.coe_mem
  rw [OreLocalization.expand _ _ _ hs₃rasb]
  have ha' : ↑((sb * sa) * s₂) = sb * ra * s₃ := by simp [ha, mul_assoc]
  rw [← Subtype.coe_eq_of_eq_mk ha']
  rcases oreDivSMulChar' ((sb * ra) • r₃) r₁ (sb * sa * s₂) s₁ with ⟨rc, sc, hc, hc'⟩
  rw [hc']
  rw [oreDiv_add_char _ _ 1 sc (by simp [mul_assoc])]
  rw [OreLocalization.expand' (sa • r₂ + ra • r₃) (sa * s₂) (sc * sb)]
  simp only [smul_eq_mul, one_smul, Submonoid.smul_def, mul_add, Submonoid.coe_mul] at hb hc ⊢
  rw [mul_assoc, hb, mul_assoc, ← mul_assoc _ ra, hc, ← mul_assoc, ← add_mul]
  rw [OreLocalization.smul_cancel']
  simp only [add_smul, ← mul_assoc, smul_smul]

end Module

section Semiring

variable {R : Type*} [Semiring R] {S : Submonoid R} [OreSet S]

attribute [local instance] OreLocalization.oreEqv

protected theorem zero_mul (x : R[S⁻¹]) : 0 * x = 0 :=
  OreLocalization.zero_smul x
#align ore_localization.zero_mul OreLocalization.zero_mul

protected theorem mul_zero (x : R[S⁻¹]) : x * 0 = 0 :=
  OreLocalization.smul_zero x
#align ore_localization.mul_zero OreLocalization.mul_zero

protected theorem left_distrib (x y z : R[S⁻¹]) : x * (y + z) = x * y + x * z :=
  OreLocalization.smul_add _ _ _
#align ore_localization.left_distrib OreLocalization.left_distrib

theorem right_distrib (x y z : R[S⁻¹]) : (x + y) * z = x * z + y * z :=
  OreLocalization.add_smul _ _ _
#align ore_localization.right_distrib OreLocalization.right_distrib

instance : Semiring R[S⁻¹] where
  __ := inferInstanceAs (Monoid (R[S⁻¹]))
  zero_mul := OreLocalization.zero_mul
  mul_zero := OreLocalization.mul_zero
  left_distrib := OreLocalization.left_distrib
  right_distrib := right_distrib

variable {X : Type*} [AddCommMonoid X] [Module R X]

instance : Module R[S⁻¹] X[S⁻¹] where
  add_smul := OreLocalization.add_smul
  zero_smul := OreLocalization.zero_smul

section UMP

variable {T : Type*} [Semiring T]
variable (f : R →+* T) (fS : S →* Units T)
variable (hf : ∀ s : S, f s = fS s)

/-- The universal lift from a ring homomorphism `f : R →+* T`, which maps elements in `S` to
units of `T`, to a ring homomorphism `R[S⁻¹] →+* T`. This extends the construction on
monoids. -/
def universalHom : R[S⁻¹] →+* T :=
  {
    universalMulHom f.toMonoidHom fS
      hf with
    map_zero' := by
      -- Porting note: `change` required because of new `Coe`
      change (universalMulHom f.toMonoidHom fS hf : R[S⁻¹] → T) 0 = 0
      rw [OreLocalization.zero_def, universalMulHom_apply]
      simp
    map_add' := fun x y => by
      -- Porting note: `change` required because of new `Coe`
      change (universalMulHom f.toMonoidHom fS hf : R[S⁻¹] → T) (x + y)
        = (universalMulHom f.toMonoidHom fS hf : R[S⁻¹] → T) x
        + (universalMulHom f.toMonoidHom fS hf : R[S⁻¹] → T) y
      induction' x using OreLocalization.ind with r₁ s₁
      induction' y using OreLocalization.ind with r₂ s₂
      rcases oreDivAddChar' r₁ r₂ s₁ s₂ with ⟨r₃, s₃, h₃, h₃'⟩
      rw [h₃']
      clear h₃'
      simp only [RingHom.toMonoidHom_eq_coe, smul_eq_mul, universalMulHom_apply, MonoidHom.coe_coe,
        Submonoid.smul_def]
      simp only [mul_inv_rev, MonoidHom.map_mul, RingHom.map_add, RingHom.map_mul, Units.val_mul]
      rw [mul_add, mul_assoc, ← mul_assoc _ (f s₃), hf, ← Units.val_mul]
      simp only [one_mul, mul_left_inv, Units.val_one]
      congr 1
      rw [← mul_assoc]
      congr 1
      norm_cast at h₃
      have h₃' := Subtype.coe_eq_of_eq_mk h₃
      rw [← Units.val_mul, ← mul_inv_rev, ← fS.map_mul, h₃']
      rw [Units.inv_mul_eq_iff_eq_mul, Units.eq_mul_inv_iff_mul_eq, ← hf, ← hf]
      simp only [map_mul] }
#align ore_localization.universal_hom OreLocalization.universalHom

theorem universalHom_apply {r : R} {s : S} :
    universalHom f fS hf (r /ₒ s) = ((fS s)⁻¹ : Units T) * f r :=
  rfl
#align ore_localization.universal_hom_apply OreLocalization.universalHom_apply

theorem universalHom_commutes {r : R} : universalHom f fS hf (numeratorHom r) = f r := by
  simp [numeratorHom_apply, universalHom_apply]
#align ore_localization.universal_hom_commutes OreLocalization.universalHom_commutes

theorem universalHom_unique (φ : R[S⁻¹] →+* T) (huniv : ∀ r : R, φ (numeratorHom r) = f r) :
    φ = universalHom f fS hf :=
  RingHom.coe_monoidHom_injective <| universalMulHom_unique (RingHom.toMonoidHom f) fS hf (↑φ) huniv
#align ore_localization.universal_hom_unique OreLocalization.universalHom_unique

end UMP

end Semiring

section Ring

variable {R : Type*} [Ring R] {S : Submonoid R} [OreSet S]

instance : Ring R[S⁻¹] where
  __ := inferInstanceAs (Semiring R[S⁻¹])
  __ := inferInstanceAs (AddGroup R[S⁻¹])

open nonZeroDivisors

theorem numeratorHom_inj (hS : S ≤ nonZeroDivisorsRight R) :
    Function.Injective (numeratorHom : R → R[S⁻¹]) :=
  fun r₁ r₂ h => by
  rw [numeratorHom_apply, numeratorHom_apply, oreDiv_eq_iff] at h
  rcases h with ⟨u, v, h₁, h₂⟩
  simp only [S.coe_one, mul_one, Submonoid.smul_def, smul_eq_mul] at h₁ h₂
  rw [← h₂, ← sub_eq_zero, ← mul_sub] at h₁
  exact (sub_eq_zero.mp (hS u.2 _ h₁)).symm
#align ore_localization.numerator_hom_inj OreLocalization.numeratorHom_inj

theorem subsingleton_iff :
    Subsingleton R[S⁻¹] ↔ 0 ∈ S := by
  rw [← subsingleton_iff_zero_eq_one, OreLocalization.one_def,
    OreLocalization.zero_def, oreDiv_eq_iff]
  simp

theorem nontrivial_iff :
    Nontrivial R[S⁻¹] ↔ 0 ∉ S := by
  rw [← not_subsingleton_iff_nontrivial, subsingleton_iff]

theorem nontrivial_of_nonZeroDivisors [Nontrivial R] (hS : S ≤ R⁰) :
    Nontrivial R[S⁻¹] :=
  nontrivial_iff.mpr (fun e ↦ one_ne_zero <| hS e 1 (mul_zero _))
#align ore_localization.nontrivial_of_non_zero_divisors OreLocalization.nontrivial_of_nonZeroDivisors

end Ring

noncomputable section DivisionRing

open nonZeroDivisors

open scoped Classical

variable {R : Type*} [Ring R] [Nontrivial R] [OreSet R⁰]

instance nontrivial : Nontrivial R[R⁰⁻¹] :=
  nontrivial_of_nonZeroDivisors (refl R⁰)

variable [NoZeroDivisors R]

/-- The inversion of Ore fractions for a ring without zero divisors, satisying `0⁻¹ = 0` and
`(r /ₒ r')⁻¹ = r' /ₒ r` for `r ≠ 0`. -/
protected def inv : R[R⁰⁻¹] → R[R⁰⁻¹] :=
  liftExpand
    (fun r s =>
      if hr : r = (0 : R) then (0 : R[R⁰⁻¹])
      else s /ₒ ⟨r, fun _ => eq_zero_of_ne_zero_of_mul_right_eq_zero hr⟩)
    (by
      intro r t s hst
      by_cases hr : r = 0
      · simp [hr]
      · by_cases ht : t = 0
        · exfalso
          apply nonZeroDivisors.coe_ne_zero ⟨_, hst⟩
          simp [ht, mul_zero]
        · simp only [hr, ht, dif_neg, not_false_iff, or_self_iff, mul_eq_zero, smul_eq_mul]
          apply OreLocalization.expand)
#align ore_localization.inv OreLocalization.inv

instance inv' : Inv R[R⁰⁻¹] :=
  ⟨OreLocalization.inv⟩

protected theorem inv_def {r : R} {s : R⁰} :
    (r /ₒ s)⁻¹ =
      if hr : r = (0 : R) then (0 : R[R⁰⁻¹])
      else s /ₒ ⟨r, fun _ => eq_zero_of_ne_zero_of_mul_right_eq_zero hr⟩ :=
  rfl
#align ore_localization.inv_def OreLocalization.inv_def

protected theorem mul_inv_cancel (x : R[R⁰⁻¹]) (h : x ≠ 0) : x * x⁻¹ = 1 := by
  induction' x using OreLocalization.ind with r s
  rw [OreLocalization.inv_def, OreLocalization.one_def]
  by_cases hr : r = 0
  · exfalso
    apply h
    simp [hr]
  · simp only [hr, ↓reduceDIte]
    apply OreLocalization.mul_inv ⟨r, _⟩
#align ore_localization.mul_inv_cancel OreLocalization.mul_inv_cancel

protected theorem inv_zero : (0 : R[R⁰⁻¹])⁻¹ = 0 := by
  rw [OreLocalization.zero_def, OreLocalization.inv_def]
  simp
#align ore_localization.inv_zero OreLocalization.inv_zero

instance : DivisionRing R[R⁰⁻¹] where
  mul_inv_cancel := OreLocalization.mul_inv_cancel
  inv_zero := OreLocalization.inv_zero
  nnqsmul := _
  qsmul := _

end DivisionRing

end OreLocalization
