/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Kevin Klinge, Andrew Yang
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.OreLocalization.NonZeroDivisors

/-!

# Module and Ring instances of Ore Localizations

The `Monoid` and `DistribMulAction` instances and additive versions are provided in
`Mathlib/RingTheory/OreLocalization/Basic.lean`.

-/

assert_not_exists Subgroup

universe u

namespace OreLocalization

section Module

variable {R : Type*} [Semiring R] {S : Submonoid R} [OreSet S]
variable {X : Type*} [AddCommMonoid X] [Module R X]

protected theorem zero_smul (x : X[S⁻¹]) : (0 : R[S⁻¹]) • x = 0 := by
  induction x with | _ r s
  rw [OreLocalization.zero_def, oreDiv_smul_char 0 r 1 s 0 1 (by simp)]; simp

protected theorem add_smul (y z : R[S⁻¹]) (x : X[S⁻¹]) :
    (y + z) • x = y • x + z • x := by
  induction x with | _ r₁ s₁
  induction y with | _ r₂ s₂
  induction z with | _ r₃ s₃
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

@[deprecated zero_mul (since := "2025-08-20")]
protected theorem zero_mul (x : R[S⁻¹]) : 0 * x = 0 :=
  OreLocalization.zero_smul x

@[deprecated mul_zero (since := "2025-08-20")]
protected theorem mul_zero (x : R[S⁻¹]) : x * 0 = 0 :=
  OreLocalization.smul_zero x

protected theorem left_distrib (x y z : R[S⁻¹]) : x * (y + z) = x * y + x * z :=
  OreLocalization.smul_add _ _ _

theorem right_distrib (x y z : R[S⁻¹]) : (x + y) * z = x * z + y * z :=
  OreLocalization.add_smul _ _ _

instance : Semiring R[S⁻¹] where
  __ := inferInstanceAs (MonoidWithZero (R[S⁻¹]))
  __ := inferInstanceAs (AddCommMonoid (R[S⁻¹]))
  left_distrib := OreLocalization.left_distrib
  right_distrib := right_distrib

variable {X : Type*} [AddCommMonoid X] [Module R X]

instance : Module R[S⁻¹] X[S⁻¹] where
  add_smul := OreLocalization.add_smul
  zero_smul := OreLocalization.zero_smul

instance {R₀} [Semiring R₀] [Module R₀ X] [Module R₀ R]
    [IsScalarTower R₀ R X] [IsScalarTower R₀ R R] :
    Module R₀ X[S⁻¹] where
  add_smul r s x := by simp only [← smul_one_oreDiv_one_smul, add_smul, ← add_oreDiv]
  zero_smul x := by rw [← smul_one_oreDiv_one_smul, zero_smul, zero_oreDiv, zero_smul]

@[simp]
lemma nsmul_eq_nsmul (n : ℕ) (x : X[S⁻¹]) :
    letI inst := OreLocalization.instModuleOfIsScalarTower (R₀ := ℕ) (R := R) (X := X) (S := S)
    HSMul.hSMul (self := @instHSMul _ _ inst.toSMul) n x = n • x := by
  letI inst := OreLocalization.instModuleOfIsScalarTower (R₀ := ℕ) (R := R) (X := X) (S := S)
  exact congr($(AddCommMonoid.uniqueNatModule.2 inst).smul n x)

/-- The ring homomorphism from `R` to `R[S⁻¹]`, mapping `r : R` to the fraction `r /ₒ 1`. -/
@[simps!]
def numeratorRingHom : R →+* R[S⁻¹] where
  __ := numeratorHom
  map_zero' := by with_unfolding_all exact OreLocalization.zero_def
  map_add' _ _ := add_oreDiv.symm

instance {R₀} [CommSemiring R₀] [Algebra R₀ R] : Algebra R₀ R[S⁻¹] where
  __ := inferInstanceAs (Module R₀ R[S⁻¹])
  algebraMap := numeratorRingHom.comp (algebraMap R₀ R)
  commutes' r x := by
    induction x using OreLocalization.ind with | _ r₁ s₁
    dsimp
    rw [mul_div_one, oreDiv_mul_char _ _ _ _ (algebraMap R₀ R r) s₁ (Algebra.commutes _ _).symm,
      Algebra.commutes, mul_one]
  smul_def' r x := by
    dsimp
    rw [Algebra.algebraMap_eq_smul_one, ← smul_eq_mul, smul_one_oreDiv_one_smul]

section UMP

variable {T : Type*} [Semiring T]
variable (f : R →+* T) (fS : S →* Units T)
variable (hf : ∀ s : S, f s = fS s)

/-- The universal lift from a ring homomorphism `f : R →+* T`, which maps elements in `S` to
units of `T`, to a ring homomorphism `R[S⁻¹] →+* T`. This extends the construction on
monoids. -/
def universalHom : R[S⁻¹] →+* T :=
  { universalMulHom f.toMonoidHom fS hf with
    map_zero' := by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe]
      rw [OreLocalization.zero_def, universalMulHom_apply]
      simp
    map_add' := fun x y => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe]
      induction x with | _ r₁ s₁
      induction y with | _ r₂ s₂
      rcases oreDivAddChar' r₁ r₂ s₁ s₂ with ⟨r₃, s₃, h₃, h₃'⟩
      rw [h₃']
      clear h₃'
      simp only [smul_eq_mul, universalMulHom_apply, MonoidHom.coe_coe,
        Submonoid.smul_def]
      simp only [mul_inv_rev, MonoidHom.map_mul, RingHom.map_add, RingHom.map_mul, Units.val_mul]
      rw [mul_add, mul_assoc, ← mul_assoc _ (f s₃), hf, ← Units.val_mul]
      simp only [one_mul, inv_mul_cancel, Units.val_one]
      congr 1
      rw [← mul_assoc]
      congr 1
      norm_cast at h₃
      have h₃' := Subtype.coe_eq_of_eq_mk h₃
      rw [← Units.val_mul, ← mul_inv_rev, ← fS.map_mul, h₃']
      rw [Units.inv_mul_eq_iff_eq_mul, Units.eq_mul_inv_iff_mul_eq, ← hf, ← hf]
      simp only [map_mul] }

theorem universalHom_apply {r : R} {s : S} :
    universalHom f fS hf (r /ₒ s) = ((fS s)⁻¹ : Units T) * f r :=
  rfl

theorem universalHom_commutes {r : R} : universalHom f fS hf (numeratorHom r) = f r := by
  simp [numeratorHom_apply, universalHom_apply]

theorem universalHom_unique (φ : R[S⁻¹] →+* T) (huniv : ∀ r : R, φ (numeratorHom r) = f r) :
    φ = universalHom f fS hf :=
  RingHom.coe_monoidHom_injective <| universalMulHom_unique (RingHom.toMonoidHom f) fS hf (↑φ) huniv

end UMP

end Semiring

section Ring

variable {R : Type*} [Ring R] {S : Submonoid R} [OreSet S]
variable {X : Type*} [AddCommGroup X] [Module R X]

instance : Ring R[S⁻¹] where
  __ := inferInstanceAs (Semiring R[S⁻¹])
  __ := inferInstanceAs (AddGroup R[S⁻¹])

@[simp]
lemma zsmul_eq_zsmul (n : ℤ) (x : X[S⁻¹]) :
    letI inst := OreLocalization.instModuleOfIsScalarTower (R₀ := ℤ) (R := R) (X := X) (S := S)
    HSMul.hSMul (self := @instHSMul _ _ inst.toSMul) n x = n • x := by
  letI inst := OreLocalization.instModuleOfIsScalarTower (R₀ := ℤ) (R := R) (X := X) (S := S)
  exact congr($(AddCommGroup.uniqueIntModule.2 inst).smul n x)

open nonZeroDivisors

theorem numeratorHom_inj (hS : S ≤ nonZeroDivisorsLeft R) :
    Function.Injective (numeratorHom : R → R[S⁻¹]) :=
  fun r₁ r₂ h => by
  rw [numeratorHom_apply, numeratorHom_apply, oreDiv_eq_iff] at h
  rcases h with ⟨u, v, h₁, h₂⟩
  simp only [S.coe_one, mul_one, Submonoid.smul_def, smul_eq_mul] at h₁ h₂
  rw [← h₂, ← sub_eq_zero, ← mul_sub] at h₁
  exact (sub_eq_zero.mp (hS u.2 _ h₁)).symm

end Ring

noncomputable section DivisionRing

open nonZeroDivisors

variable {R : Type*} [Ring R] [Nontrivial R] [NoZeroDivisors R] [OreSet R⁰]

instance : DivisionRing R[R⁰⁻¹] where
  mul_inv_cancel := OreLocalization.mul_inv_cancel
  inv_zero := OreLocalization.inv_zero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

end DivisionRing

section CommSemiring

variable {R : Type*} [CommSemiring R] {S : Submonoid R} [OreSet S]

instance : CommSemiring R[S⁻¹] where
  __ := inferInstanceAs (Semiring R[S⁻¹])
  __ := inferInstanceAs (CommMonoid R[S⁻¹])

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] {S : Submonoid R} [OreSet S]

instance : CommRing R[S⁻¹] where
  __ := inferInstanceAs (Ring R[S⁻¹])
  __ := inferInstanceAs (CommMonoid R[S⁻¹])

end CommRing

section Field

open nonZeroDivisors

variable {R : Type*} [CommRing R] [Nontrivial R] [NoZeroDivisors R] [OreSet R⁰]

noncomputable
instance : Field R[R⁰⁻¹] where
  __ := inferInstanceAs (DivisionRing R[R⁰⁻¹])
  __ := inferInstanceAs (CommMonoid R[R⁰⁻¹])

end Field

end OreLocalization
