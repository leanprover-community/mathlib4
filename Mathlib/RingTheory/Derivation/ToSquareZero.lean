/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Andrew Yang
-/
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.QuotientOperations

#align_import ring_theory.derivation.to_square_zero from "leanprover-community/mathlib"@"b608348ffaeb7f557f2fd46876037abafd326ff3"

/-!
# Results

- `derivationToSquareZeroOfLift`: The `R`-derivations from `A` into a square-zero ideal `I`
  of `B` corresponds to the lifts `A →ₐ[R] B` of the map `A →ₐ[R] B ⧸ I`.

-/


section ToSquareZero

universe u v w

variable {R : Type u} {A : Type v} {B : Type w} [CommSemiring R] [CommSemiring A] [CommRing B]

variable [Algebra R A] [Algebra R B] (I : Ideal B) (hI : I ^ 2 = ⊥)

/-- If `f₁ f₂ : A →ₐ[R] B` are two lifts of the same `A →ₐ[R] B ⧸ I`,
  we may define a map `f₁ - f₂ : A →ₗ[R] I`. -/
def diffToIdealOfQuotientCompEq (f₁ f₂ : A →ₐ[R] B)
    (e : (Ideal.Quotient.mkₐ R I).comp f₁ = (Ideal.Quotient.mkₐ R I).comp f₂) : A →ₗ[R] I :=
  LinearMap.codRestrict (I.restrictScalars _) (f₁.toLinearMap - f₂.toLinearMap) (by
    intro x
    -- ⊢ ↑(AlgHom.toLinearMap f₁ - AlgHom.toLinearMap f₂) x ∈ Submodule.restrictScala …
    change f₁ x - f₂ x ∈ I
    -- ⊢ ↑f₁ x - ↑f₂ x ∈ I
    rw [← Ideal.Quotient.eq, ← Ideal.Quotient.mkₐ_eq_mk R, ← AlgHom.comp_apply, e]
    -- ⊢ ↑(AlgHom.comp (Ideal.Quotient.mkₐ R I) f₂) x = ↑(Ideal.Quotient.mkₐ R I) (↑f …
    rfl)
    -- 🎉 no goals
#align diff_to_ideal_of_quotient_comp_eq diffToIdealOfQuotientCompEq

@[simp]
theorem diffToIdealOfQuotientCompEq_apply (f₁ f₂ : A →ₐ[R] B)
    (e : (Ideal.Quotient.mkₐ R I).comp f₁ = (Ideal.Quotient.mkₐ R I).comp f₂) (x : A) :
    ((diffToIdealOfQuotientCompEq I f₁ f₂ e) x : B) = f₁ x - f₂ x :=
  rfl
#align diff_to_ideal_of_quotient_comp_eq_apply diffToIdealOfQuotientCompEq_apply

variable [Algebra A B] [IsScalarTower R A B]

/-- Given a tower of algebras `R → A → B`, and a square-zero `I : Ideal B`, each lift `A →ₐ[R] B`
of the canonical map `A →ₐ[R] B ⧸ I` corresponds to an `R`-derivation from `A` to `I`. -/
def derivationToSquareZeroOfLift (f : A →ₐ[R] B)
    (e : (Ideal.Quotient.mkₐ R I).comp f = IsScalarTower.toAlgHom R A (B ⧸ I)) :
    Derivation R A I := by
  refine'
    { diffToIdealOfQuotientCompEq I f (IsScalarTower.toAlgHom R A B) _ with
      map_one_eq_zero' := _
      leibniz' := _ }
  · rw [e]; ext; rfl
    -- ⊢ IsScalarTower.toAlgHom R A (B ⧸ I) = AlgHom.comp (Ideal.Quotient.mkₐ R I) (I …
            -- ⊢ ↑(IsScalarTower.toAlgHom R A (B ⧸ I)) x✝ = ↑(AlgHom.comp (Ideal.Quotient.mkₐ …
                 -- 🎉 no goals
  · ext; change f 1 - algebraMap A B 1 = 0; rw [map_one, map_one, sub_self]
    -- ⊢ ↑(↑{ toAddHom := src✝.toAddHom, map_smul' := (_ : ∀ (r : R) (x : A), AddHom. …
         -- ⊢ ↑f 1 - ↑(algebraMap A B) 1 = 0
                                            -- 🎉 no goals
  · intro x y
    -- ⊢ ↑{ toAddHom := src✝.toAddHom, map_smul' := (_ : ∀ (r : R) (x : A), AddHom.to …
    let F := diffToIdealOfQuotientCompEq I f (IsScalarTower.toAlgHom R A B) (by rw [e]; ext; rfl)
    -- ⊢ ↑{ toAddHom := src✝.toAddHom, map_smul' := (_ : ∀ (r : R) (x : A), AddHom.to …
    have : (f x - algebraMap A B x) * (f y - algebraMap A B y) = 0 := by
      rw [← Ideal.mem_bot, ← hI, pow_two]
      convert Ideal.mul_mem_mul (F x).2 (F y).2 using 1
    ext
    -- ⊢ ↑(↑{ toAddHom := src✝.toAddHom, map_smul' := (_ : ∀ (r : R) (x : A), AddHom. …
    dsimp only [Submodule.coe_add, Submodule.coe_mk, LinearMap.coe_mk,
      diffToIdealOfQuotientCompEq_apply, Submodule.coe_smul_of_tower, IsScalarTower.coe_toAlgHom',
      LinearMap.toFun_eq_coe]
    simp only [map_mul, sub_mul, mul_sub, Algebra.smul_def] at this ⊢
    -- ⊢ ↑(↑(diffToIdealOfQuotientCompEq I f (IsScalarTower.toAlgHom R A B) (_ : AlgH …
    rw [sub_eq_iff_eq_add, sub_eq_iff_eq_add] at this
    -- ⊢ ↑(↑(diffToIdealOfQuotientCompEq I f (IsScalarTower.toAlgHom R A B) (_ : AlgH …
    simp only [LinearMap.coe_toAddHom, diffToIdealOfQuotientCompEq_apply, map_mul, this,
      IsScalarTower.coe_toAlgHom']
    ring
    -- 🎉 no goals
#align derivation_to_square_zero_of_lift derivationToSquareZeroOfLift

theorem derivationToSquareZeroOfLift_apply (f : A →ₐ[R] B)
    (e : (Ideal.Quotient.mkₐ R I).comp f = IsScalarTower.toAlgHom R A (B ⧸ I)) (x : A) :
    (derivationToSquareZeroOfLift I hI f e x : B) = f x - algebraMap A B x :=
  rfl
#align derivation_to_square_zero_of_lift_apply derivationToSquareZeroOfLift_apply

/-- Given a tower of algebras `R → A → B`, and a square-zero `I : Ideal B`, each `R`-derivation
from `A` to `I` corresponds to a lift `A →ₐ[R] B` of the canonical map `A →ₐ[R] B ⧸ I`. -/
@[simps (config := { isSimp := false })]
def liftOfDerivationToSquareZero (f : Derivation R A I) : A →ₐ[R] B :=
  { ((I.restrictScalars R).subtype.comp f.toLinearMap + (IsScalarTower.toAlgHom R A B).toLinearMap :
      A →ₗ[R] B) with
    toFun := fun x => f x + algebraMap A B x
    map_one' := by dsimp; rw [map_one, f.map_one_eq_zero, Submodule.coe_zero, zero_add]
                   -- ⊢ ↑(↑f 1) + ↑(algebraMap A B) 1 = 1
                          -- 🎉 no goals
    map_mul' := fun x y => by
      have : (f x : B) * f y = 0 := by
        rw [← Ideal.mem_bot, ← hI, pow_two]
        convert Ideal.mul_mem_mul (f x).2 (f y).2 using 1
      simp only [map_mul, f.leibniz, add_mul, mul_add, Submodule.coe_add,
        Submodule.coe_smul_of_tower, Algebra.smul_def, this]
      ring
      -- 🎉 no goals
    commutes' := fun r => by
      simp only [Derivation.map_algebraMap, eq_self_iff_true, zero_add, Submodule.coe_zero, ←
        IsScalarTower.algebraMap_apply R A B r]
    map_zero' := ((I.restrictScalars R).subtype.comp f.toLinearMap +
      (IsScalarTower.toAlgHom R A B).toLinearMap).map_zero }
#align lift_of_derivation_to_square_zero liftOfDerivationToSquareZero

-- @[simp] -- Porting note: simp normal form is `liftOfDerivationToSquareZero_mk_apply'`
theorem liftOfDerivationToSquareZero_mk_apply (d : Derivation R A I) (x : A) :
    Ideal.Quotient.mk I (liftOfDerivationToSquareZero I hI d x) = algebraMap A (B ⧸ I) x := by
  rw [liftOfDerivationToSquareZero_apply, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr (d x).prop,
    zero_add]
  rfl
  -- 🎉 no goals
#align lift_of_derivation_to_square_zero_mk_apply liftOfDerivationToSquareZero_mk_apply

@[simp]
theorem liftOfDerivationToSquareZero_mk_apply' (d : Derivation R A I) (x : A) :
    (Ideal.Quotient.mk I) (d x) + (algebraMap A (B ⧸ I)) x = algebraMap A (B ⧸ I) x := by
  simp only [Ideal.Quotient.eq_zero_iff_mem.mpr (d x).prop, zero_add]
  -- 🎉 no goals

/-- Given a tower of algebras `R → A → B`, and a square-zero `I : ideal B`,
there is a 1-1 correspondence between `R`-derivations from `A` to `I` and
lifts `A →ₐ[R] B` of the canonical map `A →ₐ[R] B ⧸ I`. -/
@[simps!]
def derivationToSquareZeroEquivLift : Derivation R A I ≃
    { f : A →ₐ[R] B // (Ideal.Quotient.mkₐ R I).comp f = IsScalarTower.toAlgHom R A (B ⧸ I) } := by
  refine' ⟨fun d => ⟨liftOfDerivationToSquareZero I hI d, _⟩, fun f =>
    (derivationToSquareZeroOfLift I hI f.1 f.2 : _), _, _⟩
  · ext x; exact liftOfDerivationToSquareZero_mk_apply I hI d x
    -- ⊢ ↑(AlgHom.comp (Ideal.Quotient.mkₐ R I) (liftOfDerivationToSquareZero I hI d) …
           -- 🎉 no goals
  · intro d; ext x; exact add_sub_cancel (d x : B) (algebraMap A B x)
    -- ⊢ (fun f => derivationToSquareZeroOfLift I hI ↑f (_ : AlgHom.comp (Ideal.Quoti …
             -- ⊢ ↑(↑((fun f => derivationToSquareZeroOfLift I hI ↑f (_ : AlgHom.comp (Ideal.Q …
                    -- 🎉 no goals
  · rintro ⟨f, hf⟩; ext x; exact sub_add_cancel (f x) (algebraMap A B x)
    -- ⊢ (fun d => { val := liftOfDerivationToSquareZero I hI d, property := (_ : Alg …
                    -- ⊢ ↑↑((fun d => { val := liftOfDerivationToSquareZero I hI d, property := (_ :  …
                           -- 🎉 no goals
#align derivation_to_square_zero_equiv_lift derivationToSquareZeroEquivLift

end ToSquareZero
