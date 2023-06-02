/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module data.mv_polynomial.derivation
! leanprover-community/mathlib commit b608348ffaeb7f557f2fd46876037abafd326ff3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.MvPolynomial.Supported
import Mathlib.RingTheory.Derivation.Basic

/-!
# Derivations of multivariate polynomials

In this file we prove that a derivation of `mv_polynomial σ R` is determined by its values on all
monomials `mv_polynomial.X i`. We also provide a constructor `mv_polynomial.mk_derivation` that
builds a derivation from its values on `X i`s and a linear equivalence
`mv_polynomial.equiv_derivation` between `σ → A` and `derivation (mv_polynomial σ R) A`.
-/


namespace MvPolynomial

open scoped BigOperators

noncomputable section

variable {σ R A : Type _} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [Module (MvPolynomial σ R) A]

section

variable (R)

/-- The derivation on `mv_polynomial σ R` that takes value `f i` on `X i`, as a linear map.
Use `mv_polynomial.mk_derivation` instead. -/
def mkDerivationₗ (f : σ → A) : MvPolynomial σ R →ₗ[R] A :=
  Finsupp.lsum R fun xs : σ →₀ ℕ =>
    (LinearMap.ringLmapEquivSelf R R A).symm <|
      xs.Sum fun i k => monomial (xs - Finsupp.single i 1) (k : R) • f i
#align mv_polynomial.mk_derivationₗ MvPolynomial.mkDerivationₗ

end

theorem mkDerivationₗ_monomial (f : σ → A) (s : σ →₀ ℕ) (r : R) :
    mkDerivationₗ R f (monomial s r) =
      r • s.Sum fun i k => monomial (s - Finsupp.single i 1) (k : R) • f i :=
  sum_monomial_eq <| LinearMap.map_zero _
#align mv_polynomial.mk_derivationₗ_monomial MvPolynomial.mkDerivationₗ_monomial

theorem mkDerivationₗ_c (f : σ → A) (r : R) : mkDerivationₗ R f (C r) = 0 :=
  (mkDerivationₗ_monomial f _ _).trans (smul_zero _)
#align mv_polynomial.mk_derivationₗ_C MvPolynomial.mkDerivationₗ_c

theorem mkDerivationₗ_x (f : σ → A) (i : σ) : mkDerivationₗ R f (X i) = f i :=
  (mkDerivationₗ_monomial f _ _).trans <| by simp
#align mv_polynomial.mk_derivationₗ_X MvPolynomial.mkDerivationₗ_x

@[simp]
theorem derivation_c (D : Derivation R (MvPolynomial σ R) A) (a : R) : D (C a) = 0 :=
  D.map_algebraMap a
#align mv_polynomial.derivation_C MvPolynomial.derivation_c

@[simp]
theorem derivation_c_mul (D : Derivation R (MvPolynomial σ R) A) (a : R) (f : MvPolynomial σ R) :
    D (C a * f) = a • D f := by rw [C_mul', D.map_smul]
#align mv_polynomial.derivation_C_mul MvPolynomial.derivation_c_mul

/-- If two derivations agree on `X i`, `i ∈ s`, then they agree on all polynomials from
`mv_polynomial.supported R s`. -/
theorem derivation_eqOn_supported {D₁ D₂ : Derivation R (MvPolynomial σ R) A} {s : Set σ}
    (h : Set.EqOn (D₁ ∘ X) (D₂ ∘ X) s) {f : MvPolynomial σ R} (hf : f ∈ supported R s) :
    D₁ f = D₂ f :=
  Derivation.eqOn_adjoin (Set.ball_image_iff.2 h) hf
#align mv_polynomial.derivation_eq_on_supported MvPolynomial.derivation_eqOn_supported

theorem derivation_eq_of_forall_mem_vars {D₁ D₂ : Derivation R (MvPolynomial σ R) A}
    {f : MvPolynomial σ R} (h : ∀ i ∈ f.vars, D₁ (X i) = D₂ (X i)) : D₁ f = D₂ f :=
  derivation_eqOn_supported h f.mem_supported_vars
#align mv_polynomial.derivation_eq_of_forall_mem_vars MvPolynomial.derivation_eq_of_forall_mem_vars

theorem derivation_eq_zero_of_forall_mem_vars {D : Derivation R (MvPolynomial σ R) A}
    {f : MvPolynomial σ R} (h : ∀ i ∈ f.vars, D (X i) = 0) : D f = 0 :=
  show D f = (0 : Derivation R (MvPolynomial σ R) A) f from derivation_eq_of_forall_mem_vars h
#align mv_polynomial.derivation_eq_zero_of_forall_mem_vars MvPolynomial.derivation_eq_zero_of_forall_mem_vars

@[ext]
theorem derivation_ext {D₁ D₂ : Derivation R (MvPolynomial σ R) A} (h : ∀ i, D₁ (X i) = D₂ (X i)) :
    D₁ = D₂ :=
  Derivation.ext fun f => derivation_eq_of_forall_mem_vars fun i _ => h i
#align mv_polynomial.derivation_ext MvPolynomial.derivation_ext

variable [IsScalarTower R (MvPolynomial σ R) A]

theorem leibniz_iff_x (D : MvPolynomial σ R →ₗ[R] A) (h₁ : D 1 = 0) :
    (∀ p q, D (p * q) = p • D q + q • D p) ↔
      ∀ s i,
        D (monomial s 1 * X i) =
          (monomial s 1 : MvPolynomial σ R) • D (X i) +
            (X i : MvPolynomial σ R) • D (monomial s 1) := by
  refine' ⟨fun H p i => H _ _, fun H => _⟩
  have hC : ∀ r, D (C r) = 0 := by intro r; rw [C_eq_smul_one, D.map_smul, h₁, smul_zero]
  have : ∀ p i, D (p * X i) = p • D (X i) + (X i : MvPolynomial σ R) • D p := by
    intro p i
    induction' p using MvPolynomial.induction_on' with s r p q hp hq
    · rw [← mul_one r, ← C_mul_monomial, mul_assoc, C_mul', D.map_smul, H, C_mul', smul_assoc,
        smul_add, D.map_smul, smul_comm r (X i)]
      infer_instance
    · rw [add_mul, map_add, map_add, hp, hq, add_smul, smul_add, add_add_add_comm]
  intro p q
  induction q using MvPolynomial.induction_on
  case h_C c =>
    rw [mul_comm, C_mul', hC, smul_zero, zero_add, D.map_smul, C_eq_smul_one, smul_one_smul]
  case h_add q₁ q₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂, smul_add, add_smul]; abel
  case h_X q i hq =>
    simp only [this, ← mul_assoc, hq, mul_smul, smul_add, smul_comm (X i), add_assoc]
#align mv_polynomial.leibniz_iff_X MvPolynomial.leibniz_iff_x

variable (R)

/-- The derivation on `mv_polynomial σ R` that takes value `f i` on `X i`. -/
def mkDerivation (f : σ → A) : Derivation R (MvPolynomial σ R) A where
  toLinearMap := mkDerivationₗ R f
  map_one_eq_zero' := mkDerivationₗ_c _ 1
  leibniz' :=
    (leibniz_iff_x (mkDerivationₗ R f) (mkDerivationₗ_c _ 1)).2 fun s i => by
      simp only [mk_derivationₗ_monomial, X, monomial_mul, one_smul, one_mul]
      rw [Finsupp.sum_add_index'] <;> [skip; · simp;
        · intros; simp only [Nat.cast_add, (monomial _).map_add, add_smul]]
      rw [Finsupp.sum_single_index, Finsupp.sum_single_index] <;> [skip; · simp; · simp]
      rw [tsub_self, add_tsub_cancel_right, Nat.cast_one, ← C_apply, C_1, one_smul, add_comm,
        Finsupp.smul_sum]
      refine' congr_arg₂ (· + ·) rfl (Finset.sum_congr rfl fun j hj => _); dsimp only
      rw [smul_smul, monomial_mul, one_mul, add_comm s, add_tsub_assoc_of_le]
      rwa [Finsupp.single_le_iff, Nat.succ_le_iff, pos_iff_ne_zero, ← Finsupp.mem_support_iff]
#align mv_polynomial.mk_derivation MvPolynomial.mkDerivation

@[simp]
theorem mkDerivation_x (f : σ → A) (i : σ) : mkDerivation R f (X i) = f i :=
  mkDerivationₗ_x f i
#align mv_polynomial.mk_derivation_X MvPolynomial.mkDerivation_x

theorem mkDerivation_monomial (f : σ → A) (s : σ →₀ ℕ) (r : R) :
    mkDerivation R f (monomial s r) =
      r • s.Sum fun i k => monomial (s - Finsupp.single i 1) (k : R) • f i :=
  mkDerivationₗ_monomial f s r
#align mv_polynomial.mk_derivation_monomial MvPolynomial.mkDerivation_monomial

/-- `mv_polynomial.mk_derivation` as a linear equivalence. -/
def mkDerivationEquiv : (σ → A) ≃ₗ[R] Derivation R (MvPolynomial σ R) A :=
  LinearEquiv.symm <|
    { invFun := mkDerivation R
      toFun := fun D i => D (X i)
      map_add' := fun D₁ D₂ => rfl
      map_smul' := fun c D => rfl
      left_inv := fun D => derivation_ext <| mkDerivation_x _ _
      right_inv := fun f => funext <| mkDerivation_x _ _ }
#align mv_polynomial.mk_derivation_equiv MvPolynomial.mkDerivationEquiv

end MvPolynomial

