/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Mathlib.Algebra.MvPolynomial.Monad

/-!
## Expand multivariate polynomials

Given a multivariate polynomial `φ`, one may replace every occurrence of `X i` by `X i ^ n`,
for some natural number `n`.
This operation is called `MvPolynomial.expand` and it is an algebra homomorphism.

### Main declaration

* `MvPolynomial.expand`: expand a polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.
-/


namespace MvPolynomial

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S]

/-- Expand the polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.

See also `Polynomial.expand`. -/
noncomputable def expand (p : ℕ) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  bind₁ fun i ↦ X i ^ p

theorem expand_C (p : ℕ) (r : R) : expand p (C r : MvPolynomial σ R) = C r :=
  eval₂Hom_C _ _ _

@[simp]
theorem expand_X (p : ℕ) (i : σ) : expand p (X i : MvPolynomial σ R) = X i ^ p :=
  eval₂Hom_X' _ _ _

@[simp]
theorem expand_monomial (p : ℕ) (d : σ →₀ ℕ) (r : R) :
    expand p (monomial d r) = monomial (p • d) r := by
  rw [expand, bind₁_monomial, monomial_eq, Finsupp.prod_of_support_subset _ Finsupp.support_smul]
  · simp [pow_mul]
  · simp

@[simp]
lemma expand_zero :
    expand 0 (σ := σ) (R := R) = .comp (Algebra.ofId R _) (MvPolynomial.aeval (1 : σ → R)) := by
  ext1 i
  simp

lemma expand_zero_apply (p : MvPolynomial σ R) : expand 0 p = .C (MvPolynomial.eval 1 p) := by
  simp

@[simp]
theorem expand_one : expand 1 = AlgHom.id R (MvPolynomial σ R) := by
  ext1 i
  simp

theorem expand_one_apply (f : MvPolynomial σ R) : expand 1 f = f := by simp

theorem expand_comp_bind₁ (p : ℕ) (f : σ → MvPolynomial τ R) :
    (expand p).comp (bind₁ f) = bind₁ fun i ↦ expand p (f i) := by
  ext1 i
  simp

theorem expand_bind₁ (p : ℕ) (f : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    expand p (bind₁ f φ) = bind₁ (fun i ↦ expand p (f i)) φ := by
  rw [← AlgHom.comp_apply, expand_comp_bind₁]

@[simp]
theorem map_expand (f : R →+* S) (p : ℕ) (φ : MvPolynomial σ R) :
    map f (expand p φ) = expand p (map f φ) := by simp [expand, map_bind₁]

@[simp]
theorem rename_comp_expand (f : σ → τ) (p : ℕ) :
    (rename f).comp (expand p) =
      (expand p).comp (rename f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) := by
  ext1 i
  simp

@[simp]
theorem rename_expand (f : σ → τ) (p : ℕ) (φ : MvPolynomial σ R) :
    rename f (expand p φ) = expand p (rename f φ) :=
  DFunLike.congr_fun (rename_comp_expand f p) φ

lemma eval₂Hom_comp_expand (f : R →+* S) (g : σ → S) (p : ℕ) :
    (eval₂Hom f g).comp (expand p (σ := σ) (R := R) : MvPolynomial σ R →+* MvPolynomial σ R) =
      eval₂Hom f (g ^ p) := by
  ext <;> simp

@[simp]
lemma eval₂_expand (f : R →+* S) (g : σ → S) (φ : MvPolynomial σ R) (p : ℕ) :
    eval₂ f g (expand p φ) = eval₂ f (g ^ p) φ :=
  DFunLike.congr_fun (eval₂Hom_comp_expand f g p) φ

@[simp]
lemma aeval_comp_expand {A : Type*} [CommSemiring A] [Algebra R A] (f : σ → A) (p : ℕ) :
    (aeval f).comp (expand p) = aeval (R := R) (f ^ p) := by
  ext; simp

@[simp]
lemma aeval_expand {A : Type*} [CommSemiring A] [Algebra R A]
    (f : σ → A) (φ : MvPolynomial σ R) (p : ℕ) :
    aeval f (expand p φ) = aeval (f ^ p) φ :=
  eval₂_expand ..

@[simp]
lemma eval_expand (f : σ → R) (φ : MvPolynomial σ R) (p : ℕ) :
    eval f (expand p φ) = eval (f ^ p) φ :=
  eval₂_expand ..

theorem expand_mul_eq_comp (p q : ℕ) :
    expand (σ := σ) (R := R) (p * q) = (expand p).comp (expand q) := by
  ext1 i
  simp [pow_mul]

theorem expand_mul (p q : ℕ) (φ : MvPolynomial σ R) : φ.expand (p * q) = (φ.expand q).expand p :=
  DFunLike.congr_fun (expand_mul_eq_comp p q) φ

@[simp]
lemma coeff_expand_smul (φ : MvPolynomial σ R) {p : ℕ} (hp : p ≠ 0) (m : σ →₀ ℕ) :
    (expand p φ).coeff (p • m) = φ.coeff m := by
  classical
  induction φ using induction_on' <;> simp [*, nsmul_right_inj hp]

lemma support_expand_subset [DecidableEq σ] (φ : MvPolynomial σ R) (p : ℕ) :
    (expand p φ).support ⊆ φ.support.image (p • ·) := by
  conv_lhs => rw [φ.as_sum]
  simp only [map_sum, expand_monomial]
  refine MvPolynomial.support_sum.trans ?_
  aesop (add simp Finset.subset_iff)

lemma coeff_expand_of_not_dvd (φ : MvPolynomial σ R) {p : ℕ} {m : σ →₀ ℕ} {i : σ} (h : ¬(p ∣ m i)) :
    (expand p φ).coeff m = 0 := by
  classical
  contrapose! h
  grw [← mem_support_iff, support_expand_subset, Finset.mem_image] at h
  rcases h with ⟨a, -, rfl⟩
  exact ⟨a i, by simp⟩

lemma support_expand [DecidableEq σ] (φ : MvPolynomial σ R) {p : ℕ} (hp : p ≠ 0) :
    (expand p φ).support = φ.support.image (p • ·) := by
  refine (support_expand_subset φ p).antisymm ?_
  simp [Finset.image_subset_iff, hp]

end MvPolynomial
