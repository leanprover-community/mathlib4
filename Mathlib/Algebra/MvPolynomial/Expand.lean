/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Irreducible.Lemmas
import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Order.Ring.Finset
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
## Expand multivariate polynomials

Given a multivariate polynomial `φ`, one may replace every occurrence of `X i` by `X i ^ n`,
for some natural number `n`.
This operation is called `MvPolynomial.expand` and it is an algebra homomorphism.

### Main declaration

* `MvPolynomial.expand`: expand a polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.
-/

@[expose] public section


namespace MvPolynomial

section CommSemiring

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

/-- Expand the polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.

See also `Polynomial.expand`. -/
noncomputable def expand : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  bind₁ fun i ↦ X i ^ p

theorem coe_expand :
    (expand p (R := R) (σ := σ)) = eval₂ C ((fun s ↦ X s : σ → MvPolynomial σ R) ^ p) := rfl

theorem expand_C (r : R) : expand p (C r : MvPolynomial σ R) = C r :=
  eval₂Hom_C _ _ _

@[simp]
theorem expand_X (i : σ) : expand p (X i : MvPolynomial σ R) = X i ^ p :=
  eval₂Hom_X' _ _ _

@[simp]
theorem expand_monomial (d : σ →₀ ℕ) (r : R) :
    expand p (monomial d r) = monomial (p • d) r := by
  rw [expand, bind₁_monomial, monomial_eq, Finsupp.prod_of_support_subset _ Finsupp.support_smul]
  · simp [pow_mul]
  · simp

@[simp]
lemma expand_zero :
    expand 0 (σ := σ) (R := R) = .comp (Algebra.ofId R _) (MvPolynomial.aeval (1 : σ → R)) := by
  ext1 i
  simp

lemma expand_zero_apply (f : MvPolynomial σ R) : expand 0 f = .C (MvPolynomial.eval 1 f) := by
  simp

@[simp]
theorem expand_one : expand 1 = AlgHom.id R (MvPolynomial σ R) := by
  ext1 i
  simp

theorem expand_one_apply (f : MvPolynomial σ R) : expand 1 f = f := by simp

theorem expand_mul_eq_comp (q : ℕ) :
    expand (σ := σ) (R := R) (p * q) = (expand p).comp (expand q) := by
  ext1 i
  simp [pow_mul]

theorem expand_mul (q : ℕ) (φ : MvPolynomial σ R) : φ.expand (p * q) = (φ.expand q).expand p :=
  DFunLike.congr_fun (expand_mul_eq_comp p q) φ

@[simp]
lemma coeff_expand_smul (hp : p ≠ 0) (φ : MvPolynomial σ R) (m : σ →₀ ℕ) :
    (expand p φ).coeff (p • m) = φ.coeff m := by
  classical
  induction φ using induction_on' <;> simp [*, nsmul_right_inj hp]

@[simp]
lemma coeff_expand_zero (hp : p ≠ 0) (φ : MvPolynomial σ R) :
    (expand p φ).coeff 0 = φ.coeff 0 :=
  calc (expand p φ).coeff 0 = (expand p φ).coeff (p • 0) := by rw [smul_zero]
                          _ = φ.coeff 0 := by rw [coeff_expand_smul p hp]

/-- Expansion is injective. -/
theorem expand_injective {n : ℕ} (hn : 0 < n) : Function.Injective (expand n (R := R) (σ := σ)) :=
  fun g g' H => by
    ext d
    rw [← coeff_expand_smul _ (n.ne_zero_iff_zero_lt.mpr hn), H, coeff_expand_smul _
      (n.ne_zero_iff_zero_lt.mpr hn)]

theorem expand_inj {p : ℕ} (hp : 0 < p) {f g : MvPolynomial σ R} :
    expand p f = expand p g ↔ f = g := (expand_injective hp).eq_iff

theorem expand_eq_zero {p : ℕ} (hp : 0 < p) {f : MvPolynomial σ R} : expand p f = 0 ↔ f = 0 :=
  (expand_injective hp).eq_iff' (map_zero _)

theorem expand_ne_zero {p : ℕ} (hp : 0 < p) {f : MvPolynomial σ R} : expand p f ≠ 0 ↔ f ≠ 0 :=
  (expand_eq_zero hp).not

theorem expand_eq_C {p : ℕ} (hp : 0 < p) {f : MvPolynomial σ R} {r : R} :
    expand p f = C r ↔ f = C r := by
  rw [← expand_C, expand_inj hp, expand_C]

theorem expand_comp_bind₁ (p : ℕ) (f : σ → MvPolynomial τ R) :
    (expand p).comp (bind₁ f) = bind₁ fun i ↦ expand p (f i) := by
  ext1 i
  simp

theorem expand_bind₁ (f : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    expand p (bind₁ f φ) = bind₁ (fun i ↦ expand p (f i)) φ := by
  rw [← AlgHom.comp_apply, expand_comp_bind₁]

@[simp]
theorem map_expand (f : R →+* S) (φ : MvPolynomial σ R) :
    map f (expand p φ) = expand p (map f φ) := by simp [expand, map_bind₁]

@[simp]
theorem rename_comp_expand (f : σ → τ) :
    (rename f).comp (expand p) =
      (expand p).comp (rename f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) := by
  ext1 i
  simp

@[simp]
theorem rename_expand (f : σ → τ) (φ : MvPolynomial σ R) :
    rename f (expand p φ) = expand p (rename f φ) :=
  DFunLike.congr_fun (rename_comp_expand p f) φ

lemma eval₂Hom_comp_expand (f : R →+* S) (g : σ → S) :
    (eval₂Hom f g).comp (expand p (σ := σ) (R := R) : MvPolynomial σ R →+* MvPolynomial σ R) =
      eval₂Hom f (g ^ p) := by
  ext <;> simp

@[simp]
lemma eval₂_expand (f : R →+* S) (g : σ → S) (φ : MvPolynomial σ R) :
    eval₂ f g (expand p φ) = eval₂ f (g ^ p) φ :=
  DFunLike.congr_fun (eval₂Hom_comp_expand p f g) φ

@[simp]
lemma aeval_comp_expand {A : Type*} [CommSemiring A] [Algebra R A] (f : σ → A) :
    (aeval f).comp (expand p) = aeval (R := R) (f ^ p) := by
  ext; simp

@[simp]
lemma aeval_expand {A : Type*} [CommSemiring A] [Algebra R A]
    (f : σ → A) (φ : MvPolynomial σ R) :
    aeval f (expand p φ) = aeval (f ^ p) φ :=
  eval₂_expand ..

@[simp]
lemma eval_expand (f : σ → R) (φ : MvPolynomial σ R) :
    eval f (expand p φ) = eval (f ^ p) φ :=
  eval₂_expand ..

section

variable {p} (φ : MvPolynomial σ R)

lemma support_expand_subset [DecidableEq σ] :
    (expand p φ).support ⊆ φ.support.image (p • ·) := by
  conv_lhs => rw [φ.as_sum]
  simp only [map_sum, expand_monomial]
  refine MvPolynomial.support_sum.trans ?_
  aesop (add simp Finset.subset_iff)

lemma coeff_expand_of_not_dvd {m : σ →₀ ℕ} {i : σ} (h : ¬ p ∣ m i) :
    (expand p φ).coeff m = 0 := by
  classical
  contrapose! h
  grw [← mem_support_iff, support_expand_subset, Finset.mem_image] at h
  rcases h with ⟨a, -, rfl⟩
  exact ⟨a i, by simp⟩

lemma support_expand [DecidableEq σ] (hp : p ≠ 0) :
    (expand p φ).support = φ.support.image (p • ·) := by
  refine (support_expand_subset φ).antisymm ?_
  simp [Finset.image_subset_iff, hp]

theorem totalDegree_expand (f : MvPolynomial σ R) :
    (expand p f).totalDegree = f.totalDegree * p := by
  classical
  rcases p.eq_zero_or_pos with hp | hp
  · simp [hp]
  by_cases hf : f = 0
  · rw [hf, map_zero, totalDegree_zero, zero_mul]
  simp_rw [totalDegree_eq, support_expand _ (p.ne_zero_iff_zero_lt.mpr hp)]
  simp only [Finsupp.card_toMultiset, Finset.sup_image, Finset.sup_mul₀, Function.comp_def]
  congr! 2 with d
  rw [Finsupp.sum_of_support_subset _ Finsupp.support_smul _ (by simp)]
  simp [Finsupp.sum, Finset.sum_mul, mul_comm p]

end

end CommSemiring

section CommRing

variable (R σ : Type*) [CommRing R]

theorem isLocalHom_expand {p : ℕ} (hp : p ≠ 0) : IsLocalHom (expand p (R := R) (σ := σ)) := by
  refine ⟨fun f hf => ?_⟩
  rw [MvPolynomial.isUnit_iff] at hf ⊢
  simp only [coeff_expand_zero p hp] at hf
  refine ⟨hf.1, fun i hi ↦ ?_⟩
  rw [← coeff_expand_smul p hp]
  apply hf.2
  simp [hi, hp]

variable {R}

theorem of_irreducible_expand {p : ℕ} (hp : p ≠ 0) {f : MvPolynomial σ R}
    (hf : Irreducible (expand p f)) :
    Irreducible f :=
  let _ := isLocalHom_expand R σ hp
  hf.of_map

end CommRing

end MvPolynomial
