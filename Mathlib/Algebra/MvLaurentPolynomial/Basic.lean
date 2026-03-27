/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Laurent monomials relative to a basis

This file develops a basis-parametric Laurent-monomial API on `AddMonoidAlgebra R M`, where
`M` is an additive abelian group equipped with a chosen basis `v : Basis σ ℤ M`. In this setting,
`AddMonoidAlgebra R M` can be thought of as the algebra of multivariate Laurent polynomials whose
variables are indexed by `σ`.

## Important definitions

* `MvLaurentPolynomial.monomial v d r` : the Laurent monomial with exponent vector `d` and
  coefficient `r` with respect to the basis `v`
* `MvLaurentPolynomial.X v n` : the Laurent monomial corresponding to the variable `n` with respect
  to the basis `v`
* `MvLaurentPolynomial.basisAlgEquiv v` : the algebra equivalence from `AddMonoidAlgebra R M` to
  the coordinate Laurent model `AddMonoidAlgebra R (σ →₀ ℤ)` induced by `v`
* `MvPolynomial.toMvLaurent` : the natural inclusion from multivariate polynomials to
  Laurent monomials written in the basis `v`

-/

@[expose] public section

open Function AddMonoidAlgebra Module

noncomputable section

variable {R : Type*} {S : Type*} {σ : Type*} {M : Type*}

namespace AddMonoidAlgebra

section CommSemiring

variable [CommSemiring R] [AddCommGroup M] {p q : AddMonoidAlgebra R M}

/-- The Laurent monomial with exponent vector `d`, expressed in the basis `v`. -/
abbrev monomial (v : σ → M) (d : σ →₀ ℤ) : R →ₗ[R] AddMonoidAlgebra R M :=
  lsingle (Finsupp.linearCombination ℤ v d)

theorem one_eq_monomial (v : σ → M) :
    (1 : AddMonoidAlgebra R M) = monomial v 0 1 := by
  rfl

theorem single_eq_monomial (v : σ → M) (d : σ →₀ ℤ) (r : R) :
    single (Finsupp.linearCombination ℤ v d) r = monomial v d r := by
  rfl

theorem mul_eq_sum_monomial (v : Basis σ ℤ M) :
    p * q = p.sum fun d r ↦ q.sum fun e s ↦ monomial v (v.repr d + v.repr e) (r * s) := by
  simp [AddMonoidAlgebra.mul_def, monomial]

/-- The Laurent variable corresponding to the basis vector indexed by `i`. -/
abbrev X (v : σ → M) (i : σ) : AddMonoidAlgebra R M := monomial v (Finsupp.single i 1) 1

theorem X_eq_monomial (v : σ → M) (i : σ) :
    X v i = monomial v (Finsupp.single i 1) (1 : R) := by
  simp [X, monomial]

theorem monomial_left_injective (v : Basis σ ℤ M) {r : R} (hr : r ≠ 0) :
    Function.Injective fun d : σ →₀ ℤ ↦ monomial v d r := by
  intro d e h
  exact v.repr.symm.injective (Finsupp.single_left_injective hr (by simpa using h))

theorem monomial_left_inj (v : Basis σ ℤ M) {d e : σ →₀ ℤ} {r : R} (hr : r ≠ 0) :
    monomial v d r = monomial v e r ↔ d = e :=
  (monomial_left_injective v hr).eq_iff

theorem smul_monomial {T : Type*} [SMulZeroClass T R] (t : T) (v : Basis σ ℤ M)
    (d : σ →₀ ℤ) (r : R) : t • monomial v d r = monomial v d (t • r) := by
  simp [monomial]

theorem X_injective (v : Basis σ ℤ M) [Nontrivial R] :
    Function.Injective (X v : σ → AddMonoidAlgebra R M) :=
  (monomial_left_injective v one_ne_zero).comp (Finsupp.single_left_injective (one_ne_zero))

theorem X_inj (v : Basis σ ℤ M) [Nontrivial R] {i j : σ} :
    X v i = (X v j : AddMonoidAlgebra R M) ↔ i = j :=
  ⟨fun h ↦ X_injective v h, fun h ↦ congrArg _ h⟩

theorem monomial_pow (v : σ → M) (d : σ →₀ ℤ) (r : R) (n : ℕ) :
    monomial v d r ^ n = monomial v (n • d) (r ^ n) := by
  simp only [monomial, lsingle_apply, single_pow, LinearMap.map_smul_of_tower]

theorem X_pow_eq_monomial (v : σ → M) (i : σ) (e : ℕ) :
    X v i ^ e = monomial v (Finsupp.single i (e : ℤ)) (1 : R) := by
  simp only [X, monomial, Finsupp.linearCombination_single, one_smul, lsingle_apply, single_pow,
    one_pow, natCast_zsmul]

theorem monomial_mul (v : σ → M) {d e : σ →₀ ℤ} {r s : R} :
    monomial v d r * monomial v e s = monomial v (d + e) (r * s) := by
  simp [monomial, AddMonoidAlgebra.single_mul_single]

theorem isUnit_monomial (v : σ → M) (d : σ →₀ ℤ) :
    IsUnit (monomial v d (1 : R) : AddMonoidAlgebra R M) :=
  ⟨⟨monomial v d 1, monomial v (-d) 1, by simp [← one_def], by simp [← one_def]⟩, rfl⟩

theorem monomial_add_single (v : σ → M) (d : σ →₀ ℤ) (i : σ) (e : ℕ) (r : R) :
    monomial v (d + Finsupp.single i (e : ℤ)) r = monomial v d r * X v i ^ e := by
  rw [X_pow_eq_monomial, monomial_mul, mul_one]

theorem monomial_single_add (v : σ → M) (d : σ →₀ ℤ) (i : σ) (e : ℕ) (r : R) :
    monomial v (Finsupp.single i (e : ℤ) + d) r = X v i ^ e * monomial v d r := by
  rw [X_pow_eq_monomial, monomial_mul, one_mul]

theorem monomial_zero (v : σ → M) {d : σ →₀ ℤ} : monomial v d (0 : R) = 0 := by
  rw [monomial]
  exact Finsupp.single_eq_zero.2 rfl

theorem monomial_eq_zero (v : σ → M) {d : σ →₀ ℤ} {r : R} :
    monomial v d r = 0 ↔ r = 0 := by
  simp

theorem sum_monomial_eq {A : Type*} [AddCommMonoid A] (v : σ → M) {d : σ →₀ ℤ} {r : R}
    {f : M → R → A} (h0 : f ((Finsupp.linearCombination ℤ v) d) 0 = 0) :
    (monomial v d r).sum f = f (Finsupp.linearCombination ℤ v d) r := by
  simpa [monomial] using (Finsupp.sum_single_index h0 : _)

theorem support_monomial (v : σ → M) {d : σ →₀ ℤ} {r : R} [Decidable (r = 0)] :
    (monomial v d r : AddMonoidAlgebra R M).support =
      if r = 0 then ∅ else {Finsupp.linearCombination ℤ v d} := by
  by_cases hr : r = 0
  · simp [monomial, hr]
  · simpa [monomial, hr] using Finsupp.support_single_ne_zero (Finsupp.linearCombination ℤ v d) hr

theorem support_monomial_subset (v : σ → M) (d : σ →₀ ℤ) (r : R) :
    (monomial v d r : AddMonoidAlgebra R M).support ⊆ {Finsupp.linearCombination ℤ v d} := by
  classical
  by_cases hr : r = 0
  · simp [monomial, hr]
  · grind [lsingle_apply]

theorem X_ne_zero (v : σ → M) [Nontrivial R] (i : σ) :
    X v i ≠ (0 : AddMonoidAlgebra R M) := by
  simp

section AsSum

theorem support_sum_monomial_coeff (v : Basis σ ℤ M) (p : AddMonoidAlgebra R M) :
    (∑ m ∈ p.support, monomial v (v.repr m) (p m)) = p := by
  simpa [Finsupp.sum, monomial] using (Finsupp.sum_single p)

theorem as_sum (v : Basis σ ℤ M) (p : AddMonoidAlgebra R M) :
    p = ∑ m ∈ p.support, monomial v (v.repr m) (p m) :=
  (support_sum_monomial_coeff v p).symm

end AsSum

/-- To prove something about Laurent monomials relative to `v`, it suffices to prove it for
monomials and to show that it is preserved by addition. -/
@[elab_as_elim]
theorem induction_on' (v : Basis σ ℤ M) {P : AddMonoidAlgebra R M → Prop} (p : AddMonoidAlgebra R M)
    (hmonomial : ∀ (d : σ →₀ ℤ) (r : R), P (monomial v d r))
    (hadd : ∀ p q : AddMonoidAlgebra R M, P p → P q → P (p + q)) : P p := by
  refine Finsupp.induction p ?_ ?_
  · simpa [monomial] using hmonomial 0 0
  · intro m r p _ _ hp
    simpa [monomial] using hadd (monomial v (v.repr m) r) p (hmonomial (v.repr m) r) hp

/-- The algebra equivalence to the coordinate Laurent model induced by the basis `v`. -/
def laurentBasisAlgEquiv (v : Basis σ ℤ M) :
    AddMonoidAlgebra R M ≃ₐ[R] AddMonoidAlgebra R (σ →₀ ℤ) :=
  AddMonoidAlgebra.domCongr R R v.repr.toAddEquiv

theorem laurentBasisAlgEquiv_monomial (v : Basis σ ℤ M) (d : σ →₀ ℤ) (r : R) :
    laurentBasisAlgEquiv v (monomial v d r) = AddMonoidAlgebra.single d r := by
  ext e
  simp [laurentBasisAlgEquiv, monomial]

@[simp]
theorem laurentBasisAlgEquiv_apply (v : Basis σ ℤ M) (p : AddMonoidAlgebra R M) (d : σ →₀ ℤ) :
    laurentBasisAlgEquiv v p d = p (v.repr.symm d) := by
  simp [laurentBasisAlgEquiv]

end CommSemiring

end AddMonoidAlgebra

namespace MvPolynomial

section CommSemiring

variable [CommSemiring R] [AddCommGroup M]

/-- The natural inclusion from multivariate polynomials to multivariate Laurent polynomials
written in the basis `v`. -/
def toMvLaurent (v : Basis σ ℤ M) : MvPolynomial σ R →ₐ[R] AddMonoidAlgebra R M :=
  (AddMonoidAlgebra.laurentBasisAlgEquiv v).symm.toAlgHom.comp
    (AddMonoidAlgebra.mapDomainAlgHom R R
      (Finsupp.mapRange.addMonoidHom (Int.ofNatHom : ℕ →+ ℤ)))

@[simp]
theorem laurentBasisAlgEquiv_toMvLaurent (v : Basis σ ℤ M) (p : MvPolynomial σ R) :
    AddMonoidAlgebra.laurentBasisAlgEquiv v (p.toMvLaurent v) =
      (AddMonoidAlgebra.mapDomainAlgHom R R
        (Finsupp.mapRange.addMonoidHom (Int.ofNatHom : ℕ →+ ℤ))) p := by
  simp only [toMvLaurent, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp, AlgHom.coe_coe, comp_apply,
    AlgEquiv.apply_symm_apply, mapDomainAlgHom_apply]
  rfl

@[simp]
theorem toMvLaurent_monomial (v : Basis σ ℤ M) (d : σ →₀ ℕ) (r : R) :
    (MvPolynomial.monomial d r).toMvLaurent v =
      AddMonoidAlgebra.monomial v (d.mapRange Int.ofNat (by simp)) r := by
  apply (AddMonoidAlgebra.laurentBasisAlgEquiv v).injective
  simp only [laurentBasisAlgEquiv_toMvLaurent, mapDomainAlgHom_apply,
    AddMonoidAlgebra.laurentBasisAlgEquiv_monomial]
  apply mapDomain_single

@[simp]
theorem toMvLaurent_X (v : Basis σ ℤ M) (i : σ) :
    (MvPolynomial.X i : MvPolynomial σ R).toMvLaurent v = AddMonoidAlgebra.X v i := by
  simp only [X, toMvLaurent_monomial, Finsupp.mapRange_single, Int.ofNat_eq_natCast, Nat.cast_one,
    AddMonoidAlgebra.X_eq_monomial]

theorem toMvLaurent_injective (v : Basis σ ℤ M) :
    Function.Injective fun p : MvPolynomial σ R ↦ p.toMvLaurent v := by
  intro p q hpq
  apply AddMonoidAlgebra.mapDomain_injective
    (Finsupp.mapRange_injective Int.ofNat (by simp) Int.ofNat_injective)
  simpa [laurentBasisAlgEquiv_toMvLaurent] using
    congrArg (AddMonoidAlgebra.laurentBasisAlgEquiv v) hpq

theorem toMvLaurent_inj (v : Basis σ ℤ M) {p q : MvPolynomial σ R} :
    p.toMvLaurent v = q.toMvLaurent v ↔ p = q :=
  (toMvLaurent_injective v).eq_iff

theorem toMvLaurent_eq_zero (v : Basis σ ℤ M) {p : MvPolynomial σ R} :
    p.toMvLaurent v = 0 ↔ p = 0 :=
  map_eq_zero_iff _ (toMvLaurent_injective v)

theorem toMvLaurent_ne_zero (v : Basis σ ℤ M) {p : MvPolynomial σ R} :
    p.toMvLaurent v ≠ 0 ↔ p ≠ 0 :=
  map_ne_zero_iff _ (toMvLaurent_injective v)

end CommSemiring

end MvPolynomial

namespace MvLaurentPolynomial

section CommSemiring

variable [CommSemiring R] [AddCommGroup M] [Free ℤ M]

instance algebraMvPolynomial :
    Algebra (MvPolynomial (Free.ChooseBasisIndex ℤ M) R) (AddMonoidAlgebra R M) where
  __ := (MvPolynomial.toMvLaurent <| Free.chooseBasis ℤ M).toAlgebra

@[simp]
theorem algebraMap_eq_toMvLaurent (p : MvPolynomial (Free.ChooseBasisIndex ℤ M) R) :
    algebraMap (MvPolynomial (Free.ChooseBasisIndex ℤ M) R) (AddMonoidAlgebra R M) p =
      p.toMvLaurent (Free.chooseBasis ℤ M) :=
  rfl

end CommSemiring

end MvLaurentPolynomial
