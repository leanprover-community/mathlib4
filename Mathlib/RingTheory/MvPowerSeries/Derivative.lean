/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.MvPowerSeries.Trunc

/-!
# Formal partial derivatives of multivariate power series

This file defines `MvPowerSeries.pderiv R i`, the formal partial derivative of a multivariate
power series with respect to variable `i`, as a
`Derivation R (MvPowerSeries σ R) (MvPowerSeries σ R)`.

See also `PowerSeries.derivative` for the univariate setting.

## Main definitions

- `MvPowerSeries.pderiv R i`: the formal partial derivative with respect to `i`, as a derivation.

## Main results

- `MvPowerSeries.coeff_pderiv`: coefficient formula
  `coeff n (pderiv R i f) = coeff (n + single i 1) f * (n i + 1)`.
- `MvPowerSeries.pderiv_coe`: compatibility with `MvPolynomial.pderiv`.
- `MvPowerSeries.trunc_pderiv`: truncation commutes with partial differentiation.
- `MvPowerSeries.pderiv.ext`: a power series is determined by its constant term and its partial
  derivatives.
- `MvPowerSeries.pderiv_pow`: power rule.
- `MvPowerSeries.pderiv_inv`, `MvPowerSeries.pderiv_inv'`: derivative of an inverse.
- `MvPowerSeries.continuous_pderiv`: `pderiv R i` is continuous for the product topology.
- `MvPowerSeries.pderiv_subst_tsum`: the chain rule for substitution,
  `pderiv S i (subst a f) = ∑' j, subst a (pderiv R j f) * pderiv S i (a j)`.
- `MvPowerSeries.pderiv_subst`: the same chain rule as a `Finset.sum`, when there are only
  finitely many variables.

-/

@[expose] public section

namespace MvPowerSeries

open MvPolynomial Finsupp

variable {σ R : Type*}

section Semiring

variable [Semiring R]

/-- The underlying function of the formal partial derivative with respect to variable `i`.
This is packaged as a derivation in `MvPowerSeries.pderiv`. -/
noncomputable def pderivFun (i : σ) (f : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun d ↦ coeff (d + single i 1) f * (d i + 1)

theorem coeff_pderivFun {i : σ} (f : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    coeff d (f.pderivFun i) = coeff (d + single i 1) f * (d i + 1) := by
  rfl

theorem pderivFun_add {i : σ} (f g : MvPowerSeries σ R) :
    pderivFun i (f + g) = pderivFun i f + pderivFun i g := by
  ext
  rw [coeff_pderivFun, map_add, map_add, coeff_pderivFun, coeff_pderivFun, add_mul]

theorem pderivFun_C {i : σ} (r : R) : pderivFun i (C r) = 0 := by
  ext n
  rw [coeff_pderivFun, coeff_add_single_C, zero_mul, (coeff n).map_zero]

theorem pderivFun_one {i : σ} : pderivFun i (1 : MvPowerSeries σ R) = 0 := by
  rw [← map_one C, pderivFun_C (1 : R)]

end Semiring

section CommSemiring

variable [CommSemiring R]

private theorem pderivFun_coe {i : σ} (f : MvPolynomial σ R) :
    (f : MvPowerSeries σ R).pderivFun i = f.pderiv i := by
  ext
  rw [coeff_pderivFun, coeff_coe, coeff_coe, coeff_pderiv]

private theorem trunc_pderivFun [DecidableEq σ] {i : σ} (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    trunc R n (pderivFun i f) = pderiv i (trunc R (n + single i 1) f) := by
  ext
  rw [coeff_trunc]
  split_ifs with h
  · rw [coeff_pderivFun, coeff_pderiv, coeff_trunc, ite_eq_left (add_lt_add_left h _)]
  · rw [coeff_pderiv, coeff_trunc, ite_eq_right ((add_lt_add_iff_right _).not.mpr h), zero_mul]

-- A special case of `pderivFun_mul`, used in its proof.
private theorem pderivFun_coe_mul_coe {i : σ} (f g : MvPolynomial σ R) :
    pderivFun i (f * g : MvPowerSeries σ R) = f * pderiv i g + g * pderiv i f := by
  rw [← coe_mul, pderivFun_coe, pderiv_mul, add_comm, mul_comm _ g, ← coe_mul, ← coe_mul,
    MvPolynomial.coe_add]

private theorem pderivFun_mul {i : σ} (f g : MvPowerSeries σ R) :
    pderivFun i (f * g) = f • g.pderivFun i + g • f.pderivFun i := by
  classical
  ext n
  have h₁ : n < n + single i 1 := lt_def.mpr ⟨self_le_add_right _ _, i, by simp⟩
  have h₂ : n + single i 1 < n + single i 1 + single i 1 :=
    lt_def.mpr ⟨self_le_add_right _ _, i, by simp⟩
  have h₃ : n < n + single i 1 + single i 1 := lt_trans h₁ h₂
  rw [coeff_pderivFun, map_add, ← coeff_trunc_mul_trunc_eq_coeff_mul _ _ _ h₂, smul_eq_mul,
    smul_eq_mul, ← coeff_trunc_mul_trunc_eq_coeff_mul₂ _ _ g (f.pderivFun i) h₃ h₁,
    ← coeff_trunc_mul_trunc_eq_coeff_mul₂ _ _ f (g.pderivFun i) h₃ h₁, trunc_pderivFun,
    trunc_pderivFun, ← coeff_coe, ← coeff_coe, ← coeff_coe, ← map_add, coe_mul, coe_mul, coe_mul,
    ← pderivFun_coe_mul_coe, coeff_pderivFun]

private theorem pderivFun_smul {i : σ} (r : R) (f : MvPowerSeries σ R) :
    pderivFun i (r • f) = r • pderivFun i f := by
  rw [smul_eq_C_mul, smul_eq_C_mul, pderivFun_mul, pderivFun_C, smul_zero, add_zero, smul_eq_mul]

variable (R) in
/-- The formal partial derivative of a multivariate formal power series with respect to
variable `i`, as an `R`-derivation on `MvPowerSeries σ R`. -/
@[no_expose]
noncomputable def pderiv (i : σ) : Derivation R (MvPowerSeries σ R) (MvPowerSeries σ R) where
  toFun := pderivFun i
  map_add' := pderivFun_add
  map_smul' := pderivFun_smul
  map_one_eq_zero' := pderivFun_one
  leibniz' := pderivFun_mul

@[simp] theorem pderiv_C {i : σ} {r : R} : pderiv R i (C r) = 0 := pderivFun_C r

theorem pderiv_one {i : σ} : pderiv R i 1 = 0 := pderiv_C

theorem coeff_pderiv {i : σ} (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    coeff n (pderiv R i f) = coeff (n + single i 1) f * (n i + 1) :=
  coeff_pderivFun f n

theorem pderiv_coe {i : σ} (f : MvPolynomial σ R) :
    pderiv R i f = MvPolynomial.pderiv i f := pderivFun_coe f

@[simp]
theorem pderiv_X_self {i : σ} : pderiv R i (X i) = 1 := by
  classical
  ext n
  simp only [coeff_pderiv, coeff_X, boole_mul, add_eq_right, coeff_one]
  split_ifs <;> simp_all

@[simp]
theorem pderiv_X_of_ne {i j : σ} (h : j ≠ i) : pderiv R i (X j) = 0 := by
  classical
  ext n
  simpa only [coeff_pderiv, coeff_X, boole_mul, coeff_zero] using
    ite_eq_right (ne_iff.mpr ⟨i, by grind [Finsupp.add_apply]⟩)

theorem pderiv_X [DecidableEq σ] (i j : σ) :
    pderiv R i (X j) = Pi.single (M := fun _ => MvPowerSeries σ R) i 1 j := by
  by_cases h : i = j
  · subst h; simp only [pderiv_X_self, Pi.single_eq_same]
  · grind [pderiv_X_of_ne]

theorem trunc_pderiv [DecidableEq σ] {i : σ} (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    trunc R n (pderiv R i f) = MvPolynomial.pderiv i (trunc R (n + single i 1) f) :=
  trunc_pderivFun ..

/-- The partial derivative of `g^n` equals `n * g^(n-1) * g'`. -/
theorem pderiv_pow {i : σ} (g : MvPowerSeries σ R) (n : ℕ) :
    pderiv R i (g ^ n) = n * g ^ (n - 1) * pderiv R i g := by
  rw [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, mul_assoc]

end CommSemiring

/-- If `f` and `g` have the same constant term and all partial derivatives, then they are equal.

The `CommRing` assumption is needed because the proof uses `smul_right_inj`, which requires
cancellation of addition in `R`; `IsAddTorsionFree` alone does not suffice. -/
theorem pderiv.ext [CommRing R] [IsAddTorsionFree R] {f g : MvPowerSeries σ R}
    (hD : ∀ i, pderiv R i f = pderiv R i g) (hc : constantCoeff f = constantCoeff g) : f = g := by
  ext n
  by_cases h : n = 0
  · rw [h, coeff_zero_eq_constantCoeff, hc]
  obtain ⟨i, hi : n i ≠ 0⟩ := ne_iff.mp h
  have : single i 1 ≤ n := fun j ↦ by
    by_cases hj : j = i <;> grind [single_eq_same, single_eq_of_ne]
  have e := congr(coeff (n - single i 1) $(hD i))
  rwa [coeff_pderiv, coeff_pderiv, tsub_add_cancel_of_le this, coe_tsub, Pi.sub_apply,
    single_eq_same, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hi), Nat.cast_one, sub_add_cancel,
    mul_comm, ← nsmul_eq_mul, mul_comm, ← nsmul_eq_mul, smul_right_inj hi] at e

@[simp]
theorem pderiv_inv {i : σ} [CommRing R] (f : (MvPowerSeries σ R)ˣ) :
    pderiv R i ↑f⁻¹ = -(↑f⁻¹ : MvPowerSeries σ R) ^ 2 * pderiv R i f :=
  (pderiv R i).leibniz_of_mul_eq_one f.inv_mul

@[simp]
theorem pderiv_invOf {i : σ} [CommRing R] (f : MvPowerSeries σ R) [Invertible f] :
    pderiv R i ⅟f = -⅟f ^ 2 * pderiv R i f :=
  (pderiv R i).leibniz_invOf f

/-
The following theorem is stated only in the case that `R` is a field. This is because
there is currently no instance of `Inv (MvPowerSeries σ R)` for more general base rings `R`.
-/

@[simp]
theorem pderiv_inv' {i : σ} [Field R] (f : MvPowerSeries σ R) :
    pderiv R i f⁻¹ = -f⁻¹ ^ 2 * pderiv R i f := by
  by_cases h : constantCoeff f = 0
  · suffices f⁻¹ = 0 by
      rw [this, pow_two, zero_mul, neg_zero, zero_mul, map_zero]
    rwa [MvPowerSeries.inv_eq_zero]
  apply Derivation.leibniz_of_mul_eq_one
  exact MvPowerSeries.inv_mul_cancel (h := h)

section Substitution

open Filter WithPiTopology

variable {τ S : Type*}

section Continuity

variable [CommSemiring R] [TopologicalSpace R] [ContinuousMul R]

/-- The formal partial derivative is continuous for the product topology. -/
@[fun_prop]
theorem continuous_pderiv (i : σ) :
    Continuous (pderiv R i : MvPowerSeries σ R → MvPowerSeries σ R) := by
  refine continuous_pi_iff.mpr fun d ↦ ?_
  simp only [← coeff_apply, coeff_pderiv]
  exact (continuous_coeff R _).mul continuous_const

end Continuity

variable [CommRing R] [CommRing S] [Algebra R S] {a : σ → MvPowerSeries τ S}

/-- Only finitely many members of a substitutable family `a` contribute to a given coefficient
of a product `u * pderiv S i (a j)`. -/
theorem eventually_coeff_mul_pderiv_eq_zero (ha : HasSubst a) (i : τ) (e : τ →₀ ℕ) :
    ∀ᶠ j in cofinite, ∀ u : MvPowerSeries τ S, coeff e (u * pderiv S i (a j)) = 0 := by
  classical
  have h : ∀ᶠ j in cofinite, ∀ x ∈ Finset.antidiagonal e,
      coeff (x.2 + single i 1) (a j) = 0 := by
    rw [eventually_all_finset]
    exact fun x _ ↦ eventually_cofinite.mpr (ha.coeff_zero _)
  filter_upwards [h] with j hj u
  rw [coeff_mul]
  exact Finset.sum_eq_zero fun x hx ↦ by rw [coeff_pderiv, hj x hx, zero_mul, mul_zero]

/-- The finite set of indices `j` outside of which `u * pderiv S i (a j)` cannot contribute to
the coefficient `e`. -/
noncomputable def pderivSupport (ha : HasSubst a) (i : τ) (e : τ →₀ ℕ) : Finset σ :=
  (eventually_cofinite.mp (eventually_coeff_mul_pderiv_eq_zero ha i e)).toFinset

theorem coeff_mul_pderiv_eq_zero_of_notMem (ha : HasSubst a) (i : τ) (e : τ →₀ ℕ)
    {j : σ} (hj : j ∉ pderivSupport ha i e) (u : MvPowerSeries τ S) :
    coeff e (u * pderiv S i (a j)) = 0 := by
  revert u
  simpa [pderivSupport] using hj

section Subst

variable [UniformSpace S] [DiscreteUniformity S]

omit [DiscreteUniformity S] in
theorem summable_mul_pderiv (ha : HasSubst a) (u : σ → MvPowerSeries τ S) (i : τ) :
    Summable fun j ↦ u j * pderiv S i (a j) :=
  summable_iff_summable_coeff.mpr fun e ↦ summable_of_ne_finset_zero (s := pderivSupport ha i e)
    fun _ hj ↦ coeff_mul_pderiv_eq_zero_of_notMem ha i e hj _

theorem coeff_tsum_mul_pderiv (ha : HasSubst a) (u : σ → MvPowerSeries τ S) (i : τ) (e : τ →₀ ℕ) :
    coeff e (∑' j, u j * pderiv S i (a j))
      = ∑ j ∈ pderivSupport ha i e, coeff e (u j * pderiv S i (a j)) := by
  rw [← (hasSum_iff_hasSum_coeff.mp (summable_mul_pderiv ha u i).hasSum e).tsum_eq]
  exact tsum_eq_sum fun _ hj ↦ coeff_mul_pderiv_eq_zero_of_notMem ha i e hj _

omit [DiscreteUniformity S] in
theorem summable_aeval_pderiv (a : σ → MvPowerSeries τ S) (i : τ) (p : MvPolynomial σ R) :
    Summable fun j ↦ MvPolynomial.aeval a (MvPolynomial.pderiv j p) * pderiv S i (a j) :=
  summable_of_ne_finset_zero (s := p.vars) fun j hj ↦ by
    rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars hj, map_zero, zero_mul]

/-- The chain rule for the evaluation of a polynomial at a family of power series. -/
theorem pderiv_aeval_tsum (a : σ → MvPowerSeries τ S) (i : τ) (p : MvPolynomial σ R) :
    pderiv S i (MvPolynomial.aeval a p) =
      ∑' j : σ, MvPolynomial.aeval a (MvPolynomial.pderiv j p) * pderiv S i (a j) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp [algebraMap_apply]
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq,
      ← (summable_aeval_pderiv a i p).tsum_add (summable_aeval_pderiv a i q)]
    exact tsum_congr fun j ↦ by rw [map_add, map_add, add_mul]
  | mul_X p j hp =>
    have key : ∀ k : σ, MvPolynomial.aeval a ((MvPolynomial.pderiv k) (p * MvPolynomial.X j))
        = (if k = j then MvPolynomial.aeval a p else 0)
          + a j * MvPolynomial.aeval a ((MvPolynomial.pderiv k) p) := fun k ↦ by
      rw [Derivation.leibniz]
      rcases eq_or_ne k j with h | h
      · subst h; simp
      · simp [MvPolynomial.pderiv_X_of_ne (Ne.symm h), h]
    have hsum1 : Summable fun k : σ ↦
        (if k = j then MvPolynomial.aeval a p else 0) * pderiv S i (a k) :=
      summable_of_ne_finset_zero (s := {j}) fun k hk ↦ by simp_all
    have hsum2 : Summable fun k : σ ↦
        a j * (MvPolynomial.aeval a ((MvPolynomial.pderiv k) p) * pderiv S i (a k)) :=
      (summable_aeval_pderiv a i p).mul_left _
    trans (∑' k : σ, (if k = j then MvPolynomial.aeval a p else 0) * pderiv S i (a k))
      + ∑' k : σ, a j * (MvPolynomial.aeval a ((MvPolynomial.pderiv k) p) * pderiv S i (a k))
    · simp only [ite_mul, zero_mul, tsum_ite_eq]
      rw [(summable_aeval_pderiv a i p).tsum_mul_left, ← hp, map_mul, MvPolynomial.aeval_X,
        Derivation.leibniz]
      simp [smul_eq_mul]
    · rw [← hsum1.tsum_add hsum2]
      exact tsum_congr fun k ↦ by rw [key, add_mul, mul_assoc]

variable [UniformSpace R] [DiscreteUniformity R]

/-- **Chain rule** for substitution of multivariate power series,
`(∂/∂Xᵢ) f(a) = ∑ⱼ (∂f/∂Xⱼ)(a) * (∂aⱼ/∂Xᵢ)`.

This form makes no finiteness assumption on the type `σ` of variables; see
`MvPowerSeries.pderiv_subst` for the version with a `Finset.sum`. -/
theorem pderiv_subst_tsum (ha : HasSubst a) (f : MvPowerSeries σ R) (i : τ) :
    pderiv S i (subst a f) = ∑' j : σ, subst a (pderiv R j f) * pderiv S i (a j) := by
  revert f
  rw [← funext_iff]
  refine DenseRange.equalizer denseRange_toMvPowerSeries ?_ ?_ ?_
  · exact (continuous_pderiv i).comp (continuous_subst ha)
  · refine continuous_pi_iff.mpr fun e ↦ ?_
    simp only [← coeff_apply, coeff_tsum_mul_pderiv ha _ i e]
    exact continuous_finsetSum _ fun j _ ↦ (continuous_coeff S e).comp
      (((continuous_subst ha).comp (continuous_pderiv j)).mul continuous_const)
  · funext p
    simp only [Function.comp_apply, subst_coe, pderiv_coe, pderiv_aeval_tsum]

end Subst

/-- **Chain rule** for substitution of multivariate power series in finitely many variables,
`(∂/∂Xᵢ) f(a) = ∑ⱼ (∂f/∂Xⱼ)(a) * (∂aⱼ/∂Xᵢ)`.

See `MvPowerSeries.pderiv_subst_tsum` for a version valid for an arbitrary type of variables. -/
theorem pderiv_subst [Fintype σ] (ha : HasSubst a) (f : MvPowerSeries σ R) (i : τ) :
    pderiv S i (subst a f) = ∑ j, subst a (pderiv R j f) * pderiv S i (a j) := by
  let : UniformSpace R := ⊥
  let : UniformSpace S := ⊥
  rw [pderiv_subst_tsum ha, tsum_fintype]

/-- The chain rule for the evaluation of a polynomial at a family of power series indexed by a
finite type. -/
theorem pderiv_aeval [Fintype σ] (a : σ → MvPowerSeries τ S) (i : τ) (p : MvPolynomial σ R) :
    pderiv S i (MvPolynomial.aeval a p) =
      ∑ j : σ, MvPolynomial.aeval a (MvPolynomial.pderiv j p) * pderiv S i (a j) := by
  let : UniformSpace S := ⊥
  rw [pderiv_aeval_tsum, tsum_fintype]

end Substitution

end MvPowerSeries
