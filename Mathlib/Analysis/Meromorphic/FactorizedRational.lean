/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.IsolatedZeros
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Factorized Rational Functions

This file discusses functions `𝕜 → 𝕜` of the form `∏ᶠ u, (· - u) ^ d u`, where `d : 𝕜 → ℤ` is
integer-valued. We call these functions "factorized rational functions", introduce the notation
`Function.factorizedRational d`, and show that they are meromorphic in normal form, with divisor
equal to `d`.

Under suitable assumptions, we show that meromorphic functions are equivalent, modulo equality on
codiscrete sets, to the product of a factorized rational function and an analytic function without
zeros.

Implementation Note: The function `Function.factorizedRational d` is defined as the finprod of
functions, `∏ᶠ u, (· - u) ^ d u`. If the support of `d` is finite, then evaluation of functions
commutes with finprod, and the helper lemma `Function.FactorizedRational.finprod_eq_fun` asserts
that `factorizedRational d` equals the function `fun x ↦ ∏ᶠ u, (x - u) ^ d u`. If `d` has infinite
support, this equality is wrong in general. There are elementary examples of functions `d` where
`factorizedRational d` is constant one, while `fun x ↦ ∏ᶠ u, (x - u) ^ d u` is not continuous.
-/

public section

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜}

open Filter Function Real Set

/--
The factorized rational function associated with `d : 𝕜 → ℤ`, defined as the product of functions
`∏ᶠ u, (· - u) ^ d u`. If the support of `d` is infinite, this is the constant function `1`.
-/
@[expose] noncomputable def Function.factorizedRational (d : 𝕜 → ℤ) : 𝕜 → 𝕜 := ∏ᶠ u, (· - u) ^ d u

namespace Function.FactorizedRational

/-!
## Elementary Properties of Factorized Rational Functions
-/

/--
Helper Lemma: Identify the support of `d` as the mulsupport of the product defining the factorized
rational function.
-/
lemma mulSupport (d : 𝕜 → ℤ) :
    (fun u ↦ (· - u) ^ d u).mulSupport = d.support := by
  ext u
  constructor <;> intro h
  · simp_all only [mem_mulSupport, ne_eq, mem_support]
    by_contra hCon
    simp_all
  · simp_all only [mem_mulSupport, ne_eq, ne_iff]
    use u
    simp_all [zero_zpow_eq_one₀]

set_option backward.isDefEq.respectTransparency false in
/--
Helper Lemma: If the support of `d` is finite, then evaluation of functions commutes with finprod,
and the function `factorizedRational d` equals `fun x ↦ ∏ᶠ u, (x - u) ^ d u`.
-/
lemma finprod_eq_fun {d : 𝕜 → ℤ} (h : d.HasFiniteSupport) :
    factorizedRational d = fun x ↦ ∏ᶠ u, (x - u) ^ d u := by
  ext x
  rw [factorizedRational, finprod_eq_prod_of_mulSupport_subset (s := h.toFinset),
    finprod_eq_prod_of_mulSupport_subset (s := h.toFinset)]
  · simp
  · intro u
    contrapose
    simp_all
  · simp [mulSupport d]

/--
If the support of `d` is infinite, then the factorized rational function associated with `d` is the
constant function `1`.
-/
lemma eq_one_of_not_hasFiniteSupport {d : 𝕜 → ℤ} (h : ¬d.HasFiniteSupport) :
    factorizedRational d = 1 := by
  rw [factorizedRational, finprod_of_infinite_mulSupport (by rwa [mulSupport])]

/--
Factorized rational functions are analytic wherever the exponent is non-negative.
-/
theorem analyticAt {d : 𝕜 → ℤ} {x : 𝕜} (h : 0 ≤ d x) :
    AnalyticAt 𝕜 (factorizedRational d) x := by
  apply analyticAt_finprod
  intro u
  by_cases h₂ : x = u
  · apply AnalyticAt.fun_zpow_nonneg (by fun_prop)
    rwa [← h₂]
  · apply AnalyticAt.fun_zpow (by fun_prop)
    rwa [sub_ne_zero]

/--
Factorized rational functions are non-zero wherever the exponent is zero.
-/
theorem ne_zero {d : 𝕜 → ℤ} {x : 𝕜} (h : d x = 0) :
    factorizedRational d x ≠ 0 := by
  unfold factorizedRational
  by_cases h₁ : (fun u ↦ (· - u) ^ d u).HasFiniteMulSupport
  · rw [finprod_eq_prod _ h₁, Finset.prod_apply, Finset.prod_ne_zero_iff]
    intro z hz
    simp only [Pi.pow_apply, ne_eq]
    by_cases h₂ : x = z <;> simp_all [zpow_ne_zero, sub_ne_zero]
  · simp [finprod_of_infinite_mulSupport h₁]

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
Helper Lemma for Computations: Extract one factor out of a factorized rational function.
-/
lemma extractFactor {d : 𝕜 → ℤ} (u₀ : 𝕜) (hd : d.HasFiniteSupport) :
    factorizedRational d = ((· - u₀) ^ d u₀) * factorizedRational (update d u₀ 0) := by
  unfold factorizedRational
  by_cases h₁d : d u₀ = 0
  · simp [← eq_update_self_iff.2 h₁d, h₁d]
  · have : (fun u ↦ (fun x ↦ x - u) ^ d u).mulSupport ⊆ hd.toFinset := by
      simp [mulSupport]
    rw [finprod_eq_prod_of_mulSupport_subset _ this]
    have : u₀ ∈ hd.toFinset := by simp_all
    rw [← Finset.mul_prod_erase hd.toFinset _ this]
    congr 1
    have : (fun u ↦ (· - u) ^ (update d u₀ 0 u)).mulSupport ⊆ hd.toFinset.erase u₀ := by
      rw [mulSupport]
      intro x hx
      by_cases h₁x : x = u₀ <;> simp_all
    simp_all [finprod_eq_prod_of_mulSupport_subset _ this, Finset.prod_congr rfl]

/--
If the support of `d` is finite, then the factorized rational function associated with `d` takes the
value zero wherever the exponent is non-zero. This includes the poles, in accordance with the
convention that `0⁻¹ = 0`.
-/
theorem eq_zero {d : 𝕜 → ℤ} {x : 𝕜} (h₁ : d.HasFiniteSupport) (h₂ : d x ≠ 0) :
    factorizedRational d x = 0 := by
  classical
  simp [extractFactor x h₁, zero_zpow _ h₂]

/--
Factorized rational functions are meromorphic in normal form on `univ`.
-/
theorem meromorphicNFOn_univ (d : 𝕜 → ℤ) :
    MeromorphicNFOn (factorizedRational d) univ := by
  classical
  by_cases hd : d.support.Finite
  · intro z hz
    rw [extractFactor z hd]
    right
    use d z, factorizedRational (update d z 0)
    simp [analyticAt, ne_zero]
  · rw [eq_one_of_not_hasFiniteSupport hd]
    exact AnalyticOnNhd.meromorphicNFOn analyticOnNhd_const

/--
Factorized rational functions are meromorphic in normal form on arbitrary subsets of `𝕜`.
-/
theorem meromorphicNFOn (d : 𝕜 → ℤ) (U : Set 𝕜) :
    MeromorphicNFOn (factorizedRational d) U := fun _ _ ↦ meromorphicNFOn_univ d (trivial)

/--
Factorized rational functions are meromorphic.
-/
@[fun_prop]
theorem meromorphic (d : 𝕜 → ℤ) :
    Meromorphic (factorizedRational d) := fun _ ↦ (meromorphicNFOn_univ d).meromorphicOn _ trivial

/-!
## Orders and Divisors of Factorized Rational Functions
-/

/--
The order of the factorized rational function `factorizedRational d` at `z` equals `d z`.
-/
theorem meromorphicOrderAt_eq {z : 𝕜} (d : 𝕜 → ℤ) (h₁d : d.HasFiniteSupport) :
    meromorphicOrderAt (factorizedRational d) z = d z := by
  classical
  rw [meromorphicOrderAt_eq_int_iff ((meromorphicNFOn_univ d).meromorphicOn _ (mem_univ _))]
  use factorizedRational (update d z 0)
  simp only [update_self, le_refl, analyticAt, ne_eq, ne_zero, not_false_eq_true, smul_eq_mul,
    true_and]
  filter_upwards
  simp [extractFactor z h₁d]

/--
Factorized rational functions are nowhere locally constant zero.
-/
theorem meromorphicOrderAt_ne_top {z : 𝕜} (d : 𝕜 → ℤ) :
    meromorphicOrderAt (factorizedRational d) z ≠ ⊤ := by
  classical
  by_cases hd : d.support.Finite
  · simp [meromorphicOrderAt_eq d hd]
  · simp [eq_one_of_not_hasFiniteSupport hd]

/--
If `D` is a divisor, then the divisor of the factorized rational function equals `D`.
-/
theorem divisor {U : Set 𝕜} {D : locallyFinsuppWithin U ℤ} (hD : D.support.Finite) :
    MeromorphicOn.divisor (factorizedRational D) U = D := by
  ext z
  by_cases hz : z ∈ U
  <;> simp [(meromorphicNFOn D U).meromorphicOn, hz, meromorphicOrderAt_eq D hD]

open scoped Classical in
private lemma mulSupport_update {d : 𝕜 → ℤ} {x : 𝕜}
    (h : d.support.Finite) :
    (fun u ↦ (x - u) ^ Function.update d x 0 u).mulSupport ⊆ h.toFinset := by
  intro u
  contrapose
  simp only [mem_mulSupport, ne_eq, Decidable.not_not]
  by_cases h₁ : u = x
  · rw [h₁]
    simp
  · simp_all

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
Compute the trailing coefficient of the factorized rational function associated with `d : 𝕜 → ℤ`.
-/
/-
Low-priority TODO: Using that non-trivially normed fields contain infinitely many elements that are
no roots of unity, it might be possible to drop assumption `h` here and in some of the theorems
below.
-/
theorem meromorphicTrailingCoeffAt_factorizedRational {d : 𝕜 → ℤ} {x : 𝕜} (h : d.HasFiniteSupport) :
    meromorphicTrailingCoeffAt (factorizedRational d) x = ∏ᶠ u, (x - u) ^ update d x 0 u := by
  have : (fun u ↦ (· - u) ^ d u).mulSupport ⊆ h.toFinset := by
    simp [Function.FactorizedRational.mulSupport]
  rw [factorizedRational, finprod_eq_prod_of_mulSupport_subset _ this,
    meromorphicTrailingCoeffAt_prod
      (fun _ ↦ by fun_prop), finprod_eq_prod_of_mulSupport_subset _ (mulSupport_update h)]
  apply Finset.prod_congr rfl
  intro y hy
  rw [MeromorphicAt.meromorphicTrailingCoeffAt_zpow (by fun_prop)]
  by_cases hxy : x = y
  · rw [hxy, meromorphicTrailingCoeffAt_id_sub_const]
    simp_all
  · grind [meromorphicTrailingCoeffAt_id_sub_const]

set_option backward.isDefEq.respectTransparency false in
/--
Variant of `meromorphicTrailingCoeffAt_factorizedRational`: Compute the trailing coefficient of the
factorized rational function associated with `d : 𝕜 → ℤ` at points outside the support of `d`.
-/
theorem meromorphicTrailingCoeffAt_factorizedRational_off_support {d : 𝕜 → ℤ} {x : 𝕜}
    (h₁ : d.HasFiniteSupport) (h₂ : x ∉ d.support) :
    meromorphicTrailingCoeffAt (factorizedRational d) x = ∏ᶠ u, (x - u) ^ d u := by
  classical
  rw [meromorphicTrailingCoeffAt_factorizedRational h₁,
    finprod_eq_prod_of_mulSupport_subset _ (mulSupport_update h₁)]
  have : (fun u ↦ (x - u) ^ d u).mulSupport ⊆ h₁.toFinset := by
    intro u
    contrapose
    simp_all
  rw [finprod_eq_prod_of_mulSupport_subset _ this, Finset.prod_congr rfl]
  intro y hy
  congr
  apply Function.update_of_ne
  by_contra hCon
  simp_all

set_option backward.isDefEq.respectTransparency false in
/--
Variant of `meromorphicTrailingCoeffAt_factorizedRational`: Compute log of the norm of the trailing
coefficient.  The convention that `log 0 = 0` gives a closed formula easier than the one in
`meromorphicTrailingCoeffAt_factorizedRational`.
-/
theorem log_norm_meromorphicTrailingCoeffAt {d : 𝕜 → ℤ} {x : 𝕜} (h : d.HasFiniteSupport) :
    log ‖meromorphicTrailingCoeffAt (factorizedRational d) x‖ = ∑ᶠ u, (d u) * log ‖x - u‖ := by
  classical
  rw [meromorphicTrailingCoeffAt_factorizedRational h,
    finprod_eq_prod_of_mulSupport_subset _ (mulSupport_update h)]
  have : ∀ y ∈ h.toFinset, ‖(x - y) ^ update d x 0 y‖ ≠ 0 := by
    intro y _
    by_cases h : x = y
    · rw [h]
      simp_all
    · simp_all [zpow_ne_zero, sub_ne_zero]
  rw [norm_prod, log_prod this]
  have : (fun u ↦ (d u) * log ‖x - u‖).support ⊆ h.toFinset := by
    intro u
    contrapose
    simp_all
  rw [finsum_eq_sum_of_support_subset _ this]
  apply Finset.sum_congr rfl
  intro y hy
  rw [norm_zpow, Real.log_zpow]
  by_cases h : x = y
  · simp [h]
  · rw [Function.update_of_ne (by tauto)]

/-!
## Logarithm of the Norm of Factorized Rational Functions
-/

/--
Helper Lemma: Identify the support of `d` as the support of the sum `∑ᶠ u, (d u * log ‖· - u‖)`.
-/
lemma support_mul_log_norm_sub (d : 𝕜 → ℤ) :
    (fun u ↦ (d u * log ‖· - u‖)).support = d.support := by
  obtain ⟨y, hy⟩ := NormedField.exists_one_lt_norm 𝕜
  ext u
  refine ⟨fun h h' ↦ h (by simp [h', Pi.zero_def]), fun h h' ↦ h ?_⟩
  simpa [(log_pos hy).ne'] using congr($h' (y + u))

/--
If the support of `d` is infinite, then the functions `log ‖factorizedRational d ·‖` and
`∑ᶠ u, (d u * log ‖· - u‖)` both vanish identically.
-/
lemma log_norm_eq_of_not_hasFiniteSupport {d : 𝕜 → ℤ} (hd : ¬d.HasFiniteSupport) :
    (log ‖factorizedRational d ·‖) = ∑ᶠ u, (d u * log ‖· - u‖) := by
  rw [finsum_of_infinite_support (by rwa [support_mul_log_norm_sub]),
    eq_one_of_not_hasFiniteSupport hd]
  ext x
  simp

/--
Away from the support of `d`, the function `log ‖factorizedRational d ·‖` agrees with the function
`∑ᶠ u, (d u * log ‖· - u‖)`.
-/
theorem log_norm_eqOn (d : 𝕜 → ℤ) :
    EqOn (log ‖factorizedRational d ·‖) (∑ᶠ u, (d u * log ‖· - u‖)) d.supportᶜ := by
  -- Trivial case: the support of d is infinite
  by_cases hd : d.support.Finite
  case neg => exact fun x _ ↦ congrFun (log_norm_eq_of_not_hasFiniteSupport hd) x
  -- General case: on the complement, it is exactly the trailing coefficient
  intro z hz
  rw [finsum_apply (by simpa [HasFiniteSupport, support_mul_log_norm_sub]),
    ← log_norm_meromorphicTrailingCoeffAt hd,
    (analyticAt (by simp_all)).meromorphicTrailingCoeffAt_of_ne_zero (ne_zero (by simp_all))]

/--
If `D` is a function with locally finite support within `U`, such as the divisor of a meromorphic
function, then `log ‖factorizedRational D ·‖` is equivalent, modulo equality on codiscrete subsets
of `U`, to `∑ᶠ u, (D u * log ‖· - u‖)`.
-/
theorem log_norm_eventuallyEq_codiscreteWithin (D : locallyFinsuppWithin U ℤ) :
    (log ‖factorizedRational D ·‖) =ᶠ[codiscreteWithin U] ∑ᶠ u, (D u * log ‖· - u‖) := by
  filter_upwards [D.eq_zero_codiscreteWithin] with z hz
  exact log_norm_eqOn D (by simpa using hz)

/--
The function `log ‖factorizedRational d ·‖` is equivalent, modulo equality on codiscrete sets, to
`∑ᶠ u, (d u * log ‖· - u‖)`.
-/
theorem log_norm_eventuallyEq_codiscrete (d : 𝕜 → ℤ) :
    (log ‖factorizedRational d ·‖) =ᶠ[codiscrete 𝕜] ∑ᶠ u, (d u * log ‖· - u‖) := by
  by_cases hd : d.support.Finite
  · filter_upwards [hd.compl_mem_codiscrete] with z hz
    exact log_norm_eqOn d hz
  · exact .of_eq (log_norm_eq_of_not_hasFiniteSupport hd)

end Function.FactorizedRational

open Function.FactorizedRational

/-!
## Elimination of Zeros and Poles

This section shows that every meromorphic function with finitely many zeros and poles is equivalent,
modulo equality on codiscrete sets, to the product of a factorized rational function and an analytic
function without zeros.

We provide analogous results for functions of the form `log ‖meromorphic‖`.
-/

/-
TODO: Identify some of the terms that appear in the decomposition.
-/

/--
If `f` is meromorphic on an open set `U`, if `f` is nowhere locally constant zero, and if the
support of the divisor of `f` is finite, then there exists an analytic function `g` on `U` without
zeros such that `f` is equivalent, modulo equality on codiscrete sets, to the product of `g` and the
factorized rational function associated with the divisor of `f`.
-/
theorem MeromorphicOn.extract_zeros_poles {f : 𝕜 → E} (h₁f : MeromorphicOn f U)
    (h₂f : ∀ u : U, meromorphicOrderAt f u ≠ ⊤) (h₃f : (divisor f U).support.Finite) :
    ∃ g : 𝕜 → E, AnalyticOnNhd 𝕜 g U ∧ (∀ u : U, g u ≠ 0) ∧
      f =ᶠ[codiscreteWithin U] factorizedRational (divisor f U) • g := by
  -- Take `g` as the inverse of the Laurent polynomial defined below, converted to a meromorphic
  -- function in normal form. Then check all the properties.
  let φ := factorizedRational (divisor f U)
  have hφ : MeromorphicOn φ U := (meromorphicNFOn (divisor f U) U).meromorphicOn
  let g := toMeromorphicNFOn (φ⁻¹ • f) U
  have hg : MeromorphicNFOn g U := by apply meromorphicNFOn_toMeromorphicNFOn
  refine ⟨g, ?_, ?_, ?_⟩
  · -- AnalyticOnNhd 𝕜 g U
    rw [← hg.divisor_nonneg_iff_analyticOnNhd, divisor_of_toMeromorphicNFOn (hφ.inv.smul h₁f),
      divisor_smul hφ.inv h₁f _ (fun z hz ↦ h₂f ⟨z, hz⟩), divisor_inv,
      Function.FactorizedRational.divisor h₃f, neg_add_cancel]
    intro z hz
    simpa [meromorphicOrderAt_inv] using meromorphicOrderAt_ne_top (divisor f U)
  · -- ∀ (u : ↑U), g ↑u ≠ 0
    intro ⟨u, hu⟩
    rw [← (hg hu).meromorphicOrderAt_eq_zero_iff, ← meromorphicOrderAt_congr
        (toMeromorphicNFOn_eq_self_on_nhdsNE (hφ.inv.smul h₁f) hu).symm,
      meromorphicOrderAt_smul (hφ u hu).inv (h₁f u hu), meromorphicOrderAt_inv,
      meromorphicOrderAt_eq _ h₃f]
    simp only [h₁f, hu, divisor_apply]
    lift meromorphicOrderAt f u to ℤ using (h₂f ⟨u, hu⟩) with n hn
    rw [WithTop.untop₀_coe, ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add]
    simp
  · -- f =ᶠ[codiscreteWithin U] factorizedRational (divisor f U) • g
    filter_upwards [(divisor f U).eq_zero_codiscreteWithin,
      (hφ.inv.smul h₁f).meromorphicNFAt_mem_codiscreteWithin,
      self_mem_codiscreteWithin U] with a h₂a h₃a h₄a
    unfold g
    simp only [Pi.smul_apply', toMeromorphicNFOn_eq_toMeromorphicNFAt (hφ.inv.smul h₁f) h₄a,
      toMeromorphicNFAt_eq_self.2 h₃a, Pi.inv_apply]
    rw [← smul_assoc, smul_eq_mul, mul_inv_cancel₀ _, one_smul]
    rwa [← ((meromorphicNFOn_univ (divisor f U)) trivial).meromorphicOrderAt_eq_zero_iff,
      meromorphicOrderAt_eq, h₂a, Pi.zero_apply, WithTop.coe_zero]

/--
In the setting of `MeromorphicOn.extract_zeros_poles`, the function `log ‖f‖` is equivalent, modulo
equality on codiscrete subsets, to `log ‖factorizedRational (divisor f U) ·‖ + log ‖g ·‖`.

See `MeromorphicOn.extract_zeros_poles_log` for a variant where the first summand is written as a
sum of logarithms.
-/
theorem MeromorphicOn.log_norm_extract_zeros_poles {f g : 𝕜 → E}
    {D : Function.locallyFinsuppWithin U ℤ} (hg : ∀ u : U, g u ≠ 0)
    (h : f =ᶠ[codiscreteWithin U] factorizedRational D • g) :
    (log ‖f ·‖) =ᶠ[codiscreteWithin U] (log ‖factorizedRational D ·‖) + (log ‖g ·‖) := by
  filter_upwards [h, D.eq_zero_codiscreteWithin, self_mem_codiscreteWithin U] with z hz h₂z h₃z
  simp [hz, norm_smul, log_mul (norm_ne_zero_iff.2 (FactorizedRational.ne_zero h₂z))
    (norm_ne_zero_iff.2 (hg ⟨z, h₃z⟩))]

/--
In the setting of `MeromorphicOn.extract_zeros_poles`, the function `log ‖f‖` is equivalent, modulo
equality on codiscrete subsets, to `∑ᶠ u, (divisor f U u * log ‖· - u‖) + log ‖g ·‖`.
-/
theorem MeromorphicOn.extract_zeros_poles_log {f g : 𝕜 → E} {D : Function.locallyFinsuppWithin U ℤ}
    (hg : ∀ u : U, g u ≠ 0) (h : f =ᶠ[codiscreteWithin U] factorizedRational D • g) :
    (log ‖f ·‖) =ᶠ[codiscreteWithin U] ∑ᶠ u, (D u * log ‖· - u‖) + (log ‖g ·‖) :=
  (log_norm_extract_zeros_poles hg h).trans
    ((log_norm_eventuallyEq_codiscreteWithin D).add .rfl)

open scoped Classical in
/--
In the setting of `MeromorphicOn.extract_zeros_poles`, compute the trailing
coefficient of `f` in terms of `divisor f U` and `g x`.
-/
theorem MeromorphicOn.meromorphicTrailingCoeffAt_extract_zeros_poles
    {x : 𝕜} {f g : 𝕜 → E} {D : 𝕜 → ℤ} (hD : D.HasFiniteSupport) (h₁x : x ∈ U) (h₂x : AccPt x (𝓟 U))
    (hf : MeromorphicAt f x) (h₁g : AnalyticAt 𝕜 g x) (h₂g : g x ≠ 0)
    (h : f =ᶠ[codiscreteWithin U] factorizedRational D • g) :
    meromorphicTrailingCoeffAt f x = (∏ᶠ u, (x - u) ^ Function.update D x 0 u) • g x := by
  have t₀ : MeromorphicAt (factorizedRational D) x :=
    (FactorizedRational.meromorphicNFOn D U).meromorphicOn x h₁x
  rw [meromorphicTrailingCoeffAt_congr_nhdsNE
      (hf.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin (by fun_prop) h₁x h₂x h),
    t₀.meromorphicTrailingCoeffAt_smul h₁g.meromorphicAt,
    h₁g.meromorphicTrailingCoeffAt_of_ne_zero h₂g]
  simp [meromorphicTrailingCoeffAt_factorizedRational hD]

/--
In the setting of `MeromorphicOn.extract_zeros_poles`, compute the log of the
norm of the trailing coefficient of `f` in terms of `divisor f U` and `g x`.
-/
theorem MeromorphicOn.log_norm_meromorphicTrailingCoeffAt_extract_zeros_poles
    {x : 𝕜} {f g : 𝕜 → E} {D : 𝕜 → ℤ} (hD : D.HasFiniteSupport) (h₁x : x ∈ U) (h₂x : AccPt x (𝓟 U))
    (hf : MeromorphicAt f x) (h₁g : AnalyticAt 𝕜 g x) (h₂g : g x ≠ 0)
    (h : f =ᶠ[codiscreteWithin U] factorizedRational D • g) :
    log ‖meromorphicTrailingCoeffAt f x‖ = ∑ᶠ u, (D u) * log ‖x - u‖ + log ‖g x‖ := by
  rw [meromorphicTrailingCoeffAt_congr_nhdsNE
      (hf.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
        (((FactorizedRational.meromorphicNFOn D U).meromorphicOn x h₁x).smul h₁g.meromorphicAt)
          h₁x h₂x h),
    ((FactorizedRational.meromorphicNFOn D U).meromorphicOn x h₁x).meromorphicTrailingCoeffAt_smul
      h₁g.meromorphicAt, h₁g.meromorphicTrailingCoeffAt_of_ne_zero h₂g,
    norm_smul, log_mul, log_norm_meromorphicTrailingCoeffAt hD]
  · simp only [ne_eq, norm_eq_zero]
    apply MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero
      ((FactorizedRational.meromorphicNFOn D U).meromorphicOn x h₁x)
    apply FactorizedRational.meromorphicOrderAt_ne_top
  · simp_all
