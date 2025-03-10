/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Michael Stoll
-/
import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Analytic continuation of Dirichlet L-functions

We show that if `χ` is a Dirichlet character `ZMod N → ℂ`, for a positive integer `N`, then the
L-series of `χ` has analytic continuation (away from a pole at `s = 1` if `χ` is trivial), and
similarly for completed L-functions.

All definitions and theorems are in the `DirichletCharacter` namespace.

## Main definitions

* `LFunction χ s`: the L-function, defined as a linear combination of Hurwitz zeta functions.
* `completedLFunction χ s`: the completed L-function, which for *almost* all `s` is equal to
  `LFunction χ s * gammaFactor χ s` where `gammaFactor χ s` is the archimedean Gamma-factor.
* `rootNumber`: the global root number of the L-series of `χ` (for `χ` primitive; junk otherwise).

## Main theorems

* `LFunction_eq_LSeries`: if `1 < re s` then the `LFunction` coincides with the naive `LSeries`.
* `differentiable_LFunction`: if `χ` is nontrivial then `LFunction χ s` is differentiable
  everywhere.
* `LFunction_eq_completed_div_gammaFactor`: we have
  `LFunction χ s = completedLFunction χ s / gammaFactor χ s`, unless `s = 0` and `χ` is the trivial
  character modulo 1.
* `differentiable_completedLFunction`: if `χ` is nontrivial then `completedLFunction χ s` is
  differentiable everywhere.
* `IsPrimitive.completedLFunction_one_sub`: the **functional equation** for Dirichlet L-functions,
  showing that if `χ` is primitive modulo `N`, then
  `completedLFunction χ s = N ^ (s - 1 / 2) * rootNumber χ * completedLFunction χ⁻¹ s`.
-/

open HurwitzZeta Complex Finset ZMod Filter

open scoped Real Topology

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/--
The unique meromorphic function `ℂ → ℂ` which agrees with `∑' n : ℕ, χ n / n ^ s` wherever the
latter is convergent. This is constructed as a linear combination of Hurwitz zeta functions.

Note that this is not the same as `LSeries χ`: they agree in the convergence range, but
`LSeries χ s` is defined to be `0` if `re s ≤ 1`.
-/
@[pp_nodot]
noncomputable def LFunction (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ := ZMod.LFunction χ s

/--
The L-function of the (unique) Dirichlet character mod 1 is the Riemann zeta function.
(Compare `DirichletCharacter.LSeries_modOne_eq`.)
-/
@[simp] lemma LFunction_modOne_eq {χ : DirichletCharacter ℂ 1} :
    LFunction χ = riemannZeta := by
  ext; rw [LFunction, ZMod.LFunction_modOne_eq, (by rfl : (0 : ZMod 1) = 1), map_one, one_mul]

/--
For `1 < re s` the L-function of a Dirichlet character agrees with the sum of the naive Dirichlet
series.
-/
lemma LFunction_eq_LSeries (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < re s) :
    LFunction χ s = LSeries (χ ·) s :=
  ZMod.LFunction_eq_LSeries χ hs

lemma deriv_LFunction_eq_deriv_LSeries (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    deriv (LFunction χ) s = deriv (LSeries (χ ·)) s := by
  refine Filter.EventuallyEq.deriv_eq ?_
  have h : {z | 1 < z.re} ∈ nhds s :=
    (isOpen_lt continuous_const continuous_re).mem_nhds hs
  filter_upwards [h] with z hz
  exact LFunction_eq_LSeries χ hz

/--
The L-function of a Dirichlet character is differentiable, except at `s = 1` if the character is
trivial.
-/
@[fun_prop]
lemma differentiableAt_LFunction (χ : DirichletCharacter ℂ N) (s : ℂ) (hs : s ≠ 1 ∨ χ ≠ 1) :
    DifferentiableAt ℂ (LFunction χ) s :=
  ZMod.differentiableAt_LFunction χ s (hs.imp_right χ.sum_eq_zero_of_ne_one)

/-- The L-function of a non-trivial Dirichlet character is differentiable everywhere. -/
@[fun_prop]
lemma differentiable_LFunction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Differentiable ℂ (LFunction χ) :=
  (differentiableAt_LFunction _ · <| Or.inr hχ)

/-- The L-function of an even Dirichlet character vanishes at strictly negative even integers. -/
@[simp]
lemma Even.LFunction_neg_two_mul_nat_add_one {χ : DirichletCharacter ℂ N} (hχ : Even χ) (n : ℕ) :
    LFunction χ (-(2 * (n + 1))) = 0 :=
  ZMod.LFunction_neg_two_mul_nat_add_one hχ.to_fun n

/-- The L-function of an even Dirichlet character vanishes at strictly negative even integers. -/
@[simp]
lemma Even.LFunction_neg_two_mul_nat {χ : DirichletCharacter ℂ N} (hχ : Even χ) (n : ℕ) [NeZero n] :
    LFunction χ (-(2 * n)) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact_mod_cast hχ.LFunction_neg_two_mul_nat_add_one m

/-- The L-function of an odd Dirichlet character vanishes at negative odd integers. -/
@[simp] lemma Odd.LFunction_neg_two_mul_nat_sub_one
  {χ : DirichletCharacter ℂ N} (hχ : Odd χ) (n : ℕ) :
    LFunction χ (-(2 * n) - 1) = 0 :=
  ZMod.LFunction_neg_two_mul_nat_sub_one hχ.to_fun n

/-!
### Results on changing levels
-/

private lemma LFunction_changeLevel_aux {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : s ≠ 1) :
    LFunction (changeLevel hMN χ) s =
      LFunction χ s * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s)) := by
  have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (rank_real_complex ▸ Nat.one_lt_ofNat) _)
      |>.isPreconnected
  have hne : 2 ∈ ({1}ᶜ : Set ℂ) := by norm_num
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    (g := fun s ↦ LFunction χ s * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s))) ?_ ?_ hpc hne ?_ hs
  · refine DifferentiableOn.analyticOnNhd (fun s hs ↦ ?_) isOpen_compl_singleton
    exact (differentiableAt_LFunction _ _ (.inl hs)).differentiableWithinAt
  · refine DifferentiableOn.analyticOnNhd (fun s hs ↦ ?_) isOpen_compl_singleton
    refine ((differentiableAt_LFunction _ _ (.inl hs)).mul ?_).differentiableWithinAt
    refine .finset_prod fun i h ↦ ?_
    have : NeZero i := ⟨(Nat.pos_of_mem_primeFactors h).ne'⟩
    fun_prop
  · refine eventually_of_mem ?_  (fun t (ht : 1 < t.re) ↦ ?_)
    · exact (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num : 1 < (2 : ℂ).re)
    · simpa [LFunction_eq_LSeries _ ht] using LSeries_changeLevel hMN χ ht

/-- If `χ` is a Dirichlet character and its level `M` divides `N`, then we obtain the L function
of `χ` considered as a Dirichlet character of level `N` from the L function of `χ` by multiplying
with `∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s))`.
(Note that `1 - χ p * p ^ (-s) = 1` when `p` divides `M`). -/
lemma LFunction_changeLevel {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) {s : ℂ} (h : χ ≠ 1 ∨ s ≠ 1) :
    LFunction (changeLevel hMN χ) s =
      LFunction χ s * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s)) := by
  rcases h with h | h
  · have hχ : changeLevel hMN χ ≠ 1 := h ∘ (changeLevel_eq_one_iff hMN).mp
    have h' : Continuous fun s ↦ LFunction χ s * ∏ p ∈ N.primeFactors, (1 - χ p * ↑p ^ (-s)) :=
      (differentiable_LFunction h).continuous.mul <| continuous_finset_prod _ fun p hp ↦ by
        have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
        fun_prop
    exact congrFun ((differentiable_LFunction hχ).continuous.ext_on
      (dense_compl_singleton 1) h' (fun _ h ↦ LFunction_changeLevel_aux hMN χ h)) s
  · exact LFunction_changeLevel_aux hMN χ h

/-!
### The `L`-function of the trivial character mod `N`
-/

/-- The `L`-function of the trivial character mod `N`. -/
noncomputable abbrev LFunctionTrivChar (N : ℕ) [NeZero N] :=
  (1 : DirichletCharacter ℂ N).LFunction

/-- The L function of the trivial Dirichlet character mod `N` is obtained from the Riemann
zeta function by multiplying with `∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))`. -/
lemma LFunctionTrivChar_eq_mul_riemannZeta {s : ℂ} (hs : s ≠ 1) :
    LFunctionTrivChar N s = (∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s := by
  rw [← LFunction_modOne_eq (χ := 1), LFunctionTrivChar, ← changeLevel_one N.one_dvd, mul_comm]
  convert LFunction_changeLevel N.one_dvd 1 (.inr hs) using 4 with p
  rw [MulChar.one_apply <| isUnit_of_subsingleton _, one_mul]

/-- The L function of the trivial Dirichlet character mod `N` has a simple pole with
residue `∏ p ∈ N.primeFactors, (1 - p⁻¹)` at `s = 1`. -/
lemma LFunctionTrivChar_residue_one :
    Tendsto (fun s ↦ (s - 1) * LFunctionTrivChar N s) (𝓝[≠] 1)
      (𝓝 <| ∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹)) := by
  have H : (fun s ↦ (s - 1) * LFunctionTrivChar N s) =ᶠ[𝓝[≠] 1]
        fun s ↦ (∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))) * ((s - 1) * riemannZeta s) := by
    refine Set.EqOn.eventuallyEq_nhdsWithin fun s hs ↦ ?_
    rw [mul_left_comm, LFunctionTrivChar_eq_mul_riemannZeta hs]
  rw [tendsto_congr' H]
  conv => enter [3, 1]; rw [← mul_one <| Finset.prod ..]; enter [1, 2, p]; rw [← cpow_neg_one]
  refine .mul (f := fun s ↦ ∏ p ∈ N.primeFactors, _) ?_ riemannZeta_residue_one
  refine tendsto_nhdsWithin_of_tendsto_nhds <| Continuous.tendsto ?_ 1
  exact continuous_finset_prod _ fun p hp ↦ by
    have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    fun_prop

/-!
### Completed L-functions and the functional equation
-/

section gammaFactor

omit [NeZero N] -- not required for these declarations

open scoped Classical in
/-- The Archimedean Gamma factor: `Gammaℝ s` if `χ` is even, and `Gammaℝ (s + 1)` otherwise. -/
noncomputable def gammaFactor (χ : DirichletCharacter ℂ N) (s : ℂ) :=
  if χ.Even then Gammaℝ s else Gammaℝ (s + 1)

lemma Even.gammaFactor_def {χ : DirichletCharacter ℂ N} (hχ : χ.Even) (s : ℂ) :
    gammaFactor χ s = Gammaℝ s := by
  simp [gammaFactor, hχ]

lemma Odd.gammaFactor_def {χ : DirichletCharacter ℂ N} (hχ : χ.Odd) (s : ℂ) :
    gammaFactor χ s = Gammaℝ (s + 1) := by
  simp [gammaFactor, hχ.not_even]

end gammaFactor

/--
The completed L-function of a Dirichlet character, almost everywhere equal to
`LFunction χ s * gammaFactor χ s`.
-/
@[pp_nodot] noncomputable def completedLFunction (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ZMod.completedLFunction χ s

/--
The completed L-function of the (unique) Dirichlet character mod 1 is the completed Riemann zeta
function.
-/
lemma completedLFunction_modOne_eq {χ : DirichletCharacter ℂ 1} :
    completedLFunction χ = completedRiemannZeta := by
  ext; rw [completedLFunction, ZMod.completedLFunction_modOne_eq, map_one, one_mul]

/--
The completed L-function of a Dirichlet character is differentiable, with the following
exceptions: at `s = 1` if `χ` is the trivial character (to any modulus); and at `s = 0` if the
modulus is 1. This result is best possible.

Note both `χ` and `s` are explicit arguments: we will always be able to infer one or other
of them from the hypotheses, but it's not clear which!
-/
lemma differentiableAt_completedLFunction (χ : DirichletCharacter ℂ N) (s : ℂ)
    (hs₀ : s ≠ 0 ∨ N ≠ 1) (hs₁ : s ≠ 1 ∨ χ ≠ 1) :
    DifferentiableAt ℂ (completedLFunction χ) s :=
  ZMod.differentiableAt_completedLFunction _ _ (by have := χ.map_zero'; tauto)
    (by have := χ.sum_eq_zero_of_ne_one; tauto)

/-- The completed L-function of a non-trivial Dirichlet character is differentiable everywhere. -/
lemma differentiable_completedLFunction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Differentiable ℂ (completedLFunction χ) := by
  refine fun s ↦ differentiableAt_completedLFunction _ _ (Or.inr ?_) (Or.inr hχ)
  exact hχ ∘ level_one' _

/--
Relation between the completed L-function and the usual one. We state it this way around so
it holds at the poles of the gamma factor as well.
-/
lemma LFunction_eq_completed_div_gammaFactor (χ : DirichletCharacter ℂ N) (s : ℂ)
    (h : s ≠ 0 ∨ N ≠ 1) : LFunction χ s = completedLFunction χ s / gammaFactor χ s := by
  rcases χ.even_or_odd with hχ | hχ <;>
  rw [hχ.gammaFactor_def]
  · exact LFunction_eq_completed_div_gammaFactor_even hχ.to_fun _ (h.imp_right χ.map_zero')
  · apply LFunction_eq_completed_div_gammaFactor_odd hχ.to_fun

open scoped Classical in
/--
Global root number of `χ` (for `χ` primitive; junk otherwise). Defined as
`gaussSum χ stdAddChar / I ^ a / N ^ (1 / 2)`, where `a = 0` if even, `a = 1` if odd. (The factor
`1 / I ^ a` is the Archimedean root number.) This is a complex number of absolute value 1.
-/
noncomputable def rootNumber (χ : DirichletCharacter ℂ N) : ℂ :=
  gaussSum χ stdAddChar / I ^ (if χ.Even then 0 else 1) / N ^ (1 / 2 : ℂ)

/-- The root number of the unique Dirichlet character modulo 1 is 1. -/
lemma rootNumber_modOne (χ : DirichletCharacter ℂ 1) : rootNumber χ = 1 := by
  simp [rootNumber, gaussSum, -univ_unique, ← singleton_eq_univ (1 : ZMod 1),
    (show stdAddChar (1 : ZMod 1) = 1 from AddChar.map_zero_eq_one _),
    (show χ.Even from map_one _)]

namespace IsPrimitive

/-- **Functional equation** for primitive Dirichlet L-functions. -/
theorem completedLFunction_one_sub {χ : DirichletCharacter ℂ N} (hχ : IsPrimitive χ) (s : ℂ) :
    completedLFunction χ (1 - s) = N ^ (s - 1 / 2) * rootNumber χ * completedLFunction χ⁻¹ s := by
  classical
  -- First handle special case of Riemann zeta
  rcases eq_or_ne N 1 with rfl | hN
  · simp [completedLFunction_modOne_eq, completedRiemannZeta_one_sub, rootNumber_modOne]
  -- facts about `χ` as function
  have h_sum : ∑ j, χ j = 0 := by
    refine χ.sum_eq_zero_of_ne_one (fun h ↦ hN.symm ?_)
    rwa [IsPrimitive, h, conductor_one (NeZero.ne _)] at hχ
  let ε := I ^ (if χ.Even then 0 else 1)
  -- gather up powers of N
  rw [rootNumber, ← mul_comm_div, ← mul_comm_div, ← cpow_sub _ _ (NeZero.ne _), sub_sub, add_halves]
  calc completedLFunction χ (1 - s)
  _ = N ^ (s - 1) * χ (-1) /  ε * ZMod.completedLFunction (𝓕 χ) s := by
    simp only [ε]
    split_ifs with h
    · rw [pow_zero, div_one, h, mul_one, completedLFunction,
        completedLFunction_one_sub_even h.to_fun _ (.inr h_sum) (.inr <| χ.map_zero' hN)]
    · replace h : χ.Odd := χ.even_or_odd.resolve_left h
      rw [completedLFunction, completedLFunction_one_sub_odd h.to_fun,
        pow_one, h, div_I, mul_neg_one, ← neg_mul, neg_neg]
  _ = (_) * ZMod.completedLFunction (fun j ↦ χ⁻¹ (-1) * gaussSum χ stdAddChar * χ⁻¹ j) s := by
    congr 2 with j
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, ← neg_one_mul j, map_mul, mul_right_comm]
  _ = N ^ (s - 1) / ε * gaussSum χ stdAddChar * completedLFunction χ⁻¹ s * (χ (-1) * χ⁻¹ (-1)):= by
    rw [completedLFunction, completedLFunction_const_mul]
    ring
  _ = N ^ (s - 1) / ε * gaussSum χ stdAddChar * completedLFunction χ⁻¹ s := by
    rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply (isUnit_one.neg), mul_one]

end IsPrimitive

end DirichletCharacter

/-!
### The logarithmic derivative of the L-function of a Dirichlet character

We show that `s ↦ -(L' χ s) / L χ s + 1 / (s - 1)` is continuous outside the zeros of `L χ`
when `χ` is a trivial Dirichlet character and that `-L' χ / L χ` is continuous outside
the zeros of `L χ` when `χ` is nontrivial.
-/

namespace DirichletCharacter

open Complex

section trivial

variable (n : ℕ) [NeZero n]

/-- The function obtained by "multiplying away" the pole of `L χ` for a trivial Dirichlet
character `χ`. Its (negative) logarithmic derivative is used to prove Dirichlet's Theorem
on primes in arithmetic progression. -/
noncomputable abbrev LFunctionTrivChar₁ : ℂ → ℂ :=
  Function.update (fun s ↦ (s - 1) * LFunctionTrivChar n s) 1
    (∏ p ∈ n.primeFactors, (1 - (p : ℂ)⁻¹))

lemma LFunctionTrivChar₁_apply_one_ne_zero : LFunctionTrivChar₁ n 1 ≠ 0 := by
  simp only [Function.update_self]
  refine Finset.prod_ne_zero_iff.mpr fun p hp ↦ ?_
  simpa [sub_ne_zero] using (Nat.prime_of_mem_primeFactors hp).ne_one

/-- `s ↦ (s - 1) * L χ s` is an entire function when `χ` is a trivial Dirichlet character. -/
lemma differentiable_LFunctionTrivChar₁ : Differentiable ℂ (LFunctionTrivChar₁ n) := by
  rw [← differentiableOn_univ,
    ← differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]
  refine ⟨DifferentiableOn.congr (f := fun s ↦ (s - 1) * LFunctionTrivChar n s)
    (fun _ hs ↦ DifferentiableAt.differentiableWithinAt <| by fun_prop (disch := simp_all [hs]))
   fun _ hs ↦ Function.update_of_ne (Set.mem_diff_singleton.mp hs).2 ..,
    continuousWithinAt_compl_self.mp ?_⟩
  simpa using LFunctionTrivChar_residue_one

lemma deriv_LFunctionTrivChar₁_apply_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    deriv (LFunctionTrivChar₁ n) s =
      (s - 1) * deriv (LFunctionTrivChar n) s + LFunctionTrivChar n s := by
  have H : deriv (LFunctionTrivChar₁ n) s =
      deriv (fun w ↦ (w - 1) * LFunctionTrivChar n w) s := by
    refine eventuallyEq_iff_exists_mem.mpr ?_ |>.deriv_eq
    exact ⟨_, isOpen_ne.mem_nhds hs, fun _ hw ↦ Function.update_of_ne (Set.mem_setOf.mp hw) ..⟩
  rw [H, deriv_mul (by fun_prop) (differentiableAt_LFunction _ s (.inl hs)), deriv_sub_const,
    deriv_id'', one_mul, add_comm]

/-- The negative logarithmtic derivative of `s ↦ (s - 1) * L χ s` for a trivial
Dirichlet character `χ` is continuous away from the zeros of `L χ` (including at `s = 1`). -/
lemma continuousOn_neg_logDeriv_LFunctionTrivChar₁ :
    ContinuousOn (fun s ↦ -deriv (LFunctionTrivChar₁ n) s / LFunctionTrivChar₁ n s)
      {s | s = 1 ∨ LFunctionTrivChar n s ≠ 0} := by
  simp_rw [neg_div]
  have h := differentiable_LFunctionTrivChar₁ n
  refine ((h.contDiff.continuous_deriv le_rfl).continuousOn.div
    h.continuous.continuousOn fun w hw ↦ ?_).neg
  rcases eq_or_ne w 1 with rfl | hw'
  · exact LFunctionTrivChar₁_apply_one_ne_zero _
  · rw [LFunctionTrivChar₁, Function.update_of_ne hw', mul_ne_zero_iff]
    exact ⟨sub_ne_zero_of_ne hw', (Set.mem_setOf.mp hw).resolve_left hw'⟩

end trivial

section nontrivial

variable {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n}

/-- The negative logarithmic derivative of the L-function of a nontrivial Dirichlet character
is continuous away from the zeros of the L-function. -/
lemma continuousOn_neg_logDeriv_LFunction_of_nontriv (hχ : χ ≠ 1) :
    ContinuousOn (fun s ↦ -deriv (LFunction χ) s / LFunction χ s) {s | LFunction χ s ≠ 0} := by
  have h := differentiable_LFunction hχ
  simpa [neg_div] using ((h.contDiff.continuous_deriv le_rfl).continuousOn.div
    h.continuous.continuousOn fun _ hw ↦ hw).neg

end nontrivial

end DirichletCharacter
