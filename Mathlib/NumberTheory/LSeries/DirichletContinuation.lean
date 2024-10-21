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
L-series of `χ` has analytic continuation (away from a pole at `s = 1` if `χ` is trivial).

All definitions and theorems are in the `DirichletCharacter` namespace.

## Main definitions

* `LFunction χ s`: the L-function, defined as a linear combination of Hurwitz zeta functions.

## Main theorems

* `LFunction_eq_LSeries`: if `1 < re s` then the `LFunction` coincides with the naive `LSeries`.
* `differentiable_LFunction`: if `χ` is nontrivial then `LFunction χ s` is differentiable
  everywhere.
-/

open Complex Filter

open scoped Topology

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/--
The unique meromorphic function `ℂ → ℂ` which agrees with `∑' n : ℕ, χ n / n ^ s` wherever the
latter is convergent. This is constructed as a linear combination of Hurwitz zeta functions.

Note that this is not the same as `LSeries χ`: they agree in the convergence range, but
`LSeries χ s` is defined to be `0` if `re s ≤ 1`.
 -/
noncomputable def LFunction (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ := ZMod.LFunction χ s

/-- The L-function of the (unique) Dirichlet character mod 1 is the Riemann zeta function.
(Compare `DirichletCharacter.LSeries_modOne_eq`.) -/
@[simp] lemma LFunction_modOne_eq {χ : DirichletCharacter ℂ 1} :
    LFunction χ = riemannZeta := by
  ext1; rw [LFunction, ZMod.LFunction_modOne_eq, (by rfl : (0 : ZMod 1) = 1), map_one, one_mul]

/--
For `1 < re s` the L-function of a Dirichlet character agrees with the sum of the naive Dirichlet
series.
-/
lemma LFunction_eq_LSeries (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < re s) :
    LFunction χ s = LSeries (χ ·) s :=
  ZMod.LFunction_eq_LSeries χ hs

/--
The L-function of a Dirichlet character is differentiable, except at `s = 1` if the character is
trivial.
-/
lemma differentiableAt_LFunction (χ : DirichletCharacter ℂ N) (s : ℂ) (hs : s ≠ 1 ∨ χ ≠ 1) :
    DifferentiableAt ℂ (LFunction χ) s :=
  ZMod.differentiableAt_LFunction χ s (hs.imp_right χ.sum_eq_zero_of_ne_one)

/-- The L-function of a non-trivial Dirichlet character is differentiable everywhere. -/
lemma differentiable_LFunction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Differentiable ℂ (LFunction χ) :=
  (differentiableAt_LFunction _ · <| Or.inr hχ)

/-!
## Results on changing levels
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
    refine .finset_prod fun i h ↦ (differentiableAt_const _).sub ((differentiableAt_const _).mul ?_)
    have : NeZero i := ⟨(Nat.pos_of_mem_primeFactors h).ne'⟩
    apply differentiable_const_cpow_neg
  · refine eventually_of_mem ?_  (fun t (ht : 1 < t.re) ↦ ?_)
    · exact (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num : 1 < (2 : ℂ).re)
    · simpa only [LFunction_eq_LSeries _ ht] using LSeries_changeLevel hMN χ ht

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
      (differentiable_LFunction h).continuous.mul <|
        continuous_finset_prod _ fun p hp ↦ continuous_const.sub <| continuous_const.mul <|
          have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩;
          continuous_const_cpow_neg _
    exact congrFun ((differentiable_LFunction hχ).continuous.ext_on
      (dense_compl_singleton 1) h' (fun _ h ↦ LFunction_changeLevel_aux hMN χ h)) s
  · exact LFunction_changeLevel_aux hMN χ h

/-!
## The `L`-function of the trivial character mod `N`
-/

/-- The `L`-function of the trivial character mod `N`. -/
noncomputable abbrev LFunction_triv_char (N : ℕ) [NeZero N] :=
  (1 : DirichletCharacter ℂ N).LFunction

/-- The L function of the trivial Dirichlet character mod `N` is obtained from the Riemann
zeta function by multiplying with `∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))`. -/
lemma LFunction_one_eq_mul_riemannZeta {s : ℂ} (hs : s ≠ 1) :
    LFunction_triv_char N s = (∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s := by
  rw [← LFunction_modOne_eq (χ := 1), LFunction_triv_char, ← changeLevel_one N.one_dvd, mul_comm]
  convert LFunction_changeLevel N.one_dvd 1 (.inr hs) using 4 with p
  rw [MulChar.one_apply <| isUnit_of_subsingleton _, one_mul]

/-- The L function of the trivial Dirichlet character mod `N` has a simple pole with
residue `∏ p ∈ N.primeFactors, (1 - p⁻¹)` at `s = 1`. -/
lemma LFunction_one_residue_one :
    Tendsto (fun s ↦ (s - 1) * LFunction_triv_char N s) (𝓝[≠] 1)
      (𝓝 <| ∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹)) := by
  have H : (fun s ↦ (s - 1) * LFunction_triv_char N s) =ᶠ[𝓝[≠] 1]
        fun s ↦ (∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))) * ((s - 1) * riemannZeta s) := by
    refine Set.EqOn.eventuallyEq_nhdsWithin fun s hs ↦ ?_
    rw [mul_left_comm, LFunction_one_eq_mul_riemannZeta hs]
  rw [tendsto_congr' H]
  conv => enter [3, 1]; rw [← mul_one <| Finset.prod ..]; enter [1, 2, p]; rw [← cpow_neg_one]
  refine .mul (f := fun s ↦ ∏ p ∈ N.primeFactors, _) ?_ riemannZeta_residue_one
  refine tendsto_nhdsWithin_of_tendsto_nhds <| Continuous.tendsto ?_ 1
  exact continuous_finset_prod _ fun p hp ↦
    have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    continuous_const.sub (continuous_const_cpow_neg _)

end DirichletCharacter
