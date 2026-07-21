/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Riccardo Brasca, Xavier Roblot
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.Sandbox

/-!
# Dirichlet density of a set of prime ideals

Let `K` be a number field and let `S` be a set of nonzero prime ideals of `𝓞 K`, that is a set of
elements of `IsDedekindDomain.HeightOneSpectrum (𝓞 K)`. The Dirichlet density of `S` is

  δ(S) = lim_{s → 1⁺} Σ_{𝔭 ∈ S} N 𝔭 ^ (-s) / Σ_𝔭 N 𝔭 ^ (-s),

when this limit exists, the sum in the denominator running over all nonzero prime ideals.

## Main definitions

* `NumberField.primeIdealZetaSum` — the partial Dirichlet series `Σ_{𝔭 ∈ S} N 𝔭 ^ (-s)`.
* `NumberField.HasDirichletDensity` — `S` has Dirichlet density `δ`.

## Main results

* `NumberField.primeIdealZetaSum_le_card_of_finite` — for a finite `S`, the partial sum is bounded
  above by the number of elements of `S`.
* `NumberField.hasDirichletDensity_empty` — the empty set has Dirichlet density `0`.

-/

@[expose] public section

noncomputable section

open Filter IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology Set

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The partial Dirichlet series `∑_{𝔭 ∈ S} N𝔭 ^ (-s)`. -/
def primeIdealZetaSum (S : Set (HeightOneSpectrum (𝓞 K))) (s : ℝ) : ℝ :=
  ∑' 𝔭 : S, (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)

theorem primeIdealZetaSum_def (s : ℝ) :
    primeIdealZetaSum S s = ∑' 𝔭 : S, (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) := rfl

theorem primeIdealZetaSum_nonneg (s : ℝ) :
    0 ≤ primeIdealZetaSum S s :=
  tsum_nonneg fun _ ↦ by positivity

private theorem sum_fiber_le {s : ℝ} (hs : 0 ≤ s) (v : HeightOneSpectrum ℤ) :
    ∑' 𝔭 : {𝔭 : HeightOneSpectrum (𝓞 K) // 𝔭.under ℤ = v}, (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)
        ≤ (Module.finrank ℤ (𝓞 K) : ℝ) * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) := by
  have := Fintype.ofFinite {𝔭 : HeightOneSpectrum (𝓞 K) // 𝔭.under ℤ = v}
  rw [tsum_fintype]
  refine le_trans (Finset.univ.sum_le_card_nsmul _ ((Ideal.absNorm v.asIdeal : ℝ) ^ (-s)) ?_) ?_
  · intro 𝔭 _
    refine Real.rpow_le_rpow_of_nonpos ?_ (by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero fun h ↦ 𝔭.1.ne_bot
        (Ideal.absNorm_eq_zero_iff.mp h))
        (by rw [show v.asIdeal = 𝔭.1.asIdeal.under ℤ by rw [← under_asIdeal, 𝔭.2]]
            exact Ideal.absNorm_under_dvd_absNorm 𝔭.1.asIdeal)) (by simpa)
    exact_mod_cast Nat.pos_of_ne_zero fun h ↦ v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  · rw [Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul]
    gcongr
    exact_mod_cast show Nat.card {𝔭 : HeightOneSpectrum (𝓞 K) // 𝔭.under ℤ = v} ≤
        Module.finrank ℤ (𝓞 K) by
      rw [Nat.card_congr (primesOverEquiv v), Nat.card_coe_set_eq]
      exact Ideal.ncard_primesOver_le

/-- The prime-ideal zeta sum converges for real `s > 1`. -/
theorem summable_primeIdealZetaSum {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) := by
  have hbase : Summable (fun v : HeightOneSpectrum ℤ ↦ (Ideal.absNorm v.asIdeal : ℝ) ^ (-s)) := by
    rw [← primesEquiv.symm.summable_iff]
    simp only [Function.comp_def, primesEquiv_symm_apply_asIdeal, Ideal.absNorm_span_singleton,
      Algebra.norm_self, MonoidHom.id_apply, Int.natAbs_natCast]
    exact Nat.Primes.summable_rpow.mpr <| by rwa [neg_lt_neg_iff]
  rw [← (Equiv.sigmaFiberEquiv (fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ 𝔭.under ℤ)).summable_iff]
  simp only [Function.comp_def]
  rw [summable_sigma_of_nonneg (fun _ ↦ by positivity)]
  refine ⟨fun _ ↦ .of_finite, ?_⟩
  exact Summable.of_nonneg_of_le (fun v ↦ tsum_nonneg fun _ ↦ by positivity)
    (fun v ↦ sum_fiber_le (by linarith) v) (hbase.mul_left _)

variable {S} in
/-- For a finite set `S` of prime ideals, the partial sum `∑_{𝔭 ∈ S} N𝔭 ^ (-s)` is bounded above
by the number of elements of `S`. -/
theorem primeIdealZetaSum_le_card_of_finite (hS : S.Finite) {s : ℝ} (hs : 0 ≤ s) :
    primeIdealZetaSum S s ≤ S.ncard := by
  let : Fintype S := @Fintype.ofFinite _ hS.to_subtype
  rw [primeIdealZetaSum_def, tsum_fintype, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  calc ∑ 𝔭 : S, (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)
      ≤ ∑ 𝔭 : S, 1 := by
        refine Finset.sum_le_sum fun 𝔭 _ ↦ Real.rpow_le_one_of_one_le_of_nonpos ?_ (by linarith)
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact 𝔭.1.ne_bot)
    _ = Fintype.card S := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- `S` has Dirichlet density `δ` when the ratio `∑_{𝔭 ∈ S} N𝔭 ^ (-s) / ∑_𝔭 N𝔭 ^ (-s)`, of the
partial sum over `S` to the sum over all nonzero prime ideals, tends to `δ` as `s ↓ 1`. -/
def HasDirichletDensity (δ : ℝ) : Prop :=
  Tendsto (fun s : ℝ ↦ primeIdealZetaSum S s /
    primeIdealZetaSum (univ : Set (HeightOneSpectrum (𝓞 K))) s) (𝓝[>] 1) (𝓝 δ)

variable {S}

/-- The Dirichlet density of `S`, when it exists, is unique. -/
theorem HasDirichletDensity.unique {δ₁ δ₂ : ℝ} (h₁ : HasDirichletDensity S δ₁)
    (h₂ : HasDirichletDensity S δ₂) :
    δ₁ = δ₂ :=
  tendsto_nhds_unique h₁ h₂

/-- The Dirichlet density of the empty set is `0`. -/
theorem hasDirichletDensity_empty :
    HasDirichletDensity (∅ : Set (HeightOneSpectrum (𝓞 K))) 0 := by
  simp [HasDirichletDensity, primeIdealZetaSum_def]

/-- The Dirichlet density is nonnegative. -/
theorem HasDirichletDensity.nonneg {δ : ℝ} (h : HasDirichletDensity S δ) :
    0 ≤ δ :=
  ge_of_tendsto h <| Eventually.of_forall fun s ↦
    div_nonneg (primeIdealZetaSum_nonneg S s) (primeIdealZetaSum_nonneg univ s)

end NumberField
