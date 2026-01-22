/-
Copyright (c) 2026 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/
import Mathlib.Analysis.Complex.CanonicalProduct
import Mathlib.Analysis.Complex.DivisorIndex
import Mathlib.Analysis.Complex.DivisorConvergence
import Mathlib.Analysis.Complex.DivisorFiber
import Mathlib.Analysis.Complex.DivisorUnits
import Mathlib.Analysis.Complex.DivisorComplement
import Mathlib.Analysis.Complex.DivisorPartialProductFactor
import Mathlib.Analysis.Complex.DivisorQuotientConvergence
import Mathlib.Analysis.Complex.DivisorQuotientRemovable
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.DivisorSupport
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Data.Set.Countable
import Mathlib.Topology.LocallyFinsupp
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Order.Filter.Cofinite
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Hadamard factorization (preliminaries)

This file develops preliminary lemmas towards Hadamard factorization for entire functions on `ℂ`.
The main idea is to index zeros (with multiplicity) using the intrinsic divisor
`MeromorphicOn.divisor`, and to form the corresponding canonical product.

## Main definitions

- `Complex.Hadamard.divisorZeroIndex`, `Complex.Hadamard.divisorZeroIndex₀`: index types enumerating
  zeros with multiplicity.
- `Complex.Hadamard.divisorCanonicalProduct`: the canonical product indexed by `divisorZeroIndex₀`.
- `Complex.Hadamard.divisorComplementCanonicalProduct`: the canonical product with the fiber over a
  fixed point `z₀` removed.

## Main results

- The support of the divisor is discrete and countable, and meets compact sets in finitely many
  points.
- Under the standard summability hypothesis, the canonical product converges uniformly on compact
  sets, and its analytic order agrees with the expected multiplicity away from `0`.
-/

noncomputable section

namespace Complex.Hadamard

/-!
## Nonvanishing helpers for Weierstrass factors
-/

open scoped Topology
open Set

/-!
## Local finiteness on compact sets

For `D : Function.locallyFinsuppWithin U ℤ`, the support is *locally finite within `U`*.
Hence any compact `K ⊆ U` meets `D.support` only finitely often.

This yields “eventually in `cofinite`” bounds for divisor-indexed products.
-/

/-!
## Entire functions are never locally zero (under a global nontriviality witness)

If `f` is differentiable on `ℂ` and not identically zero, then it is not locally zero anywhere,
hence `analyticOrderAt f z ≠ ⊤` for all `z`.
-/

lemma analyticOrderAt_ne_top_of_exists_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnot : ∃ z : ℂ, f z ≠ 0) :
    ∀ z : ℂ, analyticOrderAt f z ≠ ⊤ := by
  classical
  rcases hnot with ⟨z1, hz1⟩
  have hf_an : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) := by
    intro z hz
    exact (Differentiable.analyticAt (f := f) hf z)
  have hz1_not_top : analyticOrderAt f z1 ≠ ⊤ := by
    have : analyticOrderAt f z1 = 0 :=
      (hf.analyticAt z1).analyticOrderAt_eq_zero.2 hz1
    simp [this]
  intro z
  exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (hf := hf_an)
    (U := (Set.univ : Set ℂ)) (x := z1) (y := z) (by simpa using isPreconnected_univ)
    (by simp) (by simp) hz1_not_top

/-!
## Avoiding zeros on a circle

If `f` is entire and not identically zero, and if a radius `r > 0` is different from the norms of
all (nonzero) divisor-indexed zeros inside an ambient bound `B`, then `f` has no zeros on the circle
`‖z‖ = r`.
-/

lemma no_zero_on_sphere_of_forall_val_norm_ne
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    {B r : ℝ} (hrpos : 0 < r) (hBr : r ≤ B)
    (hr_not :
      ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        ‖divisorZeroIndex₀_val p‖ ≤ B → r ≠ ‖divisorZeroIndex₀_val p‖) :
    ∀ u : ℂ, ‖u‖ = r → f u ≠ 0 := by
  classical
  intro u hur
  have hu0 : u ≠ 0 := by
    intro hu0
    subst hu0
    have : (0 : ℝ) = r := by simpa using hur
    exact (ne_of_gt hrpos) this.symm
  intro hfu0
  have hnotTop : analyticOrderAt f u ≠ ⊤ :=
    analyticOrderAt_ne_top_of_exists_ne_zero (f := f) hf hnot u
  have hord_ne0 : analyticOrderNatAt f u ≠ 0 := by
    intro h0
    have hEN : (analyticOrderNatAt f u : ENat) = 0 := by simp [h0]
    have hAt0 : analyticOrderAt f u = 0 := by
      have hcast : (analyticOrderNatAt f u : ENat) = analyticOrderAt f u :=
        Nat.cast_analyticOrderNatAt (f := f) (z₀ := u) hnotTop
      simpa [hcast] using hEN
    have han : AnalyticAt ℂ f u := Differentiable.analyticAt (f := f) hf u
    exact ((han.analyticOrderAt_eq_zero).1 hAt0) hfu0
  have hcard_pos : 0 < (divisorZeroIndex₀_fiberFinset (f := f) u).card := by
    have hcard :=
      divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt (hf := hf) (z₀ := u) hu0
    have : 0 < analyticOrderNatAt f u := Nat.pos_of_ne_zero hord_ne0
    simpa [hcard] using this
  rcases Finset.card_pos.mp hcard_pos with ⟨p, hp⟩
  have hpval : divisorZeroIndex₀_val p = u :=
    (mem_divisorZeroIndex₀_fiberFinset (f := f) (z₀ := u) p).1 hp
  have hpB : ‖divisorZeroIndex₀_val p‖ ≤ B := by
    have : ‖divisorZeroIndex₀_val p‖ = r := by simp [hpval, hur]
    simpa [this] using hBr
  have : r ≠ ‖divisorZeroIndex₀_val p‖ := hr_not p hpB
  exact this (by simp [hpval, hur])

/-!
## Basic correctness: the divisor canonical product vanishes at indexed zeros

If one of the factors is `0` at `z`, then the infinite product is `0`.
-/

theorem divisorCanonicalProduct_eq_zero_of_exists
    (m : ℕ) (f : ℂ → ℂ) (z : ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (h0 : ∃ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
      weierstrassFactor m (z / divisorZeroIndex₀_val p) = 0) :
    divisorCanonicalProduct m f (Set.univ : Set ℂ) z = 0 := by
  classical
  have hloc :
      HasProdLocallyUniformlyOn
        (fun (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (w : ℂ) =>
          weierstrassFactor m (w / divisorZeroIndex₀_val p))
        (divisorCanonicalProduct m f (Set.univ : Set ℂ))
        (Set.univ : Set ℂ) :=
    hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ (m := m) (f := f) h_sum
  have hprod :
      HasProd (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
          weierstrassFactor m (z / divisorZeroIndex₀_val p))
        (divisorCanonicalProduct m f (Set.univ : Set ℂ) z) :=
    hloc.hasProd (by simp : z ∈ (Set.univ : Set ℂ))
  have hzero :
      HasProd (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
          weierstrassFactor m (z / divisorZeroIndex₀_val p))
        0 := by
    refine hasProd_zero_of_exists_eq_zero (L := (SummationFilter.unconditional
      (divisorZeroIndex₀ f (Set.univ : Set ℂ)))) ?_
    rcases h0 with ⟨p, hp⟩
    exact ⟨p, hp⟩
  exact (hprod.unique hzero)

theorem divisorCanonicalProduct_eq_zero_at_index
    (m : ℕ) (f : ℂ → ℂ)
    (h_sum : Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    divisorCanonicalProduct m f (Set.univ : Set ℂ) (divisorZeroIndex₀_val p) = 0 := by
  classical
  refine divisorCanonicalProduct_eq_zero_of_exists (m := m) (f := f)
    (z := divisorZeroIndex₀_val p) h_sum ?_
  refine ⟨p, ?_⟩
  have hp0 : divisorZeroIndex₀_val p ≠ 0 := p.property
  simp [hp0, weierstrassFactor]

/-!
## The fiber finite product has the expected order at `z₀`

This packages the finite multiplicity calculation for the specific finset corresponding to the fiber
`{p | divisorZeroIndex₀_val p = z₀}`.
-/

theorem analyticOrderAt_prod_fiberFinset
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) :
    analyticOrderAt (fun z : ℂ => ∏ p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀,
            weierstrassFactor m (z / divisorZeroIndex₀_val p))
      z₀ = ((divisorZeroIndex₀_fiberFinset (f := f) z₀).card : ℕ∞) := by
  classical
  have h :=
    analyticOrderAt_finset_prod_weierstrassFactor_divisorZeroIndex₀
      (m := m) (f := f) (s := divisorZeroIndex₀_fiberFinset (f := f) z₀) (z₀ := z₀)
  have hfilter :
      (divisorZeroIndex₀_fiberFinset (f := f) z₀).filter (fun p => divisorZeroIndex₀_val p = z₀) =
        divisorZeroIndex₀_fiberFinset (f := f) z₀ := by
    ext p; simp
  simpa [hfilter] using h

theorem analyticOrderNatAt_prod_fiberFinset
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) : analyticOrderNatAt (fun z : ℂ =>
          ∏ p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀,
            weierstrassFactor m (z / divisorZeroIndex₀_val p)) z₀ =
      (divisorZeroIndex₀_fiberFinset (f := f) z₀).card := by
  simpa [analyticOrderNatAt] using
    congrArg ENat.toNat (analyticOrderAt_prod_fiberFinset (m := m) (f := f) (z₀ := z₀))

/-!
## Refining the factorization: factoring out `(z - z₀)^k` using the fiber-only product

When `s` contains the fiber finset, we can write the partial product as

`divisorPartialProduct s = (z - z₀)^k • (divisorComplementPartialProduct s * u)`

where `u` is the analytic quotient coming from the fiber-only product.
-/

theorem eventually_exists_analyticAt_eq_pow_smul_divisorComplementPartialProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ) :
    ∀ᶠ s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) in (Filter.atTop : Filter _),
      ∃ u : ℂ → ℂ,
        AnalyticAt ℂ u z₀ ∧ u z₀ ≠ 0 ∧
          (fun z : ℂ => divisorPartialProduct m f s z)
            =ᶠ[𝓝 z₀]
            fun z : ℂ =>
              (z - z₀) ^ (divisorZeroIndex₀_fiberFinset (f := f) z₀).card •
                (divisorComplementPartialProduct m f z₀ s z * u z) := by
  classical
  let fiber : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
    divisorZeroIndex₀_fiberFinset (f := f) z₀
  have hfib : ∃ u : ℂ → ℂ, AnalyticAt ℂ u z₀ ∧ u z₀ ≠ 0 ∧ (fun z : ℂ =>
      divisorPartialProduct m f fiber z) =ᶠ[𝓝 z₀] fun z : ℂ => (z - z₀) ^ fiber.card • u z := by
    simpa [fiber, divisorPartialProduct] using
      (exists_analyticAt_eq_pow_smul_of_partialProduct_contains_fiber (m := m) (f := f) (z₀ := z₀)
        (s := fiber) (by rfl : fiber ⊆ fiber))
  rcases hfib with ⟨u, huA, hu0, huEq⟩
  refine (eventually_atTop_subset_fiberFinset (f := f) z₀).mono ?_
  intro s hs
  refine ⟨u, huA, hu0, ?_⟩
  have hmul : ∀ z : ℂ, divisorPartialProduct m f s z =
        divisorPartialProduct m f fiber z * divisorComplementPartialProduct m f z₀ s z := by
    intro z
    simpa [fiber] using
      (divisorPartialProduct_eq_fiber_mul_complement_of_subset (m := m) (f := f) (z₀ := z₀)
        (z := z) (s := s) hs)
  have hmul_ev : (fun z : ℂ => divisorPartialProduct m f s z) =ᶠ[𝓝 z₀] fun z : ℂ =>
      ((z - z₀) ^ fiber.card • u z) * divisorComplementPartialProduct m f z₀ s z := by
    filter_upwards [huEq] with z hz
    have hsplit_z : divisorPartialProduct m f s z =
          divisorPartialProduct m f fiber z * divisorComplementPartialProduct m f z₀ s z :=
      hmul z
    calc
      divisorPartialProduct m f s z = divisorPartialProduct m f fiber z *
        divisorComplementPartialProduct m f z₀ s z := hsplit_z
      _ = (((z - z₀) ^ fiber.card • u z) * divisorComplementPartialProduct m f z₀ s z) := by
            simpa [mul_assoc] using congrArg (fun t => t *
              divisorComplementPartialProduct m f z₀ s z) hz
  filter_upwards [hmul_ev] with z hz
  simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, fiber] using hz

lemma divisorPartialProduct_ne_zero_on_ball_punctured
    (m : ℕ) {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hball :
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) :
    ∀ z ∈ Metric.ball z₀ ε, z ≠ z₀ → divisorPartialProduct m f s z ≠ 0 := by
  classical
  intro z hz hz0
  have hfac :
      ∀ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p) ≠ 0 := by
    intro p hp
    exact weierstrassFactor_div_ne_zero_on_ball_punctured
      (m := m) (f := f) (z₀ := z₀) (ε := ε) hball z hz hz0 p
  simpa [divisorPartialProduct, Finset.prod_ne_zero_iff] using hfac


end Hadamard
end Complex
