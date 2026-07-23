/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.DvdKAssembly
import Archive.GaussianMomentConjecture.DvdKPhiCoincide
import Archive.GaussianMomentConjecture.DvdKTransposeAssembly
import Archive.GaussianMomentConjecture.DvdKUnivariateReduction
import Archive.GaussianMomentConjecture.DvdKWeierstrass
import Archive.GaussianMomentConjecture.FrameBridgeAssembly
import Mathlib

set_option linter.minImports true

/-!
# The Omega-wiring: discharging `SinglePolyCrux`, hence unconditional GMC(2)

Composes the landed pieces over `Ω = AlgebraicClosure (LaurentSeries ℂ)`:
* `smallRootFactor_map_dvd_phiVieta_map` — the divisor `Pω ∣ Φ` over `LaurentSeries ℂ`;
* `smallRootFactor_coeff0_of_vanish` — the value `P.coeff 0 = −X·r₀`;
* `hS_of_dvd_value` — the packet product `∏β = algebraMap((-1)ᴹ·v)`.

The `Algebra (RatFunc ℂ) (LaurentSeries ℂ)` instance is non-synthesizable, so it is provided locally via
`rfToL`; then `AlgebraicClosure.instAlgebra` lifts it to `Ω` and `IsAlgClosed.lift` supplies
the embedding `ψ`.
-/

open Polynomial

namespace GMC2DvdKOmegaWiring

/-- **`SinglePolyCrux` holds** — the sole remaining hypothesis of `gmc2_of_crux`. -/
theorem singlePolyCrux_holds : GMC2DvdKUnivariateReduction.SinglePolyCrux := by
  classical
  intro R M hM hMd hR0 hvanish
  set Φ := GMC2PhiVieta.Phi R M with hΦdef
  have hΦ0 : Φ ≠ 0 := (GMC2DvdKAssembly.irreducible_Phi R M hM hR0).ne_zero
  -- the non-synthesizable base algebra, via `rfToL`
  letI algRL : Algebra (RatFunc ℂ) (LaurentSeries ℂ) := (GMC2DvdKPhiCoincide.rfToL).toAlgebra
  set Ω := AlgebraicClosure (LaurentSeries ℂ) with hΩ
  haveI : IsScalarTower (RatFunc ℂ) (LaurentSeries ℂ) Ω :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsAlgebraic (RatFunc ℂ) Φ.SplittingField :=
    Algebra.IsAlgebraic.of_finite (RatFunc ℂ) Φ.SplittingField
  let ψ : Φ.SplittingField →ₐ[RatFunc ℂ] Ω := IsAlgClosed.lift
  -- the divisor over Ω
  set Pω : Polynomial Ω :=
    ((GMC2DvdKWeierstrass.smallRootFactor R M).map (HahnSeries.ofPowerSeries ℤ ℂ)).map
      (algebraMap (LaurentSeries ℂ) Ω) with hPωdef
  have halg : (algebraMap (LaurentSeries ℂ) Ω).comp (GMC2DvdKPhiCoincide.rfToL)
      = algebraMap (RatFunc ℂ) Ω := rfl
  -- monic
  have hmonic : Pω.Monic :=
    ((GMC2DvdKWeierstrass.smallRootFactor_monic R M).map _).map _
  -- splits (over the algebraically closed Ω) and nodup roots
  have hPωsplit : Pω.Splits := IsAlgClosed.splits Pω
  -- divisibility over Ω
  have hdvd : Pω ∣ Φ.map (algebraMap (RatFunc ℂ) Ω) := by
    rw [← halg, ← Polynomial.map_map]
    exact (Polynomial.map_dvd_map' (algebraMap (LaurentSeries ℂ) Ω)).mpr
      (GMC2DvdKPhiCoincide.smallRootFactor_map_dvd_phiVieta_map R M)
  -- Φ.map is separable ⇒ its divisor Pω is squarefree ⇒ nodup roots
  have hsepΦ : (Φ.map (algebraMap (RatFunc ℂ) Ω)).Separable :=
    ((PerfectField.separable_of_irreducible (GMC2DvdKAssembly.irreducible_Phi R M hM hR0))).map
  have hPωnd : Pω.roots.Nodup :=
    Polynomial.nodup_roots (hsepΦ.of_dvd hdvd)
  -- the value: Pω.coeff 0 = algebraMap v, v = -C(r0)·X
  set v : RatFunc ℂ := - RatFunc.C (R.coeff 0) * RatFunc.X with hvdef
  have hval : Pω.coeff 0 = algebraMap (RatFunc ℂ) Ω v := by
    rw [hPωdef, Polynomial.coeff_map, Polynomial.coeff_map,
      GMC2DvdKTransposeAssembly.smallRootFactor_coeff0_of_vanish R M hM hvanish]
    rw [hvdef, ← halg, RingHom.comp_apply]
    congr 1
    -- ofPowerSeries(-X·r0) = rfToL(-C r0 · X)  in LaurentSeries ℂ
    have hcC : (HahnSeries.ofPowerSeries ℤ ℂ) ((algebraMap ℂ (PowerSeries ℂ)) (R.coeff 0))
        = GMC2DvdKPhiCoincide.rfToL (RatFunc.C (R.coeff 0)) := by
      rw [← RingHom.comp_apply, GMC2DvdKPhiCoincide.ofPowerSeries_comp_C,
        ← RatFunc.algebraMap_eq_C, ← RingHom.comp_apply, GMC2DvdKPhiCoincide.rfToL_comp_algebraMap]
    rw [map_mul, map_neg, map_mul, map_neg, HahnSeries.ofPowerSeries_X,
      GMC2DvdKPhiCoincide.rfToL_X, hcC]
    ring
  -- assemble via bridge
  obtain ⟨S, hS⟩ := GMC2FrameBridgeAssembly.hS_of_dvd_value Φ hΦ0 ψ Pω hmonic hPωsplit hPωnd hdvd v hval
  -- a root of Φ for the (unused) `x0` witness
  have hdeg : 0 < Φ.natDegree := by rw [hΦdef, GMC2PhiVieta.natDegree_Phi R M hMd]; omega
  obtain ⟨x0, hx0⟩ : ∃ x : Φ.SplittingField, x ∈ Φ.rootSet Φ.SplittingField := by
    have hsm : (Φ.map (algebraMap (RatFunc ℂ) Φ.SplittingField)).Splits :=
      Polynomial.IsSplittingField.splits Φ.SplittingField Φ
    have hnd : (Φ.map (algebraMap (RatFunc ℂ) Φ.SplittingField)).natDegree ≠ 0 := by
      rw [Polynomial.natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective _ _),
        hΦdef, GMC2PhiVieta.natDegree_Phi R M hMd]; omega
    obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero (hsm.roots_ne_zero hnd)
    refine ⟨x, Polynomial.mem_rootSet.mpr ⟨hΦ0, ?_⟩⟩
    have hr := (Polynomial.mem_roots'.mp hx).2
    rwa [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def] at hr
  have hPωdeg : Pω.natDegree = M := by
    rw [hPωdef, Polynomial.natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective _ _),
      Polynomial.natDegree_map_eq_of_injective (HahnSeries.ofPowerSeries_injective),
      GMC2DvdKWeierstrass.smallRootFactor_natDegree]
  refine ⟨S, ⟨x0, hx0⟩, (-1) ^ (M + 1) * R.coeff 0,
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hR0, ?_⟩
  rw [hS, hPωdeg, hvdef]
  rw [show ((-1 : RatFunc ℂ) ^ M * (-RatFunc.C (R.coeff 0) * RatFunc.X))
      = RatFunc.C ((-1) ^ (M + 1) * R.coeff 0) * RatFunc.X by
    rw [map_mul, map_pow, map_neg, map_one, pow_succ]; ring]

/-- **GMC(2), unconditional.**  `gmc2_of_crux` applied to the now-proved `SinglePolyCrux`.
Every input — the analytic core (`hderiv`), the frame factorization, the degree lemma, and this
Omega-wiring — is kernel-pure. -/
theorem gmc2_unconditional (P Q : MvPolynomial (Fin 2) ℂ)
    (hnull : ∀ m : ℕ, 1 ≤ m → GMC2.E (P ^ m) = 0) :
    ∃ N : ℕ, ∀ m ≥ N, GMC2.E (Q * P ^ m) = 0 :=
  GMC2DvdKUnivariateReduction.gmc2_of_crux singlePolyCrux_holds P Q hnull

end GMC2DvdKOmegaWiring

