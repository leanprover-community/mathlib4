/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.DvdKFrameDegree
import Archive.GaussianMomentConjecture.DvdKFrameExtraction
import Archive.GaussianMomentConjecture.DvdKFrameHSide
import Archive.GaussianMomentConjecture.DvdKHderivAssembly
import Archive.GaussianMomentConjecture.DvdKMultiplicativeClosing
import Archive.GaussianMomentConjecture.DvdKTranspose
import Archive.GaussianMomentConjecture.DvdKUnitOrigin
import Mathlib

set_option linter.minImports true

/-!
# Transpose glue: the concrete data feeding kps's `hderiv_via_transpose`

transpose `GMC2.DvdKTranspose.phi : F⟦t⟧⟦x⟧ →+* (F⸨x⸩)⟦t⟧` (the swap `τ` followed by `F⟦x⟧ ↪ F⸨x⸩`)
and kps's `GMC2.DvdKHderivAssembly.hderiv_via_transpose` (which supplies the h-side (a) and the
`F = 1` extraction internally) leave exactly the **concrete transpose glue** open — the piece
flagged as "`phi_Phi` connector remaining". This module provides it:

* `phi_Phi` : `φ(Φ) = PhiFrame (Rl R) M` — the frame factorization (`hfact` via `map_mul`);
* `coeff0_Pfr` / `coeff_Pfr_support` : `φP` is monic of `x`-degree `M`, higher `t`-coeffs of degree
  `< M` — feeds the degree lemma `(c)` (`hc`);
* `xCoeff0_phi_unit` : `xCoeff0(φ h) = unitCoeff0` — the `x⁰`-part is `h(0,t)` (`hbridge`, `hg`);
* `Rl_pow_coeff` : `(Rlᵐ).coeff(M·m) = (Rᵐ).coeff(M·m)` — transports the polynomial vanishing to the
  frame (`hvanish`).

Payload `hderiv_final` : `d_t(unitCoeff0) = 0` under the DvdK vanishing, which makes
`GMC2.DvdKMultiplicativeClosing.smallRootFactor_coeff0_eq_of_derivative_vanishes` unconditional —
`P.coeff 0 = c·t`, the last analytic gap of the multiplicative DvdK route.
-/

open PowerSeries HahnSeries GMC2.DvdKFrame GMC2.DvdKTranspose GMC2.DvdKWeierstrass

namespace GMC2.DvdKTransposeAssembly

variable {F : Type*} [Field F]

/-- The frame `R`: the Laurent image of `R`'s power series (`φ` sends the `Φ`-coefficient `R` here).
-/
noncomputable def Rl (R : Polynomial F) : LaurentSeries F :=
  HahnSeries.ofPowerSeries ℤ F (R : PowerSeries F)

/-- The DvdK frame moment `(Rlᵐ).coeff(M·m)` equals the polynomial central coefficient
`(Rᵐ).coeff(M·m)` — the bridge from `SinglePolyCrux`'s vanishing hypothesis to the frame's. -/
theorem Rl_pow_coeff (R : Polynomial F) (M m : ℕ) :
    (Rl R ^ m).coeff ((M : ℤ) * m) = (R ^ m).coeff (M * m) := by
  have hm : (Rl R) ^ m = HahnSeries.ofPowerSeries ℤ F ((R ^ m : Polynomial F) : PowerSeries F) := by
    rw [Rl, ← map_pow, Polynomial.coe_pow]
  rw [hm]
  have hcast : ((M : ℤ) * m) = ((M * m : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, LaurentSeries.coeff_coe_powerSeries, Polynomial.coeff_coe]

/-- `τ` sends `R(x)` (scalar coefficients, embedded via `algebraMap`) to `C (R : F⟦t⟧)`. -/
theorem tau_Rcoe (R : Polynomial F) :
    tau ((R.map (algebraMap F (PowerSeries F)) : (PowerSeries F)⟦X⟧))
      = PowerSeries.C (R : PowerSeries F) := by
  refine PowerSeries.ext fun a => PowerSeries.ext fun b => ?_
  rw [coeff_coeff_tau, Polynomial.coeff_coe, Polynomial.coeff_map]
  by_cases ha : a = 0
  · subst ha
    simp [PowerSeries.coeff_C, Polynomial.coeff_coe]
  · rw [show (algebraMap F (PowerSeries F)) (R.coeff b) = PowerSeries.C (R.coeff b) from rfl]
    simp [PowerSeries.coeff_C, ha]

/-- `φ` sends `R(x)` to the constant-in-`t` Laurent series `C (Rl R)`. -/
theorem phi_Rcoe (R : Polynomial F) :
    phi ((R.map (algebraMap F (PowerSeries F)) : (PowerSeries F)⟦X⟧))
      = PowerSeries.C (Rl R) := by
  rw [phi, RingHom.comp_apply,
    show tauHom ((R.map (algebraMap F (PowerSeries F)) : (PowerSeries F)⟦X⟧))
      = PowerSeries.C (R : PowerSeries F) from tau_Rcoe R, PowerSeries.map_C, Rl]

/-- **The frame identity** (flagged connector).  `φ` sends `Φ = xᴹ − t·R` to
`PhiFrame (Rl R) M`. -/
theorem phi_Phi (R : Polynomial F) (M : ℕ) :
    phi (Phi R M) = PhiFrame (Rl R) M := by
  rw [GMC2.DvdKWeierstrass.Phi, map_sub, map_mul, phi_C_X, phi_Rcoe, PhiFrame]
  congr 1
  rw [map_pow, phi_X, ← map_pow]

/-- **The seam.**  `xCoeff0 (φ h) = h(0,t) = unitCoeff0 R M` — the frame's `x⁰`-extraction of the
transported Weierstrass unit recovers exactly its `x`-constant term. -/
theorem xCoeff0_phi_unit (R : Polynomial F) (M : ℕ) :
    xCoeff0 (phi (PowerSeries.weierstrassUnit (Phi R M) (phi_residue_ne_zero R M)))
      = GMC2.DvdKMultiplicativeClosing.unitCoeff0 R M := by
  have hmap : phi (PowerSeries.weierstrassUnit (Phi R M) (phi_residue_ne_zero R M))
      = PowerSeries.map (HahnSeries.ofPowerSeries ℤ F)
          (tau (PowerSeries.weierstrassUnit (Phi R M) (phi_residue_ne_zero R M))) := rfl
  rw [hmap, GMC2.DvdKFrameHSide.xCoeff0_map_ofPowerSeries]
  ext a
  rw [coeff_map, ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_coeff_tau,
    GMC2.DvdKMultiplicativeClosing.unitCoeff0, ← PowerSeries.coeff_zero_eq_constantCoeff]

/-- If a power series `g` vanishes in degrees `≥ M`, its Laurent image is supported below `M`. -/
theorem support_ofPowerSeries_subset {g : PowerSeries F} {M : ℕ}
    (hg : ∀ b : ℕ, M ≤ b → PowerSeries.coeff (R := F) b g = 0) :
    (HahnSeries.ofPowerSeries ℤ F g).support ⊆ Set.Iio (M : ℤ) := by
  intro z hz
  rw [HahnSeries.mem_support] at hz
  by_contra hznot
  simp only [Set.mem_Iio, not_lt] at hznot
  have hz0 : 0 ≤ z := le_trans (Int.natCast_nonneg M) hznot
  lift z to ℕ using hz0 with k
  rw [LaurentSeries.coeff_coe_powerSeries] at hz
  exact hz (hg k (by exact_mod_cast hznot))

/-- The `t⁰`-coefficient of `τ P` is `xᴹ` (`P ≡ xᴹ mod t`, the distinguished-polynomial property).
-/
theorem tau_smallRootFactor_coeff0 (R : Polynomial F) (M : ℕ) :
    PowerSeries.coeff (R := PowerSeries F) 0 (tau ((smallRootFactor R M : (PowerSeries F)⟦X⟧)))
      = PowerSeries.X ^ M := by
  ext b
  rw [coeff_coeff_tau, PowerSeries.coeff_zero_eq_constantCoeff, ← PowerSeries.coeff_map,
    GMC2.DvdKUnitOrigin.map_constantCoeff_smallRootFactor]

/-- `φP`'s constant-in-`t` term is `xᴹ = single M 1` — feeds the degree lemma's `h0`. -/
theorem coeff0_Pfr (R : Polynomial F) (M : ℕ) :
    PowerSeries.coeff (R := LaurentSeries F) 0 (phi (smallRootFactor R M : (PowerSeries F)⟦X⟧))
      = HahnSeries.single (M : ℤ) 1 := by
  rw [phi, RingHom.comp_apply, coeff_map,
    show tauHom (smallRootFactor R M : (PowerSeries F)⟦X⟧)
      = tau (smallRootFactor R M : (PowerSeries F)⟦X⟧) from rfl,
    tau_smallRootFactor_coeff0, HahnSeries.ofPowerSeries_X_pow]

/-- Every higher `t`-coefficient of `φP` has `x`-degree `< M` — feeds the degree lemma's `hlt`. -/
theorem coeff_Pfr_support (R : Polynomial F) (M : ℕ) (n : ℕ) (hn : 1 ≤ n) :
    (PowerSeries.coeff (R := LaurentSeries F) n
        (phi (smallRootFactor R M : (PowerSeries F)⟦X⟧))).support ⊆ Set.Iio (M : ℤ) := by
  rw [phi, RingHom.comp_apply,
    show tauHom (smallRootFactor R M : (PowerSeries F)⟦X⟧)
      = tau (smallRootFactor R M : (PowerSeries F)⟦X⟧) from rfl,
    coeff_map]
  apply support_ofPowerSeries_subset
  intro b hb
  rw [coeff_coeff_tau, Polynomial.coeff_coe]
  rcases eq_or_lt_of_le hb with heq | hlt
  · have hlc : (smallRootFactor R M).coeff M = 1 := by
      have hm := smallRootFactor_monic R M
      rw [Polynomial.Monic, Polynomial.leadingCoeff, smallRootFactor_natDegree R M] at hm
      exact hm
    rw [← heq, hlc, PowerSeries.coeff_one, if_neg (by omega)]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [smallRootFactor_natDegree R M]; omega),
      map_zero]

theorem isUnit_Pfr (R : Polynomial F) (M : ℕ) :
    IsUnit (phi (smallRootFactor R M : (PowerSeries F)⟦X⟧)) := by
  rw [isUnit_iff_constantCoeff_ne_zero, ← PowerSeries.coeff_zero_eq_constantCoeff, coeff0_Pfr]
  exact HahnSeries.single_ne_zero one_ne_zero

theorem isUnit_xCoeff0_phi_unit (R : Polynomial F) (M : ℕ) :
    IsUnit (xCoeff0 (phi (PowerSeries.weierstrassUnit (Phi R M) (phi_residue_ne_zero R M)))) := by
  rw [xCoeff0_phi_unit, PowerSeries.isUnit_iff_constantCoeff,
    GMC2.DvdKUnitOrigin.unitCoeff0_constantCoeff_eq_one]
  exact isUnit_one

/-- **`hderiv`, delivered from the transpose glue.** Under the DvdK vanishing of every central power
coefficient `(Rᵐ).coeff(M·m)` (`m ≥ 1`), the `t`-derivative of `h(0,t) = unitCoeff0 R M` vanishes.
This wires the concrete glue of this module into kps's `hderiv_of_transpose_glue`. -/
theorem hderiv_final (R : Polynomial F) (M : ℕ)
    (hvanish : ∀ m : ℕ, 1 ≤ m → (R ^ m).coeff (M * m) = 0) :
    PowerSeries.derivative _ (GMC2.DvdKMultiplicativeClosing.unitCoeff0 R M) = 0 := by
  have H := PowerSeries.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (phi_residue_ne_zero R M)
  have hfact : PhiFrame (Rl R) M
      = phi (smallRootFactor R M : (PowerSeries F)⟦X⟧)
        * phi (PowerSeries.weierstrassUnit (Phi R M) (phi_residue_ne_zero R M)) := by
    rw [← map_mul,
      show (smallRootFactor R M : (PowerSeries F)⟦X⟧)
          * PowerSeries.weierstrassUnit (Phi R M) (phi_residue_ne_zero R M) = Phi R M
        from H.eq_mul.symm, phi_Phi]
  exact GMC2.DvdKHderivAssembly.hderiv_of_transpose_glue (Rl R) M
    (PowerSeries.weierstrassUnit (Phi R M) (phi_residue_ne_zero R M)) H.isUnit
    (phi (smallRootFactor R M : (PowerSeries F)⟦X⟧))
    hfact (isUnit_Pfr R M)
    (GMC2.DvdKFrameDegree.xCoeff0_logDeriv_eq_zero_of_monic _ (isUnit_Pfr R M) M
      (coeff0_Pfr R M) (coeff_Pfr_support R M))
    (isUnit_xCoeff0_phi_unit R M)
    (fun m hm => by rw [Rl_pow_coeff]; exact hvanish m hm)
    (GMC2.DvdKMultiplicativeClosing.unitCoeff0 R M)
    (xCoeff0_phi_unit R M)

/-- **The multiplicative crux, unconditional (given the vanishing).**  `hderiv_final` + the origin
normalization `hconst` close `smallRootFactor_coeff0_eq_of_derivative_vanishes`:
`P.coeff 0 = −t·r₀ = c·t` whenever every central power coefficient vanishes. -/
theorem smallRootFactor_coeff0_of_vanish [CharZero F] (R : Polynomial F) (M : ℕ) (hM : 1 ≤ M)
    (hvanish : ∀ m : ℕ, 1 ≤ m → (R ^ m).coeff (M * m) = 0) :
    (smallRootFactor R M).coeff 0
      = - PowerSeries.X * (algebraMap F (PowerSeries F)) (R.coeff 0) :=
  GMC2.DvdKMultiplicativeClosing.smallRootFactor_coeff0_eq_of_derivative_vanishes R M hM
    (GMC2.DvdKUnitOrigin.unitCoeff0_constantCoeff_eq_one R M)
    (hderiv_final R M hvanish)

end GMC2.DvdKTransposeAssembly

