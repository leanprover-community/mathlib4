/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Mathlib.RingTheory.PowerSeries.LogDeriv
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Substitution

set_option linter.minImports true

/-!
# The unified `(LaurentSeries F)⟦t⟧` frame for the DvdK log-derivative identity (`hderiv`)

The last open lemma of the whole GMC(2) formalization is `hderiv`: `d_t(h(0,t)) = 0` under the DvdK
vanishing `D_m = 0`, where `h` is the Weierstrass unit of `Φ = xᴹ − t·R` over `F⟦t⟧`. flagged the
obstacle as *"taking `[x⁰]` consistently across two completions"* — `h(0,t)` is `x`-adic
(`h ∈ F⟦t⟧⟦x⟧`), while the generating function `F(t) = [x⁰](xᴹ/Φ)` is `t`-adic.

**This module supplies the resolution: work in the single ring `PowerSeries (LaurentSeries F)`
(`= (F⸨x⸩)⟦t⟧`).**  Because `LaurentSeries F = F⸨x⸩` is a **field** (`IsFractionRing F⟦x⟧ F⸨x⸩`), a
`t`-power-series is a unit as soon as its constant-in-`t` coefficient is nonzero.  So `Φ` (const-`t`
coeff `xᴹ ≠ 0`), the distinguished factor `P` (const-`t` coeff `xᴹ`), and the unit `h` (const-`t`
coeff `1`) are **all units in one ring** — no fraction field, honest division, and `h ∈ F⟦t⟧⟦x⟧`
embeds here (its `x`-support is bounded below).  The two completions collapse to one.

The `[x⁰]` extraction is then the `F⟦t⟧`-additive map `xCoeff0 : (F⸨x⸩)⟦t⟧ →+ F⟦t⟧` reading the `x⁰`
Hahn-coefficient of each `t`-coefficient. In this frame the `hderiv` identity is
`xCoeff0 (−R/Φ) = xCoeff0 (P_t/P) + xCoeff0 (h_t/h)`, with `xCoeff0 (P_t/P) = 0` (P monic of
`x`-degree `M`, `P_t` of `x`-degree `< M`) and `xCoeff0 (h_t/h) = d_t(h(0,t))/h(0,t)`.
-/

open PowerSeries

namespace GMC2.DvdKFrame

variable {F : Type*} [Field F]

/-- **A `t`-power-series over the field `F⸨x⸩` is a unit iff its constant-in-`t` term is nonzero.**
This is the whole point of the frame: in a field, "nonzero constant term" is all it takes. -/
theorem isUnit_iff_constantCoeff_ne_zero (φ : PowerSeries (LaurentSeries F)) :
    IsUnit φ ↔ PowerSeries.constantCoeff (R := LaurentSeries F) φ ≠ 0 := by
  rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]

/-- `Φ = xᴹ − t·R` in the frame (`t = PowerSeries.X`, inner `x` the Laurent-series variable
`single 1 1`, `R` a Laurent series embedded constant-in-`t`). -/
noncomputable def PhiFrame (Rl : LaurentSeries F) (M : ℕ) : PowerSeries (LaurentSeries F) :=
  PowerSeries.C ((HahnSeries.single (1 : ℤ) (1 : F)) ^ M) - PowerSeries.X * PowerSeries.C Rl

theorem constantCoeff_PhiFrame (Rl : LaurentSeries F) (M : ℕ) :
    PowerSeries.constantCoeff (R := LaurentSeries F) (PhiFrame Rl M)
      = (HahnSeries.single (1 : ℤ) (1 : F)) ^ M := by
  simp [PhiFrame]

/-- **`Φ` is a unit in `(LaurentSeries F)⟦t⟧`.** (`xᴹ = single 1 1 ^ M ≠ 0` in the field `F⸨x⸩`.) -/
theorem isUnit_PhiFrame (Rl : LaurentSeries F) (M : ℕ) : IsUnit (PhiFrame Rl M) := by
  rw [isUnit_iff_constantCoeff_ne_zero, constantCoeff_PhiFrame]
  exact pow_ne_zero M (by simp)

/-- **The `[x⁰]` functional** `(F⸨x⸩)⟦t⟧ →+ F⟦t⟧`: read the `x⁰` Hahn-coefficient of each
`t`-coefficient.  It is additive (`x⁰`-coefficient is `F`-linear on `F⸨x⸩`), the operator that turns
the frame identity into a `t`-series identity. -/
noncomputable def xCoeff0 : PowerSeries (LaurentSeries F) →+ PowerSeries F where
  toFun φ := PowerSeries.mk fun k => (PowerSeries.coeff (R := LaurentSeries F) k φ).coeff 0
  map_zero' := by ext k; simp
  map_add' a b := by
    ext k
    simp only [PowerSeries.coeff_mk, map_add, HahnSeries.coeff_add]

@[simp] theorem coeff_xCoeff0 (φ : PowerSeries (LaurentSeries F)) (k : ℕ) :
    PowerSeries.coeff (R := F) k (xCoeff0 φ)
      = (PowerSeries.coeff (R := LaurentSeries F) k φ).coeff 0 := by
  simp [xCoeff0, PowerSeries.coeff_mk]

/-- `xCoeff0` sends `1 ↦ 1`. -/
@[simp] theorem xCoeff0_one : xCoeff0 (1 : PowerSeries (LaurentSeries F)) = 1 := by
  ext k
  rw [coeff_xCoeff0]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · rw [PowerSeries.coeff_one, if_neg (by omega), PowerSeries.coeff_one, if_neg (by omega)]
    simp

/-- `xCoeff0` intertwines multiplication by `t = PowerSeries.X` (the `t`-shift). -/
theorem xCoeff0_X_mul (φ : PowerSeries (LaurentSeries F)) :
    xCoeff0 (PowerSeries.X * φ) = PowerSeries.X * xCoeff0 φ := by
  ext k
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp [coeff_xCoeff0]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [coeff_xCoeff0, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul, coeff_xCoeff0]

/-- `xCoeff0` of a constant-in-`t` series `C a` is `C (a₀)`, the constant `x⁰`-coefficient. -/
@[simp] theorem xCoeff0_C (a : LaurentSeries F) :
    xCoeff0 (PowerSeries.C a) = PowerSeries.C (a.coeff 0) := by
  ext k
  rw [coeff_xCoeff0]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  · rw [PowerSeries.coeff_C, if_neg (by omega), PowerSeries.coeff_C, if_neg (by omega)]
    simp

/-- **(b): the `−R/Φ` side.**  Since `xᴹ = Φ + t·R`, dividing by the unit `Φ` gives
`xᴹ/Φ = 1 + t·(R/Φ)`, so `xCoeff0 (xᴹ/Φ) = 1 + t·xCoeff0 (R/Φ)` — the relation feeding the assembly
(with `F(t) := xCoeff0(xᴹ/Φ) = ∑ D_m tᵐ`, this reads `xCoeff0(R/Φ) = (F−1)/t`). -/
theorem xCoeff0_xM_div_PhiFrame (Rl : LaurentSeries F) (M : ℕ) :
    xCoeff0 (PowerSeries.C ((HahnSeries.single (1 : ℤ) (1 : F)) ^ M) * Ring.inverse (PhiFrame Rl M))
      = 1 + PowerSeries.X * xCoeff0 (PowerSeries.C Rl * Ring.inverse (PhiFrame Rl M)) := by
  have hΦ : IsUnit (PhiFrame Rl M) := isUnit_PhiFrame Rl M
  have hxM : PowerSeries.C ((HahnSeries.single (1 : ℤ) (1 : F)) ^ M)
      = PhiFrame Rl M + PowerSeries.X * PowerSeries.C Rl := by rw [PhiFrame]; ring
  have hkey : PowerSeries.C ((HahnSeries.single (1 : ℤ) (1 : F)) ^ M) * Ring.inverse (PhiFrame Rl M)
      = 1 + PowerSeries.X * (PowerSeries.C Rl * Ring.inverse (PhiFrame Rl M)) := by
    rw [hxM, add_mul, Ring.mul_inverse_cancel _ hΦ, mul_assoc]
  rw [hkey, map_add, xCoeff0_one, xCoeff0_X_mul]

/-! ## The logarithmic derivative

The one structural fact behind the `hderiv` identity is that `PowerSeries.logDeriv` is additive on
products of units: `Φ = P * h` gives `logDeriv Φ = logDeriv P + logDeriv h`, i.e.
`-R/Φ = P_t/P + h_t/h`. -/

/-- **The `hderiv` identity assembles for free in the frame.** For `Φ = φ·ψ` with `φ, ψ` units in
`(LaurentSeries F)⟦t⟧`, the `[x⁰]` of the log-derivative splits additively:
`[x⁰](logDeriv Φ) = [x⁰](logDeriv φ) + [x⁰](logDeriv ψ)` — immediate from `logDeriv_mul` (Stage 2)
plus additivity of `xCoeff0` (Stage 1). Instantiated at the Weierstrass `Φ = P·h`, the left side is
`[x⁰](−R/Φ) = −∑_{m≥1} D_m t^{m-1}` (the generating function) and the right side is
`[x⁰](P_t/P) + [x⁰](h_t/h) = 0 + d_t(h(0,t))/h(0,t)` — so under `D_m = 0`,
`d_t(h(0,t)) = 0 = hderiv`. The three remaining inputs are all frame-local: `[x⁰](logDeriv P) = 0`
(P monic of x-degree M), `[x⁰](−R/Φ) = −∑ D_m t^{m-1}` (geometric series), and the transpose
embedding `F⟦t⟧⟦x⟧ ↪ (F⸨x⸩)⟦t⟧` carrying the Weierstrass `P, h`. -/
theorem xCoeff0_logDeriv_mul {φ ψ : PowerSeries (LaurentSeries F)}
    (hφ : IsUnit φ) (hψ : IsUnit ψ) :
    xCoeff0 (logDeriv (φ * ψ)) = xCoeff0 (logDeriv φ) + xCoeff0 (logDeriv ψ) := by
  rw [logDeriv_mul hφ hψ, map_add]

end GMC2.DvdKFrame

