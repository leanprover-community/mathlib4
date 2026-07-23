/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.FrameBridgeDvd
import Archive.GaussianMomentConjecture.PhiVieta
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.LaurentSeries

/-!
# The Φ-coincidence connector: `PhiPoly` and `GMC2.PhiVieta.Phi` agree over `LaurentSeries F`

The bridge proves `smallRootFactor R M ∣ PhiPoly R M` in `(PowerSeries F)[X]`, where
`PhiPoly = Xᴹ − C(PowerSeries.X)·R.map` is the Weierstrass deformation over `F⟦t⟧`. But the frame
contradiction `GMC2.FrameBridgeAssembly.false_of_frame_data` consumes a divisor of
`GMC2.PhiVieta.Phi`, the Vieta deformation `Xᴹ − C(RatFunc.X)·R.map` over `F(t) = RatFunc F`. These
are **the same polynomial** once both coefficient rings are pushed into the shared Laurent frame
`LaurentSeries F`, because `ofPowerSeries` sends `PowerSeries.X ↦ single 1 1` and the coercion
`RatFunc F → LaurentSeries F` sends `RatFunc.X ↦ single 1 1` (`RatFunc.coe_X`): both become
`Xᴹ − C(single 1 1)·R.map`.

This is a *polynomial equality* — no valuation, no `x/t` transpose (that swap is only for the
analytic `hderiv` leg). The one subtlety: `algebraMap (RatFunc F) (LaurentSeries F)` is **not** a
synthesizable instance (it is baked into Mathlib's `coeToLaurentSeries` via a scalar tower local to
`RingTheory/LaurentSeries.lean`). We sidestep it entirely with `rfToL`, the coercion bundled as a
ring hom (its hom axioms are `push_cast`), so `Polynomial.map rfToL` needs no
`Algebra (RatFunc F) _` instance.

Mapping `(PowerSeries F)[X]` divisibility along `ofPowerSeries` and rewriting the target by this
coincidence yields `smallRootFactor.map ∣ GMC2.PhiVieta.Phi.map rfToL` over `LaurentSeries F`, which
the final assembly then transports `LaurentSeries F → Ω`.
-/

open Polynomial

namespace GMC2.DvdKPhiCoincide

variable {F : Type*} [Field F]

/-- The `RatFunc F → LaurentSeries F` coercion bundled as a ring hom.  Avoids the non-synthesizable
`Algebra (RatFunc F) (LaurentSeries F)` instance: the coe respects `+,*,0,1` by `push_cast`. -/
noncomputable def rfToL : RatFunc F →+* LaurentSeries F where
  toFun x := (x : LaurentSeries F)
  map_one' := by push_cast; ring
  map_mul' a b := by push_cast; ring
  map_zero' := by push_cast; ring
  map_add' a b := by push_cast; ring

@[simp] theorem rfToL_apply (x : RatFunc F) : rfToL x = (x : LaurentSeries F) := rfl

/-- `rfToL` sends the Vieta variable `RatFunc.X` to the frame variable `single 1 1`. -/
theorem rfToL_X : rfToL (RatFunc.X : RatFunc F) = HahnSeries.single (1 : ℤ) 1 := by
  rw [rfToL_apply, RatFunc.coe_X]

/-- Both coefficient inclusions `F → LaurentSeries F` — through `F⟦t⟧` (`ofPowerSeries ∘ C`) and
through `F(t)` (`rfToL ∘ algebraMap F (RatFunc F)`) — are the canonical
`algebraMap F (LaurentSeries F)`. -/
theorem ofPowerSeries_comp_C :
    (HahnSeries.ofPowerSeries ℤ F).comp (algebraMap F (PowerSeries F))
      = algebraMap F (LaurentSeries F) := by
  refine RingHom.ext fun a => ?_
  rw [RingHom.comp_apply, show (algebraMap F (PowerSeries F)) a = PowerSeries.C a from rfl,
    HahnSeries.ofPowerSeries_C, ← LaurentSeries.algebraMap_apply]

theorem rfToL_comp_algebraMap :
    (rfToL (F := F)).comp (algebraMap F (RatFunc F)) = algebraMap F (LaurentSeries F) := by
  refine RingHom.ext fun a => ?_
  rw [RingHom.comp_apply, rfToL_apply, LaurentSeries.algebraMap_apply,
    show (algebraMap F (RatFunc F) a : RatFunc F)
        = ((Polynomial.C a : Polynomial F) : RatFunc F) by
      rw [IsScalarTower.algebraMap_apply F (Polynomial F) (RatFunc F)]; rfl,
    ← RatFunc.coe_coe, Polynomial.coe_C, PowerSeries.coe_C]

/-- **The Φ-coincidence.** `PhiPoly` (over `F⟦t⟧`) and `GMC2.PhiVieta.Phi` (over `F(t)`) map to the
*same* polynomial `Xᴹ − C(single 1 1)·R.map` over `LaurentSeries F`. -/
theorem phiPoly_map_eq_phiVieta_map (R : Polynomial F) (M : ℕ) :
    (GMC2.FrameBridgeDvd.PhiPoly R M).map (HahnSeries.ofPowerSeries ℤ F)
      = (GMC2.PhiVieta.Phi R M).map (rfToL (F := F)) := by
  rw [GMC2.FrameBridgeDvd.PhiPoly, GMC2.PhiVieta.Phi, Polynomial.map_sub, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_X,
    Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
    Polynomial.map_map, Polynomial.map_map, ofPowerSeries_comp_C, rfToL_comp_algebraMap,
    HahnSeries.ofPowerSeries_X, rfToL_X]

/-- **The mapped divisibility.** Pushing `(PowerSeries F)[X]` divisibility along `ofPowerSeries` and
rewriting the target by the coincidence: the Weierstrass factor divides the *Vieta* `Φ` over
`LaurentSeries F`. This is the divisor `Pω` (pre-`Ω`-lift) that `false_of_frame_data` consumes. -/
theorem smallRootFactor_map_dvd_phiVieta_map (R : Polynomial F) (M : ℕ) :
    (GMC2.DvdKWeierstrass.smallRootFactor R M).map (HahnSeries.ofPowerSeries ℤ F)
      ∣ (GMC2.PhiVieta.Phi R M).map (rfToL (F := F)) := by
  rw [← phiPoly_map_eq_phiVieta_map]
  obtain ⟨c, hc⟩ := GMC2.FrameBridgeDvd.smallRootFactor_dvd_PhiPoly R M
  exact ⟨c.map (HahnSeries.ofPowerSeries ℤ F), by rw [← Polynomial.map_mul, ← hc]⟩

end GMC2.DvdKPhiCoincide

