/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# The adele ring of `ℚ` is `ℝ × 𝔸_f`

`ℚ` has a single infinite place, and it is real, so the infinite adele ring
`InfiniteAdeleRing ℚ = ∏_{v | ∞} ℚ_v` is a one-factor product whose factor is `ℝ`. Hence
`AdeleRing ℤ ℚ = InfiniteAdeleRing ℚ × FiniteAdeleRing ℤ ℚ ≃ ℝ × FiniteAdeleRing ℤ ℚ`, as rings
and as topological spaces, and the equivalence sends the diagonal `q ↦ (q)_v` to `(q, (q)_p)`.

* `Rat.InfiniteAdeleRing.ringEquivReal`, `Rat.InfiniteAdeleRing.homeomorphReal`
* `Rat.InfiniteAdeleRing.ringEquivReal_algebraMap`
* `Rat.AdeleRing.ringEquivProd`, `Rat.AdeleRing.homeomorphProd`
* `Rat.AdeleRing.ringEquivProd_algebraMap`
-/

@[expose] public section

open NumberField IsDedekindDomain

namespace Rat.InfiniteAdeleRing

/-- The infinite adele ring of `ℚ` is `ℝ`: a one-factor product of completions, at the
unique infinite place, which is real. -/
noncomputable def ringEquivReal : InfiniteAdeleRing ℚ ≃+* ℝ :=
  (RingEquiv.piUnique (fun v : InfinitePlace ℚ => v.Completion)).trans
    (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)

/-- The identification `ℚ∞ ≃ ℝ` is a homeomorphism. -/
noncomputable def homeomorphReal : InfiniteAdeleRing ℚ ≃ₜ ℝ :=
  (Homeomorph.piUnique (fun v : InfinitePlace ℚ => v.Completion)).trans
    (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).toHomeomorph

theorem homeomorphReal_apply (x : InfiniteAdeleRing ℚ) : homeomorphReal x = ringEquivReal x :=
  rfl

/-- The diagonal embedding of `ℚ` into `ℚ∞` is the inclusion into `ℝ`. -/
theorem ringEquivReal_algebraMap (q : ℚ) :
    ringEquivReal (algebraMap ℚ (InfiniteAdeleRing ℚ) q) = (q : ℝ) :=
  eq_ratCast (ringEquivReal.toRingHom.comp (algebraMap ℚ (InfiniteAdeleRing ℚ))) q

end Rat.InfiniteAdeleRing

namespace Rat.AdeleRing

/-- `𝔸_ℚ ≃+* ℝ × 𝔸_ℚ^f`. -/
noncomputable def ringEquivProd : AdeleRing ℤ ℚ ≃+* ℝ × FiniteAdeleRing ℤ ℚ :=
  RingEquiv.prodCongr InfiniteAdeleRing.ringEquivReal (RingEquiv.refl _)

/-- `𝔸_ℚ ≃ₜ ℝ × 𝔸_ℚ^f`. -/
noncomputable def homeomorphProd : AdeleRing ℤ ℚ ≃ₜ ℝ × FiniteAdeleRing ℤ ℚ :=
  Homeomorph.prodCongr InfiniteAdeleRing.homeomorphReal (Homeomorph.refl _)

theorem homeomorphProd_apply (x : AdeleRing ℤ ℚ) : homeomorphProd x = ringEquivProd x := rfl

/-- The diagonal `ℚ → 𝔸_ℚ` is `q ↦ (q, (q)_p)` on `ℝ × 𝔸_ℚ^f`. -/
theorem ringEquivProd_algebraMap (q : ℚ) :
    ringEquivProd (algebraMap ℚ (AdeleRing ℤ ℚ) q) =
      ((q : ℝ), algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q) :=
  Prod.ext (InfiniteAdeleRing.ringEquivReal_algebraMap q) rfl

end Rat.AdeleRing
