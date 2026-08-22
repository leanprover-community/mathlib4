/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import SOS.Core
public import Mathlib.Data.Real.Basic

/-!
# Real semantics for the SOS expression language

This file interprets the engine's typed polynomial syntax over the real numbers.
-/

@[expose] public section

namespace SOS.Poly

/-- Real-valued denotation of the typed AST under a `Fin n → ℝ` valuation. -/
def evalReal {n : Nat} (φ : Fin n → ℝ) : SOS.Poly n → ℝ
  | .const r   => (r : ℝ)
  | .var i     => φ i
  | .neg p     => -evalReal φ p
  | .add p q   => evalReal φ p + evalReal φ q
  | .sub p q   => evalReal φ p - evalReal φ q
  | .mul p q   => evalReal φ p * evalReal φ q
  | .pow p k   => evalReal φ p ^ k

end SOS.Poly
