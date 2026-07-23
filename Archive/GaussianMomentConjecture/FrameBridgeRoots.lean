/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.SplittingField.Construction

set_option linter.minImports true

/-!
# Root transport under the splitting-field embedding

The remaining `Ω`-side obligation of the frame bridge (`GMC2.FrameBridge.hS_of_splits`) constructs
the packet `S` as the roots of `Φ` (in the splitting field) that land on the Weierstrass
distinguished factor `P` after embedding into `Ω = AlgebraicClosure (LaurentSeries F)`. The
foundation for that construction is that the embedding `ψ` transports the full root multiset of `Φ`
verbatim: every root in `Ω` is the `ψ`-image of a unique splitting-field root. This holds because
`Φ` already splits in its splitting field, so `Splits.roots_map` applies.
-/

open Polynomial

namespace GMC2.FrameBridgeRoots

variable {F : Type*} [Field F]

/-- **Root transport.** For any `RatFunc F`-algebra embedding `ψ` of the splitting field of `Φ` into
a field `Ω`, the multiset of roots of `Φ` in `Ω` is the `ψ`-image of the multiset of roots in the
splitting field. (Since `Φ` splits in `SplittingField`, `Splits.roots_map` moves its roots along
`ψ`, and `ψ ∘ algebraMap = algebraMap` identifies the mapped polynomial with `Φ` over `Ω`.) -/
theorem aroots_map_embedding (Φ : (RatFunc F)[X])
    {Ω : Type*} [Field Ω] [Algebra (RatFunc F) Ω]
    (ψ : Φ.SplittingField →ₐ[RatFunc F] Ω) :
    (Φ.aroots Φ.SplittingField).map ψ = Φ.aroots Ω := by
  have hsplit : (Φ.map (algebraMap (RatFunc F) Φ.SplittingField)).Splits :=
    Polynomial.IsSplittingField.splits Φ.SplittingField Φ
  rw [Polynomial.aroots_def, Polynomial.aroots_def, ← ψ.comp_algebraMap, ← Polynomial.map_map,
    hsplit.roots_map]
  rfl

end GMC2.FrameBridgeRoots

