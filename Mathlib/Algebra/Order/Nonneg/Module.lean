/-
Copyright (c) 2023 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
import Mathlib.Algebra.Order.Nonneg.Ring
import Mathlib.Algebra.Module.Basic


/-!
# Modules over nonnegative elements

This file defines instances and prove some properties about modules over nonnegative elements
`{c : 𝕜 // 0 ≤ c}` of an arbitrary `OrderedSemiring 𝕜`.

These instances are useful for working with `ConvexCone`.

-/

variable {𝕜 E : Type*}

variable [OrderedSemiring 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]


namespace Nonneg

-- TODO: remove `prettyPrint := false` once #6833 is merged
local notation3 (prettyPrint := false) "𝕜≥0" => { c : 𝕜 // 0 ≤ c }

/-- A module over and ordered Semiring is also a module over just the non-negative scalars. -/
instance instModule : Module 𝕜≥0 E :=
  Module.compHom E (@Nonneg.coeRingHom 𝕜 _)

@[simp, norm_cast]
lemma coe_smul (a : 𝕜≥0) (x : E) : (a : 𝕜) • x = a • x :=
  rfl

@[simp]
lemma mk_smul (a) (ha) (x : E) : (⟨a, ha⟩ : 𝕜≥0) • x = a • x :=
  rfl

instance instIsScalarTower : IsScalarTower 𝕜≥0 𝕜 E :=
  SMul.comp.isScalarTower ↑Nonneg.coeRingHom

end Nonneg
