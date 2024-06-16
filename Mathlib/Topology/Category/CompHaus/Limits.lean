/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.Topology.Category.CompHausLike.Limits

/-!

# Explicit limits and colimits

This file collects some constructions of explicit limits and colimits in `CompHaus`,
which may be useful due to their definitional properties.

So far, we have the following:
- Explicit pullbacks, defined in the "usual" way as a subset of the product.
- Explicit finite coproducts, defined as a disjoint union.

-/

namespace CompHaus

/-
Previously, this had accidentally been made a global instance,
and we now turn it on locally when convenient.
-/
attribute [local instance] CategoryTheory.ConcreteCategory.instFunLike

universe u w

open CategoryTheory Limits CompHausLike

instance : HasExplicitPullbacks (fun _ ↦ True) where
  hasExplicitPullbacks _ _ := inferInstance

instance : HasExplicitFiniteCoproducts (fun _ ↦ True) where
  hasProp _ := inferInstance

example : FinitaryExtensive CompHaus := inferInstance

/-- A one-element space is terminal in `CompHaus` -/
abbrev isTerminalPUnit : IsTerminal (CompHaus.of PUnit.{u + 1}) := CompHausLike.isTerminalPUnit

/-- The isomorphism from an arbitrary terminal object of `CompHaus` to a one-element space. -/
noncomputable def terminalIsoPUnit : ⊤_ CompHaus.{u} ≅ CompHaus.of PUnit :=
  terminalIsTerminal.uniqueUpToIso CompHaus.isTerminalPUnit

noncomputable example : PreservesFiniteCoproducts compHausToTop := inferInstance

end CompHaus
