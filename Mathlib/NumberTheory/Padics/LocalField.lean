/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.NumberTheory.Padics.ValuativeRel

/-!
# `ℚ_[p]` is a non-archimedean local field

This file records the instance `IsNonarchimedeanLocalField ℚ_[p]`.
-/

public section

variable {p : ℕ} [Fact p.Prime]

/-- The `p`-adic numbers form a non-archimedean local field: the topology comes from the valuative
relation, `ℚ_[p]` is locally compact, and the valuation is nontrivial. -/
instance : IsNonarchimedeanLocalField ℚ_[p] := ⟨⟩
