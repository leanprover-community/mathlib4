/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.CompHausLike.Cartesian
import Mathlib.Topology.Category.LightProfinite.Basic

/-!

# Cartesian monoidal structure on `LightProfinite`

This file defines the cartesian monoidal structure on `LightProfinite` given by the type-theoretic
product.
-/

universe u

open CategoryTheory Limits CompHausLike

namespace LightProfinite

noncomputable instance : CartesianMonoidalCategory LightProfinite.{u} :=
  cartesianMonoidalCategory

end LightProfinite
