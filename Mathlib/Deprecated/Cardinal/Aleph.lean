/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Deprecated.Cardinal.PartENat

/-!
# Deprecated material from Mathlib.SetTheory.Cardinal.Aleph

Moved here so we can reduce imports sooner.
-/

namespace Cardinal

@[simp, deprecated aleph_toENat (since := "2024-12-01")]
theorem aleph_toPartENat (o : Ordinal) : toPartENat (ℵ_ o) = ⊤ :=
  toPartENat_apply_of_aleph0_le <| aleph0_le_aleph o

end Cardinal
