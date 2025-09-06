/-
Copyright (c) 2025 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/

import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.AlexandrovDiscrete

/-!
# T1 Alexandrov-discrete topology is discrete
-/

open Filter

variable {X : Type*} [TopologicalSpace X]

@[simp]
lemma nhdsKer_eq_of_t1Space [T1Space X] (s : Set X) : nhdsKer s = s := by
  ext; simp [mem_nhdsKer_iff_specializes]

instance (priority := low) [AlexandrovDiscrete X] [T1Space X] : DiscreteTopology X := by
  simp [discreteTopology_iff_nhds, ← principal_nhdsKer_singleton]
