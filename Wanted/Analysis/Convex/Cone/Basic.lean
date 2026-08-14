/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Cone.Basic

variable {𝕜 E : Type*} [AddCommGroup E] [TopologicalSpace E]

namespace ConvexCone
variable [Semifield 𝕜] [LinearOrder 𝕜] [Module 𝕜 E] {s : Set E}

-- TODO: This result generalises to `G`-submodules in the sense of the Zulip thread linked below.

variable [IsStrictOrderedRing 𝕜] [IsTopologicalAddGroup E] in
/-- This is true essentially by `Submodule.span_eq_iUnion_nat`, except that `Submodule` currently
doesn't support that use case. See
https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/G-submodules/with/514426583 -/
proof_wanted isOpen_hull (hs : IsOpen s) : IsOpen (hull 𝕜 s : Set E)

end ConvexCone
