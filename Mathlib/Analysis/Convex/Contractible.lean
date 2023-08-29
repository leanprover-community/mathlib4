/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Convex.Star
import Mathlib.Topology.Homotopy.Contractible

#align_import analysis.convex.contractible from "leanprover-community/mathlib"@"3339976e2bcae9f1c81e620836d1eb736e3c4700"

/-!
# A convex set is contractible

In this file we prove that a (star) convex set in a real topological vector space is a contractible
topological space.
-/


variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousSMul ℝ E] {s : Set E} {x : E}

/-- A non-empty star convex set is a contractible space. -/
protected theorem StarConvex.contractibleSpace (h : StarConvex ℝ x s) (hne : s.Nonempty) :
    ContractibleSpace s := by
  refine'
    (contractible_iff_id_nullhomotopic s).2
      ⟨⟨x, h.mem hne⟩,
        ⟨⟨⟨fun p => ⟨p.1.1 • x + (1 - p.1.1) • (p.2 : E), _⟩, _⟩, fun x => _, fun x => _⟩⟩⟩
  · exact h p.2.2 p.1.2.1 (sub_nonneg.2 p.1.2.2) (add_sub_cancel'_right _ _)
    -- 🎉 no goals
  · exact
      ((continuous_subtype_val.fst'.smul continuous_const).add
            ((continuous_const.sub continuous_subtype_val.fst').smul
              continuous_subtype_val.snd')).subtype_mk
        _
  · ext1
    -- ⊢ ↑(ContinuousMap.toFun (ContinuousMap.mk fun p => { val := ↑p.fst • x✝ + (1 - …
    simp
    -- 🎉 no goals
  · ext1
    -- ⊢ ↑(ContinuousMap.toFun (ContinuousMap.mk fun p => { val := ↑p.fst • x✝ + (1 - …
    simp
    -- 🎉 no goals
#align star_convex.contractible_space StarConvex.contractibleSpace

/-- A non-empty convex set is a contractible space. -/
protected theorem Convex.contractibleSpace (hs : Convex ℝ s) (hne : s.Nonempty) :
    ContractibleSpace s :=
  let ⟨_, hx⟩ := hne
  (hs.starConvex hx).contractibleSpace hne
#align convex.contractible_space Convex.contractibleSpace

instance (priority := 100) RealTopologicalVectorSpace.contractibleSpace : ContractibleSpace E :=
  (Homeomorph.Set.univ E).contractibleSpace_iff.mp <|
    convex_univ.contractibleSpace Set.univ_nonempty
#align real_topological_vector_space.contractible_space RealTopologicalVectorSpace.contractibleSpace
