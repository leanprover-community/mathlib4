/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.Normed
import Mathlib.Analysis.Convex.Complex
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Topology.Homotopy.Contractible

#align_import analysis.complex.upper_half_plane.topology from "leanprover-community/mathlib"@"57f9349f2fe19d2de7207e99b0341808d977cdcf"

/-!
# Topology on the upper half plane

In this file we introduce a `TopologicalSpace` structure on the upper half plane and provide
various instances.
-/


noncomputable section

open Set Filter Function TopologicalSpace Complex

open scoped Filter Topology UpperHalfPlane

namespace UpperHalfPlane

instance : TopologicalSpace ℍ :=
  instTopologicalSpaceSubtype

theorem openEmbedding_coe : OpenEmbedding ((↑) : ℍ → ℂ) :=
  IsOpen.openEmbedding_subtype_val <| isOpen_lt continuous_const Complex.continuous_im
#align upper_half_plane.open_embedding_coe UpperHalfPlane.openEmbedding_coe

theorem embedding_coe : Embedding ((↑) : ℍ → ℂ) :=
  embedding_subtype_val
#align upper_half_plane.embedding_coe UpperHalfPlane.embedding_coe

theorem continuous_coe : Continuous ((↑) : ℍ → ℂ) :=
  embedding_coe.continuous
#align upper_half_plane.continuous_coe UpperHalfPlane.continuous_coe

theorem continuous_re : Continuous re :=
  Complex.continuous_re.comp continuous_coe
#align upper_half_plane.continuous_re UpperHalfPlane.continuous_re

theorem continuous_im : Continuous im :=
  Complex.continuous_im.comp continuous_coe
#align upper_half_plane.continuous_im UpperHalfPlane.continuous_im

instance : SecondCountableTopology ℍ :=
  TopologicalSpace.Subtype.secondCountableTopology _

instance : T3Space ℍ := Subtype.t3Space

instance : T4Space ℍ := inferInstance

instance : ContractibleSpace ℍ :=
  (convex_halfspace_im_gt 0).contractibleSpace ⟨I, one_pos.trans_eq I_im.symm⟩

instance : LocPathConnectedSpace ℍ :=
  locPathConnected_of_isOpen <| isOpen_lt continuous_const Complex.continuous_im

instance : NoncompactSpace ℍ := by
  refine' ⟨fun h => _⟩
  have : IsCompact (Complex.im ⁻¹' Ioi 0) := isCompact_iff_isCompact_univ.2 h
  replace := this.isClosed.closure_eq
  rw [closure_preimage_im, closure_Ioi, Set.ext_iff] at this
  exact absurd ((this 0).1 (@left_mem_Ici ℝ _ 0)) (@lt_irrefl ℝ _ 0)

instance : LocallyCompactSpace ℍ :=
  openEmbedding_coe.locallyCompactSpace

end UpperHalfPlane
