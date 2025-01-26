/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Fredholm operators

TODO: create a doc-string here, once time comes

## TODO
- generalise to e.g. TVS: proving things about them will require e.g. a version
of the Hahn-Banach theorem for TVS, which does not exist yet

-/

-- Let 𝕜 be a field, and X, Y and Z be normed spaces over 𝕜.
variable {𝕜: Type*} [NormedField 𝕜]
  {X Y Z: Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  {S T : X →L[𝕜] Y}

open FiniteDimensional

variable (𝕜) in
/-- A bounded linear operator `T: X → Y` is Fredholm iff its kernel and cokernel
are finite-dimensional (and it has closed range?). -/
def IsFredholm (T : X →L[𝕜] Y) : Prop :=
  FiniteDimensional 𝕜 (LinearMap.ker T) ∧ FiniteDimensional 𝕜 (Y ⧸ LinearMap.range T)

variable (𝕜 X Y) in
/-- The **Fredholm index** of a bounded linear operator is `dim ker T - dim coker T`. -/
noncomputable def index (T : X →L[𝕜] Y) : ℤ :=
(Module.finrank 𝕜 (LinearMap.ker T) : ℤ) - (Module.finrank 𝕜 (Y ⧸ LinearMap.range T) : ℤ)


-- TODO: in the future
/-- If X and Y are complete, closedness of `range T` is automatic for Fredholm operators. -/
theorem IsFredholm.closedRange_of_completeSpace [CompleteSpace X] [CompleteSpace Y]
    (hT : IsFredholm 𝕜 T) : IsClosed (LinearMap.range T: Set Y) := sorry

namespace IsFredholm

/-- A continuous linear equivalence is Fredholm, with Fredholm index 0. -/
lemma _root_.ContinuousLinearEquiv.isFredholm (T : X ≃L[𝕜] Y) :
    IsFredholm 𝕜 (X := X) (Y := Y) T := by
  -- TODO: why are these erw's needed?
  constructor
  · erw [LinearEquiv.ker T.toLinearEquiv]
    exact Module.Finite.bot 𝕜 X
  · erw [LinearEquiv.range T.toLinearEquiv]
    exact Module.Finite.of_finite

lemma _root_.ContinuousLinearEquiv.index_eq (T : X ≃L[𝕜] Y) : index 𝕜 X Y T = 0 := by
  simp only [index]
  -- TODO: remove these!
  erw [LinearEquiv.ker T.toLinearEquiv, LinearEquiv.range T.toLinearEquiv]
  rw [finrank_bot, Module.finrank_zero_of_subsingleton, Int.sub_eq_zero]

/-- The identity map is Fredholm. -/
lemma refl : IsFredholm 𝕜 (X := X) (Y := X) (ContinuousLinearEquiv.refl 𝕜 X) :=
  _root_.ContinuousLinearEquiv.isFredholm _

/-- The identity map has Fredholm index zero. -/
lemma index_refl : index 𝕜 X X (ContinuousLinearEquiv.refl 𝕜 X) = 0 :=
  _root_.ContinuousLinearEquiv.index_eq _

/-- An index zero Fredholm operator is injective iff it is surjective. -/
lemma index_zero_injective_iff_surjective {T : X ≃L[𝕜] Y}
    (hT : IsFredholm 𝕜 (X := X) (Y := Y) T) (h_ind : index 𝕜 X Y T = 0) :
    Function.Injective T ↔ Function.Surjective T := by
  rw [index, Int.sub_eq_zero] at h_ind
  rw [← LinearMapClass.ker_eq_bot, ← LinearMap.range_eq_top]
  constructor
  · intro h
    erw [h] at h_ind
    rw [finrank_bot] at h_ind
    -- norm_cast at h_ind
    -- replace h_ind := h_ind.symm
    have : Subsingleton (Y ⧸ LinearMap.range ↑T) := by sorry
    rw [Submodule.subsingleton_quotient_iff_eq_top] at this
    exact this
  · intro h
    erw [h] at h_ind
    have : Module.finrank 𝕜 ↥(LinearMap.ker ↑T) = 0 := by
      clear h
      -- have : Module.finrank 𝕜 (Y ⧸ ⊤) = 0 := sorry
      sorry -- follows from prev
    rw [← Submodule.rank_eq_zero]
    have : Module.Finite 𝕜 ↥(LinearMap.ker T) := sorry
    rw [← Module.finrank_eq_rank]
    norm_cast

/-- A surjective or injective index zero Fredholm operator between Banach spaces
is a linear isomorphism. -/
noncomputable def ContinuousLinearEquiv.of_index_zero_of_surjective_of_isFredholm_of_completeSpace
    [CompleteSpace X] [CompleteSpace Y] {T : X ≃L[𝕜] Y}
    (hT : IsFredholm 𝕜 (X := X) (Y := Y) T)
    (h_ind : index 𝕜 X Y T = 0)
    (hsurj: Function.Surjective T) : X ≃L[𝕜] Y where
  -- T is bijective by the preceding result, hence a linear isomorphism.
  -- XXX: ContinuousLinearEquiv.ofBijective T doesn't apply...
  toLinearEquiv := LinearEquiv.ofBijective T.toLinearEquiv
    ⟨(hT.index_zero_injective_iff_surjective h_ind).mpr hsurj, hsurj⟩
  continuous_toFun := by simpa using T.continuous
  -- -- The inverse $T^{-1}$ is bounded by the open mapping theorem,
  -- since domain and codomain are Banach spaces.
  continuous_invFun := sorry -- this requires the Banach open mapping theorem,
    -- i.e. some completeness! simpa using T.symm.continuous

/-- An injective index zero Fredholm operator between Banach spaces
is a linear isomorphism. -/
noncomputable def ContinuousLinearEquiv.of_index_zero_of_injective_of_isFredholm_of_completeSpace
    [CompleteSpace X] [CompleteSpace Y] {T : X ≃L[𝕜] Y}
    (hT : IsFredholm 𝕜 (X := X) (Y := Y) T)
    (h_ind : index 𝕜 X Y T = 0)
    (hinj: Function.Injective T) : X ≃L[𝕜] Y :=
  ContinuousLinearEquiv.of_index_zero_of_surjective_of_isFredholm_of_completeSpace hT h_ind
    ((hT.index_zero_injective_iff_surjective h_ind).mp hinj)

-- A Fredholm operator between Banach spaces has closed image.
-- (Chris' notes, Lemma 3.6 plus Exercise 3.7. might exist in mathlib already.)

/-- A (continuous) linear map `T : X → Y` between finite-dimensional spaces
is Fredholm. -/
lemma of_continuousLinearEquiv_of_finiteDimensional
    [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y] {T : X ≃L[𝕜] Y} :
    IsFredholm 𝕜 (X := X) (Y := Y) T := by
  constructor
  · exact finiteDimensional_submodule _
  · sorry
    -- TODO: don't understand quotient sub-modules in Lean yet...
    -- apply finiteDimensional_submodule (Y ⧸ LinearMap.range T)
    --exact Module.Finite.quotient 𝕜 (LinearMap.range ↑T)

-- use the rank-nullity theorem
lemma index_of_finiteDimensional
    [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y] {T : X ≃L[𝕜] Y} :
    index 𝕜 X Y T = (Module.finrank 𝕜 X : ℤ) - (Module.finrank 𝕜 Y : ℤ) := by
  rw [index]
  rw [sub_eq_sub_iff_add_eq_add]
  norm_cast
  -- rank-nullity theorem: dimension of the quotient
  have : (Module.finrank 𝕜 Y) =
    Module.finrank 𝕜 (LinearMap.range T) + (Module.finrank 𝕜 (Y ⧸ LinearMap.range ↑T)) := by
    -- have : HasRankNullity 𝕜 := sorry
    -- rw [Submodule.finrank_quotient_add_finrank]
    sorry
  rw [this]
  -- can cancel on the rhs
  -- rank-nullity theorem: dimension of kernel and range
  set K := Module.finrank 𝕜 (LinearMap.ker ↑T)
  set R := Module.finrank 𝕜 (LinearMap.range ↑T)

  have := LinearMap.finrank_range_add_finrank_ker (f := T.toLinearMap)
  rw [← add_assoc]

  sorry
--apply finiteDimensional_submodule
-- Any linear operator V\to W between finite-dimensional spaces
-- is Fredholm with index dim(V)-dim(W).



end IsFredholm
