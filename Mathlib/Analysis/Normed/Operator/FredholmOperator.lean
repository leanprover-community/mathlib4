/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
--import Mathlib

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

/-- The identity map is Fredholm, with Fredholm index 0. -/
lemma id : IsFredholm 𝕜 (X := X) (Y := X) (ContinuousLinearEquiv.refl 𝕜 X) :=
  _root_.ContinuousLinearEquiv.isFredholm _

/-- An index zero Fredholm operator is injective iff it's surjective. -/
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

/-- A surjective or injective index zero Fredholm operator is a linear isomorphism. -/
-- Pf. By the preceding result, T is bijective.
-- T is a bijective linear operator, hence a linear isomorphism.
-- The inverse $T^{-1}$ is bounded by the open mapping theorem --- since domain and codomain are Banach spaces.
noncomputable def ContinuousLinearEquiv.foo [CompleteSpace X] [CompleteSpace Y] {T : X ≃L[𝕜] Y}
    (hT : IsFredholm 𝕜 (X := X) (Y := Y) T)
    (h_ind : index 𝕜 X Y T = 0)
    (hsurj: Function.Surjective T) : X ≃L[𝕜] Y where
  -- XXX: ContinuousLinearEquiv.ofBijective T doesn't apply...
  toLinearEquiv := LinearEquiv.ofBijective T.toLinearEquiv
    ⟨(hT.index_zero_injective_iff_surjective h_ind).mpr hsurj, hsurj⟩
  continuous_toFun := by simpa using T.continuous
  continuous_invFun := sorry -- this requires the Banach open mapping theorem,
    -- i.e. some completeness! simpa using T.symm.continuous

-- A Fredholm operator has closed image.
-- (Chris' notes, Lemma 3.6 plus Exercise 3.7. might exist in mathlib already.)

-- Any linear operator V\to W between finite-dimensional spaces
-- is Fredholm with index dim(V)-dim(W).



end IsFredholm
