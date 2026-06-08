/-
Copyright (c) 2026 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/

import Mathlib

/-!
# Principal G-Bundle Infrastructure

Whatever

## Main definition

* `SmoothRightGAction` — class for smooth right group actions on manifolds

-/

open scoped RightActions
open Set Bundle Manifold

noncomputable section

section SmoothRightGAction

variable
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG}
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM}

/-- A smooth right G-action on a manifold M. The action is given via `MulAction Gᵐᵒᵖ M`,
    and smoothness means the map `(m, g) ↦ m <• g` is smooth. -/
class SmoothRightGAction
    (n : WithTop ℕ∞)
    (IG : ModelWithCorners ℝ EG HG)
    (IM : ModelWithCorners ℝ EM HM)
    (G : Type*) [TopologicalSpace G] [ChartedSpace HG G] [Group G]
    (M : Type*) [TopologicalSpace M] [ChartedSpace HM M]
    [MulAction Gᵐᵒᵖ M] : Prop where
  /-- The right action map `(m, g) ↦ m <• g` is smooth. -/
  smooth_smul : ContMDiff (IM.prod IG) IM n
    (fun (pg : M × G) ↦ pg.1 <• pg.2)

end SmoothRightGAction

end
