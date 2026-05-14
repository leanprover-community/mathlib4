/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# `LiesOver` instances for completions of number fields

If `L` and `K` are number fields such that `Algebra K L` then this algebra extends
naturally to the completions of `K` and `L` at places, whenever the place of `L` lies
over the place of `K`. This file contains the relevant instances and properties of this extension
as `scoped` instances. These are scoped because they create non-defeq instance diamonds when
`K = L`.
-/

public section

namespace NumberField.LiesOver

open UniformSpace.Completion InfinitePlace

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {v : InfinitePlace K} {w : InfinitePlace L}
variable [w.1.LiesOver v.1]

/-- If `w` lies over `v`, then `w.Completion` is a `v.Completion`-algebra. -/
noncomputable scoped instance : Algebra v.Completion w.Completion :=
  (LiesOver.isometry_algebraMap w v).mapRingHom.toAlgebra

scoped instance : IsScalarTower K v.Completion w.Completion :=
  .of_algebraMap_eq fun x ↦ by
    simp_rw [RingHom.algebraMap_toAlgebra, UniformSpace.Completion.algebraMap_def,
      Isometry.mapRingHom_coe]
    simp [WithAbs.algebraMap_left_apply, WithAbs.algebraMap_right_apply]

scoped instance : ContinuousSMul v.Completion w.Completion where
  continuous_smul := (UniformSpace.Completion.continuous_map.comp continuous_fst).mul
    (Continuous.comp continuous_id continuous_snd)

end NumberField.LiesOver
