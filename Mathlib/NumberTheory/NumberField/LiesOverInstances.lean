/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Valuation

/-!
# `LiesOver` instances for completions of number fields

If `L` and `K` are number fields such that `Algebra K L` then this algebra extends
naturally to the completions of `K` and `L` at places, whenever the place of `L` lies
over the place of `K`. This file contains the relevant instances and properties of this extension
as `scoped` instances. These are scoped because they create non-defeq instance diamonds when
`K = L`.
-/

@[expose] public section

namespace NumberField.LiesOver

open IsDedekindDomain HeightOneSpectrum

open UniformSpace.Completion

variable (A K L B : Type*) [CommRing A] [CommRing B] [Field K] [Algebra A B] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A] [Algebra A L]
    [Algebra K L] [IsDedekindDomain B] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing B L] [Module.IsTorsionFree A B]
    (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

/-- If `w` lies over `v`, then `w.adicCompletion L` is a `v.adicCompletion K`-algebra. -/
noncomputable scoped instance : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  mapRingHom _ (uniformContinuous_algebraMap_liesOver K L v w).continuous |>.toAlgebra

scoped instance : ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) where
  continuous_smul := (continuous_map.comp continuous_fst).mul (continuous_id.comp continuous_snd)

scoped instance : IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) :=
  .of_algebraMap_eq fun x ↦ by simp [RingHom.algebraMap_toAlgebra, algebraMap_def,
    -UniformSpace.Completion.mapRingHom_apply, mapRingHom_coe, WithVal.algebraMap_left_apply,
    WithVal.algebraMap_right_apply]

end NumberField.LiesOver
