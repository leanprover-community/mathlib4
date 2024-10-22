/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.IsTorsionFree.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Prod

/-!
# Instances about `IsMulTorsionFree`

Prove that (indexed) product of torsion free monoids is torsion free.
-/

@[to_additive]
instance Prod.instIsMulTorsionFree {M N : Type*} [Monoid M] [Monoid N] [IsMulTorsionFree M]
    [IsMulTorsionFree N] : IsMulTorsionFree (M × N) where
  eq_one_of_pow_eq_one _x _n hxn hn :=
    Prod.ext (eq_one_of_pow_eq_one (congrArg Prod.fst hxn) hn)
      (eq_one_of_pow_eq_one (congrArg Prod.snd hxn) hn)

@[to_additive]
instance Pi.instIsMulTorsionFree {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)]
    [∀ i, IsMulTorsionFree (M i)] : IsMulTorsionFree (∀ i, M i) where
  eq_one_of_pow_eq_one _x _n hxn hn := funext fun i ↦ eq_one_of_pow_eq_one (congrFun hxn i) hn

@[to_additive]
theorem Function.Injective.isMulTorsionFree {M N : Type*} [Monoid M] [Monoid N]
    [IsMulTorsionFree N] (f : M →* N) (hf : Function.Injective f) : IsMulTorsionFree M where
  eq_one_of_pow_eq_one _x _n hxn hn := hf <| by simpa [hn] using congrArg f hxn

@[to_additive]
instance Units.instIsMulTorsionFree {M : Type*} [Monoid M] [IsMulTorsionFree M] :
    IsMulTorsionFree Mˣ :=
  Units.ext.isMulTorsionFree (Units.coeHom M)
