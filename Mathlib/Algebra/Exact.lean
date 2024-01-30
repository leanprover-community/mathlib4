/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.LinearAlgebra.Basic


/-! # Exactness of a pair

* For two maps `f : M → N` and `g : N → P`, with `Zero P`,
`Function.AddExact f g` says that `Set.range f = Set.preimage {0}

* For two maps `f : M → N` and `g : N → P`, with `One P`,
`Function.Exact f g` says that `Set.range f = Set.preimage {1}

* For linear maps `f : M →ₗ[R] N`  and `g : N →ₗ[R] P`,
`Exact f g` says that `range f = ker g``

## TODO :

* add the cases of `AddMonoidHom`

* add the multiplicative case (`Function.Exact` will become `Function.AddExact`?)
-/


namespace Function

variable {M N P : Type*}

section Function

variable (f : M → N) (g : N → P)

/-- The maps `f` and `g` form an exact pair :
  `g y = 0` iff `y` belongs to the image of `f` -/
def Exact [Zero P] : Prop := ∀ y, g y = 0 ↔ y ∈ Set.range f

lemma Exact.comp_eq_zero [Zero P] (h : Exact f g) : g.comp f = 0 :=
  funext fun _ => (h _).mpr <| Set.mem_range_self _

end Function

section LinearMap

open LinearMap

variable {R : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
  [Module R M] [Module R N] [Module R P]

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

lemma Exact.linearMap_ker_eq (hfg : Exact f g) : ker g = range f :=
  SetLike.ext hfg

lemma LinearMap.exact_iff : Exact f g ↔ LinearMap.ker g = LinearMap.range f :=
  Iff.symm <| SetLike.ext_iff

lemma Exact.linearMap_comp_eq_zero (h : Exact f g) : g.comp f = 0 :=
  DFunLike.coe_injective h.comp_eq_zero

end LinearMap

end Function
