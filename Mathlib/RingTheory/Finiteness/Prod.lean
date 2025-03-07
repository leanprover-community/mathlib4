/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.LinearAlgebra.Prod
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Finitely generated product (sub)modules

-/

open Function (Surjective)
open Finsupp

namespace Submodule

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

open Set

variable {P : Type*} [AddCommMonoid P] [Module R P]

theorem FG.prod {sb : Submodule R M} {sc : Submodule R P} (hsb : sb.FG) (hsc : sc.FG) :
    (sb.prod sc).FG :=
  let ⟨tb, htb⟩ := fg_def.1 hsb
  let ⟨tc, htc⟩ := fg_def.1 hsc
  fg_def.2
    ⟨LinearMap.inl R M P '' tb ∪ LinearMap.inr R M P '' tc, (htb.1.image _).union (htc.1.image _),
      by rw [LinearMap.span_inl_union_inr, htb.2, htc.2]⟩

end Submodule

namespace Module

namespace Finite

variable {R M N : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

instance prod [hM : Module.Finite R M] [hN : Module.Finite R N] : Module.Finite R (M × N) :=
  ⟨by
    rw [← Submodule.prod_top]
    exact hM.1.prod hN.1⟩

end Finite

end Module
