/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.RingTheory.FiniteType
import Mathlib.LinearAlgebra.InvariantBasisNumber

#align_import linear_algebra.free_module.strong_rank_condition from "leanprover-community/mathlib"@"f37e88f3ec14ee5eab18a9330ace717740e9c92c"

/-!

# Strong rank condition for commutative rings

We prove that any nontrivial commutative ring satisfies `StrongRankCondition`, meaning that
if there is an injective linear map `(Fin n → R) →ₗ[R] Fin m → R`, then `n ≤ m`. This implies that
any commutative ring satisfies `InvariantBasisNumber`: the rank of a finitely generated free
module is well defined.

## Main result

* `commRing_strongRankCondition R` : `R` has the `StrongRankCondition`.

The `commRing_strongRankCondition` comes from `CommRing.orzechProperty`, proved in
`Mathlib/RingTheory/FiniteType.lean`, which states that any commutative ring satisfies
the `OrzechProperty`, that is, for any finitely generated
`R`-module `M`, any surjective homomorphism `f : N → M` from a submodule `N` of `M` to `M`
is injective.


## References

* [Orzech, Morris. *Onto endomorphisms are isomorphisms*][orzech1971]
* [Djoković, D. Ž. *Epimorphisms of modules which must be isomorphisms*][djokovic1973]
* [Ribenboim, Paulo. *Épimorphismes de modules qui sont nécessairement
  des isomorphismes*][ribenboim1971]

-/


variable (R : Type*) [CommRing R] [Nontrivial R]

/-- Any nontrivial commutative ring satisfies the `StrongRankCondition`. -/
instance (priority := 100) commRing_strongRankCondition : StrongRankCondition R :=
  inferInstance
#align comm_ring_strong_rank_condition commRing_strongRankCondition
