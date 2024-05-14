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

* `commRing_orzechProperty R` : `R` has the `OrzechProperty`.
* `commRing_strongRankCondition R` : `R` has the `StrongRankCondition`.

## References

The original proof was adapt from <https://mathoverflow.net/a/47846/7845>.
The argument is the following: it is enough to prove that for all `n`, there is no injective linear
map `(Fin (n + 1) → R) →ₗ[R] Fin n → R`. Given such an `f`, we get by extension an injective
linear map `g : (Fin (n + 1) → R) →ₗ[R] Fin (n + 1) → R`. Injectivity implies that `P`, the
minimal polynomial of `g`, has non-zero constant term `a₀ ≠ 0`. But evaluating `0 = P(g)` at the
vector `(0,...,0,1)` gives `a₀`, contradiction.

The new proof dierctly proves that any commutative ring satisfies the `OrzechProperty`,
see `Module.Finite.injective_of_surjective_of_submodule` and
`Module.Finite.injective_of_surjective_of_injective`, which is a corollary of
Noetherian rings satisfy the `OrzechProperty`
(`IsNoetherianRing.orzechProperty`,
see also `IsNoetherian.injective_of_surjective_of_submodule` and
`IsNoetherian.injective_of_surjective_of_injective`)
and Hilbert basis theorem.

-/


variable (R : Type*) [CommRing R]

/-- Any commutative ring satisfies the `OrzechProperty`.
    See also `Module.Finite.injective_of_surjective_of_submodule` and
    `Module.Finite.injective_of_surjective_of_injective`. -/
instance (priority := 100) commRing_orzechProperty : OrzechProperty R where
  injective_of_surjective_of_submodule' {M} :=
    letI := Module.addCommMonoidToAddCommGroup R (M := M)
    Module.Finite.injective_of_surjective_of_submodule

variable [Nontrivial R]

/-- Any nontrivial commutative ring satisfies the `StrongRankCondition`. -/
instance (priority := 100) commRing_strongRankCondition : StrongRankCondition R :=
  inferInstance
#align comm_ring_strong_rank_condition commRing_strongRankCondition
