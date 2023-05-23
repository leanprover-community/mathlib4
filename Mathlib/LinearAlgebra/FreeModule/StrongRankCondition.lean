/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca

! This file was ported from Lean 3 source module linear_algebra.free_module.strong_rank_condition
! leanprover-community/mathlib commit f37e88f3ec14ee5eab18a9330ace717740e9c92c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Charpoly.Basic
import Mathbin.LinearAlgebra.InvariantBasisNumber

/-!

# Strong rank condition for commutative rings

We prove that any nontrivial commutative ring satisfies `strong_rank_condition`, meaning that
if there is an injective linear map `(fin n → R) →ₗ[R] fin m → R`, then `n ≤ m`. This implies that
any commutative ring satisfies `invariant_basis_number`: the rank of a finitely generated free
module is well defined.

## Main result

* `comm_ring_strong_rank_condition R` : `R` has the `strong_rank_condition`.

## References

We follow the proof given in https://mathoverflow.net/a/47846/7845.
The argument is the following: it is enough to prove that for all `n`, there is no injective linear
map `(fin (n + 1) → R) →ₗ[R] fin n → R`. Given such an `f`, we get by extension an injective
linear map `g : (fin (n + 1) → R) →ₗ[R] fin (n + 1) → R`. Injectivity implies that `P`, the
minimal polynomial of `g`, has non-zero constant term `a₀ ≠ 0`. But evaluating `0 = P(g)` at the
vector `(0,...,0,1)` gives `a₀`, contradiction.

-/


variable (R : Type _) [CommRing R] [Nontrivial R]

open Polynomial Function Fin LinearMap

/-- Any commutative ring satisfies the `strong_rank_condition`. -/
instance (priority := 100) commRing_strongRankCondition : StrongRankCondition R :=
  by
  suffices ∀ n, ∀ f : (Fin (n + 1) → R) →ₗ[R] Fin n → R, ¬injective f by
    rwa [strongRankCondition_iff_succ R]
  intro n f
  by_contra hf
  -- Lean is unable to find these instances without help, either via this `letI`, or via duplicate
  -- instances with unecessarily strong typeclasses on `R` and `M`.
  letI : Module.Finite R (Fin n.succ → R) := Module.Finite.pi
  letI : Module.Free R (Fin n.succ → R) := Module.Free.pi _ _
  let g : (Fin (n + 1) → R) →ₗ[R] Fin (n + 1) → R := (extend_by_zero.linear_map R cast_succ).comp f
  have hg : injective g := (extend_injective (RelEmbedding.injective cast_succ) 0).comp hf
  have hnex : ¬∃ i : Fin n, cast_succ i = last n := fun ⟨i, hi⟩ => ne_of_lt (cast_succ_lt_last i) hi
  let a₀ := (minpoly R g).coeff 0
  have : a₀ ≠ 0 := minpoly_coeff_zero_of_injective hg
  have : a₀ = 0 :=
    by
    -- Evaluate `(minpoly R g) g` at the vector `(0,...,0,1)`
    have heval := LinearMap.congr_fun (minpoly.aeval R g) (Pi.single (Fin.last n) 1)
    obtain ⟨P, hP⟩ := X_dvd_iff.2 (erase_same (minpoly R g) 0)
    rw [← monomial_add_erase (minpoly R g) 0, hP] at heval
    replace heval := congr_fun heval (Fin.last n)
    simpa [hnex] using heval
  contradiction
#align comm_ring_strong_rank_condition commRing_strongRankCondition

