/-
Copyright (c) 2023 Antoine Chambert-Loir and María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández, Eric Wieser, Bhavik Mehta
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Antidiag.Prod

/-!
# Antidiagonal of functions as finsets

This file provides the finset of functions summing to a specific value on a finset. Such finsets
should be thought of as the "antidiagonals" in the space of functions.

## TODO

`Finset.finAntidiagonal` is strictly more general than `Finset.Nat.antidiagonalTuple`. Deduplicate.
-/

open Function

variable {ι μ μ' : Type*}

namespace Finset
section AddCommMonoid
variable [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {n : μ}

/-!
### `Fin d → μ`

In this section, we define the antidiagonals in `Fin d → μ` by recursion on `d`. Note that this is
computationally efficient, although probably not as efficient as `Finset.Nat.antidiagonalTuple`.
-/

/-- `finAntidiagonal d n` is the type of `d`-tuples with sum `n`.

TODO: deduplicate with the less general `Finset.Nat.antidiagonalTuple`. -/
def finAntidiagonal (d : ℕ) (n : μ) : Finset (Fin d → μ) :=
  aux d n
where
  /-- Auxiliary construction for `finAntidiagonal` that bundles a proof of lawfulness
  (`mem_finAntidiagonal`), as this is needed to invoke `disjiUnion`. Using `Finset.disjiUnion` makes
  this computationally much more efficient than using `Finset.biUnion`. -/
  aux (d : ℕ) (n : μ) : {s : Finset (Fin d → μ) // ∀ f, f ∈ s ↔ ∑ i, f i = n} :=
    match d with
    | 0 =>
      if h : n = 0 then
        ⟨{0}, by simp [h, Subsingleton.elim finZeroElim ![]]⟩
      else
        ⟨∅, by simp [Ne.symm h]⟩
    | d + 1 =>
      { val := (antidiagonal n).disjiUnion
          (fun ab => (aux d ab.2).1.map {
              toFun := Fin.cons (ab.1)
              inj' := Fin.cons_right_injective _ })
          (fun i _hi j _hj hij => Finset.disjoint_left.2 fun t hti htj => hij $ by
            simp_rw [Finset.mem_map, Embedding.coeFn_mk] at hti htj
            obtain ⟨ai, hai, hij'⟩ := hti
            obtain ⟨aj, haj, rfl⟩ := htj
            rw [Fin.cons_eq_cons] at hij'
            ext
            · exact hij'.1
            · obtain ⟨-, rfl⟩ := hij'
              rw [← (aux d i.2).prop ai |>.mp hai, ← (aux d j.2).prop ai |>.mp haj])
        property := fun f => by
          simp_rw [mem_disjiUnion, mem_antidiagonal, mem_map, Embedding.coeFn_mk, Prod.exists,
            (aux d _).prop, Fin.sum_univ_succ]
          constructor
          · rintro ⟨a, b, rfl, g, rfl, rfl⟩
            simp only [Fin.cons_zero, Fin.cons_succ]
          · intro hf
            exact ⟨_, _, hf, _, rfl, Fin.cons_self_tail f⟩ }

@[simp] lemma mem_finAntidiagonal {d : ℕ} {f : Fin d → μ} :
    f ∈ finAntidiagonal d n ↔ ∑ i, f i = n := (finAntidiagonal.aux d n).prop f

end AddCommMonoid
end Finset
