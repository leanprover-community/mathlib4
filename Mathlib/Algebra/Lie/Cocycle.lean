/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.Alternating.Basic

/-!
# The Chevalley-Eilenberg complex

Given a Lie algebra `L` over a commutative ring `R`, and an `L`-module `M`, we construct the cochain
complex of alternating multilinear maps from `L^p` to `M`.

## Main definitions (Todo for now)

* Write the Chevalley-Eilenberg dg-algebra for a Lie algebra, then define homology and cohomology
as Ext and Tor?  We get commutativity from alternating property and associativity from Jacobi.
Also, I think this gives an equivalence between dg Lie algebras and CDGAs with suitable grading.
* Standard cochain complex
* cohomology

## Main results



## References

* [N. Bourbaki, *Lie groups and {L}ie algebras. {C}hapters 1--3*][bourbaki1975]
-- cohomology is Exercises section 3 (p116, near end of book)
-/

namespace LieAlgebra

variable {L M R : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M]

/-- The first sum in the Lie algebra coboundary map. -/
def coboundary_first_sum (n : ℕ) (f : L [⋀^Fin n]→ₗ[R] M) (g : Fin (n + 1) → L) : M :=
  ∑ i in Finset.Icc 0 n, ((-1: ℤˣ) ^ i • ⁅g i, f (fun j => g (Fin.succAbove i j))⁆)

/-- The second sum in the Lie algebra cohomology map. Note that this is offset by one. -/
def coboundary_second_sum (n : ℕ) (f : L [⋀^Fin (n + 1)]→ₗ[R] M) (g : Fin (n + 2) → L) : M :=
  ∑ j in Finset.Icc 0 (n + 1), ∑ i in Finset.Ico 0 j, ((-1: ℤˣ) ^ (i + j) •
      f (fun k => if hk : k = 0 then ⁅g i, g j⁆ else
        g (Fin.succAbove j (Fin.succAbove (Nat.cast i : Fin (n + 1)) (k.pred hk)))))

/-!
/-- The image of the differential on a cochain, as a multilinear map. -/
def coboundary_multilinear (n : ℕ) (f : L [⋀^Fin n]→ₗ[R] M) :
    MultilinearMap R (fun _ : Fin (n + 1) => L) M where
  toFun g := coboundary_first_sum n f g
  map_update_add' g i x y := by
    simp only [← Finset.sum_add_distrib, coboundary_first_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [← smul_add]
    congr 1
    set j' := (Nat.cast j : Fin (n+1)) with hj'
    by_cases hij : j' = i
    · simp_all [Function.update, Fin.succAbove_ne i, ← hj']
    · simp_all only [Finset.mem_Icc, zero_le, true_and, ne_eq, not_false_eq_true,
      Function.update_of_ne, ← lie_add]
      congr 1
      by_cases hji : j' < i
      · have hjn : j'.val < n + 1 := j'.isLt
        have hNe : NeZero n := { out := by omega }
        have hsjk (k : Fin n) : Fin.succAbove j' k = i ↔ k.succ = i := by
          simp only [Fin.succAbove]
          by_cases hk : k.castSucc < j'
          · simp only [hk, ↓reduceIte]
            exact (iff_false_right <| Fin.ne_of_lt (lt_of_le_of_lt hk hji)).mpr <|
              Fin.ne_of_lt (hk.trans hji)
          · simp [hk]
        have hup : (fun k ↦ Function.update g i (x + y) (Fin.succAbove j' k)) =
            Function.update (fun k => g (Fin.succAbove j' k))
            (Fin.predAbove j' i) (x + y)  := by
          ext k
          by_cases hik : j' < k.succ
          · have : Fin.succAbove j' k = k.succ := Fin.succAbove_of_lt_succ j' k hik

            sorry
          · sorry
        simp_all

        sorry
      · have hji : i < Nat.cast j := by omega
        sorry

  map_update_smul' g i r x := by
    sorry

lemma isAlternating_of_sum (n : ℕ) (f : L [⋀^Fin n]→ₗ[R] M) (v : Fin n → L) (i j : Fin n) :
    v i = v j → i ≠ j → f v = 0 := by
  sorry
-/
end LieAlgebra
