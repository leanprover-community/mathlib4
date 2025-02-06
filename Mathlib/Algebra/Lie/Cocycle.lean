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
* [Cartan, H., Eilenberg, S., *Homological Algebra*][cartanEilenberg1956]
* [N. Bourbaki, *Lie groups and {L}ie algebras. {C}hapters 1--3*][bourbaki1975]
-- cohomology is Exercises section 3 (p116, near end of book)
-/

namespace Fin

lemma succAbove_eq_iff_eq_castPred {n : ℕ} {i j : Fin (n + 1)} (h : i < j) (k : Fin n)
    (h' := Fin.ne_last_of_lt h) : j.succAbove k = i ↔ k = i.castPred h' := by
  refine ⟨?_, fun hk => hk ▸ Fin.succAbove_castPred_of_lt j i h (Fin.ne_last_of_lt h)⟩
  intro hk
  simp_rw [← hk]
  exact (Fin.castPred_succAbove k j ((Fin.succAbove_lt_iff_castSucc_lt j k).mp <| hk ▸ h)
      (hk ▸ h')).symm

lemma succAbove_eq_iff_eq_pred {n : ℕ} {i j : Fin (n + 1)} (h : j < i) (k : Fin n)
    (h' := Fin.ne_zero_of_lt h) : Fin.succAbove j k = i ↔ k = i.pred h' := by
    simp only [Fin.succAbove]
    by_cases hk : k.castSucc < j
    · simp only [hk, ↓reduceIte]
      refine (iff_false_right <| Fin.ne_of_lt ?_).mpr <| Fin.ne_of_lt (hk.trans h)
      rw [Fin.lt_pred_iff]
      exact lt_of_le_of_lt hk h
    · simp only [hk, ↓reduceIte]
      exact ⟨fun h => by simp_rw [← h, Fin.pred_succ], fun h => by rw [h, Fin.succ_pred]⟩

lemma update_succAbove_eq_update_pred {L : Type*} {n : ℕ} (g : Fin (n + 1) → L) {i j : Fin (n + 1)}
    (h : j < i) (z : L) (h' := Fin.ne_zero_of_lt h) :
    (fun k ↦ Function.update g i z (j.succAbove k)) =
      Function.update (fun k => g (j.succAbove k)) (i.pred h') z := by
  ext k
  rw [Function.update_apply, Function.update_apply]
  by_cases hjki : j.succAbove k = i
  · have : k = i.pred h' := by rw [← Fin.succAbove_eq_iff_eq_pred h, hjki]
    rw [hjki, this]
    simp only [↓reduceIte]
  · have : ¬ k = i.pred h' := by
      rw [← Fin.succAbove_eq_iff_eq_pred h]
      exact hjki
    simp only [this, ↓reduceIte, ite_eq_right_iff]
    exact fun a ↦ False.elim (hjki a)

lemma update_succAbove_eq_update_castPred {L : Type*} {n : ℕ} (g : Fin (n + 1) → L)
    {i j : Fin (n + 1)} (h : i < j) (z : L) (h' := Fin.ne_last_of_lt h) :
    (fun k ↦ Function.update g i z (Fin.succAbove j k)) =
            Function.update (fun k => g (Fin.succAbove j k)) (i.castPred h') z := by
  ext k
  rw [Function.update_apply, Function.update_apply]
  by_cases hjki : j.succAbove k = i
  · have : k = i.castPred h' := by rw [← Fin.succAbove_eq_iff_eq_castPred h, hjki]
    rw [hjki, this]
    simp only [↓reduceIte]
  · have : ¬ k = i.castPred h' := by
      rw [← Fin.succAbove_eq_iff_eq_castPred h]
      exact hjki
    simp only [this, ↓reduceIte, ite_eq_right_iff]
    exact fun a ↦ False.elim (hjki a)

end Fin

namespace LieAlgebra

variable {L M R : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M]

/-- The first sum in the Lie algebra coboundary map. -/
def coboundary_first_sum (n : ℕ) (f : L [⋀^Fin n]→ₗ[R] M) (g : Fin (n + 1) → L) : M :=
  ∑ i ∈ Finset.Icc 0 n, ((-1: ℤˣ) ^ i • ⁅g i, f (fun j => g (Fin.succAbove i j))⁆)

/-- The second sum in the Lie algebra cohomology map. Note that this is offset by one. -/
def coboundary_second_sum (n : ℕ) (f : L [⋀^Fin (n + 1)]→ₗ[R] M) (g : Fin (n + 2) → L) : M :=
  ∑ j ∈ Finset.Icc 0 (n + 1), ∑ i ∈ Finset.Ico 0 j, ((-1: ℤˣ) ^ (i + j) •
      f (fun k => if hk : k = 0 then ⁅g i, g j⁆ else
        g (Fin.succAbove j (Fin.succAbove (Nat.cast i : Fin (n + 1)) (k.pred hk)))))

--look at MultilinearMap.restr

/-- The image of the differential on a cochain, as a multilinear map. -/
def coboundary_first_multilinear (n : ℕ) (f : L [⋀^Fin n]→ₗ[R] M) :
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
      · have hine : i ≠ 0 := Fin.ne_zero_of_lt hji
        have hup (z : L) : (fun k ↦ Function.update g i z (Fin.succAbove j' k)) =
            Function.update (fun k => g (Fin.succAbove j' k)) (i.pred hine) z := by
          convert Fin.update_succAbove_eq_update_pred g hji z hine --diamond?
        simp [hup]
      · have hji : i < j' := by omega
        have hlast : i ≠ Fin.last n := Fin.ne_last_of_lt hji
        have hup (z : L) : (fun k ↦ Function.update g i z (Fin.succAbove j' k)) =
            Function.update (fun k => g (Fin.succAbove j' k)) (i.castPred hlast) z := by
          convert Fin.update_succAbove_eq_update_castPred g hji z hlast
        simp [hup]
  map_update_smul' g i r x := by
    simp only [coboundary_first_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [smul_comm]
    congr 1
    set j' := (Nat.cast j : Fin (n+1)) with hj'
    by_cases hij : j' = i
    · simp_all [← hj', Function.update, Fin.succAbove_ne i, smul_lie]
    · simp_all only [Finset.mem_Icc, zero_le, true_and, ne_eq, not_false_eq_true,
      Function.update_of_ne, ← lie_smul]
      congr 1
      by_cases hji: j' < i
      · have hine : i ≠ 0 := Fin.ne_zero_of_lt hji
        have hup (z : L) : (fun k ↦ Function.update g i z (Fin.succAbove j' k)) =
            Function.update (fun k => g (Fin.succAbove j' k)) (i.pred hine) z := by
          convert Fin.update_succAbove_eq_update_pred g hji z hine --diamond?
        simp [hup]
      · have hji : i < j' := by omega
        have hlast : i ≠ Fin.last n := Fin.ne_last_of_lt hji
        have hup (z : L) : (fun k ↦ Function.update g i z (Fin.succAbove j' k)) =
            Function.update (fun k => g (Fin.succAbove j' k)) (i.castPred hlast) z := by
          convert Fin.update_succAbove_eq_update_castPred g hji z hlast
        simp [hup]

/-!
lemma isAlternating_of_sum (n : ℕ) (f : L [⋀^Fin n]→ₗ[R] M) (v : Fin n → L) (i j : Fin n) :
    v i = v j → i ≠ j → f v = 0 := by
  sorry
-/

end LieAlgebra
