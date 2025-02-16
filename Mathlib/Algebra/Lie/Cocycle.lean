/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Algebra.Lie.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Alternating.Basic

/-!
# The Chevalley-Eilenberg complex

Given a Lie algebra `L` over a commutative ring `R`, and an `L`-module `M`, we construct the cochain
complex of alternating multilinear maps from `L^p` to `M`.

## Main definitions

* Standard cochain complex
* cohomology

## Main results

## TODO

* Use "shape" API for homological complexes to avoid indexing problems?

* There seems to be a method of continuous group cohomology mentioned on Zulip that avoids
alternating sums. Perhaps it can be adapted here.

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

lemma removeNth_update_of_gt {n : ℕ} {α : Sort*} {p q : Fin (n + 1)} (hpq : p < q)
    (x : α) (f : Fin (n + 1) → α) (h' := Fin.ne_last_of_lt hpq) :
    removeNth q (Function.update f p x) = Function.update (removeNth q f) (p.castPred h') x := by
  ext i
  simp only [removeNth, Function.update_apply]
  by_cases h : q.succAbove i = p
  · simp [((fun h k h' ↦ (succAbove_eq_iff_eq_castPred h k h').mp) hpq i h' h).symm, h]
  · have : i ≠ p.castPred h' := fun hc ↦ h ((succAbove_eq_iff_eq_castPred hpq i h').mpr hc)
    simp [this, h]

lemma removeNth_update_of_lt {n : ℕ} {α : Sort*} {p q : Fin (n + 1)} (hqp : q < p)
    (x : α) (f : Fin (n + 1) → α) (h' := Fin.ne_zero_of_lt hqp) :
    removeNth q (Function.update f p x) = Function.update (removeNth q f) (p.pred h') x := by
  ext i
  simp only [removeNth, Function.update_apply]
  by_cases h : q.succAbove i = p
  · simp [h, ((succAbove_eq_iff_eq_pred hqp i h').mp h).symm]
  · have : i ≠ p.pred h' :=
      fun hc ↦ h ((succAbove_eq_iff_eq_pred hqp i h').mpr hc)
    simp [this, h]

lemma not_injective_of_comp_succAbove {α : Type*} {n : ℕ} {i j k : Fin (n + 1)}
    {f : Fin (n + 1) → α} (hf : f i = f j) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬Function.Injective fun a ↦ f (k.succAbove a) := by
  refine Function.not_injective_iff.mpr ?_
  by_cases hi : i < k
  · use i.castPred <| Fin.ne_last_of_lt hi
    by_cases hj : j < k
    · use j.castPred <| Fin.ne_last_of_lt hj
      constructor
      · rw [Fin.succAbove_castPred_of_lt k i hi (Fin.ne_last_of_lt hi)]
        rw [Fin.succAbove_castPred_of_lt k j hj (Fin.ne_last_of_lt hj)]
        exact hf
      · exact fun h => hij (Fin.castPred_inj.mp h)
    · have hjk' : k < j := by omega
      have : j ≠ 0 := Fin.ne_zero_of_lt hjk'
      use j.pred <| Fin.ne_zero_of_lt hjk'
      constructor
      · rw [Fin.succAbove_castPred_of_lt k i hi (Fin.ne_last_of_lt hi)]
        rw [Fin.succAbove_pred_of_lt k j hjk' (Fin.ne_zero_of_lt hjk')]
        exact hf
      · exact Fin.ne_of_lt <| lt_of_lt_of_le hi <| (Fin.castPred_le_pred_iff
          (Fin.ne_last_of_lt hjk') (Fin.ne_zero_of_lt hjk')).mpr hjk'
  · have hi : k < i := by omega
    use i.pred <| Fin.ne_zero_of_lt hi
    by_cases hj : j < k
    · use j.castPred <| Fin.ne_last_of_lt hj
      constructor
      · rw [Fin.succAbove_pred_of_lt k i hi (Fin.ne_zero_of_lt hi)]
        rw [Fin.succAbove_castPred_of_lt k j hj (Fin.ne_last_of_lt hj)]
        exact hf
      · rw [ne_comm]
        exact (Fin.ne_of_lt) <| lt_of_lt_of_le hj <| (Fin.castPred_le_pred_iff
          (Fin.ne_last_of_lt hi) (Fin.ne_zero_of_lt hi)).mpr hi
    · have hjk' : k < j := by omega
      use j.pred <| Fin.ne_zero_of_lt hjk'
      constructor
      · rw [Fin.succAbove_pred_of_lt k i hi (Fin.ne_zero_of_lt hi)]
        rw [Fin.succAbove_pred_of_lt k j hjk' (Fin.ne_zero_of_lt hjk')]
        exact hf
      · refine fun h => hij (Fin.pred_inj.mp h)

end Fin

namespace AlternatingMap

variable {L M R : Type*} [Semiring R] [AddCommMonoid L] [AddCommGroup M] [Module R L] [Module R M]

/-!
lemma removeNth_eq {n : ℕ} {i j : Fin (n + 1)} (f : L [⋀^Fin n]→ₗ[R] M) (g : Fin (n + 1) → L)
    (h : g i = g j) :
    Int.negOnePow (i.val + j.val + 1) • f (i.removeNth g) = f (j.removeNth g) := by
  -- phrase this in terms of permutations!!!　AlternatingMap.map_perm


    sorry
-/
end AlternatingMap

namespace LieAlgebra

variable {L M R : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M]

/-- version with removeNth -/
def coboundary_first_summand' (n : ℕ) (f : L [⋀^Fin n]→ₗ[R] M) (i : Fin (n + 1)) :
    MultilinearMap R (fun _ : Fin (n + 1) => L) M where
  toFun g := (Int.negOnePow i.val • ⁅g i, f (i.removeNth g)⁆)
  map_update_add' g j x y := by
    simp_rw [← smul_add]
    congr 1
    by_cases hij : j = i
    · have (z : L) : i.removeNth (Function.update g i z) = i.removeNth g := by
        convert Fin.removeNth_update i _ g
      simp only [Function.update, hij, ↓reduceDIte, eq_rec_constant, this, add_lie]
    · simp only [Function.update_of_ne (fun a ↦ hij a.symm), ← lie_add]
      congr 1
      by_cases hlt : i < j
      · have (z : L) : i.removeNth (Function.update g j z) =
            Function.update (i.removeNth g) (j.pred (Fin.ne_zero_of_lt hlt)) z := by
          convert Fin.removeNth_update_of_lt hlt z g
        simp [this]
      · have hgt : j < i := by omega
        have (z : L) : i.removeNth (Function.update g j z) =
            Function.update (i.removeNth g) (j.castPred (Fin.ne_last_of_lt hgt)) z := by
          convert Fin.removeNth_update_of_gt hgt z g
        simp [this]
  map_update_smul' g j r x := by
    simp only
    rw [smul_comm]
    congr 1
    by_cases hij : i = j
    · have (z : L) : i.removeNth (Function.update g i z) = i.removeNth g := by
        convert Fin.removeNth_update i _ g
      simp only [Function.update, ← hij, ↓reduceDIte, eq_rec_constant, this, smul_lie]
    · simp only [Function.update_of_ne hij, ← lie_smul]
      congr 1
      by_cases hlt : i < j
      · have (z : L) : i.removeNth (Function.update g j z) =
            Function.update (i.removeNth g) (j.pred (Fin.ne_zero_of_lt hlt)) z := by
          convert Fin.removeNth_update_of_lt hlt z g
        simp [this]
      · have hgt : j < i := by omega
        have (z : L) : i.removeNth (Function.update g j z) =
            Function.update (i.removeNth g) (j.castPred (Fin.ne_last_of_lt hgt)) z := by
          convert Fin.removeNth_update_of_gt hgt z g
        simp [this]

-- Use Fin.removeNth, and Fin.removeNth_update
def coboundary_first_summand (n : ℕ) (f : L [⋀^Fin n]→ₗ[R] M) (i : Fin (n + 1)) :
    MultilinearMap R (fun _ : Fin (n + 1) => L) M where
  toFun g := (Int.negOnePow i.val • ⁅g i, f (fun j => g (Fin.succAbove i j))⁆)
  map_update_add' g j x y := by
    simp_rw [← smul_add]
    congr 1
    by_cases hij : j = i
    · simp_all [Function.update, Fin.succAbove_ne i]
    · simp only [Function.update_of_ne (fun a ↦ hij a.symm), ← lie_add]
      congr 1
      by_cases hji : i < j
      · have hine : j ≠ 0 := Fin.ne_zero_of_lt hji
        have hup (z : L) : (fun k ↦ Function.update g j z (Fin.succAbove i k)) =
            Function.update (fun k => g (Fin.succAbove i k)) (j.pred hine) z := by
          convert Fin.update_succAbove_eq_update_pred g hji z hine --can't use exact :P
        simp [hup]
      · have hji : j < i := by omega
        have hlast : j ≠ Fin.last n := Fin.ne_last_of_lt hji
        have hup (z : L) : (fun k ↦ Function.update g j z (Fin.succAbove i k)) =
            Function.update (fun k => g (Fin.succAbove i k)) (j.castPred hlast) z := by
          convert Fin.update_succAbove_eq_update_castPred g hji z hlast
        simp [hup]
  map_update_smul' g j r x := by
    simp only
    rw [smul_comm]
    congr 1
    by_cases hij : i = j
    · simp_all [Function.update, Fin.succAbove_ne j, smul_lie]
    · simp only [Function.update_of_ne hij, ← lie_smul]
      congr 1
      by_cases hji: i < j
      · have hine : j ≠ 0 := Fin.ne_zero_of_lt hji
        have hup (z : L) : (fun k ↦ Function.update g j z (Fin.succAbove i k)) =
            Function.update (fun k => g (Fin.succAbove i k)) (j.pred hine) z := by
          convert Fin.update_succAbove_eq_update_pred g hji z hine
        simp [hup]
      · have hji : j < i := by omega
        have hlast : j ≠ Fin.last n := Fin.ne_last_of_lt hji
        have hup (z : L) : (fun k ↦ Function.update g j z (Fin.succAbove i k)) =
            Function.update (fun k => g (Fin.succAbove i k)) (j.castPred hlast) z := by
          convert Fin.update_succAbove_eq_update_castPred g hji z hlast
        simp [hup]

/-- The image of the first sum of the differential on a cochain, as a multilinear map. -/
def coboundary_first_multilinear (n : ℕ) (f : L [⋀^Fin n]→ₗ[R] M) :
    MultilinearMap R (fun _ : Fin (n + 1) => L) M :=
  ∑ i : Fin (n + 1), coboundary_first_summand' n f i

omit [LieModule R L M] in
lemma coboundary_first_summand_alt (n : ℕ) (f : L [⋀^Fin n]→ₗ[R] M) {g : Fin (n + 1) → L}
    {i j k : Fin (n + 1)} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hg : g i = g j) :
    Int.negOnePow k.val • ⁅g k, f fun j ↦ g (k.succAbove j)⁆ = 0 := by
  refine smul_eq_zero_of_right _ ?_
  have : f (fun j ↦ g (k.succAbove j)) = 0 :=
    AlternatingMap.map_eq_zero_of_not_injective f (fun j ↦ g (k.succAbove j)) <|
      Fin.not_injective_of_comp_succAbove hg hij hik hjk
  rw [this]
  exact lie_zero (g k)

/-!
-- use Finset.sum_eq_add_of_mem
lemma coboundary_first_alternating (n : ℕ) (f : L [⋀^Fin n]→ₗ[R] M) (g : Fin (n + 1) → L)
    (i j : Fin (n + 1)) (h : g i = g j) (hij : i ≠ j) :
    (coboundary_first_multilinear n f).toFun g = 0 := by
  simp [coboundary_first_multilinear, coboundary_first_summand']
  rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) hij]
  · rw [h]

    sorry
  · intro k hk hijk
    exact coboundary_first_summand_alt n f hij hijk.1.symm hijk.2.symm h

/-- The first half of the coboundary map. -/
def coboundary_first (n : ℕ) (f : L [⋀^Fin n]→ₗ[R] M) :
    L [⋀^Fin (n + 1)]→ₗ[R] M :=
  ⟨coboundary_first_multilinear n f, fun g i j h hi ↦ coboundary_first_alternating n f g i j h hi⟩

/-- The second sum in the Lie algebra cohomology map. Note that this is offset by one. -/
def coboundary_second_sum (n : ℕ) (f : L [⋀^Fin (n + 1)]→ₗ[R] M) (g : Fin (n + 1 + 1) → L) : M :=
  ∑ j : Fin (n + 1 + 1), ∑ i ∈ Finset.Ico 0 j, ((-1: ℤˣ) ^ (i.val + j.val) •
      f (fun k => if hk : k = 0 then ⁅g i, g j⁆ else
        g (Fin.succAbove j (Fin.succAbove i (k.pred hk)))))


--look at MultilinearMap.restr

/-- The image of the second sum of the differential on a cochain, as a multilinear map. -/
def coboundary_second_multilinear (n : ℕ)(f : L [⋀^Fin (n + 1)]→ₗ[R] M) :
    MultilinearMap R (fun _ : Fin (n + 1 + 1) => L) M where
  toFun g := coboundary_second_sum n f g
  map_update_add' g i x y := by
    simp only [← Finset.sum_add_distrib, coboundary_second_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    simp_rw [← smul_add]
    congr 1
    by_cases hij : j = i
    · simp_all [Function.update, Fin.succAbove_ne i, ← smul_add, hij]
      ext k
      congr 1




lemma isAlternating_of_sum (n : ℕ) (f : L [⋀^Fin n]→ₗ[R] M) (v : Fin n → L) (i j : Fin n) :
    v i = v j → i ≠ j → f v = 0 := by
  sorry
-/

end LieAlgebra
