/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Algebra.Lie.Basic
import Mathlib.Data.List.Intervals
import Mathlib.GroupTheory.Perm.List
import Mathlib.LinearAlgebra.Alternating.Basic

/-!
# Chevalley-Eilenberg cochains
Given a Lie algebra `L` over a commutative ring `R`, and an `L`-module `M`, we construct the
structures underlying the Chevalley-Eilenberg cochain complex, whose `p`th cochains are given by the
`R`-module of alternating `R`-multilinear maps from `L^p` to `M`.

## Main definitions
 * Standard cochain complex
 * cohomology

## Main results
* The first sum making the differential is alternating.
* The second sum making the differential is alternating.

## TODO

 * In a separate file, apply these data to the homological complex API.
 * Use "shape" API for homological complexes to avoid indexing problems?
 * There seems to be a method of continuous group cohomology mentioned on Zulip that avoids
   alternating sums. Perhaps it can be adapted here.

## References
* [Cartan, H., Eilenberg, S., *Homological Algebra*][cartanEilenberg1956]
* [N. Bourbaki, *Lie groups and {L}ie algebras. {C}hapters 1--3*][bourbaki1975]
-- cohomology is Exercises section 3 (p116, near end of book)
-/

namespace Int

theorem neg_one_pow_sub_eq_pow_add {m n : ℕ} (h : n ≤ m) :
    (-1) ^ (m - n) = (-1) ^ (m + n) := by
  rw [show m + n = m - n + 2 * n by omega, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
--#find_home! neg_one_pow_sub_eq_pow_add
--Mathlib.Data.Int.Cast.Lemmas, Mathlib.Algebra.Ring.Int.Parity,

lemma negOnePow_sub_eq_negOnePow_add {m n : ℕ} (h : n ≤ m) :
    negOnePow (m - n : ℕ) = negOnePow (m + n) := by
  refine (negOnePow_eq_iff ((m - n).cast) (m + n)).mpr ?_
  rw [show (m - n).cast - ((m : ℤ) + ↑n) = - n + - n by omega]
  exact Even.add_self _
--#find_home! negOnePow_sub_eq_negOnePow_add --[Mathlib.Algebra.Ring.NegOnePow]
end Int

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

lemma cons_eq_update_cons {L : Type*} {n : ℕ} (y z : L) (g : Fin n → L) :
    (Fin.cons z g : Fin (n + 1) → L) = Function.update (Fin.cons y g) 0 z := by
  ext l
  simp only [Fin.cons, Function.update, eq_rec_constant, dite_eq_ite]
  by_cases hl : l = 0
  · simp [hl]
  · simp only [hl, ↓reduceIte]
    obtain ⟨m, rfl⟩ : ∃ (m : Fin n), m.succ = l := Fin.exists_succ_eq_of_ne_zero hl
    simp

-- I get a diamond later if I leave out the `DecidableEq` here.
lemma removeNth_update_of_gt {n : ℕ} {α : Sort*} {p q : Fin (n + 1)}
    (hpq : p < q) (x : α) (f : Fin (n + 1) → α) (h' := Fin.ne_last_of_lt hpq) :
    removeNth q (Function.update f p x) = Function.update (removeNth q f) (p.castPred h') x := by
  ext i
  simp only [removeNth, Function.update_apply]
  by_cases h : q.succAbove i = p
  · simp [((fun h k h' ↦ (succAbove_eq_iff_eq_castPred h k h').mp) hpq i h' h).symm, h]
  · have : i ≠ p.castPred h' := fun hc ↦ h ((succAbove_eq_iff_eq_castPred hpq i h').mpr hc)
    simp [this, h]

-- I get a diamond later if I leave out the `DecidableEq` here.
lemma removeNth_update_of_lt {n : ℕ} {α : Sort*} {p q : Fin (n + 1)}
    (hqp : q < p) (x : α) (f : Fin (n + 1) → α) (h' := Fin.ne_zero_of_lt hqp) :
    removeNth q (Function.update f p x) = Function.update (removeNth q f) (p.pred h') x := by
  ext i
  simp only [removeNth, Function.update_apply]
  by_cases h : q.succAbove i = p
  · simp [h, ((succAbove_eq_iff_eq_pred hqp i h').mp h).symm]
  · have : i ≠ p.pred h' :=
      fun hc ↦ h ((succAbove_eq_iff_eq_pred hqp i h').mpr hc)
    simp [this, h]

section fromDeRham -- https://github.com/urkud/DeRhamCohomology/

theorem succAbove_succAbove_predAbove {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    (i.succAbove j).succAbove (j.predAbove i) = i := by
  ext
  simp [succAbove, predAbove, lt_def, apply_dite Fin.val, apply_ite Fin.val]
  split_ifs <;> omega

theorem succAbove_succAbove_succAbove_predAbove {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (k : Fin n) :
    (i.succAbove j).succAbove ((j.predAbove i).succAbove k) = i.succAbove (j.succAbove k) := by
  ext
  simp [succAbove, predAbove, lt_def, apply_dite Fin.val, apply_ite Fin.val]
  split_ifs <;> omega

theorem removeNth_removeNth {n : ℕ} {α : Sort*} (m : Fin (n + 2) → α)
    (i : Fin (n + 1)) (j : Fin (n + 2)) :
    i.removeNth (j.removeNth m) = (i.predAbove j).removeNth ((j.succAbove i).removeNth m) := by
  ext x
  dsimp [removeNth]
  rw [succAbove_succAbove_succAbove_predAbove]

theorem succAbove_succ_eq_succAbove_castSucc {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    i.succ.succAbove j = i.castSucc.succAbove j := by
  rcases h.lt_or_lt with hlt | hlt
  · rw [succAbove_succ_of_lt _ _ hlt, succAbove_castSucc_of_le _ _ hlt.le]
  · rw [succAbove_succ_of_le _ _ hlt.le, succAbove_castSucc_of_lt _ _ hlt]

theorem insertNth_succ {n : ℕ} {α : Sort*} (p : Fin n) (a : α) (x : Fin n → α) :
    p.succ.insertNth a x = p.castSucc.insertNth a x ∘ Equiv.swap p.castSucc p.succ := by
  ext j
  cases j using p.succ.succAboveCases
  · simp
  · rename_i j
    rw [insertNth_apply_succAbove, Function.comp_apply]
    rcases eq_or_ne j p with rfl | hne
    · rw [succAbove_succ_self, Equiv.swap_apply_left, ← succAbove_castSucc_self,
        insertNth_apply_succAbove]
    · rw [Equiv.swap_apply_of_ne_of_ne _ (succAbove_ne _ _)]
      · rw [succAbove_succ_eq_succAbove_castSucc hne.symm, insertNth_apply_succAbove]
      · rwa [← succAbove_succ_self, succAbove_right_injective.ne_iff]

end fromDeRham

theorem negOnePow_succAbove_add_predAbove {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    Int.negOnePow ((i.succAbove j : ℤ) + (j.predAbove i : ℤ)) = Int.negOnePow (i + j + 1 : ℕ) := by
  rcases lt_or_le j.castSucc i with hji | hij
  · have : 0 < (i : ℕ) := (Nat.zero_le j).trans_lt hji
    rw [succAbove_of_castSucc_lt _ _ hji, coe_castSucc, predAbove_of_castSucc_lt _ _ hji, coe_pred,
      Int.ofNat_add_out, ← Nat.add_sub_assoc this ↑j, Int.negOnePow_sub_eq_negOnePow_add,
      Nat.add_comm i, Int.ofNat_add_out]
    omega
  · rw [succAbove_of_le_castSucc _ _ hij, val_succ, predAbove_of_le_castSucc _ _ hij, coe_castPred,
      Int.ofNat_add_out, Nat.add_right_comm, Nat.add_comm i]

/-- A sequential list in Fin -/
def List.Ico {n : ℕ} (p q : Fin (n + 1)) : List (Fin (n + 1)) :=
  (_root_.List.Ico p q).pmap Fin.mk
    (by intro k h; simp only [List.Ico.mem] at h; exact h.2.trans q.isLt)

@[simp]
lemma List.Ico_mem {n : ℕ} (p q r : Fin (n + 1)) : r ∈ List.Ico p q ↔ p ≤ r ∧ r < q := by
  simp only [Ico, List.mem_pmap, List.Ico.mem]
  constructor
  · intro h
    obtain ⟨b, hb, hr⟩ := h
    rw [← hr]
    exact ⟨hb.1, hb.2⟩
  · intro hp
    use r.val
    simp [hp]

lemma formPerm_List_id_of_lt {n : ℕ} {p q r : Fin (n + 1)} (hpq : p < q) :
    (List.formPerm (List.Ico q r)) p = p := by
  refine List.formPerm_apply_of_not_mem ?_
  simp only [List.Ico, List.mem_pmap, List.Ico.mem, not_exists]
  intro s hs
  exact Fin.ne_of_gt (lt_of_lt_of_le hpq (le_def.mpr (by simp [hs.1])))

--lemma formPerm_List_succ_of_mem {n : ℕ} {p q r : Fin (n + 1)} (hpq : p ≤ q) (hqr : q + 1 < r) :
--    (List.formPerm (List.Ico p r)) q = q + 1 := by (wrong)

lemma formPerm_List_id_of_gt {n : ℕ} {p q r : Fin (n + 1)} (hqr : q < r) :
    (List.formPerm (List.Ico p q)) r = r := by
  refine List.formPerm_apply_of_not_mem ?_
  simp only [List.Ico, List.mem_pmap, List.Ico.mem, not_exists]
  intro s hs
  exact Fin.ne_of_lt (LT.lt.trans (lt_def.mpr (by simp [hs.2])) hqr)

--lemma removeNth_eq_of_cycle {n : ℕ} {α : Sort*} {p q : Fin (n + 1)} (hqp : p < q)
--    (f : Fin (n + 1) → α) (hf : f p = f q) :
--    removeNth p (f ∘ (List.formPerm (List.Ico p q))) = removeNth q f := by

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

namespace MultilinearMap

variable {L M R : Type*} [Semiring R] [AddCommMonoid L] [AddCommGroup M] [Module R L] [Module R M]

lemma cons_zero {n : ℕ} (g : Fin n → L)
    (f : MultilinearMap R (fun _ : Fin (n + 1) => L) M) :
    f (Fin.cons 0 g) = 0 :=
  map_coord_zero f 0 rfl

lemma removeNth_map_update_add {n : ℕ}
    (f : MultilinearMap R (fun _ : Fin n => L) M)
    {i j : Fin (n + 1)} (h : i ≠ j) (x y : L) (g : Fin (n + 1) → L):
  f (i.removeNth (Function.update g j (x + y))) =
    f (i.removeNth (Function.update g j x)) + f (i.removeNth (Function.update g j y)) := by
  rcases lt_or_gt_of_ne h with (hlt | hgt)
  · simp [Fin.removeNth_update_of_lt hlt _ g]
  · simp [Fin.removeNth_update_of_gt hgt _ g]

end MultilinearMap

namespace AlternatingMap

variable {L M R : Type*} [Semiring R] [AddCommMonoid L] [AddCommGroup M] [Module R L] [Module R M]

lemma cons_zero {n : ℕ} (g : Fin n → L)
    (f : L [⋀^Fin (n + 1)]→ₗ[R] M) :
    f (Fin.cons 0 g) = 0 :=
  map_coord_zero f 0 rfl

theorem negOnePow_smul_apply_cons {n : ℕ} (f : L [⋀^Fin (n + 1)]→ₗ[R] M) (x : L)
    (v : Fin n → L) (i : Fin (n + 1)) :
    Int.negOnePow i.val • f (Fin.cons x v) = f (i.insertNth x v) := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    rw [Fin.insertNth_succ, f.map_swap _ Fin.lt_succ.ne, ← ih, Fin.val_succ, Fin.coe_castSucc,
      Int.natCast_add, add_comm i.val.cast, Int.negOnePow_add, Int.natCast_one, Int.negOnePow_one,
      neg_one_mul, Units.neg_smul]

lemma negOnePow_smul_apply_removeNth_add_eq_zero_of_eq {n : ℕ}
    (f : L [⋀^Fin (n + 1)]→ₗ[R] M) {v : Fin (n + 1 + 1) → L} {i j : Fin (n + 1 + 1)}
    (hvij : v i = v j) (hij : i ≠ j) :
    Int.negOnePow i.val • f (i.removeNth v) + Int.negOnePow j.val • f (j.removeNth v) = 0 := by
  rcases Fin.exists_succAbove_eq hij with ⟨i, rfl⟩
  set w := i.removeNth (j.removeNth v) with hw
  have hw₁ : i.insertNth (v j) w = j.removeNth v := by
    rw [← hvij]
    apply Fin.insertNth_self_removeNth
  have hw₂ : (i.predAbove j).insertNth (v j) w = (j.succAbove i).removeNth v := by
    rw [hw, Fin.removeNth_removeNth, Fin.insertNth_removeNth, Function.update_eq_self_iff,
      Fin.removeNth, Fin.succAbove_succAbove_predAbove]
  simp_rw [← hw₁, ← hw₂, ← negOnePow_smul_apply_cons, smul_smul, ← Int.negOnePow_add]
  rw [Fin.negOnePow_succAbove_add_predAbove, add_eq_zero_iff_eq_neg, Nat.cast_add _ 1,
    Int.negOnePow_add, mul_comm, mul_smul, Int.natCast_one, Int.negOnePow_one, Units.neg_smul,
    one_smul, Int.ofNat_add_out]

end AlternatingMap

namespace LieAlgebra

variable {L M R : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M]

/-- version with removeNth -/
def coboundary_first_summand {n : ℕ} (f : MultilinearMap R (fun _ : Fin n => L) M)
    (i : Fin (n + 1)) : MultilinearMap R (fun _ : Fin (n + 1) => L) M where
  toFun g := (Int.negOnePow i.val • ⁅g i, f (i.removeNth g)⁆)
  map_update_add' {inst} g j x y := by
    cases Subsingleton.elim inst (instDecidableEqFin (n + 1))
    simp_rw [← smul_add]
    congr 1
    by_cases hij : j = i
    · have (z : L) : i.removeNth (Function.update g i z) = i.removeNth g := by
        convert Fin.removeNth_update i _ g
      simp only [Function.update, hij, ↓reduceDIte, eq_rec_constant, this, add_lie]
    · simp only [Function.update_of_ne (fun a ↦ hij a.symm), ← lie_add,
        MultilinearMap.removeNth_map_update_add f (Ne.symm hij) x y g]
  map_update_smul' {inst} g j r x := by
    cases Subsingleton.elim inst (instDecidableEqFin (n + 1))
    simp only
    rw [smul_comm]
    congr 1
    by_cases hij : i = j
    · have (z : L) : i.removeNth (Function.update g i z) = i.removeNth g := by
        convert Fin.removeNth_update i _ g
      simp only [Function.update, ← hij, ↓reduceDIte, eq_rec_constant, this, smul_lie]
    · simp only [Function.update_of_ne hij, ← lie_smul]
      congr 1
      rcases lt_or_gt_of_ne hij with (hlt | hgt)
      · simp [Fin.removeNth_update_of_lt hlt _ g]
      · simp [Fin.removeNth_update_of_gt hgt _ g]

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

lemma coboundary_first_alternating (n : ℕ) (f : L [⋀^Fin n]→ₗ[R] M) (g : Fin (n + 1) → L)
    (i j : Fin (n + 1)) (h : g i = g j) (hij : i ≠ j) :
    (∑ i : Fin (n + 1), coboundary_first_summand f.toMultilinearMap i).toFun g = 0 := by
  simp only [coboundary_first_summand, AlternatingMap.coe_multilinearMap,
    MultilinearMap.toFun_eq_coe, MultilinearMap.coe_sum, MultilinearMap.coe_mk, Finset.sum_apply]
  rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) hij]
  · simp_rw [h, Units.smul_def, ← lie_smul, ← lie_add]
    suffices (Int.negOnePow i.val : ℤ) • f (i.removeNth g) +
        (Int.negOnePow j.val : ℤ) • f (j.removeNth g) = 0 by
      rw [this, lie_zero]
    suffices (Int.negOnePow i.val) • f (i.removeNth g) +
        (Int.negOnePow j.val) • f (j.removeNth g) = 0 by
      exact this
    obtain ⟨m, rfl⟩ : ∃m, m + 1 = n := by
      refine Nat.exists_add_one_eq.mpr ?_
      contrapose! hij
      omega
    exact AlternatingMap.negOnePow_smul_apply_removeNth_add_eq_zero_of_eq f h hij
  · intro k hk hijk
    exact coboundary_first_summand_alt n f hij hijk.1.symm hijk.2.symm h

/-- The first half of the coboundary map. -/
def coboundary_first (n : ℕ) (f : L [⋀^Fin n]→ₗ[R] M) :
    L [⋀^Fin (n + 1)]→ₗ[R] M :=
  ⟨∑ i : Fin (n + 1), coboundary_first_summand f i,
    fun g i j h hi ↦ coboundary_first_alternating n f g i j h hi⟩

--TODO: show that this is linear

/-- The summand for the coboundary map. -/
def coboundary_second_aux {n : ℕ} (g : Fin (n + 1 + 1) → L) {i j : Fin (n + 1 + 1)} (h : i < j) :
    Fin (n + 1) → L :=
  Fin.cons ⁅g i, g j⁆ (fun k => (i.castPred (Fin.ne_last_of_lt h)).removeNth (j.removeNth g) k)

/-!
lemma le_of_Ico {n : ℕ} {i j : Fin (n + 1)} (h : i ∈ Finset.Ico 0 j) : i < j := by
  simpa [Finset.Ico, LocallyFiniteOrder.finsetIco] using h

/-- The second sum in the Lie algebra cohomology map. Note that this is offset by one. -/
def coboundary_second_sum (n : ℕ) (f : L [⋀^Fin (n + 1)]→ₗ[R] M) (g : Fin (n + 1 + 1) → L) : M :=
  ∑ j : Fin (n + 1 + 1), ∑ i ∈ Finset.Ico 0 j, (-1: ℤˣ) ^ (i.val + j.val) •
      f (coboundary_second_aux (i := i) (j := j) g (le_of_Ico sorry))
-/
--lemma (i.castPred ⋯).removeNth (i.removeNth (Function.update g k (x + y))) k_1 =

--look at MultilinearMap.restr

/-- The image of the second sum of the differential on a cochain, as a multilinear map. -/
def coboundary_second_summand_multilinear (n : ℕ) (f : L [⋀^Fin (n + 1)]→ₗ[R] M)
    {i j : Fin (n + 1 + 1)} (h : i < j) : MultilinearMap R (fun _ : Fin (n + 1 + 1) => L) M where
  toFun g := Int.negOnePow (i.val + j.val) • f (coboundary_second_aux g h)
  map_update_add' {inst} g k x y := by
    cases Subsingleton.elim inst (instDecidableEqFin (n + 1 + 1))
    simp only [coboundary_second_aux]
    rw [← smul_add]
    congr 1
    by_cases hik : i = k
    · have hjk := ne_of_gt <| hik.symm ▸ h
      simp only [hik, ite_false]
      simp_rw [show ∀ (z : L), Function.update g k z i = z by
        intros; rw [hik, Function.update_self], show ∀ (z : L), Function.update g k z j = g j by
        intros; rw [← hik, Function.update_of_ne (ne_of_lt h).symm]]
      simp_rw [Fin.removeNth_update_of_gt (hik.symm ▸ h), Fin.removeNth_update]
      simp only [add_lie]
      rw [Fin.cons_eq_update_cons 0 (⁅x, g j⁆ + ⁅y, g j⁆), Fin.cons_eq_update_cons 0 ⁅x, g j⁆,
        Fin.cons_eq_update_cons 0 ⁅y, g j⁆, AlternatingMap.map_update_add]
    · simp_all [Function.update, Fin.succAbove_ne i, ← smul_add, hik]
      by_cases hjk : j = k
      · have (z : L) : (k.removeNth (Function.update g k z)) = (k.removeNth g) := by
          convert Fin.removeNth_update k z g -- how to add DecidableEq instance?
        simp only [hjk, ↓reduceIte, lie_add, this]
        rw [Fin.cons_eq_update_cons 0 (⁅g i, x⁆ + ⁅g i, y⁆), Fin.cons_eq_update_cons 0 (⁅g i, x⁆),
          Fin.cons_eq_update_cons 0 (⁅g i, y⁆), AlternatingMap.map_update_add]
      · by_cases hjk' : j < k
        · simp only [hjk, ↓reduceIte, Fin.removeNth_update_of_lt hjk']
          have : i.castPred (Fin.ne_last_of_lt h) < k.pred (Fin.ne_zero_of_lt hjk') := by
            refine (Fin.lt_pred_iff (Fin.ne_zero_of_lt hjk')).mpr ?_
            rw [Fin.succ_castPred_eq_add_one]
            exact lt_of_le_of_lt (Fin.add_one_le_of_lt h) hjk'
          simp [Fin.removeNth_update_of_lt this]
        · have hjk' : k < j := by omega
          by_cases hik' : i < k
          · simp only [hjk, ↓reduceIte, Fin.removeNth_update_of_gt hjk']
            have : i.castPred (Fin.ne_last_of_lt h) < k.castPred (Fin.ne_last_of_lt hjk') := hik'
            simp [Fin.removeNth_update_of_lt this]
          · have hik' : k < i := by omega
            simp only [hjk, ↓reduceIte, Fin.removeNth_update_of_gt hjk']
            have : k.castPred (Fin.ne_last_of_lt hjk') < i.castPred (Fin.ne_last_of_lt h) := hik'
            simp [Fin.removeNth_update_of_gt this]
  map_update_smul' {inst} g k r x := by
    cases Subsingleton.elim inst (instDecidableEqFin (n + 1 + 1))
    simp only [coboundary_second_aux]
    rw [smul_comm r (Int.negOnePow (i.val + j.val)) _]
    congr 1
    by_cases hki : k ≤ i
    · simp only [Function.update_of_ne (ne_of_lt (lt_of_le_of_lt hki h)).symm]
      by_cases hki : k < i
      · simp only [Fin.removeNth_update_of_gt (hki.trans h)]
        have : k.castPred (Fin.ne_last_of_lt hki) < i.castPred (Fin.ne_last_of_lt h) := hki
        simp_rw [Fin.removeNth_update_of_gt this]
        have (z : L) : Function.update g k z i = g i := by
          exact Function.update_of_ne (ne_of_lt hki).symm _ _
        simp [this]
      · have hki : k = i := by omega
        simp only [Fin.removeNth_update_of_gt (lt_of_eq_of_lt hki h)]
        simp_rw [show ∀ (z : L), Function.update g k z i = z by
        intros; rw [hki, Function.update_self]]
        have : k.castPred (Fin.ne_last_of_lt (lt_of_eq_of_lt hki h)) =
            i.castPred (Fin.ne_last_of_lt h) := Fin.castPred_inj.mpr hki
        simp_rw [this, Fin.removeNth_update]
        rw [Fin.cons_eq_update_cons 0 ⁅r • x, g j⁆, Fin.cons_eq_update_cons 0 ⁅x, g j⁆]
        simp
    · have hki : i < k := by omega
      simp_rw [Function.update_of_ne (ne_of_lt hki)]
      by_cases hkj : k ≤ j
      · by_cases hjk : j = k
        · have (z : L) : j.removeNth (Function.update g k z) = j.removeNth g := by
            rw [hjk]
            convert Fin.removeNth_update k _ g
          simp_rw [this]
          have (z : L) : Function.update g k z j = z := by rw [hjk, Function.update_self]
          rw [this, Fin.cons_eq_update_cons 0 ⁅g i, r • x⁆, this,
            Fin.cons_eq_update_cons 0 ⁅g i, x⁆]
          simp
        · simp_rw [Function.update_of_ne hjk]
          have hkj : k < j := lt_of_le_of_ne hkj fun a ↦ hjk a.symm
          have : i.castPred (Fin.ne_last_of_lt hki) < k.castPred (Fin.ne_last_of_lt hkj) := hki
          simp [Fin.removeNth_update_of_gt hkj, Fin.removeNth_update_of_lt this]
      · have hkj : j < k := Fin.not_le.mp hkj
        simp_rw [Function.update_of_ne (ne_of_lt hkj), Fin.removeNth_update_of_lt hkj]
        have : i.castPred (Fin.ne_last_of_lt hki) < k.pred (Fin.ne_zero_of_lt hkj) := by
          refine (Fin.lt_pred_iff (Fin.ne_zero_of_lt hkj)).mpr ?_
          rw [Fin.succ_castPred_eq_add_one]
          exact lt_of_le_of_lt (Fin.add_one_le_of_lt h) hkj
        simp [Fin.removeNth_update_of_lt this]

/-- The second sum in the Lie algebra coboundary map, as a multilinear map. -/
def coboundary_second_multilinear (n : ℕ) (f : L [⋀^Fin (n + 1)]→ₗ[R] M) :
    MultilinearMap R (fun _ : Fin (n + 1 + 1) => L) M :=
  ∑ i ∈ Finset.univ (α := Fin (n + 1 + 1)), ∑ j ∈ Finset.univ (α := Fin (n + 1 + 1)),
    if h : j < i then coboundary_second_summand_multilinear n f h else 0

/-!
/-- The image of the second sum of the differential on a cochain, as a multilinear map. -/
def coboundary_second_summand_alternating (n : ℕ) (f : L [⋀^Fin (n + 1)]→ₗ[R] M)
    {i j : Fin (n + 1 + 1)} (h : i < j) : L [⋀^Fin (n + 1 + 1)]→ₗ[R] M :=
  { coboundary_second_multilinear n f with
    map_eq_zero_of_eq' g k l hlt hne := by
      simp only [coboundary_second_multilinear, coboundary_second_summand_multilinear,
        coboundary_second_aux, MultilinearMap.toFun_eq_coe, MultilinearMap.coe_sum,
        Finset.sum_apply]


      sorry
  }
-/

end LieAlgebra
