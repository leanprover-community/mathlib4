/-
Copyright (c) 2025 Yi.Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi.Yuan
-/
import Mathlib.GroupTheory.Perm.Fin

/-!
## Main Definitions and Results
* `Fin.natAdd_castLEEmb` as an `Embedding` from `Fin n` to `Fin m`, `natAdd_castLEEmb m hmn i`
adds `m - n` to `i`, generalizes `addNatEmb`.
* `cycleIcc i j hij` is the cycle `(i i+1 .... j)` leaving `(0 ... i-1)` and `(j+1 ... n-1)`
unchanged.
* `range_natAdd_castLEEmb`
* `cycleIcc_of_gt`
* `cycleIcc_of_le`
* `cycleIcc_of`
* `cycleRange_of_lt`
* `cycleRange_of_eq`
* `sign_cycleIcc`
-/

open Equiv Fin

/-- `Fin.natAdd_castLEEmb` as an `Embedding` from `Fin n` to `Fin m`, `natAdd_castLEEmb m hmn i`
adds `m - n` to `i`, generalizes `addNatEmb`.
-/
@[simps!]
def natAdd_castLEEmb {n : ℕ} (m : ℕ) (hmn : n ≤ m): Fin n ↪ Fin (m) :=
  (addNatEmb (m - n)).trans (finCongr (by omega)).toEmbedding

@[simp]
lemma natAdd_castLEEmb_apply {n m : ℕ} (hmn : n ≤ m) (k : Fin n) :
    ((natAdd_castLEEmb m hmn) k).1 = k.1 + (m - n) := by simp

@[simp]
lemma range_natAdd_castLEEmb {n m : ℕ} (hmn : n ≤ m) :
    Set.range (natAdd_castLEEmb m hmn) = {i | m - n ≤ i.1} := by
  simp [natAdd_castLEEmb]
  ext y
  exact ⟨fun ⟨x, hx⟩ ↦ by simp [← hx]; omega,
    fun xin ↦ ⟨subNat (m := m - n) (Fin.cast (Nat.add_sub_of_le hmn).symm y)
    (Nat.sub_le_of_le_add xin), by simp⟩⟩

/-- `cycleIcc i j hij` is the cycle `(i i+1 .... j)` leaving `(0 ... i-1)` and `(j+1 ... n-1)`
unchanged.
-/
@[simps!]
def cycleIcc {n : ℕ} {i j : Fin n} (hij : i ≤ j): Perm (Fin n) :=
  have : (j - i).1 < n - i.1 := by simp [sub_val_of_le hij, Nat.sub_lt_sub_right hij j.isLt]
  (cycleRange (Fin.castLT (j - i) this)).extendDomain
    (natAdd_castLEEmb n (by simp)).toEquivRange

theorem cycleIcc_of_gt {n : ℕ} {i j k : Fin n} (hij : i ≤ j) (h : k < i) : (cycleIcc hij) k = k :=
  Perm.extendDomain_apply_not_subtype ((j - i).castLT _).cycleRange
    (natAdd_castLEEmb n _).toEquivRange (by simp; omega)

private lemma cycleIcc_case {n : ℕ} {i j k : Fin n} (hij : i ≤ j) (h : i <= k) (kin : k ∈ Set.range
    ⇑(natAdd_castLEEmb n (cycleIcc._proof_4 (i := i)))) : (cycleIcc hij) k = (natAdd_castLEEmb n
    (cycleIcc._proof_4 (i := i))) (((j - i).castLT (cycleIcc._proof_3 hij)).cycleRange
    ((natAdd_castLEEmb n (cycleIcc._proof_4 (i := i))).toEquivRange.symm ⟨k, kin⟩)) := by
  have kin : k ∈ Set.range ⇑(natAdd_castLEEmb n (cycleIcc._proof_4 (i := i))) := by simp; omega
  simp [cycleIcc, ((j - i).castLT (cycleIcc._proof_3 hij)).cycleRange.extendDomain_apply_subtype
    (natAdd_castLEEmb n _).toEquivRange kin]

private lemma cycleIcc_simp_lemma {n : ℕ} {i k : Fin n} (h : i <= k)
    (kin : k ∈ Set.range ⇑(natAdd_castLEEmb n (cycleIcc._proof_4 (i := i)))) :
    (((addNatEmb (n - (n - i.1))).trans (finCongr _).toEmbedding).toEquivRange.symm
 ⟨k, kin⟩) = subNat i.1 (Fin.cast (by omega) k) (by simp [h]) := by
  simpa [symm_apply_eq] using eq_of_val_eq (by simp; omega)

theorem cycleIcc_of_le {n : ℕ} {i j k : Fin n} (hij : i ≤ j) (h : j < k) :
    (cycleIcc hij) k = k := by
  have kin : k ∈ Set.range ⇑(natAdd_castLEEmb n (cycleIcc._proof_4 (i := i))) := by simp; omega
  rw [cycleIcc_case hij (Fin.le_of_lt (Fin.lt_of_le_of_lt hij h)) kin]
  have : (((j - i).castLT (cycleIcc._proof_3 hij)).cycleRange
      (((addNatEmb (n - (n - i.1))).trans (finCongr _).toEmbedding).toEquivRange.symm ⟨k, kin⟩)) =
      subNat i.1 (Fin.cast (by omega) k) (by simp [le_of_lt (lt_of_le_of_lt hij h)]) := by
    rw [cycleIcc_simp_lemma (Fin.le_of_lt (Fin.lt_of_le_of_lt hij h)), cycleRange_of_gt]
    exact lt_def.mpr (by simp [sub_val_of_le hij]; omega)
  simpa only [natAdd_castLEEmb, this] using eq_of_val_eq (by simp; omega)

instance {n : ℕ} {i: Fin n} : NeZero (n - i.1) := NeZero.of_pos (by omega)

theorem cycleIcc_of {n : ℕ} {i j k : Fin n} (hij : i ≤ j) (h1 : i <= k) (h2 : k <= j) [NeZero n]:
    (cycleIcc hij) k = if k = j then i else k + 1 := by
  have kin : k ∈ Set.range ⇑(natAdd_castLEEmb n (cycleIcc._proof_4 (i := i))) := by simp; omega
  simp [cycleIcc_case hij h1 kin, natAdd_castLEEmb, cycleIcc_simp_lemma h1]
  refine eq_of_val_eq ?_
  split_ifs with h3
  · have h : subNat i.1 (Fin.cast (by omega) j) (by simp [hij]) = (j - i).castLT
        (cycleIcc._proof_3 hij) := eq_of_val_eq (by simp [subNat, coe_castLT, sub_val_of_le hij])
    simpa [h3, cycleRange_of_eq h] using by omega
  · have h : subNat i.1 (Fin.cast (by omega) k) (by simp [h1]) < (j - i).castLT
        (cycleIcc._proof_3 hij) := by simp [subNat, lt_iff_val_lt_val, sub_val_of_le hij]; omega
    have : (k.1 + 1) % n = k.1 + 1 := Nat.mod_eq_of_lt (by omega)
    rw [cycleRange_of_lt h, subNat]
    simp only [coe_cast, add_def, val_one', Nat.add_mod_mod, addNat_mk, cast_mk, this]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

theorem cycleRange_of_lt {n : ℕ} {i j k : Fin n} (hij : i ≤ j) (h1 : i <= k) (h2 : k < j)
    [NeZero n] : (cycleIcc hij) k = k + 1 := by
  simp [cycleIcc_of hij h1 (Fin.le_of_lt h2), Fin.ne_of_lt h2]

theorem cycleRange_of_eq {n : ℕ} {i j : Fin n} (hij : i ≤ j) [NeZero n] :
    (cycleIcc hij) j = i := by
  simp [cycleIcc_of hij hij (Fin.ge_of_eq rfl)]

@[simp]
theorem sign_cycleIcc {n : ℕ} {i j : Fin n} (hij : i ≤ j) :
  Perm.sign (cycleIcc hij) = (-1) ^ (j - i : ℕ) := by
  simp [cycleIcc, sub_val_of_le hij]

private lemma Nezero_simp_lemma {n : ℕ} {i j : Fin n} (hij : i < j) :
    (j - i).castLT (cycleIcc._proof_3 (Fin.le_of_lt hij)) ≠ 0 := by
  refine Ne.symm (ne_of_val_ne ?_)
  simpa [coe_sub_iff_le.mpr (Fin.le_of_lt hij)] using by omega

theorem isCycle_cycleIcc {n : ℕ} {i j : Fin n} (hij : i < j) :
    (cycleIcc (Fin.le_of_lt hij)).IsCycle := Equiv.Perm.IsCycle.extendDomain
  (natAdd_castLEEmb n _).toEquivRange (isCycle_cycleRange (Nezero_simp_lemma hij))

theorem cycleType_cycleIcc {n : ℕ} {i j : Fin n} (hij : i < j) :
    Perm.cycleType (cycleIcc (Fin.le_of_lt hij)) = {(j - i + 1: ℕ)} := by
  simpa [cycleIcc, cycleType_cycleRange (Nezero_simp_lemma hij)] using sub_val_of_le
    (Fin.le_of_lt hij)
