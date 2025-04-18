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
lemma range_natAdd_castLEEmb {n : ℕ} (m : ℕ) (hmn : n ≤ m) :
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
  (cycleRange (Fin.castLT (n := n - i.1) (j - i) this)).extendDomain
    (natAdd_castLEEmb n (by simp)).toEquivRange

theorem cycleIcc_of_gt {n : ℕ} {i j k : Fin n} (hij : i ≤ j) (h : k < i) :
    (cycleIcc hij) k = k :=
  Perm.extendDomain_apply_not_subtype ((j - i).castLT _).cycleRange
    (natAdd_castLEEmb n _).toEquivRange (by simp; omega)

theorem cycleIcc_of_le {n : ℕ} {i j k : Fin n} (hij : i ≤ j) (h : j < k) :
    (cycleIcc hij) k = k := by
  have kin : k ∈ Set.range ⇑(natAdd_castLEEmb n (cycleIcc._proof_4 (i := i))) := by simp; omega
  simp [cycleIcc,
    ((j - i).castLT (cycleIcc._proof_3 hij)).cycleRange.extendDomain_apply_subtype
    (natAdd_castLEEmb n _).toEquivRange kin]
  have : (((j - i).castLT (cycleIcc._proof_3 hij)).cycleRange
      (((addNatEmb (n - (n - i.1))).trans (finCongr _).toEmbedding).toEquivRange.symm ⟨k, kin⟩)) =
      subNat (m := i) (Fin.cast (by omega) k) (by simp [le_of_lt (lt_of_le_of_lt hij h)]) := by
    have : (((addNatEmb (n - (n - i.1))).trans (finCongr _).toEmbedding).toEquivRange.symm ⟨k, kin⟩)
        = subNat (m := i) (Fin.cast (by omega) k) (by simp [le_of_lt (lt_of_le_of_lt hij h)]) := by
      simpa [symm_apply_eq] using eq_of_val_eq (by simp; omega)
    rw [this, cycleRange_of_gt]
    refine lt_def.mpr ?_
    simp [sub_val_of_le hij]; omega
  simpa only [natAdd_castLEEmb, this] using eq_of_val_eq (by simp; omega)

theorem cycleIcc_of {n : ℕ} {i j k : Fin n} (hij : i ≤ j) (h1 : i <= k) (h2 : k <= j) [NeZero n]:
    (cycleIcc hij) k = if k = j then i else k + 1 := by
  have kin : k ∈ Set.range ⇑(natAdd_castLEEmb n (cycleIcc._proof_4 (i := i))) := by simp; omega
  simp [cycleIcc,
    Perm.extendDomain_apply_subtype ((j - i).castLT (cycleIcc._proof_3 hij)).cycleRange
    (natAdd_castLEEmb n _).toEquivRange kin]
  have : NeZero (n - i.1) := NeZero.of_pos (by omega)
  by_cases h3 : k = j
  · rw [h3] at kin
    have : (((j - i).castLT (cycleIcc._proof_3 hij)).cycleRange
      (((addNatEmb (n - (n - i.1))).trans (finCongr _).toEmbedding).toEquivRange.symm ⟨j, kin⟩)) =
      subNat (m := i) (Fin.cast (by omega) i) (by simp [hij]) := by
      have : (((addNatEmb (n - (n - i.1))).trans (finCongr _).toEmbedding).toEquivRange.symm
        ⟨j, kin⟩) = subNat (m := i) (Fin.cast (by omega) j) (by simp [hij]) := by
        simpa [symm_apply_eq] using eq_of_val_eq (by simp; omega)
      have h : (subNat (n := n - i) (i.1) (Fin.cast (by omega) j) (by simp [hij])) =
          ((j - i).castLT (cycleIcc._proof_3 hij)):=
        eq_of_val_eq (by simp [subNat, coe_castLT, sub_val_of_le hij])
      simp [this, cycleRange_of_eq h, Fin.ext_iff]
    simpa only [h3, natAdd_castLEEmb, this] using eq_of_val_eq (by simp; omega)
  · have imp : (k + 1).1 = k.1 + 1 := by
      simp only [add_def, val_one', Nat.add_mod_mod]
      rw [Nat.mod_eq_of_lt]; omega
    have : (((j - i).castLT (cycleIcc._proof_3 hij)).cycleRange (((addNatEmb (n - (n - i.1))).trans
        (finCongr _).toEmbedding).toEquivRange.symm ⟨k, kin⟩)) = subNat (m := i)
        (Fin.cast (by omega) (k + 1)) (by simp [le_iff_val_le_val, imp]; omega) := by
      have : (((addNatEmb (n - (n - i.1))).trans (finCongr _).toEmbedding).toEquivRange.symm
        ⟨k, kin⟩) = subNat (m := i) (Fin.cast (by omega) (k)) (by simp [h1]) := by
        simpa [symm_apply_eq] using eq_of_val_eq (by simp [imp]; omega)
      rw [this]
      have h : (subNat (n := n - i) (i.1) (Fin.cast (by omega) k) (by simp [h1])) <
          ((j - i).castLT (cycleIcc._proof_3 hij)):= by
        simp [subNat, lt_iff_val_lt_val, sub_val_of_le hij]; omega
      rw [cycleRange_of_lt h]
      have : (k.1 + 1) % n = k.1 + 1 := Nat.mod_eq_of_lt (by omega)
      simpa [subNat, add_def, this, Nat.sub_add_comm h1] using Nat.mod_eq_of_lt (by omega)
    simpa only [natAdd_castLEEmb, this] using eq_of_val_eq (by simp [h3]; omega)

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
