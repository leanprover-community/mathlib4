import Mathlib.GroupTheory.Perm.Fin

open Equiv Fin Equiv.Perm

/--
-/
@[simps apply]
def natAdd_castLEEmb {n : ℕ} (m : ℕ) (hmn : n ≤ m): Fin n ↪ Fin (m) :=
  (addNatEmb (m - n)).trans (finCongr (by omega)).toEmbedding

@[simp]
lemma range_natAdd_castLEEmb {n : ℕ} (m : ℕ) (hmn : n ≤ m) :
    Set.range (natAdd_castLEEmb m hmn) = {i | m - n ≤ i.1} := by
  simp [natAdd_castLEEmb]
  ext y
  constructor
  · intro ⟨x, hx⟩
    simp [← hx]
    omega
  · intro xin
    use subNat (m := m - n) (Fin.cast (Nat.add_sub_of_le hmn).symm y) (Nat.sub_le_of_le_add xin)
    simp

/-- the circle (i,i+1,...,j)
-/
def fininal {n : ℕ} (i j : Fin n) (hij : i ≤ j): Perm (Fin n) :=
  have : (j - i).1 < n - i.1 := by simp [sub_val_of_le hij, Nat.sub_lt_sub_right hij j.isLt]
  (cycleRange (Fin.castLT (n := n - i.1) (j - i) this)).extendDomain
    (natAdd_castLEEmb n (by simp)).toEquivRange

theorem cycleRange_of_gt'' {n : ℕ} {i j k : Fin n} (hij : i ≤ j) (h : k < i) :
    (fininal i j hij) k = k := by
  refine Perm.extendDomain_apply_not_subtype ((j - i).castLT _).cycleRange
      (natAdd_castLEEmb n _).toEquivRange ?_
  simp
  omega

theorem cycleRange_of_le'' {n : ℕ} {i j k : Fin n} (hij : i ≤ j) (h : k > j) :
    (fininal i j hij) k = k := by
  have kin : k ∈ Set.range ⇑(natAdd_castLEEmb n (fininal._proof_4 i)) := by simp; omega

  simp only [fininal,
    Perm.extendDomain_apply_subtype ((j - i).castLT (fininal._proof_3 i j hij)).cycleRange
      (natAdd_castLEEmb n _).toEquivRange kin,
    Function.Embedding.toEquivRange_apply, natAdd_castLEEmb_apply]

  have : (((j - i).castLT (fininal._proof_3 i j hij)).cycleRange
      (((addNatEmb (n - (n - ↑i))).trans (finCongr _).toEmbedding).toEquivRange.symm ⟨k, kin⟩)) =
      subNat (m := i) (Fin.cast (by omega) k) (by simp[le_of_lt (lt_of_le_of_lt hij h)]) := by
    have : (((addNatEmb (n - (n - ↑i))).trans (finCongr _).toEmbedding).toEquivRange.symm ⟨k, kin⟩)
      = subNat (m := i) (Fin.cast (by omega) k) (by simp[le_of_lt (lt_of_le_of_lt hij h)]) := by
      simp [symm_apply_eq]
      refine eq_of_val_eq ?_
      simp
      omega
    rw [this, cycleRange_of_gt]
    refine lt_def.mpr ?_
    simp [sub_val_of_le hij]
    omega
  simp only [natAdd_castLEEmb, this]
  refine eq_of_val_eq ?_
  simp
  omega

theorem cycleRange_of_lt'' {n : ℕ} {i j k : Fin n} (hij : i ≤ j) (h1 : i <= k) (h2 : k < j) [NeZero n] :
    (fininal i j hij) k = k + 1 := by
  have kin : k ∈ Set.range ⇑(natAdd_castLEEmb n (fininal._proof_4 i)) := by simp; omega
  simp only [fininal,
    Perm.extendDomain_apply_subtype ((j - i).castLT (fininal._proof_3 i j hij)).cycleRange
      (natAdd_castLEEmb n _).toEquivRange kin,
    Function.Embedding.toEquivRange_apply, natAdd_castLEEmb_apply]
  have imp : (k + 1).1 = k.1 + 1 := by
    simp [add_def]
    refine Nat.mod_eq_of_lt ?_
    omega
  have res2: i ≤ k + 1 := by
    rw [@le_iff_val_le_val, imp]
    omega
  have : (((j - i).castLT (fininal._proof_3 i j hij)).cycleRange
      (((addNatEmb (n - (n - ↑i))).trans (finCongr _).toEmbedding).toEquivRange.symm ⟨k, kin⟩)) =
      subNat (m := i) (Fin.cast (by omega) (k + 1)) (by simp[res2]) := by
    have : (((addNatEmb (n - (n - ↑i))).trans (finCongr _).toEmbedding).toEquivRange.symm ⟨k, kin⟩)
      = subNat (m := i) (Fin.cast (by omega) (k)) (by simp[h1]) := by
      simp [symm_apply_eq]
      refine eq_of_val_eq ?_
      simp [imp]
      omega
    rw [this]
    have h : (subNat (n := n - i) (↑i) (Fin.cast (by omega) k) (by simp[h1])) <
        ((j - i).castLT (fininal._proof_3 i j hij)):= by
      simp [subNat, lt_iff_val_lt_val, sub_val_of_le hij]
      omega
    have : NeZero (n - ↑i) := by
      refine NeZero.of_pos ?_
      omega
    have : (↑k + 1) % n = k.1 + 1 := Nat.mod_eq_of_lt (by omega)
    simp [cycleRange_of_lt h]
    simp [subNat, add_def, this]
    have : ↑k + 1 - ↑i = k.1 - i.1 + 1:= by omega
    rw [this]
    refine Nat.mod_eq_of_lt ?_
    omega
  simp only [natAdd_castLEEmb, this]
  refine eq_of_val_eq ?_
  simp
  omega

theorem cycleRange_of_eq'' {n : ℕ} {i j : Fin n} (hij : i ≤ j) [NeZero n] :
    (fininal i j hij) j = i := by
  have kin : j ∈ Set.range ⇑(natAdd_castLEEmb n (fininal._proof_4 i)) := by simp; omega
  simp only [fininal,
    Perm.extendDomain_apply_subtype ((j - i).castLT (fininal._proof_3 i j hij)).cycleRange
      (natAdd_castLEEmb n _).toEquivRange kin,
    Function.Embedding.toEquivRange_apply, natAdd_castLEEmb_apply]
  have : (((j - i).castLT (fininal._proof_3 i j hij)).cycleRange
      (((addNatEmb (n - (n - ↑i))).trans (finCongr _).toEmbedding).toEquivRange.symm ⟨j, kin⟩)) =
      subNat (m := i) (Fin.cast (by omega) i) (by simp[hij]) := by
    have : (((addNatEmb (n - (n - ↑i))).trans (finCongr _).toEmbedding).toEquivRange.symm ⟨j, kin⟩)
      = subNat (m := i) (Fin.cast (by omega) (j)) (by simp[hij]) := by
      simp [symm_apply_eq]
      refine eq_of_val_eq ?_
      simp
      omega
    rw [this]
    have h : (subNat (n := n - i) (↑i) (Fin.cast (by omega) j) (by simp[hij])) =
        ((j - i).castLT (fininal._proof_3 i j hij)):= by
      simp [subNat]
      refine eq_of_val_eq ?_
      simp [sub_val_of_le hij]
    have : NeZero (n - ↑i) := by
      refine NeZero.of_pos ?_
      omega
    rw [cycleRange_of_eq (h), Fin.ext_iff]
    simp
  simp only [natAdd_castLEEmb, this]
  refine eq_of_val_eq ?_
  simp
  omega
