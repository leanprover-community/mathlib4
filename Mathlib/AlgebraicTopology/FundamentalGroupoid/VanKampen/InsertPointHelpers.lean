module

public import Mathlib

@[expose] public section

open TopologicalSpace

open scoped unitInterval

noncomputable section

universe u

namespace InsertPointHelpers

/-- Define ts' by inserting t at position m+1 in ts_S. -/
def ts' {n : ℕ} (ts_S : Fin (n + 1) → I) (m : Fin n) (t : I) (i : Fin (n + 2)) : I :=
  if h : i.val ≤ m.val then
    ts_S ⟨i.val, by omega⟩
  else if i.val = m.val + 1 then
    t
  else
    ts_S ⟨i.val - 1, by omega⟩

/-- Define covers' by duplicating covers_S at position m. -/
def covers' {X : Type*} [TopologicalSpace X] {n : ℕ} (covers_S : Fin n → Opens X) (m : Fin n) (i : Fin (n + 1)) : Opens X :=
  if h : i.val ≤ m.val then
    covers_S ⟨i.val, by omega⟩
  else
    covers_S ⟨i.val - 1, by omega⟩

-- Helper lemmas for ts'
lemma ts'_at_before {n : ℕ} {ts_S : Fin (n + 1) → I} {m : Fin n} {t : I} {i : Fin (n + 2)}
    (h : i.val ≤ m.val) :
    ts' ts_S m t i = ts_S ⟨i.val, by omega⟩ := by
  unfold ts'
  exact dif_pos h

lemma ts'_at_mid {n : ℕ} {ts_S : Fin (n + 1) → I} {m : Fin n} {t : I} {i : Fin (n + 2)}
    (h1 : ¬(i.val ≤ m.val)) (h2 : i.val = m.val + 1) :
    ts' ts_S m t i = t := by
  unfold ts'
  rw [dif_neg h1]
  rw [if_pos h2]

lemma ts'_at_after {n : ℕ} {ts_S : Fin (n + 1) → I} {m : Fin n} {t : I} {i : Fin (n + 2)}
    (h1 : ¬(i.val ≤ m.val)) (h2 : ¬(i.val = m.val + 1)) :
    ts' ts_S m t i = ts_S ⟨i.val - 1, by omega⟩ := by
  unfold ts'
  rw [dif_neg h1]
  rw [if_neg h2]

-- Helper lemmas for covers'
lemma covers'_at_le {X : Type*} [TopologicalSpace X] {n : ℕ} {covers_S : Fin n → Opens X} {m : Fin n} {i : Fin (n + 1)}
    (h : i.val ≤ m.val) :
    covers' covers_S m i = covers_S ⟨i.val, by omega⟩ := by
  unfold covers'
  exact dif_pos h

lemma covers'_at_gt {X : Type*} [TopologicalSpace X] {n : ℕ} {covers_S : Fin n → Opens X} {m : Fin n} {i : Fin (n + 1)}
    (h : ¬(i.val ≤ m.val)) :
    covers' covers_S m i = covers_S ⟨i.val - 1, by omega⟩ := by
  unfold covers'
  exact dif_neg h

variable {X : Type u} [TopologicalSpace X]
variable {x y : X} {γ : Path x y} {S : Finset I} {t : I}
variable {n : ℕ}
variable {ts_S : Fin (n + 1) → I}
variable {m : Fin n}
variable {covers_S : Fin n → Opens X}
variable {𝒰 : Set (Opens X)}

/-- Prove that ts' is strictly monotone. -/
lemma ts'_strict
    (h_ts_S_strict : StrictMono ts_S)
    (h_m_left : ts_S (Fin.castSucc m) < t)
    (h_m_right : t < ts_S (Fin.succ m)) :
    StrictMono (ts' ts_S m t) := by
  intro i j h
  have h_ij : i.val < j.val := Fin.lt_iff_val_lt_val.mp h
  -- Case analysis on where i and j fall relative to m.val and m.val + 1
  by_cases h_i_le : i.val ≤ m.val
  · -- i ≤ m
    by_cases h_j_le : j.val ≤ m.val
    · -- j ≤ m: both before insertion point
      rw [ts'_at_before h_i_le, ts'_at_before h_j_le]
      exact h_ts_S_strict (by apply Fin.lt_iff_val_lt_val.mpr; omega)
    · -- j > m
      by_cases h_j_eq : j.val = m.val + 1
      · -- j = m + 1: j is at the insertion point
        rw [ts'_at_before h_i_le, ts'_at_mid (by omega) h_j_eq]
        have h1 : ts_S ⟨i.val, by omega⟩ ≤ ts_S (Fin.castSucc m) :=
          h_ts_S_strict.monotone (by apply Fin.le_iff_val_le_val.mpr; simp [Fin.castSucc] <;> omega)
        exact lt_of_le_of_lt h1 h_m_left
      · -- j > m + 1: j is after insertion point
        rw [ts'_at_before h_i_le, ts'_at_after (by omega) h_j_eq]
        have h_j_ge : j.val ≥ m.val + 2 := by
          have h1 : m.val < j.val := by omega
          have h2 : j.val ≠ m.val + 1 := h_j_eq
          omega
        have h_lt : i.val < j.val - 1 := by omega
        let i' : Fin (n + 1) := ⟨i.val, by omega⟩
        let j' : Fin (n + 1) := ⟨j.val - 1, by omega⟩
        have h_fin_lt : i' < j' := by
          apply Fin.lt_iff_val_lt_val.mpr
          omega
        exact h_ts_S_strict h_fin_lt
  · -- i > m
    have h_i_gt : i.val > m.val := by omega
    by_cases h_i_eq : i.val = m.val + 1
    · -- i = m + 1: i is at insertion point
      by_cases h_j_eq : j.val = m.val + 1
      · omega
      · -- j > m + 1: j is after insertion point
        rw [ts'_at_mid (by omega) h_i_eq, ts'_at_after (by omega) h_j_eq]
        have h1 : t < ts_S (Fin.succ m) := h_m_right
        have h2 : ts_S (Fin.succ m) ≤ ts_S ⟨j.val - 1, by omega⟩ :=
          h_ts_S_strict.monotone (by apply Fin.le_iff_val_le_val.mpr; simp [Fin.succ] <;> omega)
        exact lt_of_lt_of_le h1 h2
    · -- i > m + 1: both after insertion point
      have h_i_gt2 : i.val > m.val + 1 := by omega
      rw [ts'_at_after (by omega) h_i_eq, ts'_at_after (by omega) (by omega)]
      have h_lt : i.val - 1 < j.val - 1 := by omega
      exact h_ts_S_strict (Fin.lt_iff_val_lt_val.mpr h_lt)

/-- Prove that the image of ts' is S ∪ {t}. -/
lemma ts'_image
    (h_ts_S_strict : StrictMono ts_S)
    (h_ts_S_image : Finset.image ts_S Finset.univ = S) :
    Finset.image (ts' ts_S m t) Finset.univ = S ∪ {t} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton]
  constructor
  · -- Forward direction: x ∈ image ts' → x ∈ S ∨ x = t
    rintro ⟨i, rfl⟩
    by_cases h1 : i.val ≤ m.val
    · rw [ts'_at_before h1]
      left
      have h_in : ts_S ⟨i.val, by omega⟩ ∈ Finset.image ts_S Finset.univ :=
        Finset.mem_image.mpr ⟨⟨i.val, by omega⟩, Finset.mem_univ _, rfl⟩
      rw [h_ts_S_image] at h_in
      exact h_in
    · by_cases h2 : i.val = m.val + 1
      · rw [ts'_at_mid h1 h2]
        right
        rfl
      · rw [ts'_at_after h1 h2]
        left
        have h_in : ts_S ⟨i.val - 1, by omega⟩ ∈ Finset.image ts_S Finset.univ :=
          Finset.mem_image.mpr ⟨⟨i.val - 1, by omega⟩, Finset.mem_univ _, rfl⟩
        rw [h_ts_S_image] at h_in
        exact h_in
  · -- Backward direction: x ∈ S ∨ x = t → x ∈ image ts'
    rintro (h | rfl)
    · -- x ∈ S
      have h_x_in : x ∈ Finset.image ts_S Finset.univ := by rw [h_ts_S_image] <;> exact h
      rcases Finset.mem_image.mp h_x_in with ⟨k, _, rfl⟩
      by_cases h_k_le : k.val ≤ m.val
      · -- k ≤ m: use i = k (cast to Fin (n+2))
        let i : Fin (n + 2) := ⟨k.val, by omega⟩
        have h_i_le : i.val ≤ m.val := by exact h_k_le
        refine ⟨i, ?_⟩
        rw [ts'_at_before h_i_le]
        <;> simp [i]
      · -- k > m: use i = k.val + 1
        let i : Fin (n + 2) := ⟨k.val + 1, by omega⟩
        have h1 : ¬(i.val ≤ m.val) := by simp [i] <;> omega
        have h2 : ¬(i.val = m.val + 1) := by simp [i] <;> omega
        refine ⟨i, ?_⟩
        rw [ts'_at_after h1 h2]
        <;> simp [i] <;> omega
    · -- x = t: use i = m.val + 1
      let i : Fin (n + 2) := ⟨m.val + 1, by omega⟩
      have h1 : ¬(i.val ≤ m.val) := by simp [i] <;> omega
      have h2 : i.val = m.val + 1 := by simp [i] <;> omega
      refine ⟨i, ?_⟩
      rw [ts'_at_mid h1 h2]

/-- Prove that covers' are all in 𝒰. -/
lemma covers'_mem
    (hcover_mem_S : ∀ i, covers_S i ∈ 𝒰) :
    ∀ (i : Fin (n + 1)), covers' covers_S m i ∈ 𝒰 := by
  intro i
  by_cases h : i.val ≤ m.val
  · rw [covers'_at_le h]
    exact hcover_mem_S ⟨i.val, by omega⟩
  · rw [covers'_at_gt h]
    exact hcover_mem_S ⟨i.val - 1, by omega⟩

/-- Prove that covers' satisfy the range condition. -/
lemma covers'_range
    (h_ts_S_strict : StrictMono ts_S)
    (h_m_left : ts_S (Fin.castSucc m) < t)
    (h_m_right : t < ts_S (Fin.succ m))
    (h_range_S : ∀ i, ∀ (t_val : I), ts_S (Fin.castSucc i) ≤ t_val → t_val ≤ ts_S (Fin.succ i) → γ t_val ∈ (covers_S i : Set X)) :
    ∀ (i : Fin (n + 1)) (t_val : I),
      ts' ts_S m t (Fin.castSucc i) ≤ t_val →
      t_val ≤ ts' ts_S m t (Fin.succ i) →
      γ t_val ∈ (↑(covers' covers_S m i) : Set X) := by
  intro i t_val h1 h2
  by_cases h_i_lt : i.val < m.val
  · -- Case 1: i.val < m.val (strictly before m)
    have h_i_lt_n : i.val < n := by omega
    let j : Fin n := ⟨i.val, h_i_lt_n⟩
    have h_covers_eq : (covers' covers_S m i : Opens X) = covers_S j := by
      rw [covers'_at_le (by omega)]
      <;> rfl
    rw [h_covers_eq]
    have h_castSucc_le : (Fin.castSucc i).val ≤ m.val := by simp [Fin.castSucc] <;> omega
    have h_succ_le : (Fin.succ i).val ≤ m.val := by simp [Fin.succ] <;> omega
    have h_ts1 : ts' ts_S m t (Fin.castSucc i) = ts_S (Fin.castSucc j) := by
      rw [ts'_at_before h_castSucc_le]
      <;> rfl
    have h_ts2 : ts' ts_S m t (Fin.succ i) = ts_S (Fin.succ j) := by
      rw [ts'_at_before h_succ_le]
      <;> rfl
    have h1' : ts_S (Fin.castSucc j) ≤ t_val := by rw [←h_ts1]; exact h1
    have h2' : t_val ≤ ts_S (Fin.succ j) := by rw [←h_ts2]; exact h2
    exact h_range_S j t_val h1' h2'
  · -- Case 2: i.val ≥ m.val
    by_cases h_i_eq_m : i.val = m.val
    · -- Subcase 2a: i.val = m.val (exactly at m)
      have h_i_le : i.val ≤ m.val := by omega
      have h_covers_eq : (covers' covers_S m i : Opens X) = covers_S m := by
        rw [covers'_at_le h_i_le]
        apply congr_arg covers_S
        apply Fin.ext
        exact h_i_eq_m
      rw [h_covers_eq]
      have h_castSucc_le : (Fin.castSucc i).val ≤ m.val := by
        simp [Fin.castSucc, h_i_eq_m] <;> omega
      have h_ts1 : ts' ts_S m t (Fin.castSucc i) = ts_S (Fin.castSucc m) := by
        rw [ts'_at_before h_castSucc_le]
        apply congr_arg ts_S
        apply Fin.ext
        have h_eq : (Fin.castSucc i).val = (Fin.castSucc m).val := by
          simp [Fin.castSucc, h_i_eq_m]
        exact h_eq
      have h_succ_mid : (Fin.succ i).val = m.val + 1 := by
        simp [Fin.succ, h_i_eq_m] <;> omega
      have h_ts2 : ts' ts_S m t (Fin.succ i) = t :=
        ts'_at_mid (by omega) h_succ_mid
      have h1' : ts_S (Fin.castSucc m) ≤ t_val := by rw [←h_ts1]; exact h1
      have h2' : t_val ≤ t := by rw [←h_ts2]; exact h2
      have h3 : t_val ≤ ts_S (Fin.succ m) := by
        exact le_of_lt (lt_of_le_of_lt h2' h_m_right)
      exact h_range_S m t_val h1' h3
    · -- Subcase 2b: i.val > m.val
      have h_i_gt_m : i.val > m.val := by omega
      by_cases h_i_eq_succ : i.val = m.val + 1
      · -- Subsubcase 2b1: i.val = m.val + 1 (right after insertion point)
        have h_sub : i.val - 1 = m.val := by omega
        have h_covers_eq : (covers' covers_S m i : Opens X) = covers_S m := by
          rw [covers'_at_gt (by omega)]
          apply congr_arg covers_S
          apply Fin.ext
          exact h_sub
        rw [h_covers_eq]
        have h_castSucc_mid : (Fin.castSucc i).val = m.val + 1 := by
          simp [Fin.castSucc, h_i_eq_succ] <;> omega
        have h_ts1 : ts' ts_S m t (Fin.castSucc i) = t :=
          ts'_at_mid (by omega) h_castSucc_mid
        have h_succ_gt1 : ¬((Fin.succ i).val ≤ m.val) := by
          simp [Fin.succ, h_i_eq_succ] <;> omega
        have h_succ_gt2 : ¬((Fin.succ i).val = m.val + 1) := by
          simp [Fin.succ, h_i_eq_succ] <;> omega
        have h_ts2 : ts' ts_S m t (Fin.succ i) = ts_S (Fin.succ m) := by
          rw [ts'_at_after h_succ_gt1 h_succ_gt2]
          <;> apply congr_arg ts_S
          <;> apply Fin.ext
          <;> simp [Fin.succ, h_i_eq_succ] <;> omega
        have h1' : t ≤ t_val := by rw [←h_ts1]; exact h1
        have h2' : t_val ≤ ts_S (Fin.succ m) := by rw [←h_ts2]; exact h2
        have h3 : ts_S (Fin.castSucc m) ≤ t_val := by
          exact le_of_lt (lt_of_lt_of_le h_m_left h1')
        exact h_range_S m t_val h3 h2'
      · -- Subsubcase 2b2: i.val > m.val + 1 (strictly after insertion point)
        have h_i_gt_succ : i.val > m.val + 1 := by omega
        rw [covers'_at_gt (by omega)]
        have h_k_ok : i.val - 1 < n := by omega
        let k : Fin n := ⟨i.val - 1, h_k_ok⟩
        have h_k_val : k.val = i.val - 1 := by
          exact rfl
        have h_castSucc_gt1 : ¬((Fin.castSucc i).val ≤ m.val) := by
          simp [Fin.castSucc] <;> omega
        have h_castSucc_gt2 : ¬((Fin.castSucc i).val = m.val + 1) := by
          simp [Fin.castSucc] <;> omega
        have h_ts1 : ts' ts_S m t (Fin.castSucc i) = ts_S (Fin.castSucc k) := by
          rw [ts'_at_after h_castSucc_gt1 h_castSucc_gt2]
          apply congr_arg ts_S
          apply Fin.ext
          simp [Fin.castSucc, h_k_val] <;> omega
        have h_succ_gt1 : ¬((Fin.succ i).val ≤ m.val) := by
          simp [Fin.succ] <;> omega
        have h_succ_gt2 : ¬((Fin.succ i).val = m.val + 1) := by
          simp [Fin.succ] <;> omega
        have h_ts2 : ts' ts_S m t (Fin.succ i) = ts_S (Fin.succ k) := by
          rw [ts'_at_after h_succ_gt1 h_succ_gt2]
          apply congr_arg ts_S
          apply Fin.ext
          simp [Fin.succ, h_k_val] <;> omega
        have h1' : ts_S (Fin.castSucc k) ≤ t_val := by rw [←h_ts1]; exact h1
        have h2' : t_val ≤ ts_S (Fin.succ k) := by rw [←h_ts2]; exact h2
        have h_main : γ t_val ∈ (covers_S k : Set X) := h_range_S k t_val h1' h2'
        simpa [k] using h_main

end InsertPointHelpers

end

end
