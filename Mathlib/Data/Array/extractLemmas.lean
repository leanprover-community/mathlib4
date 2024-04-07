/-
Copyright (c) 2024 Jiecheng Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiecheng Zhao
-/
import Std.Data.Array
/-!
# lemmas about Array.extract

Some useful lemmas about Array.extract
-/
set_option autoImplicit true



namespace Array

theorem extract_len_aux {a : Array α} :
    ∀ i s e,
   (s + i ≤ a.size) →
   List.length (Array.extract.loop a i s e).data = i + e.size:= by
  intro i
  induction i
  intro x h
  simp only [Nat.zero_eq, Nat.add_zero, Nat.zero_add]
  unfold Array.extract.loop
  simp only [dite_eq_ite, ite_self, implies_true]
  intro x e h
  rename_i n n_ih
  unfold Array.extract.loop
  simp only [get_eq_getElem]
  have : x < Array.size a := by
    rw [Nat.add_succ] at h
    have := Nat.lt_of_succ_le h
    apply Nat.lt_of_le_of_lt _ this
    exact Nat.le_add_right x n
  simp only [this, ↓reduceDite]
  rw [show x + Nat.succ n = x + 1 + n by simp_arith] at h
  rw [n_ih (x + 1) (Array.push e a[x]) h]
  simp_arith

theorem extract_loop_len {a : Array α} :
    ∀ i s e,
   (s + i ≤ a.size) →
   (Array.extract.loop a i s e).size = i + e.size:=
    fun i s e a_1 ↦ extract_len_aux i s e a_1

theorem extract_size {a: Array α} : (e ≤ a.size) → (a.extract s e).size = e - s := by
  intro h
  by_cases h2: s ≤ e
  simp [extract, Nat.min_def, h]
  rw [Array.extract_loop_len]
  simp only [size_toArray, List.length_nil, Nat.add_zero]
  rw [Nat.add_comm, Nat.sub_add_cancel]
  exact h
  exact h2
  simp at h2
  rw [extract_empty_of_stop_le_start]
  rw [Nat.sub_eq_zero_of_le]
  exact rfl
  exact Nat.le_of_lt h2
  exact Nat.le_of_succ_le h2

theorem get_eq_list_get {a : Array α } {i : Nat} : (h: i < a.size) → (a[i]'h = a.data[i]'h) :=
  fun _ ↦ rfl

theorem get_append_aux {a b: Array α } (h : i < a.size) : i < (a ++ b).size := by
  simp only [size_append]
  apply Nat.lt_of_lt_of_le h
  exact Nat.le_add_right (size a) (size b)

theorem extract_overflow_eq_extract_to_end {a : Array α} :
  (a.size ≤ l) →  a.extract p l = a.extract p a.size := by
  intro h
  simp [extract, Nat.min_eq_right h]


theorem extract_loop_init_eq_append_aux0 {a e: Array α } : ∀ b, ∀ s, ¬ s < a.size →
  extract.loop a i s (e ++ b) = e ++ extract.loop a i s b := by
  intro b s h
  unfold extract.loop
  simp [h]

theorem append_eq_data_append {b c: Array α } : b ++ c = {data := b.data ++ c.data}
  := by
  apply ext'
  simp only [append_data]

theorem append_push {a b : Array α } : push (a ++ b) e = a ++ push b e := by
  simp [push, append_eq_data_append]

@[simp]
theorem extract_zero_length {a : Array α} :
  a.extract i i = #[] := by
  refine extract_empty_of_stop_le_start a ?h
  exact Nat.le_refl i

theorem extract_loop_take_middle_aux {b c: List α }: ∀ a e : List α ,
  Array.extract.loop {data := (a ++ b ++ c)} b.length a.length {data := e} = {data := (e ++ b)} := by
  induction b
  . unfold extract.loop
    simp only [List.append_nil, size_mk, List.length_append, List.length_nil, dite_eq_ite, ite_self,
      forall_const]
  . rename_i h t tih
    unfold extract.loop
    intro a e
    have :List.length a < List.length a + Nat.succ (List.length t + List.length c) := by
      refine Nat.lt_add_of_pos_right ?h
      exact Nat.zero_lt_succ (List.length t + List.length c)
    simp only [List.append_assoc, List.cons_append, size_mk, List.length_append, List.length_cons,
      this, ↓reduceDite, get_eq_getElem, get_eq_list_get, List.getElem_eq_get]
    have h1:= tih (a ++ [h] ) (e ++ [h])
    have h2:  [] ++ t = t := by simp only [List.nil_append]
    simp only [List.append_assoc, List.cons_append, List.length_append,
      List.length_singleton, h2] at h1
    rw [←h1]
    refine
      congrArg (extract.loop { data := a ++ h :: (t ++ c) } (List.length t) (List.length a + 1))
        ?cons.h
    simp [push]
    exact List.get_of_append rfl rfl

theorem extract_loop_take_middle {bl al : Nat} {l e: Array α } (a b c : Array α):
  l.data = a.data ++ b.data ++ c.data → bl = b.size → al = a.size →
  Array.extract.loop l bl al e = e ++ b := by
  intro h1 h2 h3
  rw [ext' h1, h2, h3, size, size, extract_loop_take_middle_aux]
  refine ext' ?h
  simp only [append_data]

theorem extract_take_middle {l a c: Array α} (b : Array α ):
  j ≤ l.size → l = a ++ b ++ c → a.size = i → b.size = j - i → l.extract i j = b := by
  intro h2 h3 h4 h5
  unfold extract
  simp only [h2, Nat.min_eq_left, Nat.sub_eq, mkEmpty_eq]
  rw [←nil_append b]
  apply extract_loop_take_middle a b c
  simp only [h3, append_data, List.append_assoc]
  rw [h5]
  rw [h4]

theorem extract_self {a: Array α } {al: Nat}: (al = a.size) → Array.extract a 0 al = a := by
  intro h1
  simp only [extract, h1, Nat.min_self, Nat.sub_eq, Nat.sub_zero, mkEmpty_eq]
  rw [extract_loop_take_middle #[] a #[]]
  simp only [nil_append]
  simp only [data_toArray, List.nil_append, List.append_nil]
  exact rfl
  exact rfl

@[simp]
theorem extract_self' {a: Array α } : Array.extract a 0 a.size = a := by
  exact extract_self rfl

theorem extract_succ_start_aux {l: Array α} (h: i < l.size):
  i < j → j ≤ l.size →
  l.extract i j = #[l[i]] ++ l.extract i.succ j := by
  intro h1 h2
  simp only [extract, h2, Nat.min_eq_left, Nat.sub_eq, mkEmpty_eq]
  conv =>
    left
    unfold extract.loop
  have : j - i = (j - i - 1).succ := by
    rw [Nat.succ_eq_add_one]
    refine (Nat.sub_eq_iff_eq_add ?h).mp rfl
    exact Nat.le_sub_of_add_le' h1
  simp only [h, ↓reduceDite, get_eq_getElem]
  rw [this]
  simp only
  rw [extract_loop_eq_aux]
  exact rfl


theorem extract_succ_start {l: Array α} (h: i < l.size):
  i < j →
  l.extract i j = #[l[i]] ++ l.extract i.succ j := by
  by_cases h1: j ≤ l.size
  . exact fun a ↦ extract_succ_start_aux h a h1
  . intro _
    have h2 :l.size ≤ j := by exact Nat.le_of_not_ge h1
    rw [extract_overflow_eq_extract_to_end h2, extract_overflow_eq_extract_to_end h2]
    refine extract_succ_start_aux h h ?_
    exact anyM.proof_1 l


theorem extract_succ_end_aux_0 {α: Type u_1}
{j i: Nat}
{l: Array α}
{h1: j < l.size}
(h2: i ≤ j)
: extract.loop l (Nat.succ j - i) i #[] = extract.loop l (j - i) i #[] ++ #[l[j]'h1] :=
  if h3: i = j
  then by
    rw [h3]
    simp only [Nat.succ_eq_one_add, Nat.add_sub_cancel, Nat.sub_self]
    unfold extract.loop
    simp only [h1, get_eq_getElem, dite_eq_ite, ite_self, nil_append, ↓reduceDite]
    exact extract_loop_zero l (push #[] l[j]) (j + 1)
  else by
    unfold extract.loop
    have h4 : i < l.size := Nat.lt_of_le_of_lt h2 h1
    simp only [h4, ↓reduceDite, get_eq_getElem]
    have h5 : Nat.succ j - i = (j - i).succ := Nat.succ_sub h2
    have h6: i < j := by exact Nat.lt_of_le_of_ne h2 h3
    have h7 : j - i = (j - (i + 1)).succ := by
      rw [Nat.succ_eq_add_one]
      refine (Nat.sub_eq_iff_eq_add ?h).mp rfl
      exact (Nat.le_sub_iff_add_le' h2).mpr h6
    simp [h5, h7]
    have h8: Nat.succ (j - (i + 1)) = Nat.succ j - (i + 1) := by
      rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one, Nat.sub_add_comm]
      exact h6
    rw [extract_loop_eq_aux _ (push #[] l[i]), extract_loop_eq_aux _ (push #[] l[i]), h8]
    rw [extract_succ_end_aux_0, Array.append_assoc]
    exact h6
termination_by j - i

theorem extract_succ_end {l: Array α} (h1: j < l.size) (h2: i ≤ j):
  l.extract i j.succ = l.extract i j ++ #[l[j]] := by
  have h3: j.succ ≤ l.size := by exact h1
  simp only [extract, Nat.min_eq_left h3, Nat.sub_eq, mkEmpty_eq, Nat.min_eq_left (Nat.le_of_lt h1)]
  exact extract_succ_end_aux_0 h2

theorem extract_mid_split {a: Array α} (h1: i ≤ j)  (h2 : j ≤ k) (h3: k ≤ a.size):
   a.extract i k = a.extract i j ++ a.extract j k :=
  if h : j = k
  then by
    rw [h]
    simp only [extract_zero_length, append_nil]
  else by
    have h4: j < k := Nat.lt_of_le_of_ne h2 h
    have h5: j < a.size := Nat.lt_of_lt_of_le h4 h3
    rw [extract_succ_start h5 h4,
      ←append_assoc,
      ←extract_succ_end h5 h1,
      ←extract_mid_split (Nat.le_succ_of_le h1) h4 h3]
termination_by k - j

theorem extract_append_left {a b: Array α} {i j : Nat} (h: j ≤ a.size):
  (a ++ b).extract i j = a.extract i j :=
  if h1 : i ≥ j
  then by
    rw [extract_empty_of_stop_le_start _ h1, extract_empty_of_stop_le_start _ h1]
  else by
    have h2 : i < j := Nat.gt_of_not_le h1
    have hia :i < a.size := Nat.lt_of_lt_of_le h2 h
    have hiab : i < (a++b).size := by
      refine get_append_aux ?h
      exact hia
    rw [extract_succ_start hiab h2,
        extract_succ_start hia h2]
    have : (a ++ b)[i] = a[i] := get_append_left hia
    rw [this, extract_append_left h]
termination_by j - i

theorem extract_append_right {a b: Array α} {i j : Nat} (h: i ≥ a.size):
    (a ++ b).extract i j = b.extract (i - a.size) (j - a.size) :=
  if h1 : i ≥ j
  then by
    rw [extract_empty_of_stop_le_start _ h1, extract_empty_of_stop_le_start]
    exact Nat.sub_le_sub_right h1 (size a)
  else if h2 : i ≥ (a ++ b).size
  then by
    have h3:extract (a ++ b) i j = #[] := extract_empty_of_size_le_start (a ++ b) h2
    have h4:extract b (i - size a) (j - size a) = #[] := by
      apply extract_empty_of_size_le_start
      rw [size_append] at h2
      exact (Nat.le_sub_iff_add_le' h).mpr h2
    rw [h3, h4]
  else by
    simp only [ge_iff_le, Nat.not_le] at h1
    simp only [ge_iff_le, Nat.not_le] at h2
    have hiab: (i - size a) < b.size := by
      rw [size_append] at h2
      exact Nat.sub_lt_left_of_lt_add h h2
    have hiaja: i - size a < j - size a := by
      apply Nat.lt_sub_of_add_lt
      rw [Nat.sub_add_cancel h]
      exact h1
    rw [extract_succ_start h2 h1,
        extract_succ_start hiab hiaja]
    have : (a ++ b)[i] = b[i - a.size] := by exact get_append_right h hiab
    rw [this, extract_append_right (Nat.le_succ_of_le h), Nat.succ_sub h]
  termination_by j - i

theorem extract_extract_aux {a : Array α } : (s1 + s2 ≤ a.size) →
  (s1 + e2 ≤ e1) → (e1 ≤ a.size) →
  (a.extract s1 e1).extract s2 e2 = a.extract (s1 + s2) (s1 + e2) := by
  intro h1 h2 h3
  by_cases h4: e2 ≤ s2
  . have hem0: (a.extract s1 e1).extract s2 e2 = #[] :=
      extract_empty_of_stop_le_start (extract a s1 e1) h4
    have hem1: a.extract (s1 + s2) (s1 + e2) = #[] := by
      apply extract_empty_of_stop_le_start a
      exact Nat.add_le_add_left h4 s1
    rw [hem0, hem1]
  . have hle1: s1 + s2 ≤ s1 + e2 := by
      refine Nat.add_le_add ?h₁ ?h₂
      simp only [Nat.le_refl]
      exact Nat.le_of_not_ge h4
    have :a.extract s1 e1 = a.extract s1 (s1 + s2) ++ a.extract (s1 + s2) e1 := by
      refine extract_mid_split ?h1 ?h2 h3
      exact Nat.le_add_right s1 s2
      apply Nat.le_trans hle1 h2
    have hs1 : s2 ≥ size (extract a s1 (s1 + s2)) := by
      rw [extract_size h1, Nat.add_comm, Nat.add_sub_cancel]
      exact Nat.le_refl s2
    rw [this, extract_append_right hs1]
    simp only [size_extract, h1, Nat.min_eq_left]
    have : (s1 + s2 - s1) = s2 := by
      rw [Nat.add_comm, Nat.add_sub_cancel]
    rw [this, Nat.sub_self]
    have : a.extract (s1 + s2) e1 =
      a.extract (s1 + s2) (s1 + e2) ++ a.extract (s1 + e2) e1 := by
      apply extract_mid_split hle1 h2 h3
    have hs2 : e2 - s2 = size (extract a (s1 + s2) (s1 + e2)) := by
      rw [extract_size (Nat.le_trans h2 h3),
       Nat.sub_add_eq, Nat.add_comm, Nat.add_sub_cancel]
    rw [this, extract_append_left (Nat.le_of_eq hs2), extract_self hs2]

theorem extract_extract {a : Array α } (h1 : s1 + s2 ≤ a.size)
  (h2 : s1 + e2 ≤ e1) :
  (a.extract s1 e1).extract s2 e2 = a.extract (s1 + s2) (s1 + e2) := by
  by_cases h: e1 ≤ a.size
  . exact extract_extract_aux h1 h2 h
  by_cases h3 : s1 + e2 ≤ a.size
  . rw [extract_overflow_eq_extract_to_end (Nat.le_of_not_ge h : e1 ≥ a.size),
        extract_extract_aux h1 _ (anyM.proof_1 a : a.size ≤ a.size)]
    exact h3
  . have h4: s1 + (extract a s1 a.size).size = a.size := by
      have : s1 ≤ a.size := by
        apply Nat.le_trans _  h1
        exact Nat.le_add_right s1 s2
      rw [extract_size (Nat.le_of_eq rfl),
          Nat.add_comm,
          Nat.sub_add_cancel this]
    have h5: e2 ≥ (extract a s1 (size a)).size := by
      apply @Nat.le_of_add_le_add_left s1
      rw [h4]
      exact Nat.le_of_not_ge h3
    rw [extract_overflow_eq_extract_to_end (Nat.le_of_not_ge h : e1 ≥ a.size),
    extract_overflow_eq_extract_to_end (Nat.le_of_not_ge h3 : s1 + e2 ≥ a.size),
    extract_overflow_eq_extract_to_end h5,
    extract_extract_aux h1 (Nat.le_of_eq h4) (Nat.le_of_eq rfl),
    h4]








end Array
