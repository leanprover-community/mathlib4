import Mathlib.Data.List.Basic

macro_rules | `($x[$i]'$h) => `(getElem $x $i $h)

@[simp] theorem List.toArrayAux_data : ∀ (l : List α) a, (l.toArrayAux a).data = a.data ++ l
| [], r => (append_nil _).symm
| a::as, r => (toArrayAux_data as (r.push a)).trans $
  by simp [Array.push, append_assoc, List.concat_eq_append]

@[simp] theorem List.toArray_data (l : List α) : l.toArray.data = l := toArrayAux_data _ _

theorem getElem?_pos [GetElem Cont Idx Elem Dom] (a : Cont) (i : Idx) (h : Dom a i) [Decidable (Dom a i)] :
    a[i]? = a[i] :=
  dif_pos h

theorem getElem?_neg [GetElem Cont Idx Elem Dom] (a : Cont) (i : Idx) (h : ¬ Dom a i) [Decidable (Dom a i)] :
    a[i]? = none :=
  dif_neg h

namespace Array

@[simp] theorem toArray_data : (a : Array α) → a.data.toArray = a
| ⟨l⟩ => ext' l.toArray_data

@[simp] theorem get_eq_getElem (a : Array α) (i : Fin a.size) : a.get i = a[i.1] := rfl
@[simp] theorem get?_eq_getElem? (a : Array α) (i : Fin a.size) : a.get? i = a[i.1]? := rfl
@[simp] theorem getData_eq_getElem (a : Array α) (i : Fin _) : a.data.get i = a[i.1] := rfl

theorem getElem?_eq_get (a : Array α) (i : Nat) (h : i < a.size) : a[i]? = a[i] := getElem?_pos _ _ _

theorem get?_len_le (a : Array α) (i : Nat) (h : a.size ≤ i) : a[i]? = none := by
  simp [getElem?_neg, h]

theorem data_get_eq_getElem (a : Array α) (i : Nat) (h : i < a.size) : a.data.get ⟨i, h⟩ = a[i] := by
  by_cases i < a.size <;> simp_all <;> rfl

theorem data_get?_eq_getElem? (a : Array α) (i : Nat) : a.data.get? i = a[i]? := by
  by_cases i < a.size <;> simp_all [getElem?_pos, getElem?_neg, List.get?_eq_get] <;> rfl

theorem get_push_lt (a : Array α) (x : α) (i : Nat) (h : i < a.size) :
    (a.push x)[i]'(by simp_all [Nat.lt_succ_iff, le_of_lt]) = a[i] := by
  simp only [push, ← data_get_eq_getElem, List.concat_eq_append]
  simp [data_get_eq_getElem, List.get_append, getElem?_pos, h]

@[simp] theorem get_push_eq (a : Array α) (x : α) : (a.push x)[a.size] = x := by
  simp only [push, ← data_get_eq_getElem, List.concat_eq_append]
  rw [List.get_append_right] <;> simp [data_get_eq_getElem]

theorem get?_push_lt (a : Array α) (x : α) (i : Nat) (h : i < a.size) :
    (a.push x)[i]? = some a[i] := by
  rw [getElem?_pos, get_push_lt]

theorem get?_push_eq (a : Array α) (x : α) : (a.push x)[a.size]? = some x := by
  rw [getElem?_pos, get_push_eq]

theorem get_push (a : Array α) (x : α) (i : Nat) (h : i < (a.push x).size) :
    (a.push x)[i] = if h : i < a.size then a[i] else x := by
  by_cases i < a.size
  case pos => simp [get_push_lt, *]
  case neg =>
    have : i = a.size := by apply le_antisymm <;> simp_all [Nat.lt_succ_iff]
    simp [get_push_lt, *]

@[simp] lemma get_set_eq (a : Array α) (i : Nat) (h : i < a.size) (v : α) : (a.set ⟨i, h⟩ v)[i]'(by simp_all) = v := by
  simp only [set, ← data_get_eq_getElem, List.get_set_eq]

@[simp] lemma get_set_ne (a : Array α) {i j : Nat} (v : α) (hi : i < a.size) (hj : j < a.size)
    (h : i ≠ j) : (a.set ⟨i, hi⟩ v)[j]'(by simp_all) = a[j] := by
  simp only [set, ← data_get_eq_getElem, List.get_set_ne h]

@[simp] lemma get?_set_eq (a : Array α) (i : Nat) (h : i < a.size) (v : α) : (a.set ⟨i, h⟩ v)[i]? = v := by
  simp [getElem?_pos, *]

@[simp] lemma get?_set_ne (a : Array α) {i j : Nat} (v : α) (hi : i < a.size)
    (h : i ≠ j) : (a.set ⟨i, hi⟩ v)[j]? = a[j]? := by
  by_cases j < a.size <;> simp [getElem?_pos, getElem?_neg, *]

lemma get?_set (a : Array α) (i j : Nat) (hi : i < a.size) (v : α) :
    (a.set ⟨i, hi⟩ v)[j]? = if i = j then some v else a[j]? := by
  by_cases i = j <;> simp [*]

lemma get_set (a : Array α) (i j : Nat) (hi : i < a.size) (hj : j < a.size) (v : α) :
    (a.set ⟨i, hi⟩ v)[j]'(by simp_all) = if i = j then v else a[j] := by
  by_cases i = j <;> simp [*]

end Array
