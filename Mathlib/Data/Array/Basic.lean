import Mathlib.Data.List.Basic
import Mathlib.Tactic.HaveI
import Mathlib.Tactic.Simpa

macro_rules | `($x[$i]'$h) => `(getElem $x $i $h)

@[simp] theorem getElem_fin [GetElem Cont Nat Elem Dom] (a : Cont) (i : Fin n) (h : Dom a i) :
    a[i] = a[i.1] := rfl

@[simp] theorem getElem?_fin [GetElem Cont Nat Elem Dom] (a : Cont) (i : Fin n)
    [Decidable (Dom a i)] : a[i]? = a[i.1]? := rfl

@[simp] theorem getElem!_fin [GetElem Cont Nat Elem Dom] (a : Cont) (i : Fin n)
    [Decidable (Dom a i)] [Inhabited Elem] : a[i]! = a[i.1]! := rfl

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

@[simp] theorem get_eq_getElem (a : Array α) (i : Fin a.size) : a.get i = a[i] := rfl
@[simp] theorem get?_eq_getElem? (a : Array α) (i : Fin a.size) : a.get? i = a[i]? := rfl
@[simp] theorem getData_eq_getElem (a : Array α) (i : Fin _) : a.data.get i = a[i] := rfl

theorem getElem?_eq_get (a : Array α) (i : Nat) (h : i < a.size) : a[i]? = a[i] := getElem?_pos _ _ _

theorem get?_len_le (a : Array α) (i : Nat) (h : a.size ≤ i) : a[i]? = none := by
  simp [getElem?_neg, h]

theorem data_get_eq_getElem (a : Array α) (i : Nat) (h : i < a.size) : a.data.get ⟨i, h⟩ = a[i] := by
  by_cases i < a.size <;> simp_all <;> rfl

theorem data_get?_eq_getElem? (a : Array α) (i : Nat) : a.data.get? i = a[i]? := by
  by_cases i < a.size <;> simp_all [getElem?_pos, getElem?_neg, List.get?_eq_get] <;> rfl

theorem get_push_lt (a : Array α) (x : α) (i : Nat) (h : i < a.size) :
    haveI : i < (a.push x).size := by simp_all [Nat.lt_succ_iff, le_of_lt]
    (a.push x)[i] = a[i] := by
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

@[simp]
theorem size_mkEmpty : (mkEmpty n : Array α).size = 0 := rfl

@[simp]
theorem size_mapIdxM_map (as : Array α) (bs : Array β) (f : Fin as.size → α → Id β) (i j h) (hj : j = bs.size) :
    (Array.mapIdxM.map as f i j h bs).size = as.size := by
  induction i generalizing j bs
  case zero => subst hj; simp [mapIdxM.map, ← h]
  case succ i ih =>
    simp only [mapIdxM.map, Id.bind_eq]
    rw [ih]
    simp [hj]

@[simp]
theorem size_mapIdxM_Id (a : Array α) (f : Fin a.size → α → Id β) :
    (a.mapIdxM f).size = a.size := by
  simp [mapIdxM, size_mapIdxM_map]

@[simp]
theorem size_mapIdx (a : Array α) (f : Fin a.size → α → β) : (a.mapIdx f).size = a.size := by
  simp [mapIdx, Id.run]

theorem getElem_mapIdxM_map (as : Array α) (bs : Array β) (f : Fin as.size → α → Id β) (i j h)
    (hj : j = bs.size) (k) (hk : k < as.size)
    (hbs : ∀ k' (hk' : k' < bs.size),
      haveI : k' < as.size := by rw [← h, hj, Nat.add_comm]; exact Nat.lt_add_right _ _ _ hk'
      bs[k'] = f ⟨k', this⟩ as[k']) :
    (Id.run (Array.mapIdxM.map as f i j h bs))[k]'(by simp_all [Id.run]) = f ⟨k, hk⟩ as[k] := by
  induction i generalizing j bs
  case zero => erw [hbs]
  case succ i ih =>
    simp only [mapIdxM.map, Id.bind_eq]
    rw [ih]
    · simp [hj]
    · intro k' hk'
      rw [get_push]
      cases (lt_or_eq_of_le <| Nat.le_of_lt_succ (by simpa using hk'))
      case inl hk' => simp [hk', hbs]
      case inr hk' => simp_all

@[simp]
theorem getElem_mapIdx (a : Array α) (f : Fin a.size → α → β) (i : Nat) (h) :
    haveI : i < a.size := by simp_all
    (a.mapIdx f)[i]'(h) = f ⟨i, this⟩ a[i] := by
  simp only [mapIdx, mapIdxM]
  rw [getElem_mapIdxM_map]
  · simp
  · intro k hk; simp at hk; contradiction

@[simp]
theorem size_swap! (a : Array α) (i j) (hi : i < a.size) (hj : j < a.size) : (a.swap! i j).size = a.size := by
  simp [swap!, hi, hj]

theorem size_reverse_rev (mid i) (a : Array α) (h : mid ≤ a.size) : (Array.reverse.rev a.size mid a i).size = a.size :=
  if hi : i < mid then by
    unfold Array.reverse.rev
    have : i < a.size := lt_of_lt_of_le hi h
    have : a.size - i - 1 < a.size := Nat.sub_lt_self i.zero_lt_succ this
    have := Array.size_reverse_rev mid (i+1) (a.swap! i (a.size - i - 1))
    simp_all
  else by
    unfold Array.reverse.rev
    simp [dif_neg hi]
termination_by _ => mid - i

@[simp]
theorem size_reverse (a : Array α) : a.reverse.size = a.size := by
  have := size_reverse_rev (a.size / 2) 0 a (Nat.div_le_self ..)
  simp only [reverse, this]

@[simp]
theorem size_ofFn_loop (n) (f : Fin n → α) (i acc) : (ofFn.loop n f i acc).size = acc.size + (n - i) :=
  if hin : i < n then by
    unfold ofFn.loop
    have : 1 + (n - (i + 1)) = n - i :=
      Nat.sub_sub .. ▸ Nat.add_sub_cancel' (Nat.le_sub_of_add_le (Nat.add_comm .. ▸ hin))
    rw [dif_pos hin, size_ofFn_loop n f (i+1), size_push, Nat.add_assoc, this]
  else by
    have : n - i = 0 := Nat.sub_eq_zero_of_le (le_of_not_lt hin)
    unfold ofFn.loop
    simp [hin, this]
termination_by size_ofFn_loop n f i acc => n - i

@[simp]
theorem size_ofFn (f : Fin n → α) : (ofFn n f).size = n := by
  simp [ofFn]

@[simp]
theorem getElem_ofFn_loop (n) (f : Fin n → α) (i acc) (k : Nat) (hki : k < n) (hin : i ≤ n) (hi : i = acc.size)
    (hacc : ∀ j, ∀ hj : j < acc.size, acc[j] = f ⟨j, lt_of_lt_of_le hj (by simp_all)⟩) :
    haveI : acc.size + (n - acc.size) = n := Nat.add_sub_cancel' (hi ▸ hin)
    (ofFn.loop n f i acc)[k]'(by simp_all) = f ⟨k, hki⟩ :=
  if hin : i < n then by
    unfold ofFn.loop
    have : 1 + (n - (i + 1)) = n - i :=
      Nat.sub_sub .. ▸ Nat.add_sub_cancel' (Nat.le_sub_of_add_le (Nat.add_comm .. ▸ hin))
    simp only [dif_pos hin]
    rw [getElem_ofFn_loop n f (i+1) _ k _ hin (by simp_all) (fun j hj => ?hacc)]
    cases (lt_or_eq_of_le <| Nat.le_of_lt_succ (by simpa using hj))
    case inl hj => simp [get_push, hj, hacc j hj]
    case inr hj => simp_all [get_push]
  else by
    unfold ofFn.loop
    simp [hin, hacc k (lt_of_lt_of_le hki (le_of_not_gt (hi ▸ hin)))]
termination_by
  getElem_ofFn_loop n f i acc k hki hin hi hacc => n - i

@[simp]
theorem getElem_ofFn (f : Fin n → α) (i : Nat) (h) : (ofFn n f)[i] = f ⟨i, by simp_all⟩ := by
  unfold ofFn
  rw [getElem_ofFn_loop] <;> try {simp}
  · intro j hj; simp at hj; contradiction

end Array
