import Mathlib.Data.List.Basic

@[simp] theorem List.toArrayAux_data : ∀ (l : List α) a, (l.toArrayAux a).data = a.data ++ l
| [], r => (append_nil _).symm
| a::as, r => (toArrayAux_data as (r.push a)).trans $
  by simp [Array.push, append_assoc, List.concat_eq_append]

@[simp] theorem List.toArray_data (l : List α) : l.toArray.data = l := toArrayAux_data _ _

namespace Array

theorem ext' : {a b : Array α} → a.data = b.data → a = b
| ⟨_⟩, ⟨_⟩, rfl => rfl

@[simp] theorem data_toArray : (a : Array α) → a.data.toArray = a
| ⟨l⟩ => ext' l.toArray_data

-- Port note: The Lean 4 core library has `toArrayLit_eq` with the same signature as this,
-- but currently its proof is `sorry`.
theorem toArrayLit_eq' (a : Array α) (n : Nat) (hsz : a.size = n) : a = toArrayLit a n hsz := by
  have := aux n
  rw [List.drop_eq_nil_of_le (Nat.le_of_eq hsz)] at this
  exact (data_toArray a).symm.trans $ congrArg List.toArray (this _).symm
where
  aux : ∀ i hi, toListLitAux a n hsz i hi (a.data.drop i) = a.data
  | 0, _ => rfl
  | i+1, hi => by
    simp [toListLitAux]
    suffices _::_ = _ by rw [this]; apply aux
    apply List.get_cons_drop

theorem get_eq_get (a : Array α) (i : Fin _) :
  a.get i = a.data.get i := rfl

theorem get?_eq_get (a : Array α) (i : Nat) (h : i < a.size) :
  a.get? i = some (a.get ⟨i, h⟩) := by simp [get?, h]

theorem get?_len_le (a : Array α) (i : Nat) (h : a.size ≤ i) :
  a.get? i = none := by simp [get?, not_lt_of_ge h]

theorem get?_eq_get? (a : Array α) (i : Nat) :
  a.get? i = a.data.get? i := by
  simp [get?]; split <;> rename_i h
  · simp [get, List.get?_eq_get h]
  · simp [List.get?_len_le (le_of_not_lt h)]

theorem get?_push_lt (a : Array α) (x : α) (i : Nat) (h : i < a.size) :
  (a.push x).get? i = some (a.get ⟨i, h⟩) := by
  simp [push, get?_eq_get?, ← List.get?_eq_get, get_eq_get, List.concat_eq_append]
  exact List.get?_append h

theorem get?_push_eq (a : Array α) (x : α) :
  (a.push x).get? a.size = some x := by
  simp [push, get?_eq_get?, ← List.get?_eq_get, get_eq_get, List.concat_eq_append]

theorem get_push (a : Array α) (x : α) (i) :
  (a.push x).get i = if h : i < a.size then a.get ⟨i, h⟩ else x := by
  split <;> (rename_i h; apply Option.some.inj; rw [← get?_eq_get])
  · apply get?_push_lt
  · match i with | ⟨i, hi⟩ => ?_
    simp at hi ⊢
    rw [le_antisymm (Nat.le_of_lt_succ hi) (le_of_not_lt h), get?_push_eq]

@[simp] lemma get?_set_eq (a : Array α) (i) (v : α) : (a.set i v).get? i = v := by
  simp [set, get?_eq_get?, List.get?_set_of_lt _ i.2]

@[simp] lemma get?_set_ne (a : Array α) {i j} (v : α)
  (h : i.1 ≠ j) : (a.set i v).get? j = a.get? j := by
  simp [set, get?_eq_get?, List.get?_set_ne _ _ h]

lemma get?_set (a : Array α) (i j) (v : α) :
  (a.set i v).get? j = if i.1 = j then some v else a.get? j := by
  split; {subst j; simp}; simp_all

end Array
