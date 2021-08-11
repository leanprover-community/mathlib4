import Mathlib.Data.List.Basic

@[simp] theorem List.toArrayAux_data : ∀ (l : List α) a, (l.toArrayAux a).data = a.data ++ l
| [], r => (append_nil _).symm
| a::as, r => (toArrayAux_data as (r.push a)).trans $
  by simp [Array.push, append_assoc, List.concat_eq_append]

@[simp] theorem List.toArray_data (l : List α) : l.toArray.data = l := toArrayAux_data _ _

namespace Array

theorem ext' : {a b : Array α} → a.data = b.data → a = b
| ⟨a⟩, ⟨_⟩, rfl => rfl

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

end Array
