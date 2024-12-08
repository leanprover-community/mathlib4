universe u v w
variable {α : Type u} {β : Type v}

namespace List

/--
This function is provide as a more efficient runtime alternative to `(l.map f).toArray`.
For verification purposes, we immediately simplify it to that form.
-/
def toArrayMap (l : List α) (f : α → β) : Array β := l.foldl (init := #[]) fun acc x ↦ acc.push (f x)

-- Future: a toArrayMapM version could be useful (e.g. in DeriveToExpr)
-- def toArrayMapM {m : Type v → Type w} [Monad m] (l : List α) (f : α → m β) : m (Array β) :=
--   l.foldlM (init := #[]) fun acc x ↦ acc.push (f x)

/-- info: #[3, 4, 5, 6] -/
#guard_msgs in
#eval toArrayMap [0, 1, 2, 3] (fun n ↦ n + 3)

theorem toArrayMap_toList (l : List α) (f : α → β ) : (l.toArrayMap f).toList = l.map f := by
  suffices ∀ (arr : Array β),
    (l.foldl (init := arr) fun acc x ↦ acc.push (f x)).toList = arr.toList ++ l.map f from
    this #[]
  induction l with
  | nil => simp
  | cons head tail tail_ih =>
    intro arr
    have : arr.toList ++ f head :: map f tail = (arr.push (f head)).toList ++ map f tail := by simp
    rw [List.foldl_cons, List.map_cons, this, ← tail_ih]

@[simp]
theorem toArrayMap_eq_toArray_map (l : List α) (f : α → β) : l.toArrayMap f = (l.map f).toArray :=
  Array.ext' (by simpa using toArrayMap_toList l f)

end List
