theorem length_append (L M : List α) : (L ++ M).length = L.length + M.length := by
  induction L with
  | nil =>
    rw [List.nil_append, List.length_nil, Nat.zero_add]
  | cons x L' ih =>
    rw [List.cons_append, List.length_cons, List.length_cons, Nat.succ_add, ih]
