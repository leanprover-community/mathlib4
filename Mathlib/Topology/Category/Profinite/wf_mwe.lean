import Mathlib.Data.List.Lex

variable (α : Type _) [LinearOrder α] [IsWellFounded α (·<·)]

instance : IsWellFounded {l : List α // l.Chain' (·>·)}
    (fun l m ↦ List.Lex (·<·) l.val m.val) :=
  sorry
