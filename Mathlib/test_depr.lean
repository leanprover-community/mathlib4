theorem not_useful (t : True) : True := t

@[deprecated not_useful] theorem True.lhish (t : True) : True := t

@[deprecated True.intro] theorem True.hish : True := .intro

example : True ∧ True := by
  refine ⟨?_, ?_⟩
  exact True.lhish True.hish
  exact True.hish
