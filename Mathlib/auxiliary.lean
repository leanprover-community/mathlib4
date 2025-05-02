import Mathlib
/-Given an open subset `s` of a real vector space `E`, functions `f : E → E` and `g : E → E` that
  agree on `s` have equal Fréchet derivatives on `s`.-/
lemma eq_fderiv_of_eq_open {E  : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → E} {s : Set E} {x : E} (hx: x ∈ s) (h1: IsOpen s) (h2: Set.EqOn f g s) :
    fderiv ℝ f x = fderiv ℝ g x :=
  (Filter.eventuallyEq_of_mem (h1.mem_nhds hx) h2).fderiv_eq

  #find_home eq_fderiv_of_eq_open
