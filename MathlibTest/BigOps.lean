import Mathlib.Algebra.BigOperators.Group.Finset.Basic

section
variable {ι M : Type*} [CommMonoid M] [AddCommMonoid M] [Fintype ι] {s : Finset ι} {p : ι → Prop}
  [DecidablePred p] {f : ι → M}

#guard_expr ∑ i, f i = Finset.sum Finset.univ fun i ↦ f i
#guard_expr ∏ i, f i = Finset.prod Finset.univ fun i ↦ f i
#guard_expr ∑ i ∈ s, f i = Finset.sum s fun i ↦ f i
#guard_expr ∏ i ∈ s, f i = Finset.prod s fun i ↦ f i
#guard_expr ∑ i with p i, f i = Finset.sum {i | p i} fun i ↦ f i
#guard_expr ∏ i with p i, f i = Finset.prod {i | p i} fun i ↦ f i
#guard_expr ∑ i ∈ s with p i, f i = Finset.sum {i ∈ s | p i} fun i ↦ f i
#guard_expr ∏ i ∈ s with p i, f i = Finset.prod {i ∈ s | p i} fun i ↦ f i

end
