import Mathlib.Algebra.BigOperators.Group.Finset.Basic

section
variable {ι M : Type*} [CommMonoid M] [AddCommMonoid M] [Fintype ι] {s : Finset ι} {p : ι → Prop}
  [DecidablePred p] {f : ι → M}


/-- info: ∑ i : ι, f i : M -/
#guard_msgs in
#check Finset.sum Finset.univ fun i ↦ f i

/-- info: ∏ i : ι, f i : M -/
#guard_msgs in
#check Finset.prod Finset.univ fun i ↦ f i

/-- info: ∑ i ∈ s, f i : M -/
#guard_msgs in
#check Finset.sum s fun i ↦ f i

/-- info: ∏ i ∈ s, f i : M -/
#guard_msgs in
#check Finset.prod s fun i ↦ f i

/-- info: ∑ i with p i, f i : M -/
#guard_msgs in
#check Finset.sum {j | p j} fun i ↦ f i

/-- info: ∏ i with p i, f i : M -/
#guard_msgs in
#check Finset.prod {j | p j} fun i ↦ f i

/-- info: ∑ i ∈ s with p i, f i : M -/
#guard_msgs in
#check Finset.sum {j ∈ s | p j} fun i ↦ f i

/-- info: ∏ i ∈ s with p i, f i : M -/
#guard_msgs in
#check Finset.prod {j ∈ s | p j} fun i ↦ f i

end
