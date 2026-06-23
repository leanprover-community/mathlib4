import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic

section
variable {ι M : Type*} [CommMonoid M] [AddCommMonoid M] [Fintype ι] {s : Finset ι} {p : ι → Prop}
  [DecidablePred p] {f : ι → M}

/-! ### Big operators over a finset -/

/-- info: ∑ i ∈ s, f i : M -/
#guard_msgs in
#check Finset.sum s fun i ↦ f i

/-- info: ∏ i ∈ s, f i : M -/
#guard_msgs in
#check Finset.prod s fun i ↦ f i

/-- info: ∑ i ∈ s with p i, f i : M -/
#guard_msgs in
#check Finset.sum {j ∈ s | p j} fun i ↦ f i

/-- info: ∏ i ∈ s with p i, f i : M -/
#guard_msgs in
#check Finset.prod {j ∈ s | p j} fun i ↦ f i

/-! ### Big operators over a finset with `funBinderTypes` on -/

set_option pp.funBinderTypes true

/-- info: ∑ i : ι, f i : M -/
#guard_msgs in
#check Finset.sum Finset.univ fun i ↦ f i

/-- info: ∏ i : ι, f i : M -/
#guard_msgs in
#check Finset.prod Finset.univ fun i ↦ f i

/-- info: ∑ i : ι with p i, f i : M -/
#guard_msgs in
#check Finset.sum {j | p j} fun i ↦ f i

/-- info: ∏ i : ι with p i, f i : M -/
#guard_msgs in
#check Finset.prod {j | p j} fun i ↦ f i

/-! ### Big operators over a finset with `funBinderTypes` off -/

set_option pp.funBinderTypes false

/-- info: ∑ i, f i : M -/
#guard_msgs in
#check Finset.sum Finset.univ fun i ↦ f i

/-- info: ∏ i, f i : M -/
#guard_msgs in
#check Finset.prod Finset.univ fun i ↦ f i

/-- info: ∑ i with p i, f i : M -/
#guard_msgs in
#check Finset.sum {j | p j} fun i ↦ f i

/-- info: ∏ i with p i, f i : M -/
#guard_msgs in
#check Finset.prod {j | p j} fun i ↦ f i

/-! ### Big operators over a finset with `pp.analyze` on -/

/-- info: ∑ i, i.toNat : ℕ -/
#guard_msgs in
#check ∑ i : Fin 3, i.toNat

/-- info: ∏ i, i.toNat : ℕ -/
#guard_msgs in
#check ∏ i : Fin 3, i.toNat

/-- info: ∑ i : Fin 3, i.toNat : ℕ -/
#guard_msgs in
set_option pp.analyze true in
#check ∑ i : Fin 3, i.toNat

/-- info: ∏ i : Fin 3, i.toNat : ℕ -/
#guard_msgs in
set_option pp.analyze true in
#check ∏ i : Fin 3, i.toNat

/-- info: ∑ i ∈ s, f i : M -/
#guard_msgs in
set_option pp.analyze true in
#check Finset.sum s fun i ↦ f i

/-- info: ∏ i ∈ s, f i : M -/
#guard_msgs in
set_option pp.analyze true in
#check Finset.prod s fun i ↦ f i

/-- info: ∑ i ∈ s with p i, f i : M -/
#guard_msgs in
set_option pp.analyze true in
#check Finset.sum {j ∈ s | p j} fun i ↦ f i

/-- info: ∏ i ∈ s with p i, f i : M -/
#guard_msgs in
set_option pp.analyze true in
#check Finset.prod {j ∈ s | p j} fun i ↦ f i

/-- info: ∑ i : ι, f i : M -/
#guard_msgs in
set_option pp.analyze true in
#check Finset.sum Finset.univ fun i ↦ f i

/-- info: ∏ i : ι, f i : M -/
#guard_msgs in
set_option pp.analyze true in
#check Finset.prod Finset.univ fun i ↦ f i

/-- info: ∑ i : ι with p i, f i : M -/
#guard_msgs in
set_option pp.analyze true in
#check Finset.sum {j | p j} fun i ↦ f i

/-- info: ∏ i : ι with p i, f i : M -/
#guard_msgs in
set_option pp.analyze true in
#check Finset.prod {j | p j} fun i ↦ f i

end
