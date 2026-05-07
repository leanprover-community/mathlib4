import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
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

/-! ### Big operators over ordered sets -/

variable {g : ℕ → M} {q : ℕ → Prop} [DecidablePred q] {n : ℕ} {i₀ : ι}

/-- info: ∏ i < n, g i : M -/
#guard_msgs in
#check Finset.prod (Finset.Iio n) fun i ↦ g i

/-- info: ∏ i ≤ n, g i : M -/
#guard_msgs in
#check Finset.prod (Finset.Iic n) fun i ↦ g i

/-- info: ∏ i < n with q i, g i : M -/
#guard_msgs in
#check Finset.prod ((Finset.Iio n).filter q) fun i ↦ g i

/-- info: ∏ i ≤ n with q i, g i : M -/
#guard_msgs in
#check Finset.prod ((Finset.Iic n).filter q) fun i ↦ g i

section Bot
variable [Preorder ι] [LocallyFiniteOrderBot ι]

/-- info: ∏ i < i₀, f i : M -/
#guard_msgs in
#check Finset.prod (Finset.Iio i₀) fun i ↦ f i

/-- info: ∏ i ≤ i₀, f i : M -/
#guard_msgs in
#check Finset.prod (Finset.Iic i₀) fun i ↦ f i

/-- info: ∏ i < i₀ with p i, f i : M -/
#guard_msgs in
#check Finset.prod ((Finset.Iio i₀).filter p) fun i ↦ f i

/-- info: ∏ i ≤ i₀ with p i, f i : M -/
#guard_msgs in
#check Finset.prod ((Finset.Iic i₀).filter p) fun i ↦ f i

end Bot

section Top
variable [Preorder ι] [LocallyFiniteOrderTop ι]

/-- info: ∏ i > i₀, f i : M -/
#guard_msgs in
#check Finset.prod (Finset.Ioi i₀) fun i ↦ f i

/-- info: ∏ i ≥ i₀, f i : M -/
#guard_msgs in
#check Finset.prod (Finset.Ici i₀) fun i ↦ f i

/-- info: ∏ i > i₀ with p i, f i : M -/
#guard_msgs in
#check Finset.prod ((Finset.Ioi i₀).filter p) fun i ↦ f i

/-- info: ∏ i ≥ i₀ with p i, f i : M -/
#guard_msgs in
#check Finset.prod ((Finset.Ici i₀).filter p) fun i ↦ f i

end Top

end
