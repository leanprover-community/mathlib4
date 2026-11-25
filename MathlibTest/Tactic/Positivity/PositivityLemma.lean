module

public import Mathlib.Tactic.Positivity.Core

/-! # Tests for `@[positivity_lemma]`

The functions below are axioms, so that no `positivity` extension applies to them.
Each section tags its lemmas with `local`, so that they are not used in the other sections.
`trace.Tactic.positivity.lemma` prints one line for every lemma that is tried. -/

axiom f {α : Type*} : α → α
axiom g {α : Type*} : α → α → α
axiom k {α β : Type*} : α → β
axiom c {α : Type*} : α
axiom P {α : Type*} : α → Prop

/-- A reducible function, which unfolds to `f`. -/
noncomputable abbrev F {α : Type*} (x : α) : α := f x

variable {α β : Type*} [Zero α] [PartialOrder α] [Zero β] [PartialOrder β]

/-! ### The forms of the conclusion and the premises -/

namespace Pos

@[local positivity_lemma] axiom c_pos : 0 < (c : α)
@[local positivity_lemma] axiom f_pos {x : α} : 0 < x → 0 < f x

example : 0 < (c : α) := by positivity
example {x : α} (hx : 0 < x) : 0 < f x := by positivity
example {x : α} (hx : 0 < x) : 0 ≤ f x := by positivity
example {x : α} (hx : 0 < x) : f x ≠ 0 := by positivity
example : 0 < f (f (c : α)) := by positivity

end Pos

namespace Nonneg

@[local positivity_lemma] axiom f_nonneg {x : α} : 0 ≤ x → 0 ≤ f x

example {x : α} (hx : 0 ≤ x) : 0 ≤ f x := by positivity

end Nonneg

namespace Nonzero

@[local positivity_lemma] axiom f_ne_zero {x : α} : x ≠ 0 → f x ≠ 0

example {x : α} (hx : x ≠ 0) : f x ≠ 0 := by positivity
example {x : α} (hx : x ≠ 0) : 0 ≠ f x := by positivity
example {x : α} (hx : 0 ≠ x) : f x ≠ 0 := by positivity

end Nonzero

namespace Nonzero'

@[local positivity_lemma] axiom zero_ne_f {x : α} : 0 ≠ x → 0 ≠ f x

example {x : α} (hx : x ≠ 0) : f x ≠ 0 := by positivity
example {x : α} (hx : 0 ≠ x) : 0 ≠ f x := by positivity

end Nonzero'

namespace GtGe

@[local positivity_lemma] axiom f_gt {x : α} : x > 0 → f x > 0
@[local positivity_lemma] axiom g_ge {x y : α} : x ≥ 0 → y ≥ 0 → g x y ≥ 0

example {x : α} (hx : 0 < x) : 0 < f x := by positivity
example {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ g x y := by positivity

end GtGe

namespace NoOrder

/-! Without a `PartialOrder`, `positivity` can still use lemmas proving `≠ 0`. -/

variable {M : Type*} [Zero M]

@[local positivity_lemma] axiom f_ne_zero {x : M} : x ≠ 0 → f x ≠ 0

example {x : M} (hx : x ≠ 0) : f x ≠ 0 := by positivity

end NoOrder

/-! ### Arguments -/

namespace Arguments

@[local positivity_lemma] axiom f_pos {x : α} : 0 < x → 0 < f x
@[local positivity_lemma] axiom g_pos {x y : α} : 0 < x → 0 < y → 0 < g x y
@[local positivity_lemma] axiom k_pos {x : α} : 0 < x → 0 < (k x : β)

example {x y : α} (hx : 0 < x) (hy : 0 < y) : 0 < g x y := by positivity
example {x y : α} (hx : 0 < x) (hy : 0 < y) : 0 < g (f x) (g y (f y)) := by positivity
example {x : α} (hx : 0 < x) : 0 < (k (f x) : β) := by positivity

/-- error: failed to prove positivity/nonnegativity/nonzeroness -/
#guard_msgs in
example {x y : α} (hx : 0 < x) : 0 < g x y := by positivity

end Arguments

namespace RepeatedArgument

@[local positivity_lemma] axiom g_nonneg {x : α} : 0 ≤ x → 0 ≤ g x x

example {x : α} (hx : 0 ≤ x) : 0 ≤ g x x := by positivity

/-- error: failed to prove positivity/nonnegativity/nonzeroness -/
#guard_msgs in
example {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ g x y := by positivity

end RepeatedArgument

namespace Unfold

/-! The head of the expression is unfolded until there is a lemma for it. -/

@[local positivity_lemma] axiom f_pos {x : α} : 0 < x → 0 < f x

example {x : α} (hx : 0 < x) : 0 < F x := by positivity

end Unfold

namespace InstancePremises

/-! Instance arguments are not premises, even if they are propositions. -/

class Good (γ : Type*) : Prop where
  good : True

instance {γ : Type*} : Good γ := ⟨⟨⟩⟩

@[local positivity_lemma] axiom f_pos [Good α] {x : α} : 0 < x → 0 < f x

example {x : α} (hx : 0 < x) : 0 < f x := by positivity

end InstancePremises

/-! ### Several lemmas for the same function -/

namespace Combine

/-! The results of different lemmas are combined: `0 ≤ f x` and `f x ≠ 0` give `0 < f x`. -/

@[local positivity_lemma] axiom f_nonneg {x : α} : 0 ≤ x → 0 ≤ f x
@[local positivity_lemma] axiom f_ne_zero {x : α} : x ≠ 0 → f x ≠ 0

example {x : α} (hx : 0 < x) : 0 < f x := by positivity

end Combine

namespace Stop

/-! Once a lemma proves `0 < f x`, the other lemmas are not tried. -/

@[local positivity_lemma high] axiom f_pos {x : α} : 0 < x → 0 < f x
@[local positivity_lemma low] axiom f_nonneg {x : α} : 0 ≤ x → 0 ≤ f x

/-- trace: [Tactic.positivity.lemma] f_pos: f x => positive -/
#guard_msgs in
set_option trace.Tactic.positivity.lemma true in
example {x : α} (hx : 0 < x) : 0 < f x := by positivity

end Stop

namespace Priority

/-! A lemma with a higher priority is tried first, even if it proves less and was tagged later. -/

@[local positivity_lemma low] axiom f_pos {x : α} : 0 < x → 0 < f x
@[local positivity_lemma high] axiom f_nonneg {x : α} : 0 ≤ x → 0 ≤ f x

/--
trace: [Tactic.positivity.lemma] f_nonneg: f x => nonnegative
[Tactic.positivity.lemma] f_pos: f x => positive
-/
#guard_msgs in
set_option trace.Tactic.positivity.lemma true in
example {x : α} (hx : 0 < x) : 0 < f x := by positivity

end Priority

namespace PremiseWithoutZero

/-! If the argument of a premise has a type without `Zero`, the lemma is skipped,
but the other lemmas for the same function are still tried. -/

@[local positivity_lemma high] axiom k_pos {x : α} : 0 < x → 0 < (k x : β)
@[local positivity_lemma low] axiom k_pos' {γ : Type*} {x : γ} : 0 < (k x : β)

/--
trace: [Tactic.positivity.lemma] k_pos: k x => none
[Tactic.positivity.lemma] k_pos': k x => positive
-/
#guard_msgs in
set_option trace.Tactic.positivity.lemma true in
example {γ : Type*} (x : γ) : 0 < (k x : β) := by positivity

end PremiseWithoutZero

/-! ### The cache -/

namespace Cache

/-! Several lemmas need `0 ≤ x + ⋯ + x` or `0 < x + ⋯ + x`, but this is only analysed once.
Without the cache, each `+` would triple the work. -/

attribute [local positivity_lemma]
  Int.add_nonneg Int.add_pos_of_nonneg_of_pos Int.add_pos_of_pos_of_nonneg

example {x : ℤ} (hx : 0 ≤ x) :
    0 ≤ x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x
        + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x
  := by positivity

end Cache

/-! ### Lemmas that are rejected -/

namespace Validation

/--
error: @[positivity_lemma] attribute only applies to lemmas
    proving 0 [</≤/≠] f x₁ ... xₙ or f x₁ ... xₙ [>/≥/≠] 0.
The premise P x is not a positivity proposition
-/
#guard_msgs in
@[local positivity_lemma]
axiom f_pos {x : α} : P x → 0 < x → 0 < f x

/--
error: @[positivity_lemma] attribute only applies to lemmas
    proving 0 [</≤/≠] f x₁ ... xₙ or f x₁ ... xₙ [>/≥/≠] 0.
The conclusion a < 0 is not a positivity proposition
-/
#guard_msgs in
@[local positivity_lemma]
theorem neg_pos' {a : ℤ} : 0 < -a → a < 0 := Int.neg_pos.mp

/--
error: @[positivity_lemma] attribute only applies to lemmas
    proving 0 [</≤/≠] f x₁ ... xₙ or f x₁ ... xₙ [>/≥/≠] 0.
The premise a < 0 is not a positivity proposition
-/
#guard_msgs in
@[local positivity_lemma]
theorem neg_pos'' {a : ℤ} : a < 0 → 0 < -a := Int.neg_pos_of_neg

/--
error: @[positivity_lemma] attribute only applies to lemmas
    proving 0 [</≤/≠] f x₁ ... xₙ or f x₁ ... xₙ [>/≥/≠] 0.
The conclusion a < 0 ↔ 0 < -a is not a positivity proposition
-/
#guard_msgs in
@[local positivity_lemma]
theorem neg_pos''' {a : ℤ} : a < 0 ↔ 0 < -a := Int.neg_pos.symm

/--
error: @[positivity_lemma] attribute only applies to lemmas
    proving 0 [</≤/≠] f x₁ ... xₙ or f x₁ ... xₙ [>/≥/≠] 0.
The premise 0 < c does not refer to a direct argument of the conclusion 0 < a - b
-/
#guard_msgs in
@[local positivity_lemma]
axiom not_direct_arg {a b c : ℤ} : 0 < c → 0 < a - b

end Validation
