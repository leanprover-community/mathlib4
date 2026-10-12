import Mathlib.Tactic.Positivity.Core

set_option trace.Tactic.positivity true
set_option trace.Tactic.positivity.failure true
set_option profiler true

section

axiom α : Type*
axiom β : Type*
variable [Zero α] [PartialOrder α] [Zero β] [PartialOrder β]

axiom c : α
axiom f : α → α
axiom g : α → β
axiom m : α → α → α
axiom P : α → Prop

namespace Basic

@[positivity_lemma]
axiom c_pos : 0 < c

@[positivity_lemma]
axiom f_pos {x : α} : 0 < x → 0 < f x

@[positivity_lemma]
axiom f_nonneg {x : α} : 0 ≤ x → 0 ≤ f x

@[positivity_lemma]
axiom f_ne_zero {x : α} : x ≠ 0 → f x ≠ 0

@[positivity_lemma]
axiom zero_ne_g {x : α} : 0 ≠ x → g x ≠ 0

@[positivity_lemma]
axiom g_pos {n : α} : 0 < n → 0 < g n

@[positivity_lemma]
axiom m_pos {x y : α} : 0 < x → 0 < y → 0 < m x y

@[positivity_lemma]
axiom m_nonneg {x y : α} : 0 ≤ x → 0 ≤ y → 0 ≤ m x y

set_option trace.Tactic.positivity true
set_option trace.Tactic.positivity.failure true

example : 0 < c := by positivity
example {x : α} (hx : 0 < x) : 0 < f x := by positivity
example {x : α} (hx : 0 ≤ x) : 0 ≤ f x := by positivity
example {x : α} (hx : x ≠ 0) : f x ≠ 0 := by positivity
example {x : α} (hx : x ≠ 0) : 0 ≠ f x := by positivity
example {x : α} (hx : 0 ≠ x) : f x ≠ 0 := by positivity
example {x : α} (hx : 0 ≠ x) : 0 ≠ f x := by positivity
example {n : α} (hn : 0 < n) : 0 < g n := by positivity

example {x : α} (hx : x ≠ 0) : g x ≠ 0 := by positivity
example {x : α} (hx : x ≠ 0) : 0 ≠ g x := by positivity
example {x : α} (hx : 0 ≠ x) : g x ≠ 0 := by positivity
example {x : α} (hx : 0 ≠ x) : 0 ≠ g x := by positivity

example {x y : α} (hx : 0 < x) (hy : 0 < y) : 0 < m x y := by positivity
example {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ m x y := by positivity

end Basic

namespace Priority

@[positivity_lemma low]
axiom f_nonneg {x : α} : 0 ≤ x → 0 ≤ f x

@[positivity_lemma high]
axiom f_pos {x : α} : 0 < x → 0 < f x

example {x : α} (hx : 0 < x) : 0 < f x := by positivity

end Priority

namespace Premises

/--
error: @[positivity_lemma] attribute only applies to lemmas
    proving 0 [</≤/≠] f x₁ ... xₙ or f x₁ ... xₙ [>/≥/≠] 0.
The premise P x is not a positivity proposition
-/
#guard_msgs in
@[positivity_lemma]
axiom f_pos {x : α} : P x → 0 < x → 0 < f x

class Good (α : Type*) : Prop where
  adorable : True

instance : Good α := ⟨⟨⟩⟩

@[positivity_lemma]
axiom f_pos' [Good α] {x : α} : 0 < x → 0 < f x

example {x : α} (hx : 0 < x) : 0 < f x := by positivity

end Premises

namespace Cache

@[positivity_lemma]
axiom m_nonneg {x y : α} : 0 ≤ x → 0 ≤ m x x
example {x : α} (hx : 0 ≤ x) : 0 ≤ m x x := by positivity

attribute [positivity_lemma]
  Int.add_nonneg
  Int.add_pos_of_nonneg_of_pos
  Int.add_pos_of_pos_of_nonneg

example {x : ℤ} (hx : 0 ≤ x)
    : 0 ≤ (((x + x) + (x + x)) + ((x + x) + (x + x))) + ((((x + x) + (x + x)) + ((x + x) + (x + x))))
  := by positivity

example {x : ℤ} (hx : 0 ≤ x) : 0 ≤ x + x + x + x + x + x + x + x := by positivity

end Cache

end

namespace FailureCache

/--
error: @[positivity_lemma] attribute only applies to lemmas
    proving 0 [</≤/≠] f x₁ ... xₙ or f x₁ ... xₙ [>/≥/≠] 0.
The conclusion {target} is not a positivity proposition
-/
#guard_msgs in
@[positivity_lemma]
theorem neg_pos' {a : ℤ} : 0 < -a → a < 0 := Int.neg_pos.mp

/--
error: @[positivity_lemma] attribute only applies to lemmas
    proving 0 [</≤/≠] f x₁ ... xₙ or f x₁ ... xₙ [>/≥/≠] 0.
The premise a < 0 is not a positivity proposition
-/
#guard_msgs in
@[positivity_lemma]
theorem neg_pos'' {a : ℤ} : a < 0 → 0 < -a := by exact fun a_1 => Int.neg_pos_of_neg a_1

/--
error: @[positivity_lemma] attribute only applies to lemmas
    proving 0 [</≤/≠] f x₁ ... xₙ or f x₁ ... xₙ [>/≥/≠] 0.
The conclusion {target} is not a positivity proposition
-/
#guard_msgs in
@[positivity_lemma]
theorem neg_pos''' {a : ℤ} : a < 0 ↔ 0 < -a := by exact Iff.symm Int.neg_pos

/--
error: @[positivity_lemma] attribute only applies to lemmas
    proving 0 [</≤/≠] f x₁ ... xₙ or f x₁ ... xₙ [>/≥/≠] 0.
The premise 0 < c does not refer to a direct argument of the conclusion 0 < a - b
-/
#guard_msgs in
@[positivity_lemma]
axiom not_direct_arg {a b c : ℤ} : 0 < c → 0 < a - b

-- TODO: support non-positivity premises via a discharger.
-- TODO: read `RunAutoParam` to support `(hx : 0 < x := by positivity)`

end FailureCache
