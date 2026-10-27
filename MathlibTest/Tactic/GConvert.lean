module

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.Basic

/-! ## General usage -/

example (p q : Nat → Prop) (h₁ : ∀ x, p x) (h₂ : ∀ x, p x → q x) : ∀ y, q y := by
  gconvert h₁ using 1
  rename_i y
  guard_target =ₐ q y
  exact h₂ _ this

example (p q : Nat → Prop) (h₁ : ∀ {x}, p x) (h₂ : ∀ x, p x → q x) : ∀ y, q y := by
  gconvert @h₁ using 1
  rename_i y
  guard_target =ₐ q y
  exact h₂ _ this

example (p q : Nat → Nat → Prop) (h₁ : ∀ {x y}, p x y) (h₂ : ∀ x y, p x y → q x y) :
    ∀ u v, q u v := by
  gconvert @h₁ using 2 with u v
  guard_target =ₐ q u v
  exact h₂ _ _ h₁

example (p q : Nat → Prop) (h₁ : ∀ x, p x) (h₂ : ∀ x, p x → q x) : ∀ y, q y := by
  gconvert h₁
  rename_i y
  guard_target =ₐ q y
  exact h₂ _ this

example (p q : Nat → Nat → Prop) (h₁ : ∀ x y, p x y) (h₂ : ∀ x y, p x y → q x y) :
    ∀ u v, q u v := by
  gconvert h₁ with u v
  guard_target =ₐ q u v
  exact h₂ _ _ this

example (p q : Nat → Prop) (h₁ : ∀ x, p x) (h₂ : ∀ x, p x → q x) : ∀ y, q y := by
  gconvert h₁ with w foo
  guard_target =ₐ q w
  exact h₂ w foo

example (p q : Nat → Prop) (h₁ : ∀ x, p x) (h₂ : ∀ x, p x → q x) : ∀ y, q y := by
  gconvert h₁ with _ foo
  rename_i w
  guard_target =ₐ q w
  exact h₂ w foo

example (p q : Nat → Prop) (h₁ : ∀ x, p x) (h₂ : ∀ x, p x → q x) : ∀ y, q y := by
  gconvert h₁ with w
  guard_target =ₐ q w
  exact h₂ w this

example (p q : Nat → Nat → Prop) (h₁ : ∀ x y, p x y) (h₂ : ∀ x y, p x y → q x y) :
    ∀ u v, q u v := by
  gconvert h₁ with s t h_peel
  guard_target =ₐ q s t
  exact h₂ s t h_peel

example (p q : Nat → Prop) (h : ∀ y, p y) (h₁ : ∀ z, p z → q z) : ∀ x, q x := by
  gconvert h
  rename_i x
  guard_target =ₐ q x
  exact h₁ _ <| by assumption

example (p q : Nat → Prop) (h : ∃ y, p y) (h₁ : ∀ z, p z → q z) : ∃ x, q x := by
  gconvert h with a h
  guard_target =ₐ q a
  exact h₁ a h

example (x y : ℝ) (h : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x + n = y + ε) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x - ε = y - n := by
  gconvert h using 5 with ε hε N n hn h_peel
  guard_target =ₐ x - ε = y - n
  linarith

set_option linter.unusedTactic false in
example (x y : ℝ) (h : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x + n = y + ε) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x - ε = y - n := by
  gconvert h using 5
  fail_if_success gconvert this using 0
  linarith

example (p q : ℝ → ℝ → Prop) (h : ∀ ε > 0, ∃ δ > 0, p ε δ)
    (hpq : ∀ x y, x > 0 → y > 0 → p x y → q x y) :
    ∀ ε > 0, ∃ δ > 0, q ε δ := by
  gconvert h with ε hε δ hδ h
  guard_target =ₐ q ε δ
  exact hpq ε δ hε hδ h

example (p q : ℝ → ℝ → Prop) (h : ∀ ε > 0, ∃ δ > 0, p ε δ)
    (hpq : ∀ x y, x > 0 → y > 0 → p x y → q x y) :
    ∀ ε > 0, ∃ δ > 0, q ε δ := by
  gconvert h with ε hε δ hδ h; exact hpq ε δ hε hδ h

example (x y : ℝ) : (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x + n = y + ε) ↔
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x - ε = y - n := by
  congr! 6
  constructor
  all_goals
    intro
    linarith

/-! ## Usage after other tactics and with multiple goals -/

example : (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1 / (n + 1 : ℚ) < ε) ↔
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1 / (n + 1 : ℚ) ≤ ε := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · gconvert h using 5 with _ _ _ _ _ h
    exact h.le
  · intro ε hε
    gconvert h (ε / 2) (half_pos hε) using 3
    exact this.trans_lt (half_lt_self hε)

example : (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1 / (n + 1 : ℚ) < ε) ↔
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1 / (n + 1 : ℚ) ≤ ε := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · gconvert h using 5; exact this.le
  · intro ε hε
    gconvert h (ε / 2) (half_pos hε) using 3; exact this.trans_lt (half_lt_self hε)
/-! ## Use with `↔` goals -/

example (x y : ℚ) (h : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x + n = y + ε) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x - ε = y - n := by
  intro ε hε
  gconvert (h ε hε) using 3
  guard_hyp this : x + ↑n = y + ε
  guard_target =ₐ x - ε = y - n
  linarith

example (x y : ℝ) : (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x + n = y + ε) ↔
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x - ε = y - n := by
  congr! 6 with ε hε N n hn
  constructor
  all_goals
    intro
    linarith

example : (∃ k > 0, ∃ n ≥ k, n = k) ↔ ∃ k > 0, ∃ n ≥ k, k = n := by
  congr! 6
  exact eq_comm

/-! ## Eventually and frequently -/

open Filter Topology

example {f : ℝ → ℝ} (h : ∀ x : ℝ, ∀ᶠ y in 𝓝 x, |f y - f x| ≤ |y - x|) :
    ∀ x : ℝ, ∀ᶠ y in 𝓝 x, |f y - f x| ^ 2 ≤ |y - x| ^ 2 := by
  gconvert h using 2 with h_peel x y
  gcongr

example (α : Type*) (f g : Filter α) (p q : α → α → Prop) (h : ∀ᶠ x in f, ∃ᶠ y in g, p x y)
    (h₁ : ∀ x y, p x y → q x y) : ∀ᶠ x in f, ∃ᶠ y in g, q x y := by
  gconvert h with x y h_peel
  exact h₁ x y h_peel

example (α : Type*) (f : Filter α) (p q : α → Prop) (h : ∀ᶠ x in f, p x) (h₁ : ∀ x, p x → q x) :
    ∀ᶠ x in f, q x := by
  gconvert h with x h_peel
  exact h₁ x h_peel

/-! ## Type classes -/

example {R : Type*} [CommRing R] (h : ∀ x : R, ∃ y : R, x + y = 2) :
    ∀ x : R, ∃ y : R, (x + y) ^ 2 = 4 := by
  gconvert h using 2
  rw [this]
  ring

example {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h : ∀ᶠ x in 𝓝 (1 : G), ∃ᶠ y in 𝓝 x, x * y⁻¹ = 1) :
    ∀ᶠ x in 𝓝 (1 : G), ∃ᶠ y in 𝓝 x, x ^ 2 = y ^ 2 := by
  gconvert h using 2 with a b h_peel
  observe : a = b⁻¹⁻¹
  simp [this]

/-! ## We need to unfold definitions -/

example {α β γ : Type*} {f : α → β} {g : β → γ} (h : Function.Injective (g ∘ f)) :
    Function.Injective f := by
  unfold Function.Injective at *
  gconvert h using 2 with x y
  intro hf
  apply this
  congrm(g $hf)

example {α β γ : Type*} {f : α → β} {g : β → γ} (h : Function.Surjective (g ∘ f)) :
    Function.Surjective g := by
  unfold Function.Surjective at *
  gconvert h using 1 with y
  fail_if_success gconvert this
  obtain ⟨x, rfl⟩ := this
  exact ⟨f x, rfl⟩

def toInf (f : ℕ → ℕ) : Prop := ∀ m, ∃ n, ∀ n' ≥ n, m ≤ f n'

@[gcongr]
theorem toInf_mono {f g : ℕ → ℕ} (h : f ≤ g) (hf : toInf f) : toInf g := by
  unfold toInf at *
  gconvert hf
  exact h _

example (f : ℕ → ℕ) (h : toInf f) : toInf (fun n => 2 * f n) := by
  gconvert h
  intro n
  dsimp
  linarith

/-! ## Error messages -/

#guard_msgs in example (x y : ℝ) (h : x = y) : x = y := by
  gconvert h

/--
error: `gcongr` did not make progress.

h : ∃ y, ∀ (x : ℕ), x ≠ y
⊢ (∃ y, ∀ (x : ℕ), x ≠ y) → ∀ (x : ℕ), ∃ y, x ≠ y
-/
#guard_msgs in
example (h : ∃ y : ℕ, ∀ x, x ≠ y) : ∀ x : ℕ, ∃ y, x ≠ y := by
  gconvert h

/--
error: `gcongr` did not make progress.

h : ∀ (n : ℕ), 0 ≤ n
⊢ (∀ (n : ℕ), 0 ≤ n) → ∀ (n : ℤ), 0 ≤ n
-/
#guard_msgs in
example (h : ∀ n : ℕ, 0 ≤ n) : ∀ n : ℤ, 0 ≤ n := by
  gconvert h

/--
error: `gcongr` did not make progress.

h : ∃ n, 0 ≤ n
⊢ (∃ n, 0 ≤ n) → ∃ n, 0 ≤ n
-/
#guard_msgs in
example (h : ∃ n : ℕ, 0 ≤ n) : ∃ n : ℤ, 0 ≤ n := by
  gconvert h using 1

/--
error: `gcongr` did not make progress.

h : ∃ᶠ (n : ℕ) in atTop, 0 ≤ n
⊢ (∃ᶠ (n : ℕ) in atTop, 0 ≤ n) → ∃ᶠ (n : ℕ) in atBot, 0 ≤ n
-/
#guard_msgs in
example (h : ∃ᶠ n : ℕ in atTop, 0 ≤ n) : ∃ᶠ n : ℕ in atBot, 0 ≤ n := by
  gconvert h using 1

/--
error: `gcongr` did not make progress.

h : ∀ᶠ (n : ℕ) in atTop, 0 ≤ n
⊢ (∀ᶠ (n : ℕ) in atTop, 0 ≤ n) → ∀ᶠ (n : ℕ) in atBot, 0 ≤ n
-/
#guard_msgs in
example (h : ∀ᶠ n : ℕ in atTop, 0 ≤ n) : ∀ᶠ n : ℕ in atBot, 0 ≤ n := by
  gconvert h using 1

/-! Testing `gcongr` on `gconvert` goals -/

example (p q : ℝ → ℝ → Prop) (h : ∀ ε > 0, ∃ δ > 0, p ε δ)
    (hpq : ∀ x y, x > 0 → y > 0 → p x y → q x y) :
    ∀ ε > 0, ∃ δ > 0, q ε δ := by
  revert h
  gcongr with ε hε δ hδ
  exact hpq ε δ hε hδ

example (x y : ℚ) (h : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x + n = y + ε) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x - ε = y - n := by
  revert h
  gcongr ∀ ε > 0, ∃ N, ∀ n ≥ _, ?_ with ε hε _ n hn
  intro this
  guard_hyp this : x + ↑n = y + ε
  guard_target =ₐ x - ε = y - n
  linarith

example {f : ℝ → ℝ} (h : ∀ x : ℝ, ∀ᶠ y in 𝓝 x, |f y - f x| ≤ |y - x|) :
    ∀ x : ℝ, ∀ᶠ y in 𝓝 x, |f y - f x| ^ 2 ≤ |y - x| ^ 2 := by
  revert h
  gcongr ∀ x, ∀ᶠ y in _, ?_
  intro
  gcongr

example (α : Type*) (f g : Filter α) (p q : α → α → Prop) (h : ∀ᶠ x in f, ∃ᶠ y in g, p x y)
    (h₁ : ∀ x y, p x y → q x y) : ∀ᶠ x in f, ∃ᶠ y in g, q x y := by
  revert h
  gcongr
  apply h₁
