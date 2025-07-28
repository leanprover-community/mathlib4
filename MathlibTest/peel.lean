import Mathlib.Tactic.Peel
import Mathlib.Topology.Instances.Real.Lemmas

open Filter Topology

/-! ## General usage -/

example (p q : Nat → Prop) (h₁ : ∀ x, p x) (h₂ : ∀ x, p x → q x) : ∀ y, q y := by
  peel 1 h₁
  rename_i y
  guard_target =ₐ q y
  exact h₂ _ this

example (p q : Nat → Prop) (h₁ : ∀ {x}, p x) (h₂ : ∀ x, p x → q x) : ∀ y, q y := by
  peel 1 h₁
  rename_i y
  guard_target =ₐ q y
  exact h₂ _ this

example (p q : Nat → Nat → Prop) (h₁ : ∀ {x y}, p x y) (h₂ : ∀ x y, p x y → q x y) :
    ∀ u v, q u v := by
  peel 2 h₁
  rename_i u v
  guard_target =ₐ q u v
  exact h₂ _ _ this

example (p q : Nat → Prop) (h₁ : ∀ x, p x) (h₂ : ∀ x, p x → q x) : ∀ y, q y := by
  peel h₁
  rename_i y
  guard_target =ₐ q y
  exact h₂ _ this

example (p q : Nat → Prop) (h₁ : ∀ x, p x) (h₂ : ∀ x, p x → q x) : ∀ y, q y := by
  peel h₁ using h₂ _ this

example (p q : Nat → Nat → Prop) (h₁ : ∀ x y, p x y) (h₂ : ∀ x y, p x y → q x y) :
    ∀ u v, q u v := by
  peel h₁
  rename_i u v
  guard_target =ₐ q u v
  exact h₂ _ _ this

example (p q : Nat → Prop) (h₁ : ∀ x, p x) (h₂ : ∀ x, p x → q x) : ∀ y, q y := by
  peel h₁ with foo
  rename_i y
  guard_target =ₐ q y
  exact h₂ _ foo

example (p q : Nat → Prop) (h₁ : ∀ x, p x) (h₂ : ∀ x, p x → q x) : ∀ y, q y := by
  peel h₁ with w foo
  guard_target =ₐ q w
  exact h₂ w foo

example (p q : Nat → Prop) (h₁ : ∀ x, p x) (h₂ : ∀ x, p x → q x) : ∀ y, q y := by
  peel h₁ with _ foo
  rename_i w
  guard_target =ₐ q w
  exact h₂ w foo

example (p q : Nat → Prop) (h₁ : ∀ x, p x) (h₂ : ∀ x, p x → q x) : ∀ y, q y := by
  peel h₁ with w _
  guard_target =ₐ q w
  exact h₂ w this

example (p q : Nat → Nat → Prop) (h₁ : ∀ x y, p x y) (h₂ : ∀ x y, p x y → q x y) :
    ∀ u v, q u v := by
  peel h₁ with s t h_peel
  guard_target =ₐ q s t
  exact h₂ s t h_peel

example (p q : Nat → Prop) (h : ∀ y, p y) (h₁ : ∀ z, p z → q z) : ∀ x, q x := by
  peel h
  rename_i x
  guard_target =ₐ q x
  exact h₁ _ <| by assumption

example (p q : Nat → Prop) (h : ∃ y, p y) (h₁ : ∀ z, p z → q z) : ∃ x, q x := by
  peel h with a h
  guard_target =ₐ q a
  exact h₁ a h

example (x y : ℝ) (h : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x + n = y + ε) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x - ε = y - n := by
  peel h with ε hε N n hn h_peel
  guard_target =ₐ x - ε = y - n
  linarith

set_option linter.unusedTactic false in
example (x y : ℝ) (h : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x + n = y + ε) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x - ε = y - n := by
  peel h
  fail_if_success peel 2 this
  peel 0 this
  fail_if_success peel this
  linarith

example (p q : ℝ → ℝ → Prop) (h : ∀ ε > 0, ∃ δ > 0, p ε δ)
    (hpq : ∀ x y, x > 0 → y > 0 → p x y → q x y) :
    ∀ ε > 0, ∃ δ > 0, q ε δ := by
  peel h with ε hε δ hδ h
  guard_target =ₐ q ε δ
  exact hpq ε δ hε hδ h

example (p q : ℝ → ℝ → Prop) (h : ∀ ε > 0, ∃ δ > 0, p ε δ)
    (hpq : ∀ x y, x > 0 → y > 0 → p x y → q x y) :
    ∀ ε > 0, ∃ δ > 0, q ε δ := by
  peel h with ε hε δ hδ h using hpq ε δ hε hδ h

example (x y : ℝ) : (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x + n = y + ε) ↔
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x - ε = y - n := by
  peel 5
  constructor
  all_goals
    intro
    linarith

/-! ## Usage after other tactics and with multiple goals -/

example : (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1 / (n + 1 : ℚ) < ε) ↔
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1 / (n + 1 : ℚ) ≤ ε := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · peel 5 h
    exact this.le
  · intro ε hε
    peel 3 h (ε / 2) (half_pos hε)
    exact this.trans_lt (half_lt_self hε)

example : (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1 / (n + 1 : ℚ) < ε) ↔
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1 / (n + 1 : ℚ) ≤ ε := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · peel 5 h using this.le
  · intro ε hε
    peel 3 h (ε / 2) (half_pos hε) using this.trans_lt (half_lt_self hε)

/-! ## Use with `↔` goals -/

example (x y : ℚ) (h : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x + n = y + ε) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x - ε = y - n := by
  intro ε hε
  peel 3 (h ε hε)
  rename_i _ n _
  guard_hyp this : x + ↑n = y + ε
  guard_target =ₐ x - ε = y - n
  linarith

example (x y : ℝ) : (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x + n = y + ε) ↔
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x - ε = y - n := by
  peel with ε hε N n hn
  constructor
  all_goals
    intro
    linarith

example : (∃ k > 0, ∃ n ≥ k, n = k) ↔ ∃ k > 0, ∃ n ≥ k, k = n := by
  peel 4
  exact eq_comm

/-! ## Eventually and frequently -/

example {f : ℝ → ℝ} (h : ∀ x : ℝ, ∀ᶠ y in 𝓝 x, |f y - f x| ≤ |y - x|) :
    ∀ x : ℝ, ∀ᶠ y in 𝓝 x, |f y - f x| ^ 2 ≤ |y - x| ^ 2 := by
  peel h with h_peel x y
  gcongr

example (α : Type*) (f g : Filter α) (p q : α → α → Prop) (h : ∀ᶠ x in f, ∃ᶠ y in g, p x y)
    (h₁ : ∀ x y, p x y → q x y) : ∀ᶠ x in f, ∃ᶠ y in g, q x y := by
  peel h with x y h_peel
  exact h₁ x y h_peel

example (α : Type*) (f : Filter α) (p q : α → Prop) (h : ∀ᶠ x in f, p x) (h₁ : ∀ x, p x → q x) :
    ∀ᶠ x in f, q x := by
  peel h with x h_peel
  exact h₁ x h_peel

/-! ## Type classes -/

example {R : Type*} [CommRing R] (h : ∀ x : R, ∃ y : R, x + y = 2) :
    ∀ x : R, ∃ y : R, (x + y) ^ 2 = 4 := by
  peel 2 h
  rw [this]
  ring

example {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h : ∀ᶠ x in 𝓝 (1 : G), ∃ᶠ y in 𝓝 x, x * y⁻¹ = 1) :
    ∀ᶠ x in 𝓝 (1 : G), ∃ᶠ y in 𝓝 x, x ^ 2 = y ^ 2 := by
  peel h with a b h_peel
  observe : a = b⁻¹⁻¹
  simp [this]

/-! ## Unfolding definitions -/

example {α β γ : Type*} {f : α → β} {g : β → γ} (h : Function.Injective (g ∘ f)) :
    Function.Injective f := by
  peel 2 h with x y _
  intro hf
  apply this
  congrm(g $hf)

example {α β γ : Type*} {f : α → β} {g : β → γ} (h : Function.Surjective (g ∘ f)) :
    Function.Surjective g := by
  peel 1 h with y _
  fail_if_success peel this
  obtain ⟨x, rfl⟩ := this
  exact ⟨f x, rfl⟩

def toInf (f : ℕ → ℕ) : Prop := ∀ m, ∃ n, ∀ n' ≥ n, m ≤ f n'

example (f : ℕ → ℕ) (h : toInf f) : toInf (fun n => 2 * f n) := by
  peel h with this m n n' h
  dsimp
  linarith

/-! ## Error messages -/

/--
error: Tactic 'peel' could not match quantifiers in
  x = y
and
  x = y
-/
#guard_msgs in example (x y : ℝ) (h : x = y) : x = y := by
  peel h

/--
error: Tactic 'peel' could not match quantifiers in
  ∃ y, ∀ (x : ℕ), x ≠ y
and
  ∀ (x : ℕ), ∃ y, x ≠ y
-/
#guard_msgs in
example (h : ∃ y : ℕ, ∀ x, x ≠ y) : ∀ x : ℕ, ∃ y, x ≠ y := by
  peel h

/--
error: Tactic 'peel' could not match quantifiers in
  ∀ (n : ℕ), 0 ≤ n
and
  ∀ (n : ℤ), 0 ≤ n
-/
#guard_msgs in
example (h : ∀ n : ℕ, 0 ≤ n) : ∀ n : ℤ, 0 ≤ n := by
  peel h

/--
error: Tactic 'peel' could not match quantifiers in
  ∃ n, 0 ≤ n
and
  ∃ n, 0 ≤ n
-/
#guard_msgs in
example (h : ∃ n : ℕ, 0 ≤ n) : ∃ n : ℤ, 0 ≤ n := by
  peel 1 h

/--
error: Tactic 'peel' could not match quantifiers in
  ∃ᶠ (n : ℕ) in atTop, 0 ≤ n
and
  ∃ᶠ (n : ℕ) in atBot, 0 ≤ n
-/
#guard_msgs in
example (h : ∃ᶠ n : ℕ in atTop, 0 ≤ n) : ∃ᶠ n : ℕ in atBot, 0 ≤ n := by
  peel 1 h

/--
error: Tactic 'peel' could not match quantifiers in
  ∀ᶠ (n : ℕ) in atTop, 0 ≤ n
and
  ∀ᶠ (n : ℕ) in atBot, 0 ≤ n
-/
#guard_msgs in
example (h : ∀ᶠ n : ℕ in atTop, 0 ≤ n) : ∀ᶠ n : ℕ in atBot, 0 ≤ n := by
  peel 1 h

/-! Testing **gcongr** on peel goals -/

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
