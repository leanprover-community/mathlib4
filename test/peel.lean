import Mathlib.Tactic.Peel
import Mathlib.Topology.Instances.Real

open Filter Topology

example (p q : Nat → Prop) (h₁ : ∀ x, p x) (h₂ : ∀ x, p x → q x) : ∀ y, q y := by
  peel 1 h₁
  exact h₂ _ this

example (p q : Nat → Nat → Prop) (h₁ : ∀ x y, p x y) (h₂ : ∀ x y, p x y → q x y) :
    ∀ u v, q u v := by
  peel 2 h₁
  exact h₂ _ _ this

example (p q : Nat → Prop) (h₁ : ∀ x, p x) (h₂ : ∀ x, p x → q x) : ∀ y, q y := by
  peel h₁
  exact h₂ _ this

example (p q : Nat → Prop) (h₁ : ∀ x, p x) (h₂ : ∀ x, p x → q x) : ∀ y, q y := by
  peel h₁ using h₂ _ this

example (p q : Nat → Nat → Prop) (h₁ : ∀ x y, p x y) (h₂ : ∀ x y, p x y → q x y) :
    ∀ u v, q u v := by
  peel h₁
  peel this
  exact h₂ _ _ this

example (p q : Nat → Prop) (h₁ : ∀ x, p x) (h₂ : ∀ x, p x → q x) : ∀ y, q y := by
  peel h₁ with foo
  exact h₂ _ foo

example (p q : Nat → Prop) (h₁ : ∀ x, p x) (h₂ : ∀ x, p x → q x) : ∀ y, q y := by
  peel h₁ with foo w
  exact h₂ w foo

example (p q : Nat → Nat → Prop) (h₁ : ∀ x y, p x y) (h₂ : ∀ x y, p x y → q x y) :
    ∀ u v, q u v := by
  peel h₁ with h_peel s t
  exact h₂ s t h_peel

example (p q : Nat → Prop) (h : ∀ y, p y) (h₁ : ∀ z, p z → q z) : ∀ x, q x := by
  peel h
  exact h₁ _ <| by assumption

example (p q : Nat → Prop) (h : ∃ y, p y) (h₁ : ∀ z, p z → q z) : ∃ x, q x := by
  peel h with h x
  exact h₁ x h

example (x y : ℝ) (h : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x + n = y + ε) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x - ε = y  - n := by
  peel h with h_peel ε hε N n hn
  linarith

example (p q : ℝ → ℝ → Prop) (h : ∀ ε > 0, ∃ δ > 0, p ε δ)
    (hpq : ∀ x y, x > 0 → y > 0 → p x y → q x y) :
    ∀ ε > 0, ∃ δ > 0, q ε δ := by
  peel h with h ε hε δ hδ
  exact hpq ε δ hε hδ h

example (p q : ℝ → ℝ → Prop) (h : ∀ ε > 0, ∃ δ > 0, p ε δ)
    (hpq : ∀ x y, x > 0 → y > 0 → p x y → q x y) :
    ∀ ε > 0, ∃ δ > 0, q ε δ := by
  peel h with h ε hε δ hδ using hpq ε δ hε hδ h

example (x y : ℚ) (h : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x + n = y + ε) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, x - ε = y  - n := by
  intro ε hε
  peel 3 (h ε hε)
  linarith

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

example {f : ℝ → ℝ} (h : ∀ x : ℝ, ∀ᶠ y in 𝓝 x, |f y - f x| ≤ |y - x|) :
    ∀ x : ℝ, ∀ᶠ y in 𝓝 x, |f y - f x| ^ 2 ≤ |y - x| ^ 2 := by
  peel h with h_peel x y
  gcongr

example (α : Type*) (f g : Filter α) (p q : α → α → Prop) (h : ∀ᶠ x in f, ∃ᶠ y in g, p x y)
    (h₁ : ∀ x y, p x y → q x y) : ∀ᶠ x in f, ∃ᶠ y in g, q x y := by
  peel h with h_peel x y
  exact h₁ x y h_peel

example (α : Type*) (f : Filter α) (p q : α → Prop) (h : ∀ᶠ x in f, p x) (h₁ : ∀ x, p x → q x) :
    ∀ᶠ x in f, q x := by
  peel h with h_peel x
  exact h₁ x h_peel

example {R : Type*} [CommRing R] (h : ∀ x : R, ∃ y : R, x + y = 2) :
    ∀ x : R, ∃ y : R, (x + y) ^ 2 = 4 := by
  peel 2 h
  rw [this]
  ring

example {G : Type*} [Group G] [TopologicalSpace G] [TopologicalGroup G]
    (h : ∀ᶠ x in 𝓝 (1 : G), ∃ᶠ y in 𝓝 x, x * y⁻¹ = 1) :
    ∀ᶠ x in 𝓝 (1 : G), ∃ᶠ y in 𝓝 x, x ^ 2 = y ^ 2 := by
  peel h with h_peel a b
  observe : a = b⁻¹⁻¹
  simp [this]
