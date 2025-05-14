import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic

theorem extracted_1 (z₀ : ℂ) (f : ℂ → ℂ) (hf : AnalyticAt ℂ f z₀)
  (hfdev : AnalyticAt ℂ (deriv f) z₀) (n : ℕ) (hn : n > 0)
  (g : ℂ → ℂ) (hg : AnalyticAt ℂ g z₀) (hgneq0 : g z₀ ≠ 0)
  (hexp : ∀ᶠ (z : ℂ) in nhds z₀, f z = (z - z₀) ^ n • g z) :
  ∀ᶠ (z : ℂ) in nhds z₀, deriv f z = (z - z₀) ^ (n - 1) • (n • g z + (z - z₀) • deriv g z) := sorry

lemma unfilter {A f} (p : A → Prop) :
  (∀ᶠ z in f, p z) ↔ ∃ U ∈ f, ∀ z ∈ U, p z := by
    constructor
    · intro h; use {x | p x}; exact ⟨h, by aesop⟩
    · intro h
      rcases h with ⟨U, ⟨hU, hUp⟩⟩
      exact Filter.mem_of_superset hU hUp
