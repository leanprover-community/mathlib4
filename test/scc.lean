/-
Copyright (c) 2023 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
import Mathlib.Tactic.SCC

example {p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ p₉ p₁₀ : Prop}
    (h₁ : p₁ → p₂) (h₂ : p₂ → p₃) (h₃ : p₃ → p₄) (h₄ : p₄ → p₅) (h₅ : p₅ → p₆)
    (h₆ : p₆ → p₇) (h₇ : p₇ → p₈) (h₈ : p₈ → p₉) (h₉ : p₉ → p₁₀) (h₁₀ : p₁₀ → p₁) : p₁ ↔ p₁₀ := by
  scc
