/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!

Marginis:

A metastable dominated convergence theorem.
Jeremy Avigad, Edward T Dean, Jason Rute.

We prove the equivalence between the two first displayed
equations mentioned on page 2. We generalize to
an arbitrary predicate `P x y` (in place of `|x - y| < ε`), over any type.

-/


open Classical

/-- A 1-variable general version of metastability over an arbitrary preorder. -/
theorem metastable_general₁' {R N : Type} [Preorder N] (P : R → Prop) (a : N → R) :
    (∃ m, ∀ x ≥ m, P (a x)) ↔
    ∀ F : N → N, ∃ m, ∀ x ∈ Set.Icc m (F m), P (a x) := by
  constructor
  · intro h F
    obtain ⟨m,hm⟩ := h
    use m
    exact fun n hn => hm n hn.1
  · intro h
    contrapose h
    push_neg at *
    have φ : ∀ m : N, ∃ k : N, ∃ n ∈ Set.Icc m k, ¬ P (a n) := by
      intro m
      obtain ⟨n,hn⟩ := h m
      exact ⟨n, n, ⟨ hn.1,le_refl _⟩, hn.2⟩
    use (fun m => Classical.choose <| φ m)
    intro m
    obtain ⟨u,hu⟩ := Classical.choose_spec <| φ m
    use u

/-- 2-variable general metastability over an upper semilattice. -/
theorem metastable_general₂' {R N : Type} [SemilatticeSup N]
    (P : R → R → Prop) (a : N → R) :
    (∃ m, ∀ x ≥ m, ∀ y ≥ m, P (a x) (a y)) ↔
    ∀ F : N → N, ∃ m, ∀ x ∈ Set.Icc m (F m), ∀ y ∈ Set.Icc m (F m), P (a x) (a y) := by
  constructor
  · intro h F
    obtain ⟨m,hm⟩ := h
    use m
    exact fun n hn n' hn' => hm n hn.1 n' hn'.1
  · intro h
    contrapose h
    push_neg at *
    have φ : ∀ m : N, ∃ k : N, ∃ n ∈ Set.Icc m k, ∃ n' ∈ Set.Icc m k, ¬ P (a n) (a n') :=
      fun m => by
      obtain ⟨n,hn⟩ := h m
      obtain ⟨n',hn'⟩ := hn.2
      exact ⟨ n ⊔ n', n, ⟨hn.1, by exact SemilatticeSup.le_sup_left n n'⟩,
        ⟨n', by simp_all, hn'.2⟩⟩
    exact ⟨fun m => Classical.choose <| φ m, fun m => Classical.choose_spec <| φ m⟩


/-- A 1-variable general version of metastability. -/
theorem metastable_general₁ {R : Type} (P : R → Prop) (a : ℕ → R) :
    (∃ m, ∀ x ≥ m, P (a x)) ↔
    ∀ F : ℕ → ℕ, ∃ m, ∀ x ∈ Set.Icc m (F m), P (a x) := by
  constructor
  · intro h F
    obtain ⟨m,hm⟩ := h
    use m
    exact fun n hn => hm n hn.1
  · intro h
    contrapose h
    push_neg at *
    have φ : ∀ m : ℕ, ∃ k : ℕ, ∃ n ∈ Set.Icc m k, ¬ P (a n) := by
      intro m
      obtain ⟨n,hn⟩ := h m
      exact ⟨n, n, by (simp only [Set.mem_Icc, le_refl, and_true];tauto), hn.2⟩
    exact ⟨fun m => Nat.find <| φ m, fun m => Nat.find_spec <| φ m⟩


/-- A 2-variable general version of metastability. -/
theorem metastable_general₂ {R : Type} (P : R → R → Prop) (a : ℕ → R) :
    (∃ m, ∀ x ≥ m, ∀ y ≥ m, P (a x) (a y)) ↔
    ∀ F : ℕ → ℕ, ∃ m, ∀ x ∈ Set.Icc m (F m), ∀ y ∈ Set.Icc m (F m), P (a x) (a y) := by
  constructor
  · intro h F
    obtain ⟨m,hm⟩ := h
    use m
    exact fun n hn n' hn' => hm n hn.1 n' hn'.1
  · intro h
    contrapose h
    push_neg at *
    have φ : ∀ m : ℕ, ∃ k : ℕ, ∃ n ∈ Set.Icc m k, ∃ n' ∈ Set.Icc m k, ¬ P (a n) (a n') :=
      fun m => by
      obtain ⟨n,hn⟩ := h m
      obtain ⟨n',hn'⟩ := hn.2
      exact ⟨ max n n', n, ⟨hn.1, Nat.le_max_left n n'⟩, ⟨n', by simp_all, hn'.2⟩⟩
    exact ⟨fun m => Nat.find <| φ m, fun m => Nat.find_spec <| φ m⟩

/-- Equivalence between the two first displayed equations mentioned on
page 2 of A metastable dominated convergence theorem by Jeremy Avigad, Edward T Dean, Jason Rute. -/
lemma metastable_example (a : ℕ → ℝ) :
    (∀ ε > 0, ∃ m, ∀ n ≥ m, ∀ n' ≥ m, dist (a n) (a n') < ε) ↔
    ∀ ε > 0, ∀ F : ℕ → ℕ, ∃ m, ∀ n  ∈ Set.Icc m (F m), ∀ n' ∈ Set.Icc m (F m),
    dist (a n) (a n') < ε := ⟨
  fun h ε hε => (metastable_general₂ (fun x y => |x - y| < ε) a).mp  (h ε hε),
  fun h ε hε => (metastable_general₂ (fun x y => |x - y| < ε) a).mpr (h ε hε)⟩
