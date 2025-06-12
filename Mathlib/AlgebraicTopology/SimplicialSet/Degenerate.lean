/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# Degenerate simplices

Given a simplicial set `X` and `n : ℕ`, we define the sets `X.degenerate n`
and `X.nonDegenerate n` of degenerate or non-degenerate simplices of dimension `n`.

## TODO (@joelriou)

* `SSet.exists_nonDegenerate` shows that any `n`-simplex can be written as `X.map f.op y`
  for some epimorphism `f : ⦋n⦌ ⟶ ⦋m⦌` and some non-degenerate simplex `y`.
  Show that `f` and `y` are unique.

-/

universe u

open CategoryTheory Simplicial Limits Opposite

namespace SSet

variable (X : SSet.{u})

/-- An `n`-simplex of a simplicial set `X` is degenerate if it is in the range
of `X.map f.op` for some morphism `f : [n] ⟶ [m]` with `m < n`. -/
def degenerate (n : ℕ) : Set (X _⦋n⦌) :=
  setOf (fun x ↦ ∃ (m : ℕ) (_ : m < n) (f : ⦋n⦌ ⟶ ⦋m⦌),
    x ∈ Set.range (X.map f.op))

/-- The set of `n`-dimensional non-degenerate simplices in a simplicial
set `X` is the complement of `X.degenerate n`. -/
def nonDegenerate (n : ℕ) : Set (X _⦋n⦌) := (X.degenerate n)ᶜ

@[simp]
lemma degenerate_zero : X.degenerate 0 = ⊥ := by
  ext x
  simp only [Set.bot_eq_empty, Set.mem_empty_iff_false, iff_false]
  rintro ⟨m, hm, _⟩
  simp at hm

@[simp]
lemma nondegenerate_zero : X.nonDegenerate 0 = ⊤ := by
  simp [nonDegenerate]

variable {n : ℕ}

lemma mem_nonDegenerate_iff_notMem_degenerate (x : X _⦋n⦌) :
    x ∈ X.nonDegenerate n ↔ x ∉ X.degenerate n := Iff.rfl

@[deprecated (since := "2025-05-23")]
alias mem_nonDegenerate_iff_not_mem_degenerate := mem_nonDegenerate_iff_notMem_degenerate

lemma mem_degenerate_iff_notMem_nonDegenerate (x : X _⦋n⦌) :
    x ∈ X.degenerate n ↔ x ∉ X.nonDegenerate n := by
  simp [nonDegenerate]

@[deprecated (since := "2025-05-23")]
alias mem_degenerate_iff_not_mem_nonDegenerate := mem_degenerate_iff_notMem_nonDegenerate

lemma σ_mem_degenerate (i : Fin (n + 1)) (x : X _⦋n⦌) :
    X.σ i x ∈ X.degenerate (n + 1) :=
  ⟨n, by omega, SimplexCategory.σ i, Set.mem_range_self x⟩

lemma mem_degenerate_iff (x : X _⦋n⦌) :
    x ∈ X.degenerate n ↔ ∃ (m : ℕ) (_ : m < n) (f : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi f),
        x ∈ Set.range (X.map f.op) := by
  constructor
  · rintro ⟨m, hm, f, y, hy⟩
    rw [← image.fac f, op_comp] at hy
    have : _ ≤ m := SimplexCategory.len_le_of_mono (f := image.ι f) inferInstance
    exact ⟨(image f).len, by omega, factorThruImage f, inferInstance, by aesop⟩
  · rintro ⟨m, hm, f, hf, hx⟩
    exact ⟨m, hm, f, hx⟩

lemma degenerate_eq_iUnion_range_σ :
    X.degenerate (n + 1) = ⋃ (i : Fin (n + 1)), Set.range (X.σ i) := by
  ext x
  constructor
  · intro hx
    rw [mem_degenerate_iff] at hx
    obtain ⟨m, hm, f, hf, y, rfl⟩ := hx
    obtain ⟨i, θ, rfl⟩ := SimplexCategory.eq_σ_comp_of_not_injective f (fun hf ↦ by
      have := SimplexCategory.le_of_mono (f := f) (by
        rwa [SimplexCategory.mono_iff_injective])
      omega)
    aesop
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_range] at hx
    obtain ⟨i, y, rfl⟩ := hx
    apply σ_mem_degenerate

lemma exists_nonDegenerate (x : X _⦋n⦌) :
    ∃ (m : ℕ) (f : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi f)
      (y : X.nonDegenerate m), x = X.map f.op y := by
  induction n with
  | zero =>
      exact ⟨0, 𝟙 _, inferInstance, ⟨x, by simp⟩, by simp⟩
  | succ n hn =>
      by_cases hx : x ∈ X.nonDegenerate (n + 1)
      · exact ⟨n + 1, 𝟙 _, inferInstance, ⟨x, hx⟩, by simp⟩
      · simp only [← mem_degenerate_iff_notMem_nonDegenerate,
          degenerate_eq_iUnion_range_σ, Set.mem_iUnion, Set.mem_range] at hx
        obtain ⟨i, y, rfl⟩ := hx
        obtain ⟨m, f, hf, z, rfl⟩ := hn y
        exact ⟨_, SimplexCategory.σ i ≫ f, inferInstance, z, by simp; rfl⟩

lemma isIso_of_nonDegenerate (x : X.nonDegenerate n)
    {m : SimplexCategory} (f : ⦋n⦌ ⟶ m) [Epi f]
    (y : X.obj (op m)) (hy : X.map f.op y = x) :
    IsIso f := by
  obtain ⟨x, hx⟩ := x
  induction' m using SimplexCategory.rec with m
  rw [mem_nonDegenerate_iff_notMem_degenerate] at hx
  by_contra!
  refine hx ⟨_ ,?_, f, y, hy⟩
  by_contra!
  obtain rfl : m = n :=
    le_antisymm (SimplexCategory.len_le_of_epi (f := f) inferInstance) this
  obtain rfl := SimplexCategory.eq_id_of_epi f
  exact this inferInstance

end SSet
