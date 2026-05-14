/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Rel.Separated
import Batteries.Tactic.Init
import Mathlib.Data.Set.Insert
import Mathlib.Init
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!
# Covers in a uniform space

This file defines covers, aka nets, which are a quantitative notion of compactness given an
entourage.

A `U`-cover of a set `s` is a set `N` such that every element of `s` is `U`-close to some element of
`N`.

The concept of uniform covers is used to define two further notions of covering:
* Metric covers: `Metric.IsCover`, defined using the distance entourage.
* Dynamical covers: `Dynamics.IsDynCoverOf`, defined using the dynamical entourage.

## References

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], Section 4.2.
-/

@[expose] public section

open Set

namespace SetRel
variable {X : Type*} {U V : SetRel X X} {s t N N₁ N₂ : Set X} {x : X}

/-- For an entourage `U`, a set `N` is a *`U`-cover* of a set `s` if every point of `s` is `U`-close
to some point of `N`.

This is also called a *`U`-net* in the literature.

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], 4.2.1. -/
def IsCover (U : SetRel X X) (s N : Set X) : Prop := ∀ ⦃x⦄, x ∈ s → ∃ y ∈ N, x ~[U] y

@[simp] lemma IsCover.empty : IsCover U ∅ N := by simp [IsCover]

@[simp] lemma isCover_empty_right : IsCover U s ∅ ↔ s = ∅ := by
  simp [IsCover, eq_empty_iff_forall_notMem]

protected nonrec lemma IsCover.nonempty (hsN : IsCover U s N) (hs : s.Nonempty) : N.Nonempty :=
  let ⟨_x, hx⟩ := hs; let ⟨y, hy, _⟩ := hsN hx; ⟨y, hy⟩

@[simp] lemma IsCover.refl (U : SetRel X X) [U.IsRefl] (s : Set X) : IsCover U s s :=
  fun a ha ↦ ⟨a, ha, U.rfl⟩

lemma IsCover.rfl {U : SetRel X X} [U.IsRefl] {s : Set X} : IsCover U s s := refl U s

@[simp] protected lemma isCover_univ : IsCover univ s N ↔ (s.Nonempty → N.Nonempty) := by
  simp [IsCover, Set.Nonempty]

lemma IsCover.mono (hN : N₁ ⊆ N₂) (h₁ : IsCover U s N₁) : IsCover U s N₂ :=
  fun _x hx ↦ let ⟨y, hy, hxy⟩ := h₁ hx; ⟨y, hN hy, hxy⟩

lemma IsCover.anti (hst : s ⊆ t) (ht : IsCover U t N) : IsCover U s N := fun _x hx ↦ ht <| hst hx

lemma IsCover.mono_entourage (hUV : U ⊆ V) (hU : IsCover U s N) : IsCover V s N :=
  fun _x hx ↦ let ⟨y, hy, hxy⟩ := hU hx; ⟨y, hy, hUV hxy⟩

lemma IsCover.union (hs : IsCover U s N₁) (ht : IsCover U t N₂) : IsCover U (s ∪ t) (N₁ ∪ N₂) := fun
  | _x, .inl hx => let ⟨y, hy, hxy⟩ := hs hx; ⟨y, .inl hy, hxy⟩
  | _x, .inr hx => let ⟨y, hy, hxy⟩ := ht hx; ⟨y, .inr hy, hxy⟩

/-- A maximal `U`-separated subset of a set `s` is a `U`-cover of `s`.

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], 4.2.6. -/
lemma IsCover.of_maximal_isSeparated [U.IsRefl] [U.IsSymm]
    (hN : Maximal (fun N ↦ N ⊆ s ∧ IsSeparated U N) N) : IsCover U s N := by
  rintro x hx
  by_contra! h
  simpa [U.rfl] using h _ <| hN.2 (y := insert x N) ⟨by simp [insert_subset_iff, hx, hN.1.1],
    hN.1.2.insert fun y hy hxy ↦ (h y hy hxy).elim⟩ (subset_insert _ _) (mem_insert _ _)

@[simp] lemma isCover_id : IsCover .id s N ↔ s ⊆ N := by simp [IsCover, subset_def]

@[deprecated (since := "2025-12-19")] alias isCover_relId := isCover_id

end SetRel
