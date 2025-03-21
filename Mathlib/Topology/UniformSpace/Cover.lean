/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Topology.UniformSpace.Separated

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

open Set

namespace UniformSpace
variable {X : Type*} {U V : Set (X × X)} {s t N N₁ N₂ : Set X} {x : X}

/-- For an entourage `U`, a set `N` is a *`U`-cover* of a set `s` if every point of `s` is `U`-close
to some point of `N`.

This is also called a *`U`-net* in the literature.

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], 4.2.1. -/
def IsCover (U : Set (X × X)) (s N : Set X) : Prop := ∀ ⦃x⦄, x ∈ s → ∃ y ∈ N, (x, y) ∈ U

@[simp] lemma IsCover.empty : IsCover U ∅ N := by simp [IsCover]

@[simp] lemma isCover_empty_right : IsCover U s ∅ ↔ s = ∅ := by
  simp [IsCover, eq_empty_iff_forall_not_mem]

@[simp] protected nonrec lemma IsCover.nonempty (hsN : IsCover U s N) (hs : s.Nonempty) :
    N.Nonempty := let ⟨_x, hx⟩ := hs; let ⟨y, hy, _⟩ := hsN hx; ⟨y, hy⟩

@[simp] protected lemma isCover_univ : IsCover univ s N ↔ (s.Nonempty → N.Nonempty) := by
  simp [IsCover, Set.Nonempty]

lemma IsCover.mono (hN : N₁ ⊆ N₂) (h₁ : IsCover U s N₁) : IsCover U s N₂ :=
  fun _x hx ↦ let ⟨y, hy, hxy⟩ := h₁ hx; ⟨y, hN hy, hxy⟩

lemma IsCover.anti (hst : s ⊆ t) (ht : IsCover U t N) : IsCover U s N := fun _x hx ↦ ht <| hst hx

lemma IsCover.mono_entourage (hUV : U ⊆ V) (hU : IsCover U s N) : IsCover V s N :=
  fun _x hx ↦ let ⟨y, hy, hxy⟩ := hU hx; ⟨y, hy, hUV hxy⟩

lemma isCover_iff_subset_iUnion_ball (hU : IsSymmetricRel U) :
    IsCover U s N ↔ s ⊆ ⋃ y ∈ N, ball y U := by simp [IsCover, subset_def, ball, hU.mk_mem_comm]

alias ⟨IsCover.subset_iUnion_ball, IsCover.of_subset_iUnion_ball⟩ := isCover_iff_subset_iUnion_ball

/-- A maximal `U`-separated subset of a set `s` is a `U`-cover of `s`.

[R. Vershynin, *High Dimensional Probability*][vershynin2018high], 4.2.6. -/
lemma IsCover.of_maximal_isSeparated (hUrefl : ∀ x, (x, x) ∈ U) (hUsymm : IsSymmetricRel U)
    (hN : Maximal (fun N ↦ N ⊆ s ∧ IsSeparated U N) N) : IsCover U s N := by
  rintro x hx
  by_contra! h
  simpa [hUrefl] using h _ <| hN.2 (y := insert x N) ⟨by simp [insert_subset_iff, hx, hN.1.1],
    hN.1.2.insert hUsymm fun y hy _ ↦ h y hy⟩ (subset_insert _ _) (mem_insert _ _)

@[simp] lemma isCover_idRel : IsCover idRel s N ↔ s ⊆ N := by simp [IsCover, subset_def]

end UniformSpace
