/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Data.Set.Finite.Basic

import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-! # Finiteness lemmas for pointwise operations on sets -/

public section

open scoped Pointwise

namespace Set

variable {G M α : Type*} [Group G] [Monoid M] [MulAction G α] [MulAction M α] {a : G} {s : Set α}

@[to_additive (attr := simp)]
lemma finite_smul_set : (a • s).Finite ↔ s.Finite := finite_image_iff (MulAction.injective _).injOn

@[to_additive (attr := simp)]
lemma infinite_smul_set : (a • s).Infinite ↔ s.Infinite :=
  infinite_image_iff (MulAction.injective _).injOn

@[to_additive] alias ⟨Finite.of_smul_set, _⟩ := finite_smul_set
@[to_additive] alias ⟨_, Infinite.smul_set⟩ := infinite_smul_set

/--
If the finite, nonempty set `s` is sent inside itself by the pointwise action of `m`, then there is
some element of `s` fixed by some nonzero power of `m`.
-/
@[to_additive /--
If the finite, nonempty set `s` is sent inside itself by the pointwise action of `m`, then there is
some element of `s` fixed by some nonzero multiple of `m`.
-/]
lemma exists_pow_smul_eq_self_of_smul_subset_self {m : M} (hsfin : s.Finite) (hs : s.Nonempty)
    (h : m • s ⊆ s) : ∃ a ∈ s, ∃ n : ℕ, n ≠ 0 ∧ m ^ n • a = a := by
  have h' : Set.MapsTo (m • ·) s s := by rwa [Set.mapsTo_iff_image_subset]
  obtain ⟨n, i, hi, h⟩ := Finite.stabilises_periodic_bounded h' hsfin
  obtain ⟨x, hx⟩ := hs
  refine ⟨(m • ·)^[n] x, h'.iterate n hx, i, hi.ne', ?_⟩
  simpa [pow_add, mul_smul] using h n le_rfl hx

@[to_additive]
lemma exists_pow_succ_smul_eq_pow_smul {m : M} (hsfin : s.Finite)
    (h : m • s ⊆ s) : ∃ n : ℕ, m ^ (n + 1) • s = m ^ n • s := by
  let f : α → α := (m • ·)
  have h' : Set.MapsTo f s s := by rwa [Set.mapsTo_iff_image_subset]
  have anti : Antitone (fun n => f^[n] '' s) := antitone_nat_of_succ_le fun n ↦ by
    rw [Function.iterate_succ, Set.image_comp]
    exact Set.image_mono h'.image_subset
  obtain ⟨n, i, hi, h⟩ := Finite.stabilises_periodic_bounded h' hsfin
  have : f^[i + n] '' s ⊆ f^[n + 1] '' s := anti (by grind)
  have : f^[n + 1] '' s = f^[n] '' s := subset_antisymm (anti (by simp)) (by grind)
  exact ⟨n, by simpa only [smul_iterate, image_smul, f] using this⟩

@[to_additive]
lemma exists_smul_eq_self_of_smul_subset {m : G} (hsfin : s.Finite) (h : m • s ⊆ s) :
    m • s = s := by
  obtain ⟨n, hn⟩ := exists_pow_succ_smul_eq_pow_smul hsfin h
  have : m ^ n • (m • s) = m ^ n • s := by rwa [pow_succ, mul_smul (m ^ n) m s] at hn
  simpa using this

end Set
