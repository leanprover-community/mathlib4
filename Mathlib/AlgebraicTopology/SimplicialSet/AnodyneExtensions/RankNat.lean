/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Rank
import Mathlib.SetTheory.Ordinal.Rank

/-!
# Existence of a rank function to natural numbers

In this file, we show that if `P : A.Pairing` is
a regular pairing of subcomplex `A` of a simplicial set `X`,
then there exists a rank function for `P` with value in `ℕ`.

-/

universe u

open Ordinal Simplicial

namespace SSet.Subcomplex.Pairing

variable {X : SSet.{u}} {A : X.Subcomplex} (P : A.Pairing)

instance (y : P.II) : Finite { x // P.AncestralRel x y } := by
  let T := { x : P.II // P.AncestralRel x y }
  let U := Σ (d : Fin (P.p y).1.dim), ⦋d⦌ ⟶ ⦋(P.p y).1.1.1.1⦌
  let ψ : U → X.S := fun ⟨d, f⟩ ↦ S.mk (X.map f.op (P.p y).1.simplex)
  have h (t : T) : ∃ u, ψ u = t.1.1.toS := by
    obtain ⟨f, _, hf⟩ := N.le_iff_exists_mono.1 t.2.2.le
    refine ⟨⟨⟨t.1.1.dim, ?_⟩, f⟩, ?_⟩
    · simpa using SSet.N.dim_lt_of_lt t.2.2
    · rwa [SSet.S.ext_iff]
  choose φ hφ using h
  apply Finite.of_injective φ
  intro t₁ t₂ h
  rw [Subtype.ext_iff, Subtype.ext_iff, N.ext_iff, SSet.N.ext_iff, ← hφ, ← hφ, h]

section IsRegular

variable [P.IsRegular]

lemma isWellFoundedRank_lt_omega (x : P.II) :
    IsWellFounded.rank P.AncestralRel x < ω := by
  induction x using IsWellFounded.induction P.AncestralRel with
  | ind y hy =>
    rw [IsWellFounded.rank_eq, ciSup_lt_iff_of_finite_of_bot_lt _ Ordinal.omega0_pos]
    rintro x
    have := hy _ x.2
    rw [Ordinal.lt_omega0] at this ⊢
    obtain ⟨n, hn⟩ := this
    exact ⟨n + 1, by simp [hn]⟩

/-- The rank function with values in `ℕ` relative to the well founded
ancestrality relation of a regular pairing. -/
noncomputable def rank (x : P.II) : ℕ :=
  (Ordinal.lt_omega0.1 (P.isWellFoundedRank_lt_omega x)).choose

@[simp]
lemma coe_rank (x : P.II) : P.rank x = IsWellFounded.rank P.AncestralRel x :=
  (Ordinal.lt_omega0.1 (P.isWellFoundedRank_lt_omega x)).choose_spec.symm

variable {P} in
lemma rank_lt {x y : P.II} (h : P.AncestralRel x y) :
    P.rank x < P.rank y := by
  simpa [← coe_rank, Nat.cast_lt] using IsWellFounded.rank_lt_of_rel h

/-- The canonical rank function with values in `ℕ` of a regular pairing. -/
noncomputable def rankFunction : P.RankFunction ℕ where
  rank := P.rank
  lt := P.rank_lt

instance : Nonempty (P.RankFunction ℕ) := ⟨P.rankFunction⟩

instance : Nonempty (P.WeakRankFunction ℕ) := ⟨P.rankFunction.toWeakRankFunction⟩

end IsRegular

lemma isRegular_iff_nonempty_rankFunction [P.IsProper] :
    P.IsRegular ↔ Nonempty (P.RankFunction ℕ) :=
  ⟨fun _ ↦ inferInstance, fun ⟨h⟩ ↦ h.isRegular⟩

lemma isRegular_iff_nonempty_weakRankFunction [P.IsProper] :
    P.IsRegular ↔ Nonempty (P.WeakRankFunction ℕ) :=
  ⟨fun _ ↦ inferInstance, fun ⟨h⟩ ↦ h.isRegular⟩

end SSet.Subcomplex.Pairing
