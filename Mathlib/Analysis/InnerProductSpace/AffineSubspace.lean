/-
Copyright (c) 2023 Ricardo Prado Cunha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ricardo Prado Cunha
-/
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Projection

/-!
# Orthogonal complements of affine subspaces

In this file, the `orthogonal` complement of an affine subspace `P` is defined, and basic API is
established. The API is made to emulate that of `Submodule.orthogonal`.

## Notation

The orthogonal complement of a subspace `s` through `b` is denoted `sᗮᗮ b`.

The proposition that two subspaces are orthogonal, `AffineSubspace.IsOrtho`, is denoted by `s ⟂⟂ t`.
Note this is not the same unicode symbol as `⊥` (`Bot`).
-/


open Affine

variable {𝕜 : Type*} {V : Type*} {P : Type*} [RCLike 𝕜]

variable [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [AffineSpace V P]

namespace AffineSubspace

variable (s : AffineSubspace 𝕜 P)

open AffineEquiv

/-- Orthogonal complement to an affine subspace passing through a given point. -/
def orthogonal (b : P) : AffineSubspace 𝕜 P := mk' b s.directionᗮ

@[inherit_doc]
infixl:55 "ᗮ@ " => AffineSubspace.orthogonal

/-- When a point is in the orthogonal complement. -/
lemma mem_orthogonal (b c : P) :
    c ∈ sᗮ@ b ↔ ∀ (v : V), v ∈ s.direction → inner 𝕜 v (c -ᵥ b) = 0 :=
  Iff.intro (fun hc v hv ↦ hc v hv) id

/-- When a point is in the orthogonal complement, with the inner product the other way around. -/
lemma mem_orthogonal' (b c : P) :
    c ∈ sᗮ@ b ↔ ∀ (v : V), v ∈ s.direction → inner 𝕜 (c -ᵥ b) v = 0 := by
  simp_rw [inner_eq_zero_symm]
  apply mem_orthogonal

/-- The direction of the orthogonal complement is the orthogonal complement of the original
direction. -/
@[simp]
lemma orthogonal_direction (b : P) : (sᗮ@ b).direction = s.directionᗮ :=
  direction_mk' b s.directionᗮ

/-- An orthogonal complement is nonempty. -/
lemma orthogonal_nonempty (b : P) : (sᗮ@ b : Set P).Nonempty := mk'_nonempty _ _

/-- `orthogonal` reverses the `≤` ordering of two affine subspaces. -/
lemma orthogonal_le {s₁ s₂ : AffineSubspace 𝕜 P} (b : P) (h : s₁ ≤ s₂) :
    s₂ᗮ@ b ≤ s₁ᗮ@ b :=
  fun _ hp v hv ↦ hp v (direction_le h hv)

/-- Double application of `orthogonal` preserves the `≤` ordering of two affine subspaces. -/
lemma orthogonal_orthogonal_monotone {s₁ s₂ : AffineSubspace 𝕜 P} (b₁ b₂ c : P) (h : s₁ ≤ s₂) :
    s₁ᗮ@ b₁ᗮ@ c ≤ s₂ᗮ@ b₂ᗮ@ c := by
  intro p hp v hv
  apply hp v
  simp_rw [orthogonal_direction] at ⊢ hv
  exact Submodule.orthogonal_le (direction_le h) hv

/-- `s` is contained in `sᗮ@ bᗮ@ c` when `c ∈ s`. -/
lemma le_orthogonal_orthogonal (b c : P) (hc : c ∈ s) : s ≤ sᗮ@ bᗮ@ c :=
  fun p hp ↦ (mem_orthogonal (sᗮ@ b) c p).mpr fun q hq ↦
    Submodule.le_orthogonal_orthogonal s.direction (vsub_mem_direction hp hc) q <|
      orthogonal_direction s b ▸ hq

@[simp]
lemma top_orthogonal_eq_mk'_of_bot (b : P) : (⊤ : AffineSubspace 𝕜 P)ᗮ@ b = mk' b ⊥ := by
  rw [orthogonal, direction_top, Submodule.top_orthogonal_eq_bot]

@[simp]
lemma orthogonal_neq_bot (b : P) : sᗮ@ b ≠ ⊥ :=
  nonempty_iff_ne_bot _ |>.mp (orthogonal_nonempty s b)

@[simp]
lemma bot_orthogonal_eq_top (b : P) : (⊥ : AffineSubspace 𝕜 P)ᗮ@ b = ⊤ := by
  rw [orthogonal, direction_bot, Submodule.bot_orthogonal_eq_top, mk'_top]

@[simp]
lemma mk'_of_bot_orthogonal_eq_top (b c : P) : (mk' b (⊥ : Submodule 𝕜 V))ᗮ@ c = ⊤ := by
  rw [orthogonal, direction_mk', Submodule.bot_orthogonal_eq_top, mk'_top]

@[simp]
lemma orthogonal_eq_top_iff (b : P) : sᗮ@ b = ⊤ ↔ s.direction = ⊥ := by
  rw [orthogonal]
  apply Iff.intro
  · intro hs
    rw [← Submodule.orthogonal_eq_top_iff, ← direction_mk' b (direction s)ᗮ, hs]
    exact direction_top _ _ _
  · intro hs
    rw [hs, Submodule.bot_orthogonal_eq_top, mk'_top]

/-- The orthogonal complements of two parallel affine subspaces through the same point are equal. -/
lemma orthogonal_of_parallel_eq (s t : AffineSubspace 𝕜 P) (b : P) (h : s ∥ t) :
    sᗮ@ b = tᗮ@ b := by
  rw [orthogonal, orthogonal, h.direction_eq]

/-- The orthogonal complements of two parallel subspaces through any two points are also parallel.
-/
lemma orthogonal_parallel_of_parallel (s t : AffineSubspace 𝕜 P) (b c : P) :
    s ∥ t → sᗮ@ b ∥ tᗮ@ c := by
  intro hpar
  apply parallel_iff_direction_eq_and_eq_bot_iff_eq_bot.mpr
  apply And.intro
  · rw [orthogonal_direction, orthogonal_direction, Parallel.direction_eq hpar]
  · simp only [orthogonal_neq_bot]

/-- The orthogonal complements of an affine subspace through any points are parallel. -/
lemma orthogonal_parallel (b c : P) : sᗮ@ b ∥ sᗮ@ c :=
  orthogonal_parallel_of_parallel s s b c (Parallel.refl s)

/-- If the direction of `s` admits orthogonal projections, then the orthogonal complement, through
one the points of `s`, of an orthogonal complement of `s`, is `s`. -/
lemma orthogonal_orthogonal [s.direction.HasOrthogonalProjection] (b c : P) :
    c ∈ s → sᗮ@ bᗮ@ c = s := by
  intro hc
  simp only [orthogonal, direction_mk', Submodule.orthogonal_orthogonal, hc, mk'_eq]

/-- Two affine subspaces whose `direction`s admit orthogonal projections are parallel iff their
orthogonal complements are parallel. -/
lemma orthogonal_parallel_iff_parallel (s t : AffineSubspace 𝕜 P) [hs : Nonempty s]
    [ht : Nonempty t] [CompleteSpace s.direction] [CompleteSpace t.direction] (b c : P) :
    s ∥ t ↔ sᗮ@ b ∥ tᗮ@ c := by
  apply Iff.intro
  · exact orthogonal_parallel_of_parallel _ _ _ _
  · intro hpar
    rcases hs with ⟨b', hb'⟩
    rcases ht with ⟨c', hc'⟩
    rw [← orthogonal_orthogonal s b b' hb', ← orthogonal_orthogonal t c c' hc']
    exact orthogonal_parallel_of_parallel _ _ _ _ hpar

end AffineSubspace

/-!
### Orthogonality of affine subspaces

In this section we define `AffineSubspace.IsOrtho`, with notation `s ⟂⟂ t`.

The API emulates that of `Submodule.IsOrtho`.
-/


namespace AffineSubspace

/-- The proposition that two affine subspaces are orthogonal. Has notation `s ⟂⟂ t`. -/
def IsOrtho (s t : AffineSubspace 𝕜 P) : Prop := s.direction ⟂ t.direction

@[inherit_doc]
infixl:50 " ⟂⟂ " => AffineSubspace.IsOrtho

@[symm]
lemma IsOrtho.symm {s t : AffineSubspace 𝕜 P} : s ⟂⟂ t → t ⟂⟂ s :=
  Submodule.IsOrtho.symm

lemma IsOrtho_comm {s t : AffineSubspace 𝕜 P} : s ⟂⟂ t ↔ t ⟂⟂ s :=
  ⟨IsOrtho.symm, IsOrtho.symm⟩

lemma symmetric_isOrtho : Symmetric (IsOrtho : AffineSubspace 𝕜 P → AffineSubspace 𝕜 P → Prop) :=
  fun _ _ => IsOrtho.symm

/-- The empty subspace is orthogonal to all subspaces. -/
@[simp]
lemma isOrtho_bot_left {s : AffineSubspace 𝕜 P} : ⊥ ⟂⟂ s := by simp [IsOrtho]

/-- All subspaces are orthogonal to the empty subspace -/
@[simp]
lemma isOrtho_bot_right {s : AffineSubspace 𝕜 P} : s ⟂⟂ ⊥ := IsOrtho.symm isOrtho_bot_left

/-- If a subspace `s₁` is orthogonal to `t`, then so is any subspace `s₂ ≤ s₁`. -/
lemma IsOrtho.mono_left {s₁ s₂ t : AffineSubspace 𝕜 P} (hs : s₂ ≤ s₁) (h : s₁ ⟂⟂ t) :
    s₂ ⟂⟂ t := by
  simp [IsOrtho]
  exact Submodule.IsOrtho.mono_left (direction_le hs) h

/-- If a subspace `s` is orthogonal to `t₁`, then it is also orthogonal to any subspace `t₂ ≤ t₁`.
-/
lemma IsOrtho.mono_right {s t₁ t₂ : AffineSubspace 𝕜 P} (ht : t₂ ≤ t₁) (h : s ⟂⟂ t₁) :
    s ⟂⟂ t₂ := (h.symm.mono_left ht).symm

/-- If a subspace `s₁` is orthogonal to `t₁`, then any subspace `s₂ ≤ s₁` is also orthogonal to
`t₂ ≤ t₁` -/
lemma IsOrtho.mono {s₁ s₂ t₁ t₂ : AffineSubspace 𝕜 P} (hs : s₂ ≤ s₁) (ht : t₂ ≤ t₁)
    (h : s₁ ⟂⟂ t₁) : s₂ ⟂⟂ t₂ := (h.mono_right ht).mono_left hs

@[simp]
lemma isOrtho_self {s : AffineSubspace 𝕜 P} : s ⟂⟂ s ↔ s.direction = ⊥ :=
  Submodule.isOrtho_self

@[simp]
lemma isOrtho_orthogonal_right {s : AffineSubspace 𝕜 P} (b : P) : s ⟂⟂ (sᗮ@ b) := by
  simp [IsOrtho, orthogonal]

@[simp]
lemma isOrtho_orthogonal_left {s : AffineSubspace 𝕜 P} (b : P) : (sᗮ@ b) ⟂⟂ s :=
  IsOrtho.symm (isOrtho_orthogonal_right b)

/-- If a subspace `s` is orthogonal to `t`, then `s` is a subspace of the orthogonal complement to
`t` through some point `b`. -/
lemma IsOrtho.le {s t : AffineSubspace 𝕜 P} (h : s ⟂⟂ t) :
    ∃ (b : P), s ≤ tᗮ@ b := by
  by_cases hs : s = ⊥
  · cases (AddTorsor.nonempty : Nonempty P) with | intro b =>
    use b
    rw [hs]
    exact bot_le
  · push_neg at hs
    rw [← nonempty_iff_ne_bot] at hs
    use hs.some
    intro p hp
    rw [IsOrtho] at h
    exact h.le (vsub_mem_direction hp hs.some_mem)

/-- If a subspace `s` is orthogonal `t`, then `t` is a subspace of the orthogonal complement to `s`
through some point `b`. -/
lemma IsOrtho.ge {s t : AffineSubspace 𝕜 P} (h : s ⟂⟂ t) : ∃ (b : P), t ≤ sᗮ@ b :=
  h.symm.le

@[simp]
lemma isOrtho_top_right {s : AffineSubspace 𝕜 P} : s ⟂⟂ ⊤ ↔ s.direction = ⊥ := by
  rw [IsOrtho, direction_top]
  exact Submodule.isOrtho_top_right

@[simp]
lemma isOrtho_top_left {s : AffineSubspace 𝕜 P} : ⊤ ⟂⟂ s ↔ s.direction = ⊥ := by
  rw [IsOrtho_comm]
  exact isOrtho_top_right

lemma IsOrtho.disjoint_direction {s t : AffineSubspace 𝕜 P} (h : s ⟂⟂ t) :
    Disjoint s.direction t.direction := Submodule.IsOrtho.disjoint h

lemma IsOrtho.inf_direction {s t : AffineSubspace 𝕜 P} (h : s ⟂⟂ t) :
    (s ⊓ t).direction = ⊥ :=
  le_bot_iff.mp (le_trans (direction_inf s t) (disjoint_iff_inf_le.mp h.disjoint))

@[simp]
lemma isOrtho_sup_left {s₁ s₂ t : AffineSubspace 𝕜 P} (h : (s₁ ⊔ s₂) ⟂⟂ t) :
    s₁ ⟂⟂ t ∧ s₂ ⟂⟂ t := by
  rw [IsOrtho, Submodule.IsOrtho] at h
  have := le_trans (sup_direction_le s₁ s₂) h
  exact Submodule.isOrtho_sup_left.mp this

@[simp]
lemma isOrtho_sup_right {s t₁ t₂ : AffineSubspace 𝕜 P} (h : s ⟂⟂ (t₁ ⊔ t₂)) :
    s ⟂⟂ t₁ ∧ s ⟂⟂ t₂ := by
  rw [IsOrtho_comm] at h
  repeat rw [@IsOrtho_comm _ _ _ _ _ _ _ s]
  exact isOrtho_sup_left h

@[simp]
lemma isOrtho_mk' (b c : P) (dir₁ dir₂ : Submodule 𝕜 V) :
    (mk' b dir₁) ⟂⟂ (mk' c dir₂) ↔ dir₁ ⟂ dir₂ := by simp [IsOrtho]

@[simp]
lemma IsOrtho.trans_parallel_right {s₁ s₂ t : AffineSubspace 𝕜 P} (hs : s₁ ∥ s₂) :
    s₁ ⟂⟂ t ↔ s₂ ⟂⟂ t := by
  apply Iff.intro
  · intro h
    rw [IsOrtho, ← Parallel.direction_eq hs]
    exact h
  · intro h
    rw [IsOrtho, Parallel.direction_eq hs]
    exact h

@[simp]
lemma IsOrtho.trans_parallel_left {s t₁ t₂ : AffineSubspace 𝕜 P} (ht : t₁ ∥ t₂) :
    s ⟂⟂ t₁ ↔ s ⟂⟂ t₂ := by
  repeat rw [IsOrtho]
  congr! 1
  exact Parallel.direction_eq ht

end AffineSubspace
