/-
Copyright (c) 2023 Ricardo Prado Cunha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ricardo Prado Cunha
-/
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Projection

/-!
# Orthogonal complements of affine subspaces

In this file, the `orthogonal` complement of an affine subspace `P` is defined, and basic API is
established. The API is made to emulate that of `Submodule.orthogonal`.
-/


open Affine

variable {𝕜 : Type _} {V : Type _} {P : Type _} [IsROrC 𝕜]

variable [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [AffineSpace V P]

namespace AffineSubspace

open AffineEquiv

/-- Orthogonal complement to an affine subspace passing through a given point. -/
def orthogonal (s : AffineSubspace 𝕜 P) (b : P) : AffineSubspace 𝕜 P := mk' b s.directionᗮ

/-- When a point is in the orthogonal complement. -/
lemma mem_orthogonal (s : AffineSubspace 𝕜 P) (b c : P) :
    c ∈ s.orthogonal b ↔ ∀ (v : V), v ∈ s.direction → @inner 𝕜 _ _ v (c -ᵥ b) = 0 := by
  apply Iff.intro
  · intro hc v hv
    rcases hc with ⟨w, hw, hc⟩
    rw [hc]
    simp
    apply (Submodule.mem_orthogonal _ w).mp
    <;> assumption
  · intro h
    simp [orthogonal]
    use c -ᵥ b
    apply And.intro
    · exact h
    · simp

/-- When a point is in the orthogonal complement, with the inner product the other way around. -/
lemma mem_orthogonal' (s : AffineSubspace 𝕜 P) (b c : P) :
    c ∈ s.orthogonal b ↔ ∀ (v : V), v ∈ s.direction → @inner 𝕜 _ _ (c -ᵥ b) v = 0 := by
  simp_rw [mem_orthogonal, inner_eq_zero_symm]

/-- `orthogonal` reverses the `≤` ordering of two affine subspaces. -/
lemma orthogonal_le (s t : AffineSubspace 𝕜 P) (b : P) (h : s ≤ t)
    : t.orthogonal b ≤ s.orthogonal b := by
  rw [orthogonal, orthogonal, le_def']
  intro p hp
  use p -ᵥ b
  apply And.intro
  · rcases hp with ⟨v, hv, rfl⟩
    simp
    exact Submodule.orthogonal_le (direction_le h) hv
  · symm
    exact vsub_vadd _ _

/-- Double application of `orthogonal` preserves the `≤` ordering of two affine subspaces. -/
lemma orthogonal_orthogonal_monotone {s t : AffineSubspace 𝕜 P} (b₁ b₂ c : P) (h : s ≤ t) :
    (s.orthogonal b₁).orthogonal c ≤ (t.orthogonal b₂).orthogonal c := by
  simp [orthogonal, le_def']
  intro p hp
  use p -ᵥ c
  apply And.intro
  · rcases hp with ⟨v, hv, rfl⟩
    simp
    exact Submodule.orthogonal_orthogonal_monotone (direction_le h) hv
  · symm
    exact vsub_vadd _ _

/-- `s` is contained in `(s.orthogonal b).orthogonal c` when `c ∈ s`. -/
lemma le_orthogonal_orthogonal (s : AffineSubspace 𝕜 P) (b c : P) (hc : c ∈ s)
    : s ≤ (s.orthogonal b).orthogonal c := by
  simp [orthogonal, le_def']
  intros p hp
  exact ⟨ p -ᵥ c
        , Submodule.le_orthogonal_orthogonal _ (vsub_mem_direction hp hc)
        , Eq.symm (vsub_vadd _ _)
        ⟩

@[simp]
lemma top_orthogonal_eq_mk'_of_bot (b : P) : orthogonal (⊤ : AffineSubspace 𝕜 P) b = mk' b ⊥ := by
  simp [orthogonal]

@[simp]
lemma bot_orthogonal_eq_top (b : P) : orthogonal (⊥ : AffineSubspace 𝕜 P) b = ⊤ := by
  simp [orthogonal]
  ext x
  exact ⟨by simp, fun _ => ⟨x -ᵥ b, by simp⟩⟩

@[simp]
lemma mk'_of_bot_orthogonal_eq_top (b c : P) : (mk' b (⊥ : Submodule 𝕜 V)).orthogonal c = ⊤ := by
  rw [orthogonal, direction_mk', Submodule.bot_orthogonal_eq_top]
  ext x
  exact ⟨by simp, fun _ => ⟨x -ᵥ c, by simp⟩⟩

@[simp]
lemma orthogonal_eq_top_iff (s : AffineSubspace 𝕜 P) (b : P) :
    s.orthogonal b = ⊤ ↔ s.direction = ⊥ := by
  apply Iff.intro
  · intro hs
    rw [orthogonal] at hs
    rw [← Submodule.orthogonal_eq_top_iff, ← direction_mk' b (direction s)ᗮ, hs]
    exact direction_top _ _ _
  · intro hs
    rw [orthogonal, hs, Submodule.bot_orthogonal_eq_top]
    ext x
    exact ⟨by simp, fun _ => ⟨x -ᵥ b, by simp⟩⟩

/-- The orthogonal complements of two parallel affine subspaces through the same point are equal. -/
lemma orthogonal_of_parallel_eq (s t : AffineSubspace 𝕜 P) (b : P) (h : s ∥ t) :
    s.orthogonal b = t.orthogonal b := by
  repeat rw [orthogonal]
  congr! 2
  exact h.direction_eq

/-- The orthogonal complements of two parallel subspaces through any two points are also parallel.
-/
lemma orthogonal_parallel_of_parallel (s t : AffineSubspace 𝕜 P) (b c : P) :
    s ∥ t → orthogonal s b ∥ orthogonal t c := by
  intro hpar
  use c -ᵥ b
  ext x
  apply Iff.intro
  · intro hx
    use x -ᵥ c +ᵥ b
    apply And.intro
    · rcases hx with ⟨w, hw, hx⟩
      rw [hx]
      simp
      rw [← Parallel.direction_eq hpar] at hw
      exact ⟨w, hw, rfl⟩
    · simp
  · intro hx
    rcases hx with ⟨w, hw, hx⟩
    rcases hw with ⟨v, hv, hw⟩
    rw [← hx, hw]
    simp
    rw [Parallel.direction_eq hpar] at hv
    exact ⟨v, hv, rfl⟩

/-- The orthogonal complements of an affine subspace through any points are parallel. -/
lemma orthogonal_parallel (s : AffineSubspace 𝕜 P) (b c : P) :
    orthogonal s b ∥ orthogonal s c :=
  orthogonal_parallel_of_parallel s s b c (Parallel.refl s)

/-- The orthogonal complement through a point `c` of the orthogonal complement of an affine subspace
is equal to the original subspace when `c` is in the original subspace and the `direction` of the
original subspace is a `CompleteSpace`. -/
lemma orthogonal_orthogonal (s : AffineSubspace 𝕜 P) [CompleteSpace s.direction] (b c : P) :
    c ∈ s → (s.orthogonal b).orthogonal c = s := by
  intro hc
  simp [orthogonal, hc]

/-- Two affine subspaces with `direction` being `CompleteSpace`s are parallel iff their orthogonal
completements through two points are parallel. -/
lemma orthogonal_parallel_iff_parallel (s t : AffineSubspace 𝕜 P) [hs : Nonempty s]
  [ht : Nonempty t] [CompleteSpace s.direction] [CompleteSpace t.direction] (b c : P) :
    s ∥ t ↔ orthogonal s b ∥ orthogonal t c := by
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

In this section we define `AffineSubspace.IsOrtho`.

The API emulates that of `Submodule.IsOrtho`.
-/


namespace AffineSubspace

/-- The proposition that two affine subspaces are orthogonal. -/
def IsOrtho (s t : AffineSubspace 𝕜 P) : Prop := s.direction ⟂ t.direction

@[symm]
lemma IsOrtho.symm {s t : AffineSubspace 𝕜 P} : s.IsOrtho t → t.IsOrtho s :=
  Submodule.IsOrtho.symm

lemma IsOrtho_comm {s t : AffineSubspace 𝕜 P} : s.IsOrtho t ↔ t.IsOrtho s :=
  ⟨IsOrtho.symm, IsOrtho.symm⟩

lemma symmetric_isOrtho : Symmetric (IsOrtho : AffineSubspace 𝕜 P → AffineSubspace 𝕜 P → Prop) :=
  fun _ _ => IsOrtho.symm

@[simp]
lemma isOrtho_bot_left {s : AffineSubspace 𝕜 P} : IsOrtho ⊥ s := by simp [IsOrtho]

@[simp]
lemma isOrtho_bot_right {s : AffineSubspace 𝕜 P} : s.IsOrtho ⊥ := IsOrtho.symm isOrtho_bot_left

lemma IsOrtho.mono_left {s₁ s₂ t : AffineSubspace 𝕜 P} (hs : s₂ ≤ s₁) (h : s₁.IsOrtho t) :
    s₂.IsOrtho t := by
  simp [IsOrtho]
  exact Submodule.IsOrtho.mono_left (direction_le hs) h

lemma IsOrtho.mono_right {s t₁ t₂ : AffineSubspace 𝕜 P} (ht : t₂ ≤ t₁) (h : s.IsOrtho t₁) :
    s.IsOrtho t₂ := (h.symm.mono_left ht).symm

lemma IsOrtho.mono {s₁ s₂ t₁ t₂ : AffineSubspace 𝕜 P} (hs : s₂ ≤ s₁) (ht : t₂ ≤ t₁)
  (h : s₁.IsOrtho t₁) : s₂.IsOrtho t₂ := (h.mono_right ht).mono_left hs

@[simp]
lemma isOrtho_self {s : AffineSubspace 𝕜 P} : s.IsOrtho s ↔ s.direction = ⊥ :=
  Submodule.isOrtho_self

@[simp]
lemma isOrtho_orthogonal_right {s : AffineSubspace 𝕜 P} (b : P) : s.IsOrtho (s.orthogonal b) := by
  simp [IsOrtho, orthogonal]

@[simp]
lemma isOrtho_orthogonal_left {s : AffineSubspace 𝕜 P} (b : P) : (s.orthogonal b).IsOrtho s :=
  IsOrtho.symm (isOrtho_orthogonal_right b)

lemma IsOrtho.le {s t : AffineSubspace 𝕜 P} (h : s.IsOrtho t) :
    ∃ (b : P), s ≤ t.orthogonal b := by
  by_cases hs : s = ⊥
  · cases (AddTorsor.Nonempty : Nonempty P) with | intro b =>
    use b
    rw [hs]
    exact bot_le
  · push_neg at hs
    rw [← nonempty_iff_ne_bot] at hs
    use hs.some
    rw [le_def', orthogonal]
    intro p hp
    use p -ᵥ hs.some
    apply And.intro
    · rw [IsOrtho] at h
      apply h.le
      exact vsub_mem_direction hp hs.some_mem
    · rw [vsub_vadd]

lemma IsOrtho.ge {s t : AffineSubspace 𝕜 P} (h : s.IsOrtho t) : ∃ (b : P), t ≤ s.orthogonal b :=
  h.symm.le

@[simp]
lemma isOrtho_top_right {s : AffineSubspace 𝕜 P} : s.IsOrtho ⊤ ↔ s.direction = ⊥ := by
  rw [IsOrtho, direction_top]
  exact Submodule.isOrtho_top_right

@[simp]
lemma isOrtho_top_left {s : AffineSubspace 𝕜 P} : IsOrtho ⊤ s ↔ s.direction = ⊥ := by
  rw [IsOrtho_comm]
  exact isOrtho_top_right

lemma IsOrtho.disjoint_direction {s t : AffineSubspace 𝕜 P} (h : s.IsOrtho t)
    : Disjoint s.direction t.direction := Submodule.IsOrtho.disjoint h

lemma IsOrtho.inf_direction {s t : AffineSubspace 𝕜 P} (h : s.IsOrtho t) :
    (s ⊓ t).direction = ⊥ :=
  le_bot_iff.mp (le_trans (direction_inf s t) (disjoint_iff_inf_le.mp h.disjoint))

@[simp]
lemma isOrtho_sup_left {s₁ s₂ t : AffineSubspace 𝕜 P} (h : (s₁ ⊔ s₂).IsOrtho t) :
    s₁.IsOrtho t ∧ s₂.IsOrtho t := by
  rw [IsOrtho, Submodule.IsOrtho] at h
  have := le_trans (sup_direction_le s₁ s₂) h
  exact Submodule.isOrtho_sup_left.mp this

@[simp]
lemma isOrtho_sup_right {s t₁ t₂ : AffineSubspace 𝕜 P} (h : s.IsOrtho (t₁ ⊔ t₂)) :
    s.IsOrtho t₁ ∧ s.IsOrtho t₂ := by
  rw [IsOrtho_comm] at h
  repeat rw [@IsOrtho_comm _ _ _ _ _ _ _ s]
  exact isOrtho_sup_left h

@[simp]
lemma isOrtho_mk' (b c : P) (dir₁ dir₂ : Submodule 𝕜 V) :
    (mk' b dir₁).IsOrtho (mk' c dir₂) ↔ dir₁ ⟂ dir₂ := by simp [IsOrtho]

@[simp]
lemma IsOrtho.trans_parallel_right {s₁ s₂ t : AffineSubspace 𝕜 P} (hs : s₁ ∥ s₂) :
    s₁.IsOrtho t ↔ s₂.IsOrtho t := by
  apply Iff.intro
  · intro h
    rw [IsOrtho, ← Parallel.direction_eq hs]
    exact h
  · intro h
    rw [IsOrtho, Parallel.direction_eq hs]
    exact h

@[simp]
lemma IsOrtho.trans_parallel_left {s t₁ t₂ : AffineSubspace 𝕜 P} (ht : t₁ ∥ t₂) :
    s.IsOrtho t₁ ↔ s.IsOrtho t₂ := by
  repeat rw [IsOrtho]
  congr! 1
  exact Parallel.direction_eq ht

end AffineSubspace
