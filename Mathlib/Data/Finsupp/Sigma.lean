/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Logic.Embedding.Basic

/-!
# Embedding a finitely supported function into a sigma type summand

This file provides `Finsupp.embSigma`, which embeds a finitely supported function `ι k →₀ M`
into the corresponding summand of `(Σ k, ι k) →₀ M`.

## Main declarations

* `Finsupp.embSigma`: Embed `ι k →₀ M` into `(Σ k, ι k) →₀ M` for a specific `k`.

## Implementation notes

This is a special case of `Finsupp.embDomain` using `Function.Embedding.sigmaMk`.
-/

@[expose] public section

noncomputable section

open Function

variable {κ : Type*} {ι : κ → Type*} {M : Type*}

namespace Finsupp

section EmbSigma

variable [Zero M]

/-- Embed a finitely supported function `f : ι k →₀ M` into the `k`-th summand
of the sigma type `(Σ k, ι k) →₀ M`.

This is `Finsupp.embDomain` specialized to `Function.Embedding.sigmaMk k`. -/
def embSigma {k : κ} (f : ι k →₀ M) : (Σ k, ι k) →₀ M :=
  embDomain (Embedding.sigmaMk k) f

@[grind =]
theorem embSigma_apply [DecidableEq κ] {k : κ} (f : ι k →₀ M) (i : Σ k, ι k) :
    embSigma f i = if h : i.1 = k then f (h ▸ i.2) else 0 := by
  rcases i with ⟨k, i⟩
  split_ifs with h
  · subst h
    simp only [embSigma, Embedding.sigmaMk]
    apply embDomain_apply
  · simp only [embSigma, Embedding.sigmaMk]
    rw [embDomain_notin_range]
    simp_all

@[simp]
theorem embSigma_apply_self {k : κ} (f : ι k →₀ M) (i : ι k) :
    embSigma f ⟨k, i⟩ = f i := by
  rw [embSigma]
  exact embDomain_apply (Embedding.sigmaMk k) f i

/-- Values of `embSigma f` at indices outside the `k`-th summand are zero. -/
theorem embSigma_apply_of_ne {k k' : κ} (f : ι k →₀ M) (hk : k' ≠ k) (i : ι k') :
    embSigma f ⟨k', i⟩ = 0 := by
  apply embDomain_notin_range
  intro ⟨j, hj⟩
  simp [Embedding.sigmaMk] at hj
  exact hk hj.1.symm

@[simp, grind =]
theorem support_embSigma {k : κ} (f : ι k →₀ M) :
    (embSigma f).support = f.support.map (Embedding.sigmaMk k) := by
  simp [embSigma]

@[simp]
theorem embSigma_zero {k : κ} : embSigma (0 : ι k →₀ M) = 0 := by
  simp [embSigma]

@[simp]
theorem embSigma_eq_zero {k : κ} {f : ι k →₀ M} :
    embSigma f = 0 ↔ f = 0 := by
  simp [embSigma]

theorem embSigma_injective {k : κ} :
    Injective (embSigma : (ι k →₀ M) → (Σ k, ι k) →₀ M) := by
  intro f g h
  ext i
  have := congr_fun (congrArg (⇑) h) ⟨k, i⟩
  simpa using this

@[simp]
theorem embSigma_inj {k : κ} {f g : ι k →₀ M} :
    embSigma f = embSigma g ↔ f = g :=
  embSigma_injective.eq_iff

end EmbSigma

section EmbSigmaAdd

variable [AddMonoid M]

theorem embSigma_add {k : κ} (f g : ι k →₀ M) :
    embSigma (f + g) = embSigma f + embSigma g := by
  ext ⟨k', i⟩
  by_cases hk : k' = k
  · subst hk
    simp
  · simp [embSigma_apply_of_ne _ hk]

-- TODO: `embSigma` could be bundled as e.g. an additive or linear map, when needed.

end EmbSigmaAdd

section EmbSigmaSingle

@[simp]
theorem embSigma_single [Zero M] {k : κ} (i : ι k) (m : M) :
    embSigma (single i m) = single ⟨k, i⟩ m := by
  classical
  ext ⟨k', j⟩
  by_cases hk : k' = k
  · subst hk
    simp [single_apply]
  · simp [embSigma_apply_of_ne _ hk, hk]

end EmbSigmaSingle

section Split

variable [Zero M]

/-- `embSigma` is a left inverse to `split` at the same index. -/
@[simp]
theorem split_embSigma_self {k : κ} (f : ι k →₀ M) :
    split (embSigma f) k = f := by
  ext i
  simp [split_apply]

/-- `split` returns zero at indices different from where `embSigma` embeds. -/
theorem split_embSigma_of_ne {k k' : κ} (f : ι k →₀ M) (hk : k' ≠ k) :
    split (embSigma f) k' = 0 := by
  ext i
  simp [split_apply, embSigma_apply_of_ne _ hk]

end Split

end Finsupp
