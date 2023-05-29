/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module analysis.calculus.darboux
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.LocalExtr

/-!
# Darboux's theorem

In this file we prove that the derivative of a differentiable function on an interval takes all
intermediate values. The proof is based on the
[Wikipedia](https://en.wikipedia.org/wiki/Darboux%27s_theorem_(analysis)) page about this theorem.
-/


open Filter Set

open scoped Topology Classical

variable {a b : ℝ} {f f' : ℝ → ℝ}

/-- **Darboux's theorem**: if `a ≤ b` and `f' a < m < f' b`, then `f' c = m` for some
`c ∈ [a, b]`. -/
theorem exists_hasDerivWithinAt_eq_of_gt_of_lt (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x) {m : ℝ} (hma : f' a < m)
    (hmb : m < f' b) : m ∈ f' '' Icc a b :=
  by
  have hab' : a < b := by
    refine' lt_of_le_of_ne hab fun hab' => _
    subst b
    exact lt_asymm hma hmb
  set g : ℝ → ℝ := fun x => f x - m * x
  have hg : ∀ x ∈ Icc a b, HasDerivWithinAt g (f' x - m) (Icc a b) x :=
    by
    intro x hx
    simpa using (hf x hx).sub ((hasDerivWithinAt_id x _).const_mul m)
  obtain ⟨c, cmem, hc⟩ : ∃ c ∈ Icc a b, IsMinOn g (Icc a b) c
  exact
    is_compact_Icc.exists_forall_le (nonempty_Icc.2 <| hab) fun x hx => (hg x hx).ContinuousWithinAt
  have cmem' : c ∈ Ioo a b := by
    cases' eq_or_lt_of_le cmem.1 with hac hac
    -- Show that `c` can't be equal to `a`
    · subst c
      refine'
        absurd (sub_nonneg.1 <| nonneg_of_mul_nonneg_right _ (sub_pos.2 hab')) (not_le_of_lt hma)
      have : b - a ∈ posTangentConeAt (Icc a b) a :=
        mem_posTangentConeAt_of_segment_subset (segment_eq_Icc hab ▸ subset.refl _)
      simpa [-sub_nonneg, -ContinuousLinearMap.map_sub] using
        hc.localize.has_fderiv_within_at_nonneg (hg a (left_mem_Icc.2 hab)) this
    cases' eq_or_lt_of_le cmem.2 with hbc hbc
    -- Show that `c` can't be equal to `b`
    · subst c
      refine'
        absurd (sub_nonpos.1 <| nonpos_of_mul_nonneg_right _ (sub_lt_zero.2 hab'))
          (not_le_of_lt hmb)
      have : a - b ∈ posTangentConeAt (Icc a b) b :=
        mem_posTangentConeAt_of_segment_subset (by rw [segment_symm, segment_eq_Icc hab])
      simpa [-sub_nonneg, -ContinuousLinearMap.map_sub] using
        hc.localize.has_fderiv_within_at_nonneg (hg b (right_mem_Icc.2 hab)) this
    exact ⟨hac, hbc⟩
  use c, cmem
  rw [← sub_eq_zero]
  have : Icc a b ∈ 𝓝 c := by rwa [← mem_interior_iff_mem_nhds, interior_Icc]
  exact (hc.is_local_min this).hasDerivAt_eq_zero ((hg c cmem).HasDerivAt this)
#align exists_has_deriv_within_at_eq_of_gt_of_lt exists_hasDerivWithinAt_eq_of_gt_of_lt

/-- **Darboux's theorem**: if `a ≤ b` and `f' a > m > f' b`, then `f' c = m` for some `c ∈ [a, b]`.
-/
theorem exists_hasDerivWithinAt_eq_of_lt_of_gt (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x) {m : ℝ} (hma : m < f' a)
    (hmb : f' b < m) : m ∈ f' '' Icc a b :=
  let ⟨c, cmem, hc⟩ :=
    exists_hasDerivWithinAt_eq_of_gt_of_lt hab (fun x hx => (hf x hx).neg) (neg_lt_neg hma)
      (neg_lt_neg hmb)
  ⟨c, cmem, neg_injective hc⟩
#align exists_has_deriv_within_at_eq_of_lt_of_gt exists_hasDerivWithinAt_eq_of_lt_of_gt

/-- **Darboux's theorem**: the image of a convex set under `f'` is a convex set. -/
theorem convex_image_hasDerivAt {s : Set ℝ} (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, HasDerivAt f (f' x) x) : Convex ℝ (f' '' s) :=
  by
  refine' ord_connected.convex ⟨_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ m ⟨hma, hmb⟩
  cases' eq_or_lt_of_le hma with hma hma
  · exact hma ▸ mem_image_of_mem f' ha
  cases' eq_or_lt_of_le hmb with hmb hmb
  · exact hmb.symm ▸ mem_image_of_mem f' hb
  cases' le_total a b with hab hab
  · have : Icc a b ⊆ s := hs.ord_connected.out ha hb
    rcases exists_hasDerivWithinAt_eq_of_gt_of_lt hab
        (fun x hx => (hf x <| this hx).HasDerivWithinAt) hma hmb with
      ⟨c, cmem, hc⟩
    exact ⟨c, this cmem, hc⟩
  · have : Icc b a ⊆ s := hs.ord_connected.out hb ha
    rcases exists_hasDerivWithinAt_eq_of_lt_of_gt hab
        (fun x hx => (hf x <| this hx).HasDerivWithinAt) hmb hma with
      ⟨c, cmem, hc⟩
    exact ⟨c, this cmem, hc⟩
#align convex_image_has_deriv_at convex_image_hasDerivAt

/-- If the derivative of a function is never equal to `m`, then either
it is always greater than `m`, or it is always less than `m`. -/
theorem deriv_forall_lt_or_forall_gt_of_forall_ne {s : Set ℝ} (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, HasDerivAt f (f' x) x) {m : ℝ} (hf' : ∀ x ∈ s, f' x ≠ m) :
    (∀ x ∈ s, f' x < m) ∨ ∀ x ∈ s, m < f' x :=
  by
  contrapose! hf'
  rcases hf' with ⟨⟨b, hb, hmb⟩, ⟨a, ha, hma⟩⟩
  exact
    (convex_image_hasDerivAt hs hf).OrdConnected.out (mem_image_of_mem f' ha)
      (mem_image_of_mem f' hb) ⟨hma, hmb⟩
#align deriv_forall_lt_or_forall_gt_of_forall_ne deriv_forall_lt_or_forall_gt_of_forall_ne

