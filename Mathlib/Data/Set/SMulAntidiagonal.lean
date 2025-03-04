/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Order.AddTorsor
import Mathlib.Order.WellFoundedSet

/-!
# Antidiagonal for scalar multiplication

Given partially ordered sets `G` and `P`, with an action of `G` on `P`, we construct, for any
element `a` in `P` and subsets `s` in `G` and `t` in `P`, the set of all pairs of an element in `s`
and an element in `t` that scalar-multiply to `a`.

## Definitions
* SMul.antidiagonal : Set-valued antidiagonal for SMul.
* VAdd.antidiagonal : Set-valued antidiagonal for VAdd.
-/

variable {G P : Type*}

namespace Set

section SMul

variable [SMul G P] {s s₁ s₂ : Set G} {t t₁ t₂ : Set P} {a : P} {x : G × P}

/-- `smulAntidiagonal s t a` is the set of all pairs of an element in `s` and an
      element in `t` that scalar multiply to `a`. -/
@[to_additive "`vaddAntidiagonal s t a` is the set of all pairs of an element in `s` and an
      element in `t` that vector-add to `a`."]
def smulAntidiagonal (s : Set G) (t : Set P) (a : P) : Set (G × P) :=
  { x | x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 • x.2 = a }

@[to_additive (attr := simp)]
theorem mem_smulAntidiagonal : x ∈ smulAntidiagonal s t a ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 • x.2 = a :=
  Iff.rfl

@[to_additive]
theorem smulAntidiagonal_mono_left (h : s₁ ⊆ s₂) :
    smulAntidiagonal s₁ t a ⊆ smulAntidiagonal s₂ t a :=
  fun _ hx => ⟨h hx.1, hx.2.1, hx.2.2⟩

@[to_additive]
theorem smulAntidiagonal_mono_right (h : t₁ ⊆ t₂) :
    smulAntidiagonal s t₁ a ⊆ smulAntidiagonal s t₂ a := fun _ hx => ⟨hx.1, h hx.2.1, hx.2.2⟩

end SMul

open SMul

namespace SMulAntidiagonal

variable {s : Set G} {t : Set P} {a : P}

section CancelSMul

variable [SMul G P] [IsCancelSMul G P] {x y : smulAntidiagonal s t a}

@[to_additive VAddAntidiagonal.fst_eq_fst_iff_snd_eq_snd]
theorem fst_eq_fst_iff_snd_eq_snd :
    (x : G × P).1 = (y : G × P).1 ↔ (x : G × P).2 = (y : G × P).2 :=
  ⟨fun h =>
    IsCancelSMul.left_cancel _ _ _
      (y.2.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm,
    fun h =>
    IsCancelSMul.right_cancel _ _ _
      (y.2.2.2.trans <| by
          rw [← h]
          exact x.2.2.2.symm).symm⟩

@[to_additive VAddAntidiagonal.eq_of_fst_eq_fst]
theorem eq_of_fst_eq_fst (h : (x : G × P).fst = (y : G × P).fst) : x = y :=
  Subtype.ext <| Prod.ext h <| fst_eq_fst_iff_snd_eq_snd.1 h

@[to_additive VAddAntidiagonal.eq_of_snd_eq_snd]
theorem eq_of_snd_eq_snd (h : (x : G × P).snd = (y : G × P).snd) : x = y :=
  Subtype.ext <| Prod.ext (fst_eq_fst_iff_snd_eq_snd.2 h) h

end CancelSMul

variable [PartialOrder G] [PartialOrder P] [SMul G P] [IsOrderedCancelSMul G P]
  {x y : smulAntidiagonal s t a}

@[to_additive VAddAntidiagonal.eq_of_fst_le_fst_of_snd_le_snd]
theorem eq_of_fst_le_fst_of_snd_le_snd (h₁ : (x : G × P).1 ≤ (y : G × P).1)
    (h₂ : (x : G × P).2 ≤ (y : G × P).2) : x = y :=
  eq_of_fst_eq_fst <|
    h₁.eq_of_not_lt fun hlt =>
      (smul_lt_smul_of_lt_of_le hlt h₂).ne <|
        (mem_smulAntidiagonal.1 x.2).2.2.trans (mem_smulAntidiagonal.1 y.2).2.2.symm

@[to_additive VAddAntidiagonal.finite_of_isPWO]
theorem finite_of_isPWO (hs : s.IsPWO) (ht : t.IsPWO) (a) : (smulAntidiagonal s t a).Finite := by
  refine Set.not_infinite.1 fun h => ?_
  have h1 : (smulAntidiagonal s t a).PartiallyWellOrderedOn (Prod.fst ⁻¹'o (· ≤ ·)) :=
    fun f ↦ hs fun n ↦ ⟨_, (mem_smulAntidiagonal.1 (f n).2).1⟩
  have h2 : (smulAntidiagonal s t a).PartiallyWellOrderedOn (Prod.snd ⁻¹'o (· ≤ ·)) :=
    fun f ↦ ht fun n ↦ ⟨_, (mem_smulAntidiagonal.1 (f n).2).2.1⟩
  obtain ⟨g, hg⟩ := h1.exists_monotone_subseq fun n ↦ (h.natEmbedding _ n).2
  obtain ⟨m, n, mn, h2'⟩ := h2 fun n ↦ h.natEmbedding _ _
  refine mn.ne (g.injective <| (h.natEmbedding _).injective ?_)
  exact eq_of_fst_le_fst_of_snd_le_snd (hg _ _ mn.le) h2'

end Set.SMulAntidiagonal
