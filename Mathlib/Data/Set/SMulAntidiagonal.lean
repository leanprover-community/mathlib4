/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Order.AddTorsor
import Mathlib.Data.Set.Pointwise.SMul
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
      element in `t` that scalar multiply to `a`.-/
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

end Set

namespace SMul

@[to_additive]
theorem smul_lt_smul_of_le_of_lt [LE G] [Preorder P] [SMul G P] [IsOrderedCancelSMul G P]
    {a b : G} {c d : P} (h₁ : a ≤ b) (h₂ : c < d) :
  a • c < b • d := by
  refine lt_of_le_of_lt (IsOrderedSMul.smul_le_smul_right a b h₁ c) ?_
  refine lt_of_le_not_le (IsOrderedSMul.smul_le_smul_left c d (le_of_lt h₂) b) ?_
  by_contra hbdc
  have h : d ≤ c := IsOrderedCancelSMul.le_of_smul_le_smul_left b d c hbdc
  rw [@lt_iff_le_not_le] at h₂
  simp_all only [not_true_eq_false, and_false]

@[to_additive]
theorem smul_lt_smul_of_lt_of_le [Preorder G] [Preorder P] [SMul G P] [IsOrderedCancelSMul G P]
    {a b : G} {c d : P} (h₁ : a < b) (h₂ : c ≤ d) : a • c < b • d := by
  refine lt_of_le_of_lt (IsOrderedSMul.smul_le_smul_left c d h₂ a) ?_
  refine lt_of_le_not_le (IsOrderedSMul.smul_le_smul_right a b (le_of_lt h₁) d) ?_
  by_contra hbad
  have h : b ≤ a := IsOrderedCancelSMul.le_of_smul_le_smul_right b a d hbad
  rw [@lt_iff_le_not_le] at h₁
  simp_all only [not_true_eq_false, and_false]

end SMul

open Pointwise

namespace Set.SMulAntidiagonal

open SMul

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
  refine' Set.not_infinite.1 fun h => _
  have h1 : (smulAntidiagonal s t a).PartiallyWellOrderedOn (Prod.fst ⁻¹'o (· ≤ ·)) := fun f hf =>
    hs (Prod.fst ∘ f) fun n => (mem_smulAntidiagonal.1 (hf n)).1
  have h2 : (smulAntidiagonal s t a).PartiallyWellOrderedOn (Prod.snd ⁻¹'o (· ≤ ·)) := fun f hf =>
    ht (Prod.snd ∘ f) fun n => (mem_smulAntidiagonal.1 (hf n)).2.1
  have isrfl : IsRefl (G × P) (Prod.fst ⁻¹'o fun x x_1 ↦ x ≤ x_1) := by
    refine { refl := ?refl }
    simp_all only [Order.Preimage, le_refl, Prod.forall, implies_true]
  have istrns : IsTrans (G × P) (Prod.fst ⁻¹'o fun x x_1 ↦ x ≤ x_1) := by
    refine { trans := ?trans }
    simp_all only [Order.Preimage, Prod.forall]
    exact fun a _ a_1 _ a_2 _ a_3 a_4 ↦ Preorder.le_trans a a_1 a_2 a_3 a_4
  obtain ⟨g, hg⟩ :=
    h1.exists_monotone_subseq (fun n => h.natEmbedding _ n) fun n => (h.natEmbedding _ n).2
  obtain ⟨m, n, mn, h2'⟩ := h2 (fun x => (h.natEmbedding _) (g x)) fun n => (h.natEmbedding _ _).2
  refine' mn.ne (g.injective <| (h.natEmbedding _).injective _)
  exact eq_of_fst_le_fst_of_snd_le_snd (hg _ _ mn.le) h2'

end Set.SMulAntidiagonal

namespace Set

@[to_additive]
theorem Nonempty.SMul [SMul G P] {s : Set G} {t : Set P} :
    s.Nonempty → t.Nonempty → (s • t).Nonempty :=
  Nonempty.image2

@[to_additive]
theorem IsPWO.SMul [PartialOrder G] [PartialOrder P] [SMul G P] [IsOrderedCancelSMul G P] {s : Set G}
    {t : Set P} (hs : s.IsPWO) (ht : t.IsPWO) : IsPWO (s • t) := by
  rw [← @image_smul_prod]
  exact (hs.prod ht).image_of_monotone (monotone_fst.SMul monotone_snd)

@[to_additive]
theorem IsWF.SMul [LinearOrder G] [LinearOrder P] [SMul G P] [IsOrderedCancelSMul G P] {s : Set G}
    {t : Set P} (hs : s.IsWF) (ht : t.IsWF) : IsWF (s • t) :=
  (hs.isPWO.SMul ht.isPWO).isWF

-- _root_ seems to be needed here, and I have no idea why.
@[to_additive]
theorem IsWF.min_SMul [LinearOrder G] [LinearOrder P] [_root_.SMul G P] [IsOrderedCancelSMul G P]
    {s : Set G} {t : Set P} (hs : s.IsWF) (ht : t.IsWF) (hsn : s.Nonempty) (htn : t.Nonempty) :
    (hs.SMul ht).min (hsn.SMul htn) = hs.min hsn • ht.min htn := by
  refine' le_antisymm (IsWF.min_le _ _ (mem_smul.2 ⟨_, hs.min_mem _, _, ht.min_mem _, rfl⟩)) _
  rw [IsWF.le_min_iff]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact IsOrderedSMul.smul_le_smul (hs.min_le _ hx) (ht.min_le _ hy)

end Set
