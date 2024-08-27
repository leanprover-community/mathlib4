/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.ENat.Basic

/-!
# Extended natural numbers form a complete linear order

This instance is not in `Data.ENat.Basic` to avoid dependency on `Finset`s.

We also restate some lemmas about `WithTop` for `ENat` to have versions that use `Nat.cast` instead
of `WithTop.some`.
-/

open Set

-- Porting note: was `deriving instance` but "default handlers have not been implemented yet"
-- Porting note: `noncomputable` through 'Nat.instConditionallyCompleteLinearOrderBotNat'
noncomputable instance : CompleteLinearOrder ENat :=
  inferInstanceAs (CompleteLinearOrder (WithTop ℕ))

noncomputable instance : CompleteLinearOrder (WithBot ENat) :=
  inferInstanceAs (CompleteLinearOrder (WithBot (WithTop ℕ)))

namespace ENat
variable {ι : Sort*} {f : ι → ℕ} {s : Set ℕ}

lemma iSup_coe_eq_top : ⨆ i, (f i : ℕ∞) = ⊤ ↔ ¬ BddAbove (range f) := WithTop.iSup_coe_eq_top
lemma iSup_coe_ne_top : ⨆ i, (f i : ℕ∞) ≠ ⊤ ↔ BddAbove (range f) := iSup_coe_eq_top.not_left
lemma iSup_coe_lt_top : ⨆ i, (f i : ℕ∞) < ⊤ ↔ BddAbove (range f) := WithTop.iSup_coe_lt_top
lemma iInf_coe_eq_top : ⨅ i, (f i : ℕ∞) = ⊤ ↔ IsEmpty ι := WithTop.iInf_coe_eq_top
lemma iInf_coe_ne_top : ⨅ i, (f i : ℕ∞) ≠ ⊤ ↔ Nonempty ι := by
  rw [Ne, iInf_coe_eq_top, not_isEmpty_iff]
lemma iInf_coe_lt_top : ⨅ i, (f i : ℕ∞) < ⊤ ↔ Nonempty ι := WithTop.iInf_coe_lt_top

lemma coe_sSup : BddAbove s → ↑(sSup s) = ⨆ a ∈ s, (a : ℕ∞) := WithTop.coe_sSup

lemma coe_sInf (hs : s.Nonempty) : ↑(sInf s) = ⨅ a ∈ s, (a : ℕ∞) :=
  WithTop.coe_sInf hs (OrderBot.bddBelow s)

lemma coe_iSup : BddAbove (range f) → ↑(⨆ i, f i) = ⨆ i, (f i : ℕ∞) := WithTop.coe_iSup _

@[norm_cast] lemma coe_iInf [Nonempty ι] : ↑(⨅ i, f i) = ⨅ i, (f i : ℕ∞) :=
  WithTop.coe_iInf (OrderBot.bddBelow _)

@[simp]
lemma iInf_eq_top_of_isEmpty [IsEmpty ι] : ⨅ i, (f i : ℕ∞) = ⊤ :=
  iInf_coe_eq_top.mpr ‹_›

lemma iInf_toNat : (⨅ i, (f i : ℕ∞)).toNat = ⨅ i, f i := by
  cases isEmpty_or_nonempty ι
  · simp
  · norm_cast

lemma iInf_eq_zero : ⨅ i, (f i : ℕ∞) = 0 ↔ ∃ i, f i = 0 := by
  cases isEmpty_or_nonempty ι
  · simp
  · norm_cast
    rw [iInf, Nat.sInf_eq_zero]
    exact ⟨fun h ↦ by simp_all, .inl⟩

variable {f : ι → ℕ∞} {s : Set ℕ∞}

lemma sSup_eq_zero : sSup s = 0 ↔ ∀ a ∈ s, a = 0 :=
  sSup_eq_bot

lemma sInf_eq_zero : sInf s = 0 ↔ 0 ∈ s := by
  rw [← lt_one_iff_eq_zero]
  simp only [sInf_lt_iff, lt_one_iff_eq_zero, exists_eq_right]

lemma sSup_eq_zero' : sSup s = 0 ↔ s = ∅ ∨ s = {0} :=
  sSup_eq_bot'

lemma iSup_eq_zero : iSup f = 0 ↔ ∀ i, f i = 0 :=
  iSup_eq_bot

lemma sSup_eq_top_of_infinite (h : s.Infinite) : sSup s = ⊤ := by
  apply (sSup_eq_top ..).mpr
  intro x hx
  cases x with
  | top => simp at hx
  | coe x =>
    contrapose! h
    simp only [not_infinite]
    apply Finite.subset <| Finite.Set.finite_image {n : ℕ | n ≤ x} (fun (n : ℕ) => (n : ℕ∞))
    intro y hy
    specialize h y hy
    have hxt : y < ⊤ := lt_of_le_of_lt h hx
    use y.toNat
    simp [toNat_le_of_le_coe h, LT.lt.ne_top hxt]

lemma finite_of_sSup_lt_top (h : sSup s < ⊤) : s.Finite := by
  contrapose! h
  simp only [top_le_iff]
  exact sSup_eq_top_of_infinite h

lemma sSup_mem_of_Nonempty_of_lt_top [Nonempty s] (hs' : sSup s < ⊤) : sSup s ∈ s :=
  Nonempty.csSup_mem nonempty_of_nonempty_subtype (finite_of_sSup_lt_top hs')

lemma exists_eq_iSup_of_lt_top [Nonempty ι] (h : ⨆ i, f i < ⊤) :
    ∃ i, f i = ⨆ i, f i :=
  sSup_mem_of_Nonempty_of_lt_top h

lemma exists_eq_iSup₂_of_lt_top {ι₁ ι₂ : Type*} {f : ι₁ → ι₂ → ℕ∞} [Nonempty ι₁] [Nonempty ι₂]
    (h : ⨆ i, ⨆ j, f i j < ⊤) : ∃ i j, f i j = ⨆ i, ⨆ j, f i j := by
  rw [iSup_prod'] at h ⊢
  exact Prod.exists'.mp (exists_eq_iSup_of_lt_top h)

end ENat
