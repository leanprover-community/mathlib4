/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.ENat.Basic

#align_import data.enat.lattice from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

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

variable {f : ι → ℕ∞} {s : Set ℕ∞}

lemma test {x : ι} {y : ℕ∞} (h : f x = y) : ⨅ i, f i ≤ y :=
  h ▸ iInf_le' (fun i ↦ f i) x

lemma test' {i : ι} (h : f i ≠ ⊤) : ⨅ i, f i ≠ ⊤ := by
  rw [ne_eq, iInf_eq_top, not_forall]
  use i

-- not true in general
-- lemma iInf_toNat : (⨅ i, f i).toNat = ⨅ i, (f i).toNat := by
--   by_cases h : ⨅ i, f i = ⊤
--   · simp [iInf_eq_top.mp h]
--   · rw [iInf_eq_top, not_forall] at h
--     obtain ⟨x, hx⟩ := h
--     have : ∃ w : ℕ∞, ⨅ i, (f i).toNat = w := exists_eq'
--     obtain ⟨w, hw⟩ := this
--     have : w ≠ ⊤ := by subst hw; simp
--     apply_fun toNat at hw
--     rw [toNat_coe, ← coe_toNat_eq_self.mpr this, toNat_coe] at hw
--     have hn : ∃n : ℕ∞, f x = n ∧ n ≠ ⊤ := by simp [hx]
--     obtain ⟨n, hn₁, hn₂⟩ := hn
--     have : (f x).toNat = n := by simp [hn₁, hn₂]
--     sorry


lemma sSup_eq_zero : sSup s = 0 ↔ s = {0} ∨ s = ∅ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← bot_eq_zero, sSup_eq_bot, bot_eq_zero] at h
    by_cases h' : s = ∅
    · apply Or.inr h'
    · apply Or.inl
      ext x
      refine ⟨h x, fun hx ↦ ?_⟩
      subst hx
      obtain ⟨u, hu⟩ := nonempty_def.mp <| nonempty_iff_ne_empty.mpr h'
      exact h u hu ▸ hu
  · cases' h with h h
    · exact h ▸ sSup_singleton
    · exact h ▸ sSup_empty

lemma sInf_eq_zero : sInf s = 0 ↔ 0 ∈ s :=
  ⟨fun h ↦ have ⟨_, h₁, h₂⟩  := (sInf_eq_bot.mp h) 1 (by decide)
  lt_one_iff_eq_zero.mp h₂ ▸ h₁, inf_eq_bot_of_bot_mem⟩

--(↑⨅ i, f i).toNat

lemma iInf_eq_zero : ⨅ i, f i = 0 ↔ ∃ i, f i = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · sorry
  · sorry

end ENat
