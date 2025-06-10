-- imports n stuff
import Mathlib.MeasureTheory.MeasureAlgebra.Defs

open scoped Function -- required for scoped `on` notation

namespace MeasureAlgebra

-- A σ-finite measure algebra is localizable (ConditionallyCompleteLattice).

-- lemma test : ConditionallyCompleteLattice α := by
--   sorry

-- should try to figure out how to make m/μ implicit
class IsSigmaFinite (α : Type*) (m : MeasurableAlgebra α) (μ : MeasureAlgebraMeasure α) : Prop where
  isSigmaFinite : ∃ (s : ℕ → α), ⨆i s = ⊤ ∧ ∀ i, μ (s i) ≤ ⊤

class IsSemiFinite (α : Type*) (m : MeasurableAlgebra α) (μ : MeasureAlgebraMeasure α) : Prop where
  isSemiFinite : ∀ (a : α), μ a = ⊤ → ∃ b, b ≤ a ∧ μ b < ⊤

-- guaranteed to be bdd
class IsConditionallyComplete (α : Type*) (m : MeasurableAlgebra α) : Prop where
  -- might need nonempty
  le_csSup : ∀ (s : Set α) (a : α), BddAbove s → a ∈ s → a ≤ sSup s
  csSup_le : ∀ (s : Set α) (a : α), s.Nonempty → a ∈ upperBounds s → sSup s ≤ a

-- other method doesnt work bc strictly localizable DNE for MA
-- class IsStrictlyLocalizable (α : Type*)
--   (m : MeasurableAlgebra α) (μ : MeasureAlgebraMeasure α) : Prop

class IsLocalizable (α : Type*)
  (m : MeasurableAlgebra α) (μ : MeasureAlgebraMeasure α) : Prop
  extends IsSemiFinite α m μ, IsConditionallyComplete α m

class IsSigmaOrderComplete (α : Type*) (m : MeasurableAlgebra α) : Prop where
  -- might need nonempty
  le_nsSup : ∀ (s : Set α) (a : α), s.Countable → BddAbove s → a ∈ s → a ≤ sSup s
  csSup_le : ∀ (s : Set α) (a : α), s.Countable → s.Nonempty → a ∈ upperBounds s → sSup s ≤ a

class IsCCC (α : Type*) (m : MeasurableAlgebra α) : Prop where
  isCCC : ∀ (s : Set α), Pairwise (Disjoint on s) → s.Countable

lemma prop322Gi_ii {α : Type*}
  {m : MeasurableAlgebra α} {μ : MeasureAlgebraMeasure α}
  (hsemi_finite : IsSemiFinite α m μ) (hsigma_finite : IsSigmaFinite α m μ) : IsCCC α m := by
  have hccc' : ∀ (s : Set α), Pairwise (Disjoint on s) → s.Countable := by
    -- uses MS
    sorry
  exact { isCCC := hccc' }

-- measure algebra are sigma order complete
lemma prop316Fa {α : Type*}
  {m : MeasurableAlgebra α}
  (hccc : IsCCC α m) : (IsConditionallyComplete α m) := by
  have ⟨hccc'⟩ := hccc
  have hepd : ∀ (s : Set α) (a : α), a ∈ s → ∃ s',
    sSup s = sSup s' ∧ Pairwise (Disjoint on s') ∧ a ∈ s' := by
    -- construction?
    intro s

    sorry
  have hle_csSup : ∀ (s : Set α) (a : α), BddAbove s → a ∈ s → a ≤ sSup s := by
    intro s a hbdd hin_s
    have ⟨s', ⟨hs_eq_s', hpd, hin_s'⟩⟩ := hepd s a hin_s
    rw [hs_eq_s']
    apply le_nsSup s' a (hccc' s' hpd) (MAbdd s').left hin_s'
  have hcsSup_le : ∀ (s : Set α) (a : α), s.Nonempty → a ∈ upperBounds s → sSup s ≤ a := by
    intro s a hne hbounds
    unfold Set.Nonempty at hne
    obtain ⟨x, hin_s⟩ := hne
    have ⟨s', ⟨hs_eq_s', hpd, hin_s'⟩⟩ := hepd s x hin_s
    rw [hs_eq_s']
    have hne' : s'.Nonempty := by
      exists x
    apply nsSup_le (hccc' s' hpd) hne' (MAbdd s').left
    · unfold upperBounds
      rw [Set.mem_setOf]
      intro x hin_s
      sorry
  exact { le_csSup := hle_csSup, csSup_le := hcsSup_le }

lemma prop322Cc {α : Type*}
  {m : MeasurableAlgebra α} {μ : MeasureAlgebraMeasure α}
  (hsigma_finite : IsSigmaFinite α m μ) : IsLocalizable α m μ := by
  have hsemi_finite' : ∀ (a : α), μ a = ⊤ → ∃ b, b ≤ a ∧ μ b < ⊤ := by
    intro a
    intro hma_top
    exists ⊥
    constructor
    · exact bot_le
    · rw [μ.zero]
      exact ENNReal.zero_lt_top
  have hsemi_finite : IsSemiFinite α m μ := by
    exact { isSemiFinite := hsemi_finite' }
  have hccc := prop322Gi_ii hsemi_finite hsigma_finite
  have hcc := prop316Fa hccc
  exact { isSemiFinite := hsemi_finite', le_csSup := hcc.le_csSup, csSup_le := hcc.csSup_le }

end MeasureAlgebra
