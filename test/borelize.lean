import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

set_option autoImplicit true

example [TopologicalSpace α] [inst : MeasurableSpace α] [BorelSpace α] :
    MeasurableSet (∅ : Set α) := by
  guard_target = @MeasurableSet α inst ∅
  borelize α
  guard_target = @MeasurableSet α (borel α) ∅
  apply MeasurableSet.empty

example [TopologicalSpace α] : True := by
  borelize α
  have h : MeasurableSet (∅ : Set α) := MeasurableSet.empty
  guard_hyp h : @MeasurableSet α (borel α) ∅
  trivial

example : True := by
  obtain ⟨α, ⟨hα⟩⟩ : ∃ α : Type, Nonempty (TopologicalSpace α) := ⟨ℕ, ⟨inferInstance⟩⟩
  borelize α
  have h : MeasurableSet (∅ : Set α) := MeasurableSet.empty
  guard_hyp h : @MeasurableSet α (borel α) ∅
  trivial

example : True := by
  set α := ℕ
  borelize α
  have h : MeasurableSet (∅ : Set α) := MeasurableSet.empty
  guard_hyp h : @MeasurableSet α (borel α) ∅
  trivial

example : True := by
  have h1 : MeasurableSet (∅ : Set ℕ) := MeasurableSet.empty
  guard_hyp h1 : @MeasurableSet ℕ Nat.instMeasurableSpace ∅
  borelize ℕ
  have h2 : MeasurableSet (∅ : Set ℕ) := MeasurableSet.empty
  guard_hyp h2 : @MeasurableSet ℕ (borel ℕ) ∅
  trivial
