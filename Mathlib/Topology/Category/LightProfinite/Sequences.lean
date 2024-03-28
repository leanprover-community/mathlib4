import Mathlib.Topology.Category.LightProfinite.Basic
import Mathlib.Topology.Compactification.OnePoint

open CategoryTheory Limits Opposite

namespace Profinite

example : TopologicalSpace (OnePoint ℕ) := inferInstance

example : CompactSpace (OnePoint ℕ) := inferInstance

example : T2Space (OnePoint ℕ) := inferInstance

instance : TotallySeparatedSpace (OnePoint ℕ) where
  isTotallySeparated_univ x _ y _ hxy := by
    cases x with
    | none =>
      cases y with
      | none => simp only [ne_eq, not_true_eq_false] at hxy
      | some val =>
        refine ⟨{some val}ᶜ, {some val}, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [OnePoint.isOpen_iff_of_mem]
          · simp only [Set.preimage_compl, compl_compl, isClosed_discrete, true_and]
            rw [isCompact_iff_finite]
            convert (Set.finite_singleton val)
            ext n
            simp only [Set.mem_preimage, Set.mem_singleton_iff]
            exact OnePoint.coe_eq_coe
          · simpa
        · rw [OnePoint.isOpen_iff_of_not_mem]
          simp only [isOpen_discrete]
          intro h
          apply hxy
          simp only [Set.mem_singleton_iff] at h
          exact h
        · simp
        · simp
        · simp [Set.union_comm]
        · simp
    | some val =>
      cases y with
      | none =>
        refine ⟨{some val}, {some val}ᶜ, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [OnePoint.isOpen_iff_of_not_mem]
          simp only [isOpen_discrete]
          intro h
          apply hxy
          simp only [Set.mem_singleton_iff] at h
          exact h.symm
        · rw [OnePoint.isOpen_iff_of_mem]
          · simp only [Set.preimage_compl, compl_compl, isClosed_discrete, true_and]
            rw [isCompact_iff_finite]
            convert (Set.finite_singleton val)
            ext n
            simp only [Set.mem_preimage, Set.mem_singleton_iff]
            exact OnePoint.coe_eq_coe
          · exact hxy.symm
        · simp
        · simp
        · simp [Set.union_comm]
        · simp
      | some val' =>
        refine ⟨{some val}, {some val}ᶜ, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [OnePoint.isOpen_iff_of_not_mem]
          simp only [isOpen_discrete]
          intro h
          exact Option.some_ne_none val h.symm
        · rw [OnePoint.isOpen_iff_of_mem]
          · simp only [Set.preimage_compl, compl_compl, isClosed_discrete, true_and]
            rw [isCompact_iff_finite]
            convert (Set.finite_singleton val)
            ext n
            simp only [Set.mem_preimage, Set.mem_singleton_iff]
            exact OnePoint.coe_eq_coe
          · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
            exact (Option.some_ne_none val).symm
        · simp
        · simpa using hxy.symm
        · simp [Set.union_comm]
        · simp

def NatUnionInfty := of (OnePoint ℕ)

end Profinite

namespace LightProfinite

def NatUnionInftyDiagram : ℕᵒᵖ ⥤ FintypeCat where
  obj n := FintypeCat.of (Finset.range (unop n + 1))
  map {_ m} _ k := if h : k.1 ∈ Finset.range (unop m + 1) then ⟨k.1, h⟩ else ⟨unop m, by simp⟩
  map_comp := by
    intro _ _ _ _ ⟨⟨⟨(h : _ ≤ _)⟩⟩⟩
    ext x
    simp
    split_ifs with h₁ h₂ _ _ h₃
    · rfl
    · exfalso
      apply h₂
      refine lt_of_lt_of_le h₁ ?_
      simpa using h
    · exfalso
      apply h₂
      refine lt_of_lt_of_le h₁ ?_
      simpa using h
    · rfl
    · congr 1
      exact (Nat.eq_of_le_of_lt_succ h h₃).symm
    · rfl

noncomputable def NatUnionInfty := of NatUnionInftyDiagram

proof_wanted NatUnionInftyIso : Nonempty (NatUnionInfty.toProfinite ≅ Profinite.NatUnionInfty)

end LightProfinite
