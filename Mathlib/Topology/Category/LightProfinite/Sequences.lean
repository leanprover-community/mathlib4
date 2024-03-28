import Mathlib.Topology.Category.LightProfinite.Basic
import Mathlib.Topology.Compactification.OnePoint

open CategoryTheory Limits Opposite Option

namespace Profinite

example : TopologicalSpace (OnePoint ℕ) := inferInstance

example : CompactSpace (OnePoint ℕ) := inferInstance

example : T2Space (OnePoint ℕ) := inferInstance

instance : TotallySeparatedSpace (OnePoint ℕ) where
  isTotallySeparated_univ x _ y _ hxy := by
    cases x with
    | none =>
      cases y with
      | none => tauto
      | some val =>
        refine ⟨{some val}ᶜ, {some val}, isOpen_compl_singleton, ?_, ?_, ?_, ?_, ?_⟩
        · refine (OnePoint.isOpen_iff_of_not_mem ?_).mpr (isOpen_discrete _)
          exact (some_ne_none val).symm
        all_goals simp [Set.union_comm]
    | some val =>
      cases y with
      | none =>
        refine ⟨{some val}, {some val}ᶜ, ?_, isOpen_compl_singleton, ?_, ?_, ?_, ?_⟩
        · refine (OnePoint.isOpen_iff_of_not_mem ?_).mpr (isOpen_discrete _)
          exact (some_ne_none val).symm
        all_goals simp
      | some val' =>
        refine ⟨{some val}, {some val}ᶜ, ?_, isOpen_compl_singleton, ?_, ?_, ?_, ?_⟩
        · refine (OnePoint.isOpen_iff_of_not_mem ?_).mpr (isOpen_discrete _)
          exact (some_ne_none val).symm
        all_goals aesop

def NatUnionInfty := of (OnePoint ℕ)

end Profinite

namespace LightProfinite

def NatUnionInftyDiagram : ℕᵒᵖ ⥤ FintypeCat where
  obj n := FintypeCat.of (Finset.range (unop n + 1))
  map {_ m} _ k := if h : k.1 ∈ Finset.range (unop m + 1) then ⟨k.1, h⟩ else ⟨unop m, by simp⟩
  map_comp := by
    intro _ _ _ _ ⟨⟨⟨(h : _ ≤ _)⟩⟩⟩
    ext x
    simp only [Nat.zero_eq, Finset.mem_range, FintypeCat.comp_apply]
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

noncomputable def NatUnionInftyIso : Profinite.NatUnionInfty ≅ NatUnionInfty.toProfinite  where
  hom := by
    refine ⟨fun a ↦ ?_, ?_⟩
    · sorry
    · sorry
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

end LightProfinite
