import Mathlib.Topology.Category.LightProfinite.IsLightIso
import Mathlib.Topology.Compactification.OnePoint

open CategoryTheory Limits Opposite Option

namespace Profinite

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

-- TODO: prove `IsLight.of_countable` and deduce this
instance : IsLight NatUnionInfty := sorry

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

def extracted_1 (n : ℕ) : LocallyConstant (ofIsLight Profinite.NatUnionInfty).toProfinite
    (NatUnionInfty.diagram.obj ⟨n⟩) where
  toFun a := by
    cases a with
    | none => exact ⟨n, Finset.self_mem_range_succ n⟩
    | some val => exact if h : _ then ⟨val, h⟩ else ⟨n, Finset.self_mem_range_succ n⟩
  isLocallyConstant := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro ⟨y, hy⟩
    by_cases h : y = n
    · rw [OnePoint.isOpen_iff_of_mem]
      · simp only [Finset.mem_range, isClosed_discrete, true_and]
        rw [isCompact_iff_finite, ← Set.preimage_compl]
        subst h
        refine Set.Finite.preimage (Function.Injective.injOn OnePoint.coe_injective _) ?_
        rw [← Set.preimage_compl]
        refine Set.Finite.preimage ?_ (inferInstance : Finite _)
        intro a ha b hb h
        cases a with
        | none => simp [OnePoint.infty] at ha
        | some a =>
          cases b with
          | none => simp [OnePoint.infty] at hb
          | some b =>
            simp only [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage,
              Set.mem_singleton_iff, dite_eq_right_iff, not_forall] at ha hb
            obtain ⟨ha, _⟩ := ha
            obtain ⟨hb, _⟩ := hb
            rw [Subtype.ext_iff_val] at h
            simp only [ha, reduceDite, hb] at h
            rw [h]
      · simp [OnePoint.infty, h]
    · rw [OnePoint.isOpen_iff_of_not_mem]
      · simp
      · simp only [OnePoint.infty, Finset.mem_range, Set.mem_preimage, Set.mem_singleton_iff]
        rw [Subtype.ext_iff_val]
        aesop

noncomputable def NatUnionInftyIso_hom :
    LightProfinite.ofIsLight Profinite.NatUnionInfty ⟶ NatUnionInfty := by
  refine homMk' extracted_1 ?_
  · intro n
    ext x
    cases x with
    | none =>
      simp only [transitionMap, extracted_1, Finset.mem_range, LocallyConstant.coe_mk,
        Function.comp_apply]
      simp [NatUnionInfty, of, NatUnionInftyDiagram]
    | some val =>
      simp [transitionMap, extracted_1]
      simp [NatUnionInfty, of, NatUnionInftyDiagram]
      split_ifs with h₁ h₂ h₃ h₄
      · rfl
      · rfl
      · simp at h₃
      · simpa using lt_of_le_of_lt (not_lt.mp h₁) h₄
      · rfl

noncomputable def NatUnionInftyIso : Profinite.NatUnionInfty ≅ NatUnionInfty.toProfinite  where
  hom := NatUnionInftyIso_hom
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

end LightProfinite
