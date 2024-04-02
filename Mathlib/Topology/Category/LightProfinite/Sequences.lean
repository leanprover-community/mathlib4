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

-- def LightProfiniteOfCountable_diagram (X : Profinite) [Countable X] : ℕᵒᵖ ⥤ FintypeCat where
--   obj n := sorry
--   map := sorry
--   map_id := sorry
--   map_comp := sorry

-- def LightProfiniteOfCountable (X : Profinite) [Countable X] : LightProfinite := sorry

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

def extracted_1 (n : ℕ) : LocallyConstant Profinite.NatUnionInfty
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
    Profinite.NatUnionInfty ⟶ NatUnionInfty.toProfinite := by
  refine fromProfinite' extracted_1 ?_
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

theorem extracted_2 : Function.Bijective NatUnionInftyIso_hom := by
  simp only [NatUnionInftyIso_hom, fromProfinite']
  constructor
  · apply homMk_injective _ _
    intro a b h
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b =>
        have hh : extracted_1 (b + 1) none = extracted_1 (b + 1) (some b) := h (b + 1)
        simp only [extracted_1, Finset.mem_range, LocallyConstant.coe_mk] at hh
        split_ifs at hh with h'
        · simpa using Subtype.ext_iff_val.mp hh
        · simp [add_assoc] at h'
    | some a =>
      cases b with
      | none =>
        have hh : extracted_1 (a + 1) (some a) = extracted_1 (a + 1) none := h (a + 1)
        simp only [extracted_1, Finset.mem_range, LocallyConstant.coe_mk, dite_eq_right_iff] at hh
        specialize hh (by simp [add_assoc])
        simpa using Subtype.ext_iff_val.mp hh
      | some b =>
        have hh : extracted_1 (a + b) (some a) = extracted_1 (a + b) (some b) := h (a + b)
        simp only [extracted_1, Finset.mem_range, LocallyConstant.coe_mk] at hh
        split_ifs at hh with h₁ h₂ h₂
        · replace hh := Subtype.ext_iff_val.mp hh
          dsimp at hh
          rw [hh]
        · simp [add_comm a b, add_assoc] at h₂
        · simp [add_assoc] at h₁
        · simp [add_comm a b, add_assoc] at h₂
  · apply homMk_surjective _ _
    intro a n
    refine ⟨some (NatUnionInfty.proj n a).1, ?_⟩
    change extracted_1 n (some (NatUnionInfty.proj n a).1) = _
    simp [extracted_1]
    intro h
    rw [Subtype.ext_iff_val]
    have := ((proj NatUnionInfty n) a).prop
    simp only [concreteCategory_forget_obj, Finset.mem_range] at this
    simpa using lt_of_le_of_lt h this

instance : Mono NatUnionInftyIso_hom := by
  rw [Profinite.mono_iff_injective]
  exact extracted_2.1

-- TODO: prove that in general, any countable profinite space is light.
instance : Profinite.NatUnionInfty.IsLight :=
  Profinite.isLight_of_mono NatUnionInftyIso_hom

noncomputable def NatUnionInftyIso : ofIsLight Profinite.NatUnionInfty ≅ NatUnionInfty :=
  isoMk (Profinite.isoOfBijective NatUnionInftyIso_hom extracted_2)

end LightProfinite
