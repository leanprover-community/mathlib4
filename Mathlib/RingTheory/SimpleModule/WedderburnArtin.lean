/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.SimpleRing.Congr

/-!
# Wedderburn-Artin Theorem
-/

universe u
variable {R : Type u} [Ring R]

/-- A simple ring is semisimple iff it is artinian, iff it has a minimal left ideal. -/
theorem IsSimpleRing.tfae [IsSimpleRing R] : List.TFAE
    [IsSemisimpleRing R, IsArtinianRing R, ∃ I : Ideal R, IsAtom I] := by
  tfae_have 1 → 2 := fun _ ↦ inferInstance
  tfae_have 2 → 3 := fun _ ↦ IsAtomic.exists_atom _
  tfae_have 3 → 1 := fun ⟨I, hI⟩ ↦ by
    have ⟨_, h⟩ := isSimpleRing_iff_isTwoSided_imp.mp ‹IsSimpleRing R›
    simp_rw [← isEndInvariant_iff_isTwoSided] at h
    have := isSimpleModule_iff_isAtom.mpr hI
    obtain eq | eq := h _ (isEndInvariant_isotypicComponent R R I)
    · exact (hI.bot_lt.not_le <| (le_sSup <| by exact ⟨.refl ..⟩).trans_eq eq).elim
    exact .congr (.symm <| .trans (.ofEq _ _ eq) Submodule.topEquiv)
  tfae_finish

theorem IsSimpleRing.isSemisimpleRing_iff_isArtinianRing [IsSimpleRing R] :
    IsSemisimpleRing R ↔ IsArtinianRing R := tfae.out 0 1

theorem isSimpleRing_isArtinianRing_iff :
    IsSimpleRing R ∧ IsArtinianRing R ↔ IsSemisimpleRing R ∧ IsIsotypic R R ∧ Nontrivial R := by
  refine ⟨fun ⟨_, _⟩ ↦ ?_, fun ⟨_, _, _⟩ ↦ ?_⟩
  on_goal 1 => have := IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mpr ‹_›
  all_goals simp_rw [isIsotypic_iff_isEndInvariant_imp_bot_or_top,
      isEndInvariant_iff_isTwoSided, isSimpleRing_iff_isTwoSided_imp] at *
  · exact ⟨this, by rwa [and_comm]⟩
  · exact ⟨⟨‹_›, ‹_›⟩, inferInstance⟩

section simple_artinian

variable (R) [IsSimpleRing R] [IsArtinianRing R]

theorem IsSimpleRing.exists_ringEquiv_matrix_end_mulOpposite :
    ∃ (n : ℕ) (_ : NeZero n) (I : Ideal R) (_ : IsSimpleModule R I),
      Nonempty (R ≃+* Matrix (Fin n) (Fin n) (Module.End R I)ᵐᵒᵖ) := by
  have ⟨_, iso, _⟩ := isSimpleRing_isArtinianRing_iff (R := R).mp ⟨‹_›, ‹_›⟩
  have ⟨n, hn, S, hS, ⟨e⟩⟩ := iso.linearEquiv_fun
  refine ⟨n, hn, S, hS, ⟨.trans (.opOp R) <| .trans (.op ?_) (.symm .mopMatrix)⟩⟩
  exact (Module.moduleEndSelf R).trans e.conjRingEquiv |>.trans (endVecRingEquivMatrixEnd ..)

theorem IsSimpleRing.exists_ringEquiv_matrix_divisionRing :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type u) (_ : DivisionRing D),
      Nonempty (R ≃+* Matrix (Fin n) (Fin n) D) := by
  have ⟨n, hn, I, _, ⟨e⟩⟩ := IsSimpleRing.exists_ringEquiv_matrix_end_mulOpposite R
  classical exact ⟨n, hn, _, inferInstance, ⟨e⟩⟩

end simple_artinian
