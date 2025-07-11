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
variable (R₀ : Type*) {R : Type u} [CommSemiring R₀] [Ring R] [Algebra R₀ R]

/-- A simple ring is semisimple iff it is artinian, iff it has a minimal left ideal. -/
theorem IsSimpleRing.tfae [IsSimpleRing R] : List.TFAE
    [IsSemisimpleRing R, IsArtinianRing R, ∃ I : Ideal R, IsAtom I] := by
  tfae_have 1 → 2 := fun _ ↦ inferInstance
  tfae_have 2 → 3 := fun _ ↦ IsAtomic.exists_atom _
  tfae_have 3 → 1 := fun ⟨I, hI⟩ ↦ by
    have ⟨_, h⟩ := isSimpleRing_iff_isTwoSided_imp.mp ‹IsSimpleRing R›
    simp_rw [← isFullyInvariant_iff_isTwoSided] at h
    have := isSimpleModule_iff_isAtom.mpr hI
    obtain eq | eq := h _ (isFullyInvariant_isotypicComponent R R I)
    · exact (hI.bot_lt.not_ge <| (le_sSup <| by exact ⟨.refl ..⟩).trans_eq eq).elim
    exact .congr (.symm <| .trans (.ofEq _ _ eq) Submodule.topEquiv)
  tfae_finish

theorem IsSimpleRing.isSemisimpleRing_iff_isArtinianRing [IsSimpleRing R] :
    IsSemisimpleRing R ↔ IsArtinianRing R := tfae.out 0 1

theorem isSimpleRing_isArtinianRing_iff :
    IsSimpleRing R ∧ IsArtinianRing R ↔ IsSemisimpleRing R ∧ IsIsotypic R R ∧ Nontrivial R := by
  refine ⟨fun ⟨_, _⟩ ↦ ?_, fun ⟨_, _, _⟩ ↦ ?_⟩
  on_goal 1 => have := IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mpr ‹_›
  all_goals simp_rw [isIsotypic_iff_isFullyInvariant_imp_bot_or_top,
      isFullyInvariant_iff_isTwoSided, isSimpleRing_iff_isTwoSided_imp] at *
  · exact ⟨this, by rwa [and_comm]⟩
  · exact ⟨⟨‹_›, ‹_›⟩, inferInstance⟩

namespace IsSimpleRing

variable (R) [IsSimpleRing R] [IsArtinianRing R]

theorem isIsotypic : IsIsotypic R R :=
  (isSimpleRing_isArtinianRing_iff.mp ⟨‹_›, ‹_›⟩).2.1

instance (priority := low) : IsSemisimpleRing R :=
  (isSimpleRing_isArtinianRing_iff.mp ⟨‹_›, ‹_›⟩).1

/-- The Wedderburn–Artin Theorem: an Artinian simple ring is isomorphic to a matrix
ring over the opposite of the endomorphism ring of its simple module. -/
theorem exists_ringEquiv_matrix_end_mulOpposite :
    ∃ (n : ℕ) (_ : NeZero n) (I : Ideal R) (_ : IsSimpleModule R I),
      Nonempty (R ≃+* Matrix (Fin n) (Fin n) (Module.End R I)ᵐᵒᵖ) := by
  have ⟨n, hn, S, hS, ⟨e⟩⟩ := (isIsotypic R).linearEquiv_fun
  refine ⟨n, hn, S, hS, ⟨.trans (.opOp R) <| .trans (.op ?_) (.symm .mopMatrix)⟩⟩
  exact .trans (.moduleEndSelf R) <| .trans e.conjRingEquiv (endVecRingEquivMatrixEnd ..)

/-- The Wedderburn–Artin Theorem: an Artinian simple ring is isomorphic to a matrix
ring over a division ring. -/
theorem exists_ringEquiv_matrix_divisionRing :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type u) (_ : DivisionRing D),
      Nonempty (R ≃+* Matrix (Fin n) (Fin n) D) := by
  have ⟨n, hn, I, _, ⟨e⟩⟩ := exists_ringEquiv_matrix_end_mulOpposite R
  classical exact ⟨n, hn, _, _, ⟨e⟩⟩

/-- The Wedderburn–Artin Theorem, algebra form: an Artinian simple algebra is isomorphic
to a matrix algebra over the opposite of the endomorphism algebra of its simple module. -/
theorem exists_algEquiv_matrix_end_mulOpposite :
    ∃ (n : ℕ) (_ : NeZero n) (I : Ideal R) (_ : IsSimpleModule R I),
      Nonempty (R ≃ₐ[R₀] Matrix (Fin n) (Fin n) (Module.End R I)ᵐᵒᵖ) := by
  have ⟨n, hn, S, hS, ⟨e⟩⟩ := (isIsotypic R).linearEquiv_fun
  refine ⟨n, hn, S, hS, ⟨.trans (.opOp R₀ R) <| .trans (.op ?_) (.symm .mopMatrix)⟩⟩
  exact .trans (.moduleEndSelf R₀) <| .trans (e.algConj R₀) (endVecAlgEquivMatrixEnd ..)

/-- The Wedderburn–Artin Theorem, algebra form: an Artinian simple algebra is isomorphic
to a matrix algebra over a division algebra. -/
theorem exists_algEquiv_matrix_divisionRing :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type u) (_ : DivisionRing D) (_ : Algebra R₀ D),
      Nonempty (R ≃ₐ[R₀] Matrix (Fin n) (Fin n) D) := by
  have ⟨n, hn, I, _, ⟨e⟩⟩ := exists_algEquiv_matrix_end_mulOpposite R₀ R
  classical exact ⟨n, hn, _, _, _, ⟨e⟩⟩

/-- The Wedderburn–Artin Theorem, algebra form, finite case: a finite Artinian simple algebra is
isomorphic to a matrix algebra over a finite division algebra. -/
theorem exists_algEquiv_matrix_divisionRing_finite [Module.Finite R₀ R] :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type u) (_ : DivisionRing D) (_ : Algebra R₀ D)
      (_ : Module.Finite R₀ D), Nonempty (R ≃ₐ[R₀] Matrix (Fin n) (Fin n) D) := by
  have ⟨n, hn, I, _, ⟨e⟩⟩ := exists_algEquiv_matrix_end_mulOpposite R₀ R
  have := Module.Finite.equiv e.toLinearEquiv
  classical exact ⟨n, hn, _, _, _, .of_surjective (Matrix.entryLinearMap R₀
    (Module.End R I)ᵐᵒᵖ (0 : Fin n) (0 : Fin n)) fun f ↦ ⟨fun _ _ ↦ f, rfl⟩, ⟨e⟩⟩

end IsSimpleRing
