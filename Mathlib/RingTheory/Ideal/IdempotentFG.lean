/-
Copyright (c) 2018 Mario Carneiro, Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Buzzard
-/
import Mathlib.Algebra.Ring.Idempotents
import Mathlib.RingTheory.Finiteness
import Mathlib.Order.Basic

#align_import ring_theory.ideal.idempotent_fg from "leanprover-community/mathlib"@"25cf7631da8ddc2d5f957c388bf5e4b25a77d8dc"

/-!
## Lemmas on idempotent finitely generated ideals
-/


namespace Ideal

/-- A finitely generated idempotent ideal is generated by an idempotent element -/
theorem isIdempotentElem_iff_of_fg {R : Type*} [CommRing R] (I : Ideal R) (h : I.FG) :
    IsIdempotentElem I ↔ ∃ e : R, IsIdempotentElem e ∧ I = R ∙ e := by
  constructor
  · intro e
    obtain ⟨r, hr, hr'⟩ :=
      Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul I I h
        (by
          rw [smul_eq_mul]
          exact e.ge)
    simp_rw [smul_eq_mul] at hr'
    refine ⟨r, hr' r hr, antisymm ?_ ((Submodule.span_singleton_le_iff_mem _ _).mpr hr)⟩
    intro x hx
    rw [← hr' x hx]
    exact Ideal.mem_span_singleton'.mpr ⟨_, mul_comm _ _⟩
  · rintro ⟨e, he, rfl⟩
    simp [IsIdempotentElem, Ideal.span_singleton_mul_span_singleton, he.eq]
#align ideal.is_idempotent_elem_iff_of_fg Ideal.isIdempotentElem_iff_of_fg

theorem isIdempotentElem_iff_eq_bot_or_top {R : Type*} [CommRing R] [IsDomain R] (I : Ideal R)
    (h : I.FG) : IsIdempotentElem I ↔ I = ⊥ ∨ I = ⊤ := by
  constructor
  · intro H
    obtain ⟨e, he, rfl⟩ := (I.isIdempotentElem_iff_of_fg h).mp H
    simp only [Ideal.submodule_span_eq, Ideal.span_singleton_eq_bot]
    apply Or.imp id _ (IsIdempotentElem.iff_eq_zero_or_one.mp he)
    rintro rfl
    simp
  · rintro (rfl | rfl) <;> simp [IsIdempotentElem]
#align ideal.is_idempotent_elem_iff_eq_bot_or_top Ideal.isIdempotentElem_iff_eq_bot_or_top

end Ideal
