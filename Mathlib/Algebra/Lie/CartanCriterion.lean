import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.Algebra.Lie.Killing

namespace LieAlgebra

variable {k L V : Type*} [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
variable [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V]

example [IsSemisimple k L] : HasTrivialRadical k L := by
  infer_instance

example [Module.Finite k L] [IsKilling k L] : IsSemisimple k L := by
  infer_instance

example [Module.Finite k L] [IsKilling k L] : HasTrivialRadical k L := by
  infer_instance

-- move this
instance [Subsingleton L] : IsSolvable k L := by
  constructor
  use 0
  ext x
  simp [Subsingleton.elim x 0]

-- move this
/-- The Killing form is symmetric. -/
lemma killingForm_symm (X Y : L) : killingForm k L X Y = killingForm k L Y X :=
  LieModule.traceForm_comm _ _ _ _ _

/-- The Killing form is symmetric. -/
lemma killingForm_isSymm : (killingForm k L).IsSymm :=
  LieModule.traceForm_isSymm _ _ _

private theorem isSolvable_iff_of_algClosed [Module.Finite k L] [IsAlgClosed k] :
    IsSolvable k L ↔ ∀ X Y : L, Y ∈ LieAlgebra.derivedSeries k L 1 → killingForm k L X Y = 0 := by
  obtain _ | _ := subsingleton_or_nontrivial L
  · simp; infer_instance
  constructor
  · intro h
    obtain ⟨χ, hχ⟩ := LieModule.exists_forall_lie_eq_smul_of_isSolvable k L L
    obtain ⟨⟨Z, hZ⟩, hZ0⟩ := exists_ne (0 : LieModule.weightSpace L χ) 
    simp only [ne_eq, LieSubmodule.mk_eq_zero] at hZ0
    simp only [LieModule.mem_weightSpace] at hZ
    sorry
  · intro h
    sorry

theorem isSolvable_iff [Module.Finite k L] :
    IsSolvable k L ↔ ∀ X Y : L, Y ∈ LieAlgebra.derivedSeries k L 1 → killingForm k L X Y = 0 := by
  obtain _ | _ := subsingleton_or_nontrivial L
  · simp; infer_instance
  constructor
  · intro h
    -- WLOG: k is algebraically closed
    -- have := LieModule.exists_forall_lie_eq_smul_of_isSolvable k L L
    sorry
  · intro h
    sorry

instance [Module.Finite k L] [HasTrivialRadical k L] : IsKilling k L := by
  constructor
  suffices IsSolvable k (LieIdeal.killingCompl k L ⊤) from HasTrivialRadical.eq_bot_of_isSolvable _
  rw [isSolvable_iff]
  intro X Y hY
  rw [LieIdeal.killingForm_eq]
  show killingForm k L X Y = 0
  have := X.2
  rw [LieIdeal.mem_killingCompl] at this
  rw [killingForm_symm]
  apply this
  simp

example [Module.Finite k L] [IsSemisimple k L] : IsKilling k L := by
  infer_instance

example [Module.Finite k L] [HasTrivialRadical k L] : IsSemisimple k L := by
  infer_instance

end LieAlgebra
