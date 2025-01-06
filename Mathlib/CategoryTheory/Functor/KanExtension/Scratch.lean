import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.CategoryTheory.Limits.Unit
import Mathlib.Data.Nat.Pairing

open CategoryTheory Limits

axiom jakob {J C H : Type*} [Category J] [Category C] [Category H] (K : J ⥤ C) (F : C ⥤ H)
  [HasLimit K] [HasLimit (K ⋙ F)] (h : F.obj (limit K) ≅ limit (K ⋙ F)) :
  PreservesLimit K F

abbrev K : Discrete WalkingPair ⥤ Discrete PUnit.{1} :=
  pair ⟨PUnit.unit⟩ ⟨PUnit.unit⟩

def F : Discrete PUnit.{1} ⥤ Type :=
  Discrete.functor fun _ => Nat

noncomputable def limitCompIso : limit (K ⋙ F) ≅ Nat × Nat :=
  HasLimit.isoOfNatIso (diagramIsoPair _) ≪≫ Types.binaryProductIso Nat Nat

instance preserves_limit : PreservesLimit K F :=
  jakob _ _ (Equiv.toIso Nat.pairEquiv.symm ≪≫ limitCompIso.symm)

theorem bijective : Function.Bijective (Prod.fst : Nat × Nat → Nat) := by
  erw [← isIso_iff_bijective, ← Types.binaryProductIso_inv_comp_fst,
    ← PreservesLimitPair.iso_inv_fst F ⟨PUnit.unit⟩ ⟨PUnit.unit⟩]
  infer_instance

theorem contr : False := by
  simpa using congrArg Prod.snd (@bijective.1 (0, 0) (0, 1) rfl)
