import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Functor.KanExtension

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C D H : Type _} [Category C] [Category D] [Category H]
  (LF : H ⥤ D) {F F' : C ⥤ D} (e : F ≅ F') {L : C ⥤ H} (α : L ⋙ LF ⟶ F)
  (W : MorphismProperty C)

abbrev IsLeftDerivedFunctor [L.IsLocalization W] := LF.IsRightKanExtension α

variable (F L)

class HasLeftDerivedFunctor : Prop where
  hasRightKanExtension' : HasRightKanExtension W.Q F

variable [L.IsLocalization W]

lemma hasLeftDerivedFunctor_iff :
    HasLeftDerivedFunctor F W ↔ HasRightKanExtension L F := by
  have : L.IsLocalization W := inferInstance
  have : HasLeftDerivedFunctor F W ↔ HasRightKanExtension W.Q F :=
    ⟨fun h => h.hasRightKanExtension', fun h => ⟨h⟩⟩
  rw [this, hasRightExtension_iff_postcomp₁ W.Q F (Localization.uniq W.Q L W),
    hasRightExtension_iff_of_iso₁ (Localization.compUniqFunctor W.Q L W) F]

variable {F}

lemma hasLeftDerivedFunctor_iff_of_iso :
    HasLeftDerivedFunctor F W ↔ HasLeftDerivedFunctor F' W := by
  rw [hasLeftDerivedFunctor_iff F W.Q W, hasLeftDerivedFunctor_iff F' W.Q W,
    hasRightExtension_iff_of_iso₂ W.Q e]

variable (F)

lemma HasLeftDerivedFunctor.hasRightKanExtension [HasLeftDerivedFunctor F W] :
    HasRightKanExtension L F := by
  simpa only [← hasLeftDerivedFunctor_iff F L W]

lemma HasLeftDerivedFunctor.mk' [LF.IsLeftDerivedFunctor α W] :
    HasLeftDerivedFunctor F W := by
  simpa only [hasLeftDerivedFunctor_iff F L W] using HasRightKanExtension.mk' LF α

section

variable [F.HasLeftDerivedFunctor W]

noncomputable def leftDerived : H ⥤ D :=
  have := HasLeftDerivedFunctor.hasRightKanExtension F L W
  rightKanExtension L F

noncomputable def leftDerivedCounit : L ⋙ F.leftDerived L W ⟶ F :=
  have := HasLeftDerivedFunctor.hasRightKanExtension F L W
  rightKanExtensionCounit L F

instance : (F.leftDerived L W).IsLeftDerivedFunctor (F.leftDerivedCounit L W) W := by
  dsimp [leftDerived, leftDerivedCounit]
  infer_instance

end

end Functor

end CategoryTheory
