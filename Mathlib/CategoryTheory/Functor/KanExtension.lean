import Mathlib.CategoryTheory.StructuredArrow

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C D H : Type _} [Category C] [Category D] [Category H]

abbrev RightExtension (L : C ⥤ H) (F : C ⥤ D) :=
  CostructuredArrow ((whiskeringLeft C H D).obj L) F

@[simps!]
def RightExtension.mk (F' : H ⥤ D) {L : C ⥤ H} {F : C ⥤ D} (α : L ⋙ F' ⟶ F) :
    RightExtension L F := CostructuredArrow.mk α

variable (F' : H ⥤ D) {L : C ⥤ H} {F : C ⥤ D} (α : L ⋙ F' ⟶ F)

class IsRightKanExtension (F' : H ⥤ D) {L : C ⥤ H} {F : C ⥤ D} (α : L ⋙ F' ⟶ F) : Prop where
  nonempty_isUniversal : Nonempty (RightExtension.mk F' α).IsUniversal

section

variable [F'.IsRightKanExtension α]

noncomputable def rightKanExtensionUniversal : (RightExtension.mk F' α).IsUniversal :=
    IsRightKanExtension.nonempty_isUniversal.some

noncomputable def rightKanExtensionLift (G : H ⥤ D) (β : L ⋙ G ⟶ F) : G ⟶ F' :=
  (F'.rightKanExtensionUniversal α).lift (RightExtension.mk G β)

lemma rightKanExtension_fac (G : H ⥤ D) (β : L ⋙ G ⟶ F) :
    whiskerLeft L (F'.rightKanExtensionLift α G β) ≫ α = β :=
  (F'.rightKanExtensionUniversal α).fac (RightExtension.mk G β)

@[reassoc (attr := simp)]
lemma rightKanExtension_fac_app (G : H ⥤ D) (β : L ⋙ G ⟶ F) (X : C) :
    (F'.rightKanExtensionLift α G β).app (L.obj X) ≫ α.app X = β.app X :=
  NatTrans.congr_app (F'.rightKanExtension_fac α G β) X

lemma rightKanExtension_ext {G : H ⥤ D} (γ₁ γ₂ : G ⟶ F')
    (hγ : whiskerLeft L γ₁ ≫ α = whiskerLeft L γ₂ ≫ α) : γ₁ = γ₂ :=
  (F'.rightKanExtensionUniversal α).hom_ext hγ

end

class HasRightKanExtension (L : C ⥤ H) (F : C ⥤ D) : Prop where
  nonempty_hasTerminal : Nonempty (HasTerminal (RightExtension L F))

lemma HasRightKanExtension.mk' (F' : H ⥤ D) {L : C ⥤ H} {F : C ⥤ D} (α : L ⋙ F' ⟶ F)
    [F'.IsRightKanExtension α] : HasRightKanExtension L F where
  nonempty_hasTerminal := ⟨(F'.rightKanExtensionUniversal α).hasTerminal⟩

section

variable (L : C ⥤ H) (F : C ⥤ D) [HasRightKanExtension L F]

noncomputable def rightExtensionTerminal : RightExtension L F :=
  have : HasTerminal (RightExtension L F) := HasRightKanExtension.nonempty_hasTerminal.some
  ⊤_ _

noncomputable def rightKanExtension : H ⥤ D := (rightExtensionTerminal L F).left
noncomputable def rightKanExtensionCounit : L ⋙ rightKanExtension L F ⟶ F := (rightExtensionTerminal L F).hom

instance : (L.rightKanExtension F).IsRightKanExtension (L.rightKanExtensionCounit F) where
  nonempty_isUniversal := ⟨by
    have : HasTerminal (RightExtension L F) := HasRightKanExtension.nonempty_hasTerminal.some
    apply terminalIsTerminal⟩

end

end Functor

end CategoryTheory
