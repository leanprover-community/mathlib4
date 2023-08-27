import Mathlib.CategoryTheory.StructuredArrow
import Mathlib.CategoryTheory.Limits.Shapes.Equivalence

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
  hasTerminal : HasTerminal (RightExtension L F)

lemma HasRightKanExtension.mk' (F' : H ⥤ D) {L : C ⥤ H} {F : C ⥤ D} (α : L ⋙ F' ⟶ F)
    [F'.IsRightKanExtension α] : HasRightKanExtension L F where
  hasTerminal := (F'.rightKanExtensionUniversal α).hasTerminal

lemma hasRightKanExtension_iff (L : C ⥤ H) (F : C ⥤ D) :
    HasRightKanExtension L F ↔ HasTerminal (RightExtension L F) :=
  ⟨fun h => h.hasTerminal, fun h => ⟨h⟩⟩

section

variable (L : C ⥤ H) (F : C ⥤ D) [HasRightKanExtension L F]

noncomputable def rightExtensionTerminal : RightExtension L F :=
  have : HasTerminal (RightExtension L F) := HasRightKanExtension.hasTerminal
  ⊤_ _

noncomputable def rightKanExtension : H ⥤ D := (rightExtensionTerminal L F).left
noncomputable def rightKanExtensionCounit : L ⋙ rightKanExtension L F ⟶ F := (rightExtensionTerminal L F).hom

instance : (L.rightKanExtension F).IsRightKanExtension (L.rightKanExtensionCounit F) where
  nonempty_isUniversal := ⟨by
    have : HasTerminal (RightExtension L F) := HasRightKanExtension.hasTerminal
    apply terminalIsTerminal⟩

end

end Functor

namespace Equivalence

variable {C D : Type _} [Category C] [Category D] (e : C ≌ D)

def whiskeringLeft (E : Type _) [Category E] : (D ⥤ E) ≌ (C ⥤ E) where
  functor := (CategoryTheory.whiskeringLeft C D E).obj e.functor
  inverse := (CategoryTheory.whiskeringLeft D C E).obj e.inverse
  unitIso := (CategoryTheory.whiskeringLeft D D E).mapIso e.counitIso.symm
  counitIso := (CategoryTheory.whiskeringLeft C C E).mapIso e.unitIso.symm
  functor_unitIso_comp F := by
    ext Y
    dsimp
    rw [← F.map_id, ← F.map_comp]
    congr 1
    simp

end Equivalence

namespace Functor

variable {C H H' : Type _} [Category C] [Category H] [Category H']

instance (F : H ⥤ H') [IsEquivalence F] :
    IsEquivalence ((whiskeringLeft H H' C).obj F) := by
  change IsEquivalence (F.asEquivalence.whiskeringLeft C).functor
  infer_instance

end Functor

namespace Functor

variable {C D H H' : Type _} [Category C] [Category D] [Category H] [Category H']
  (L L' : C ⥤ H) (iso₁ : L ≅ L') (F F' : C ⥤ D) (e : H ≌ H') (iso₂ : F ≅ F')

noncomputable def rightExtensionEquivalenceOfPostcomp₁ :
    RightExtension (L ⋙ e.functor) F ≌ RightExtension L F := by
  have := CostructuredArrow.isEquivalencePre ((whiskeringLeft H H' D).obj e.functor) ((whiskeringLeft C H D).obj L) F
  exact Functor.asEquivalence (CostructuredArrow.pre ((whiskeringLeft H H' D).obj e.functor) ((whiskeringLeft C H D).obj L) F)

lemma hasRightExtension_iff_postcomp₁ :
    HasRightKanExtension L F ↔ HasRightKanExtension (L ⋙ e.functor) F := by
  simp only [hasRightKanExtension_iff,
    (rightExtensionEquivalenceOfPostcomp₁ L F e).hasTerminal_iff]

variable {L L'}

def rightExtensionEquivalenceOfIso₁ :
    RightExtension L F ≌ RightExtension L' F :=
  CostructuredArrow.mapNatIso ((whiskeringLeft C H D).mapIso iso₁)

lemma hasRightExtension_iff_of_iso₁ :
    HasRightKanExtension L F ↔ HasRightKanExtension L' F := by
  simp only [hasRightKanExtension_iff,
    (rightExtensionEquivalenceOfIso₁ iso₁ F).hasTerminal_iff]

variable (L) {F F'}

def rightExtensionEquivalenceOfIso₂ :
    RightExtension L F ≌ RightExtension L F' :=
  CostructuredArrow.mapIso iso₂

lemma hasRightExtension_iff_of_iso₂ :
    HasRightKanExtension L F ↔ HasRightKanExtension L F' := by
  simp only [hasRightKanExtension_iff,
    (rightExtensionEquivalenceOfIso₂ L iso₂).hasTerminal_iff]

end Functor

end CategoryTheory
