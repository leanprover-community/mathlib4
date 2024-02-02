import Mathlib.CategoryTheory.StructuredArrow
import Mathlib.CategoryTheory.Limits.Shapes.Equivalence

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C D H : Type _} [Category C] [Category D] [Category H]

abbrev RightExtension (L : C ⥤ H) (F : C ⥤ D) :=
  CostructuredArrow ((whiskeringLeft C H D).obj L) F

abbrev LeftExtension (L : C ⥤ H) (F : C ⥤ D) :=
  StructuredArrow F ((whiskeringLeft C H D).obj L)

@[simps!]
def RightExtension.mk (F' : H ⥤ D) {L : C ⥤ H} {F : C ⥤ D} (α : L ⋙ F' ⟶ F) :
    RightExtension L F := CostructuredArrow.mk α

@[simps!]
def LeftExtension.mk (F' : H ⥤ D) {L : C ⥤ H} {F : C ⥤ D} (α : F ⟶ L ⋙ F') :
    LeftExtension L F := StructuredArrow.mk α

section

class IsRightKanExtension (F' : H ⥤ D) {L : C ⥤ H} {F : C ⥤ D} (α : L ⋙ F' ⟶ F) : Prop where
  nonempty_isUniversal : Nonempty (RightExtension.mk F' α).IsUniversal

variable (F' : H ⥤ D) {L : C ⥤ H} {F : C ⥤ D} (α : L ⋙ F' ⟶ F) [F'.IsRightKanExtension α]

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

section

class IsLeftKanExtension (F' : H ⥤ D) {L : C ⥤ H} {F : C ⥤ D} (α : F ⟶ L ⋙ F') : Prop where
  nonempty_isUniversal : Nonempty (LeftExtension.mk F' α).IsUniversal

variable (F' : H ⥤ D) {L : C ⥤ H} {F : C ⥤ D} (α : F ⟶ L ⋙ F') [F'.IsLeftKanExtension α]

noncomputable def leftKanExtensionUniversal : (LeftExtension.mk F' α).IsUniversal :=
    IsLeftKanExtension.nonempty_isUniversal.some

noncomputable def leftKanExtensionDesc (G : H ⥤ D) (β : F ⟶ L ⋙ G) : F' ⟶ G :=
  (F'.leftKanExtensionUniversal α).desc (LeftExtension.mk G β)

lemma leftKanExtension_fac (G : H ⥤ D) (β : F ⟶ L ⋙ G) :
    α ≫ whiskerLeft L (F'.leftKanExtensionDesc α G β) = β :=
  (F'.leftKanExtensionUniversal α).fac (LeftExtension.mk G β)

@[reassoc (attr := simp)]
lemma leftKanExtension_fac_app (G : H ⥤ D) (β : F ⟶ L ⋙ G) (X : C) :
    α.app X ≫ (F'.leftKanExtensionDesc α G β).app (L.obj X) = β.app X :=
  NatTrans.congr_app (F'.leftKanExtension_fac α G β) X

lemma leftKanExtension_ext {G : H ⥤ D} (γ₁ γ₂ : F' ⟶ G)
    (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiskerLeft L γ₂) : γ₁ = γ₂ :=
  (F'.leftKanExtensionUniversal α).hom_ext hγ

lemma isLeftKanExtension_of_iso {F' : H ⥤ D} {F'' : H ⥤ D} (e : F' ≅ F'')
    {L : C ⥤ H} {F : C ⥤ D} (α : F ⟶ L ⋙ F') (α' : F ⟶ L ⋙ F'')
    (comm : α ≫ whiskerLeft L e.hom = α') [F'.IsLeftKanExtension α] :
    F''.IsLeftKanExtension α' :=
  ⟨⟨IsInitial.ofIso (F'.leftKanExtensionUniversal α) (StructuredArrow.isoMk e comm)⟩⟩

lemma isLeftKanExtension_iff_iso {F' : H ⥤ D} {F'' : H ⥤ D} (e : F' ≅ F'')
    {L : C ⥤ H} {F : C ⥤ D} (α : F ⟶ L ⋙ F') (α' : F ⟶ L ⋙ F'')
    (comm : α ≫ whiskerLeft L e.hom = α') :
    F'.IsLeftKanExtension α ↔ F''.IsLeftKanExtension α' := by
  constructor
  · intro _
    exact isLeftKanExtension_of_iso e α α' comm
  · intro _
    refine' isLeftKanExtension_of_iso e.symm α' α _
    rw [← comm, assoc, ← whiskerLeft_comp, Iso.symm_hom, e.hom_inv_id, whiskerLeft_id', comp_id]

end

class HasRightKanExtension (L : C ⥤ H) (F : C ⥤ D) : Prop where
  hasTerminal : HasTerminal (RightExtension L F)

lemma HasRightKanExtension.mk' (F' : H ⥤ D) {L : C ⥤ H} {F : C ⥤ D} (α : L ⋙ F' ⟶ F)
    [F'.IsRightKanExtension α] : HasRightKanExtension L F where
  hasTerminal := (F'.rightKanExtensionUniversal α).hasTerminal

lemma hasRightKanExtension_iff (L : C ⥤ H) (F : C ⥤ D) :
    HasRightKanExtension L F ↔ HasTerminal (RightExtension L F) :=
  ⟨fun h => h.hasTerminal, fun h => ⟨h⟩⟩

class HasLeftKanExtension (L : C ⥤ H) (F : C ⥤ D) : Prop where
  hasInitial : HasInitial (LeftExtension L F)

lemma HasLeftKanExtension.mk' (F' : H ⥤ D) {L : C ⥤ H} {F : C ⥤ D} (α : F ⟶ L ⋙ F')
    [F'.IsLeftKanExtension α] : HasLeftKanExtension L F where
  hasInitial := (F'.leftKanExtensionUniversal α).hasInitial

lemma hasLeftKanExtension_iff (L : C ⥤ H) (F : C ⥤ D) :
    HasLeftKanExtension L F ↔ HasInitial (LeftExtension L F) :=
  ⟨fun h => h.hasInitial, fun h => ⟨h⟩⟩

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

section

variable (L : C ⥤ H) (F : C ⥤ D) [HasLeftKanExtension L F]

noncomputable def leftExtensionInitial : LeftExtension L F :=
  have : HasInitial (LeftExtension L F) := HasLeftKanExtension.hasInitial
  ⊥_ _

noncomputable def leftKanExtension : H ⥤ D := (leftExtensionInitial L F).right
noncomputable def leftKanExtensionUnit : F ⟶ L ⋙ leftKanExtension L F := (leftExtensionInitial L F).hom

instance : (L.leftKanExtension F).IsLeftKanExtension (L.leftKanExtensionUnit F) where
  nonempty_isUniversal := ⟨by
    have : HasInitial (LeftExtension L F) := HasLeftKanExtension.hasInitial
    apply initialIsInitial⟩

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
    rw [← F.map_id, ← F.map_comp, counitInv_functor_comp]

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

noncomputable def leftExtensionEquivalenceOfPostcomp₁ :
    LeftExtension (L ⋙ e.functor) F ≌ LeftExtension L F := by
  have := StructuredArrow.isEquivalencePre F ((whiskeringLeft H H' D).obj e.functor) ((whiskeringLeft C H D).obj L)
  exact Functor.asEquivalence (StructuredArrow.pre F ((whiskeringLeft H H' D).obj e.functor) ((whiskeringLeft C H D).obj L))

lemma hasLeftExtension_iff_postcomp₁ :
    HasLeftKanExtension L F ↔ HasLeftKanExtension (L ⋙ e.functor) F := by
  simp only [hasLeftKanExtension_iff,
    (leftExtensionEquivalenceOfPostcomp₁ L F e).hasInitial_iff]

variable {L L'}

def rightExtensionEquivalenceOfIso₁ :
    RightExtension L F ≌ RightExtension L' F :=
  CostructuredArrow.mapNatIso ((whiskeringLeft C H D).mapIso iso₁)

lemma hasRightExtension_iff_of_iso₁ :
    HasRightKanExtension L F ↔ HasRightKanExtension L' F := by
  simp only [hasRightKanExtension_iff,
    (rightExtensionEquivalenceOfIso₁ iso₁ F).hasTerminal_iff]

def leftExtensionEquivalenceOfIso₁ :
    LeftExtension L F ≌ LeftExtension L' F :=
  StructuredArrow.mapNatIso ((whiskeringLeft C H D).mapIso iso₁)

lemma hasLeftExtension_iff_of_iso₁ :
    HasLeftKanExtension L F ↔ HasLeftKanExtension L' F := by
  simp only [hasLeftKanExtension_iff,
    (leftExtensionEquivalenceOfIso₁ iso₁ F).hasInitial_iff]

variable (L) {F F'}

def rightExtensionEquivalenceOfIso₂ :
    RightExtension L F ≌ RightExtension L F' :=
  CostructuredArrow.mapIso iso₂

lemma hasRightExtension_iff_of_iso₂ :
    HasRightKanExtension L F ↔ HasRightKanExtension L F' := by
  simp only [hasRightKanExtension_iff,
    (rightExtensionEquivalenceOfIso₂ L iso₂).hasTerminal_iff]

def leftExtensionEquivalenceOfIso₂ :
    LeftExtension L F ≌ LeftExtension L F' :=
  StructuredArrow.mapIso iso₂

lemma hasLeftExtension_iff_of_iso₂ :
    HasLeftKanExtension L F ↔ HasLeftKanExtension L F' := by
  simp only [hasLeftKanExtension_iff,
    (leftExtensionEquivalenceOfIso₂ L iso₂).hasInitial_iff]

end Functor

end CategoryTheory
