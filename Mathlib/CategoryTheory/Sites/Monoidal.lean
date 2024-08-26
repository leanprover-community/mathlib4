import Mathlib.CategoryTheory.Closed.FunctorCategory.Complete
import Mathlib.CategoryTheory.Localization.Monoidal
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import Mathlib.CategoryTheory.Sites.Localization

open CategoryTheory MonoidalCategory MonoidalClosed Limits

namespace CategoryTheory

variable {C : Type*} [Category C] (J : GrothendieckTopology C)
variable (A : Type*) [Category A] [MonoidalCategory A] [SymmetricCategory A] [MonoidalClosed A]
variable [∀ (F : Discrete Cᵒᵖ ⥤ A), (Discrete.functor id).HasRightKanExtension F]
variable [HasLimitsOfShape WalkingParallelPair A]
variable [HasWeakSheafify J A]

instance (F G : Cᵒᵖ ⥤ A) : IsIso ((presheafToSheaf J A).map
    (F ◁ ((sheafificationAdjunction J A).unit.app G))) := by
  rw [isIso_iff_isIso_yoneda_map]
  intro H
  sorry

instance (F : Sheaf J A) (P : Cᵒᵖ ⥤ A) : IsIso ((sheafificationAdjunction J A).unit.app
    ((ihom P).obj ((sheafToPresheaf J A).obj F))) := by
  revert F P
  rw [((Monoidal.Reflective.isIso_tfae (sheafificationAdjunction J A)).out 0 4:)]
  infer_instance

lemma isSheaf_ihom (F : Sheaf J A) (P : Cᵒᵖ ⥤ A) : Presheaf.IsSheaf J ((ihom P).obj F.val) := by
  erw [Presheaf.isSheaf_of_iso_iff (asIso ((sheafificationAdjunction J A).unit.app
    ((ihom P).obj ((sheafToPresheaf J A).obj F))))]
  exact ((presheafToSheaf J A).obj _).cond

instance : (J.W (A := A)).Monoidal where
  whiskerLeft P G₁ G₂ g h := by
    intro F hF
    constructor
    · intro a b hh
      let a' : G₂ ⟶ (ihom P).obj F := (ihom.adjunction P).homEquiv _ _ a
      let b' : G₂ ⟶ (ihom P).obj F := (ihom.adjunction P).homEquiv _ _ b
      have : g ≫ a' = g ≫ b' := by
        simp only [Adjunction.homEquiv_unit, Functor.id_obj, Functor.comp_obj, tensorLeft_obj,
          ihom.ihom_adjunction_unit, ihom.coev_naturality_assoc, a', b']
        simp only [← (ihom P).map_comp, hh]
      apply ((ihom.adjunction P).homEquiv _ _).injective
      exact (h ((ihom P).obj F) (isSheaf_ihom J A ⟨F, hF⟩ P)).1 this
    · intro a
      let a' : G₁ ⟶ (ihom P).obj F := (ihom.adjunction P).homEquiv _ _ a
      obtain ⟨b, hb⟩ := (h ((ihom P).obj F) (isSheaf_ihom J A ⟨F, hF⟩ P)).2 a'
      refine ⟨(ihom.adjunction P).homEquiv _ _|>.symm b, ?_⟩
      simp only [Adjunction.homEquiv_unit, Functor.id_obj, Functor.comp_obj, tensorLeft_obj,
        ihom.ihom_adjunction_unit, a'] at hb
      erw [Adjunction.homEquiv_counit]
      simp only [← id_tensorHom, tensorLeft_obj, Functor.id_obj, tensorLeft_map,
        ihom.ihom_adjunction_counit, ← tensor_comp_assoc, Category.comp_id, hb]
      simp
  whiskerRight {G₁ G₂} g h P := by
    -- We need symmetric monoidal here, or at least `tensorRight` to have a right adjoint.
    sorry

noncomputable instance : MonoidalCategory (Sheaf J A) :=
    inferInstanceAs (MonoidalCategory ((LocalizedMonoidal (presheafToSheaf J A) J.W (Iso.refl _))))

noncomputable abbrev presheafToSheafMonoidal : MonoidalFunctor (Cᵒᵖ ⥤ A) (Sheaf J A) :=
  toLocalizedMonoidal (presheafToSheaf J A) J.W (Iso.refl _)

noncomputable abbrev sheafificationAdjunctionMonoidal :
    (presheafToSheafMonoidal J A).toFunctor ⊣ sheafToPresheaf J A := sheafificationAdjunction J A

noncomputable instance : MonoidalClosed (Sheaf J A) :=
  Monoidal.Reflective.monoidalClosed (sheafificationAdjunctionMonoidal J A)

end CategoryTheory
