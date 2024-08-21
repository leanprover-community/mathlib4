import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Localization.Monoidal
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.CategoryTheory.Sites.Localization

universe v u w

open CategoryTheory Localization MonoidalCategory Opposite MonoidalClosed

attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable (A : Type*) [Category A] [MonoidalCategory A]

instance : (J.W (A := A)).Monoidal where
  whiskerLeft P G₁ G₂ g h := by
    intro F hF
    -- This needs some more assumptions on `A`:
    let _ : MonoidalClosed (Cᵒᵖ ⥤ A) := sorry
    have hP : ∀ (P : Cᵒᵖ ⥤ A), Presheaf.IsSheaf J ((ihom P).obj F) := sorry
    constructor
    · intro a b hh
      let a' : G₂ ⟶ (ihom P).obj F := (ihom.adjunction P).homEquiv _ _ a
      let b' : G₂ ⟶ (ihom P).obj F := (ihom.adjunction P).homEquiv _ _ b
      have : g ≫ a' = g ≫ b' := by
        simp only [Adjunction.homEquiv_unit, Functor.id_obj, Functor.comp_obj, tensorLeft_obj,
          ihom.ihom_adjunction_unit, ihom.coev_naturality_assoc, a', b']
        simp only [← (ihom P).map_comp, hh]
      apply ((ihom.adjunction P).homEquiv _ _).injective
      exact (h ((ihom P).obj F) (hP P)).1 this
    · intro a
      let a' : G₁ ⟶ (ihom P).obj F := (ihom.adjunction P).homEquiv _ _ a
      obtain ⟨b, hb⟩ := (h ((ihom P).obj F) (hP P)).2 a'
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

variable [HasWeakSheafify J A]

noncomputable instance : MonoidalCategory (Sheaf J A) :=
    inferInstanceAs (MonoidalCategory ((LocalizedMonoidal (presheafToSheaf J A) J.W (Iso.refl _))))
