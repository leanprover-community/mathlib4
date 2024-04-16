import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Shift.Adjunction

namespace CategoryTheory

open Category Limits Preadditive

namespace Adjunction

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : G ⊣ F)

lemma right_adjoint_additive [G.Additive] : F.Additive where
  map_add {X Y} f g := (adj.homEquiv _ _).symm.injective (by simp)

lemma left_adjoint_additive [F.Additive] : G.Additive where
  map_add {X Y} f g := (adj.homEquiv _ _).injective (by simp)

end Adjunction

variable {C D : Type*} [Category C] [Category D] [HasZeroObject C] [HasZeroObject D]
  [Preadditive C] [Preadditive D] [HasShift C ℤ] [HasShift D ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

namespace Adjunction

open Pretriangulated

variable {G : C ⥤ D} {F : D ⥤ C} (adj : G ⊣ F) [F.CommShift ℤ] [G.CommShift ℤ]
  [adj.CommShift ℤ]
  [G.IsTriangulated]

lemma isTriangulated_rightAdjoint : F.IsTriangulated where
  map_distinguished T hT := by
    have : F.Additive := adj.right_adjoint_additive
    dsimp
    obtain ⟨Z, f, g, mem⟩ := distinguished_cocone_triangle (F.map T.mor₁)
    obtain ⟨h, ⟨h₁, h₂⟩⟩ := complete_distinguished_triangle_morphism _ _ (G.map_distinguished _ mem) hT
      (adj.counit.app T.obj₁) (adj.counit.app T.obj₂) (by simp)
    dsimp at h h₁ h₂
    have h₁' : f ≫ adj.unit.app Z ≫ F.map h = F.map T.mor₂ := by
      simpa using congr_arg (adj.homEquiv _ _).toFun h₁
    have h₂' : g ≫ (F.commShiftIso (1 : ℤ)).inv.app T.obj₁ =
        (adj.homEquiv _ _ h) ≫ F.map T.mor₃ := by
      apply (adj.homEquiv _ _).symm.injective
      simp only [Functor.comp_obj, homEquiv_counit, Functor.id_obj, Functor.map_comp, assoc, homEquiv_unit,
        counit_naturality, counit_naturality_assoc, left_triangle_components_assoc,
        ← h₂, adj.shift_counit_app, Iso.hom_inv_id_app_assoc]
    rw [assoc] at h₂
    have : Mono (adj.homEquiv _ _ h) := by
      rw [mono_iff_cancel_zero]
      intro Y φ hφ
      obtain ⟨ψ, rfl⟩ := Triangle.coyoneda_exact₃ _ mem φ (by
        dsimp
        simp at hφ
        rw [← cancel_mono ((F.commShiftIso (1 : ℤ)).inv.app T.obj₁), assoc, h₂', zero_comp,
          homEquiv_unit, assoc, reassoc_of% hφ, zero_comp])
      dsimp at ψ hφ ⊢
      obtain ⟨α, hα⟩ := T.coyoneda_exact₂ hT ((adj.homEquiv _ _).symm ψ)
        ((adj.homEquiv _ _).injective (by simpa [← h₁'] using hφ))
      have eq := congr_arg (adj.homEquiv _ _ ).toFun hα
      simp only [homEquiv_counit, Functor.id_obj, Equiv.toFun_as_coe, homEquiv_unit,
        Functor.comp_obj, Functor.map_comp, unit_naturality_assoc, right_triangle_components,
        comp_id] at eq
      rw [eq, assoc, assoc]
      erw [comp_distTriang_mor_zero₁₂ _ mem, comp_zero, comp_zero]
    have := isIso_of_yoneda_map_bijective (adj.homEquiv _ _ h) (fun Y => by
      constructor
      · intro φ₁ φ₂ hφ
        rw [← cancel_mono (adj.homEquiv _ _ h)]
        exact hφ
      · intro φ
        obtain ⟨ψ, hψ⟩ := Triangle.coyoneda_exact₁ _ mem (φ ≫ F.map T.mor₃ ≫
          (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) (by
            dsimp
            simp only [assoc]
            rw [← F.commShiftIso_hom_naturality, ← F.map_comp_assoc,
              comp_distTriang_mor_zero₃₁ _ hT, F.map_zero, zero_comp, comp_zero])
        dsimp at ψ hψ
        obtain ⟨α, hα⟩ : ∃ α, α = φ - ψ ≫ (adj.homEquiv _ _) h := ⟨_, rfl⟩
        have hα₀ : α ≫ F.map T.mor₃ = 0 := by
          rw [hα, sub_comp, ← cancel_mono ((Functor.commShiftIso F (1 : ℤ)).hom.app T.obj₁),
            assoc, sub_comp, assoc, assoc, hψ, zero_comp, sub_eq_zero,
            ← cancel_mono ((Functor.commShiftIso F (1 : ℤ)).inv.app T.obj₁), assoc,
            assoc, assoc, assoc, h₂', Iso.hom_inv_id_app, comp_id]
        suffices ∃ (β : Y ⟶ Z), β ≫ (adj.homEquiv _ _) h = α by
          obtain ⟨β, hβ⟩ := this
          refine' ⟨ψ + β, _⟩
          dsimp
          rw [add_comp, hβ, hα, add_sub_cancel]
        obtain ⟨β, hβ⟩ := T.coyoneda_exact₃ hT ((adj.homEquiv _ _).symm α)
          ((adj.homEquiv _ _).injective (by simpa using hα₀))
        refine' ⟨adj.homEquiv _ _ β ≫ f, _⟩
        simpa [h₁'] using congr_arg (adj.homEquiv _ _).toFun hβ.symm)
    refine' isomorphic_distinguished _ mem _ (Iso.symm _)
    refine' Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (asIso (adj.homEquiv Z T.obj₃ h)) _ _ _
    · dsimp
      simp
    · apply (adj.homEquiv _ _).symm.injective
      dsimp
      simp only [homEquiv_unit, homEquiv_counit, Functor.map_comp, assoc,
        counit_naturality, left_triangle_components_assoc, h₁, id_comp]
    · dsimp
      rw [Functor.map_id, comp_id, homEquiv_unit, assoc, ← F.map_comp_assoc, ← h₂,
        Functor.map_comp, Functor.map_comp, assoc, unit_naturality_assoc, assoc,
        Functor.commShiftIso_hom_naturality, ← adj.shift_unit_app_assoc,
        ← Functor.map_comp, right_triangle_components, Functor.map_id, comp_id]

end Adjunction

namespace Equivalence

variable (E : C ≌ D) [E.functor.CommShift ℤ] [E.inverse.CommShift ℤ] [E.CommShift ℤ]

class IsTriangulated : Prop where
  functor_isTriangulated : E.functor.IsTriangulated := by infer_instance
  inverse_isTriangulated : E.inverse.IsTriangulated := by infer_instance

namespace IsTriangulated

attribute [instance] functor_isTriangulated inverse_isTriangulated

lemma mk' (h : E.functor.IsTriangulated) : E.IsTriangulated where
  inverse_isTriangulated := E.toAdjunction.isTriangulated_rightAdjoint

lemma mk'' (h : E.inverse.IsTriangulated) : E.IsTriangulated where
  functor_isTriangulated := (mk' E.symm h).inverse_isTriangulated

end IsTriangulated

end Equivalence

end CategoryTheory
