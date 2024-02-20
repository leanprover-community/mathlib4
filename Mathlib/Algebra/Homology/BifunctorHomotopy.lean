/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.Homotopy

/-!
# The action of a bifunctor on homological complexes factors through homotopies

-/

open CategoryTheory Limits

variable {C₁ C₂ D I₁ I₂ J : Type*} [Category C₁] [Category C₂] [Category D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}

namespace HomologicalComplex

variable {K₁ L₁ : HomologicalComplex C₁ c₁} {f₁ f₁' : K₁ ⟶ L₁} (h₁ : Homotopy f₁ f₁')
  {K₂ L₂ : HomologicalComplex C₂ c₂} (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]
  (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]
  [HasMapBifunctor K₁ K₂ F c]
  [HasMapBifunctor L₁ L₂ F c]

namespace mapBifunctorMapHomotopy

noncomputable def hom₁ (j j' : J) :
    (mapBifunctor K₁ K₂ F c).X j ⟶ (mapBifunctor L₁ L₂ F c).X j' :=
  mapBifunctorDesc (fun i₁ i₂ _ => ComplexShape.ε₁ c₁ c₂ c (c₁.prev i₁, i₂) • (F.map (h₁.hom i₁ (c₁.prev i₁))).app (K₂.X i₂) ≫
    (F.obj (L₁.X (c₁.prev i₁))).map (f₂.f i₂) ≫ ιMapBifunctorOrZero L₁ L₂ F c _ _ j')

lemma ιMapBifunctor_hom₁ (i₁ i₁' : I₁) (i₂ : I₂) (j j' : J)
    (h : ComplexShape.π c₁ c₂ c (i₁', i₂) = j) (h' : c₁.prev i₁' = i₁) :
    ιMapBifunctor K₁ K₂ F c i₁' i₂ j h ≫ hom₁ h₁ f₂ F c j j' = ComplexShape.ε₁ c₁ c₂ c (i₁, i₂) •
      (F.map (h₁.hom i₁' i₁)).app (K₂.X i₂) ≫ (F.obj (L₁.X i₁)).map (f₂.f i₂) ≫ ιMapBifunctorOrZero L₁ L₂ F c _ _ j':= by
  subst h'
  simp [hom₁]

lemma zero₁ (j j' : J) (h : ¬ c.Rel j' j) :
    hom₁ h₁ f₂ F c j j' = 0 := by
  ext i₁ i₂ h'
  dsimp [hom₁]
  rw [comp_zero, ι_mapBifunctorDesc]
  by_cases h₃ : c₁.Rel (c₁.prev i₁) i₁
  · rw [ιMapBifunctorOrZero_eq_zero, comp_zero, comp_zero, smul_zero]
    intro h₄
    apply h
    rw [← h', ← h₄]
    exact ComplexShape.rel_π₁ c₂ c h₃ i₂
  · dsimp
    rw [h₁.zero _ _ h₃, Functor.map_zero, zero_app, zero_comp, smul_zero]

lemma comm₁ (j : J) :
    (mapBifunctorMap f₁ f₂ F c).f j =
    (mapBifunctor K₁ K₂ F c).d j (c.next j) ≫
          mapBifunctorMapHomotopy.hom₁ h₁ f₂ F c (c.next j) j +
        mapBifunctorMapHomotopy.hom₁ h₁ f₂ F c j (c.prev j) ≫
          (mapBifunctor L₁ L₂ F c).d (c.prev j) j +
      (mapBifunctorMap f₁' f₂ F c).f j := by
  ext i₁ i₂ h
  dsimp [ιMapBifunctor, mapBifunctor, mapBifunctorDesc, mapBifunctorMap]
  simp? [h₁.comm i₁, dFrom, fromNext, toPrev, dTo] says
    simp only [HomologicalComplex₂.ιTotal_map, Functor.mapBifunctorHomologicalComplex_obj_obj_X_X,
      HomologicalComplex₂.total_X, Functor.mapBifunctorHomologicalComplex_obj_obj_toGradedObject,
      comp_f, Functor.mapBifunctorHomologicalComplex_map_app_f_f, h₁.comm i₁, dNext_eq_dFrom_fromNext,
      dFrom, fromNext, AddMonoidHom.mk'_apply, prevD_eq_toPrev_dTo, toPrev, dTo, Functor.map_add,
      Functor.map_comp, NatTrans.app_add, NatTrans.comp_app,
      Functor.mapBifunctorHomologicalComplex_obj_map_f_f, Preadditive.add_comp, Category.assoc,
      Preadditive.comp_add, HomologicalComplex₂.ι_D₁_assoc, GradedObject.mapBifunctor_obj_obj,
      HomologicalComplex₂.ι_D₂_assoc, add_left_inj]
  have : ∀ {X Y : D} (a b c d e f : X ⟶ Y), a = c → b = e → f = -d →
      a + b = c + d + (e + f) := by rintro X Y a b _ d _ _ rfl rfl rfl; abel
  apply this
  · by_cases h₃ : c₁.Rel i₁ (c₁.next i₁)
    · rw [HomologicalComplex₂.d₁_eq _ _ h₃ _ _ sorry]
      dsimp
      simp
      erw [ιMapBifunctor_hom₁ _ _ _ _ i₁]
      rw [Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul]
      rw [ιMapBifunctorOrZero_eq]
      rfl
      sorry
    · sorry
  · sorry
  · sorry

end mapBifunctorMapHomotopy

noncomputable def mapBifunctorMapHomotopy₁ :
    Homotopy (mapBifunctorMap f₁ f₂ F c) (mapBifunctorMap f₁' f₂ F c) where
  hom := mapBifunctorMapHomotopy.hom₁ h₁ f₂ F c
  zero := mapBifunctorMapHomotopy.zero₁ h₁ f₂ F c
  comm := mapBifunctorMapHomotopy.comm₁ h₁ f₂ F c

end HomologicalComplex
