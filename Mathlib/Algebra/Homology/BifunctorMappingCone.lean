/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Action of bifunctor on mapping cones
-/

open CategoryTheory Limits HomologicalComplex

namespace CochainComplex

variable
  {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
  [Preadditive C₁] [HasZeroMorphisms C₂]
  {K₁ L₁ : CochainComplex C₁ ℤ} (φ : K₁ ⟶ L₁) (K₂ : CochainComplex C₂ ℤ) [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive]
  [∀ (X₁ : C₁), (F.obj X₁).PreservesZeroMorphisms]
  [HasHomotopyCofiber φ]

open HomComplex mappingCone

namespace mapBifunctorMappingCone₁Iso

variable [HasMapBifunctor (mappingCone φ) K₂ F (ComplexShape.up ℤ)]

section

variable [HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]

noncomputable def p₁₀ : Cochain (mapBifunctor (mappingCone φ) K₂ F (.up ℤ))
    (mapBifunctor K₁ K₂ F (.up ℤ)) 1 :=
  Cochain.mk (fun n m hnm ↦ mapBifunctorDesc (fun p q hpq ↦
    (F.map ((fst φ).1.v p _ rfl)).app _ ≫
      ιMapBifunctor _ _ _ _ _ _ _ (by dsimp at hpq ⊢; omega)))

@[reassoc]
lemma ι_p₁₀_v (p q n : ℤ) (hpq : p + q = n) (m : ℤ) (hnm : n + 1 = m)
    (p' : ℤ) (hp' : p + 1 = p') :
   ιMapBifunctor (mappingCone φ) K₂ F (.up ℤ) p q n hpq ≫
      (p₁₀ φ K₂ F).v n m hnm = (F.map ((fst φ).1.v p p' hp')).app _ ≫
        ιMapBifunctor _ _ _ _ _ _ _ (by dsimp; omega) := by
  subst hp'
  simp [p₁₀]

@[simps!]
noncomputable def p₁ : Cocycle (mapBifunctor (mappingCone φ) K₂ F (.up ℤ))
    (mapBifunctor K₁ K₂ F (.up ℤ)) 1 :=
  Cocycle.mk (p₁₀ φ K₂ F) 2 (by omega) (by
    ext n _ rfl p q hpq
    dsimp at hpq
    have h₁ : (ComplexShape.up ℤ).Rel (p + 1) (p + 2) := by dsimp; omega
    have h₂ : (ComplexShape.up ℤ).Rel q (q + 1) := rfl
    have h₃ : (ComplexShape.up ℤ).Rel p (p + 1) := rfl
    simp [δ_v 1 2 rfl _ n (n + 2) rfl (n + 1) (n + 1) (by omega) rfl,
      ι_p₁₀_v_assoc _ _ _ p q n hpq (n + 1) rfl (p + 1) rfl,
      ι_p₁₀_v _ _ _ p (q + 1) (n + 1) (by omega) (n + 2) (by omega) (p + 1) rfl,
      ι_p₁₀_v _ _ _ (p + 1) q (n + 1) (by omega) (n + 2) (by omega) (p + 2) (by omega),
      mapBifunctor.d_eq, Int.negOnePow_even 2 ⟨1, rfl⟩,
      mapBifunctor.d₁_eq K₁ K₂ F (.up ℤ) h₁ q (n + 2) (by dsimp; omega),
      mapBifunctor.d₂_eq K₁ K₂ F (.up ℤ) (p + 1) h₂ (n + 2) (by dsimp; omega),
      mapBifunctor.d₁_eq (mappingCone φ) K₂ F (.up ℤ) h₃ q (n + 1) (by dsimp; omega),
      mapBifunctor.d₂_eq (mappingCone φ) K₂ F (.up ℤ) p h₂ (n + 1) (by dsimp; omega),
      Int.negOnePow_succ, ← Functor.map_comp, ← Functor.map_comp_assoc,
      ← NatTrans.comp_app_assoc, ← NatTrans.comp_app,
      d_fst_v φ p (p + 1) (p + 2) rfl (by omega)]
    abel)

end

section

variable [HasMapBifunctor L₁ K₂ F (ComplexShape.up ℤ)]

noncomputable def p₂ : Cochain (mapBifunctor (mappingCone φ) K₂ F (.up ℤ))
    (mapBifunctor L₁ K₂ F (.up ℤ)) 0 :=
  Cochain.ofHoms (fun _ ↦ mapBifunctorDesc (fun _ _ hpq ↦
    (F.map ((snd φ).v _ _ (add_zero _))).app _ ≫
      ιMapBifunctor _ _ _ _ _ _ _ hpq))

@[reassoc (attr := simp)]
lemma ι_p₂_v (p q n : ℤ) (hpq : p + q = n) :
    ιMapBifunctor (mappingCone φ) K₂ F (.up ℤ) p q n hpq ≫ (p₂ φ K₂ F).v n n (add_zero n) =
      (F.map ((snd φ).v _ _ (add_zero _))).app _ ≫
        ιMapBifunctor _ _ _ _ _ _ _ hpq := by
  simp [p₂]

end

variable [HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
  [HasMapBifunctor L₁ K₂ F (ComplexShape.up ℤ)]
  [HasHomotopyCofiber (mapBifunctorMap φ (𝟙 K₂) F (.up ℤ))]

noncomputable def hom : mapBifunctor (mappingCone φ) K₂ F (.up ℤ) ⟶
      mappingCone (mapBifunctorMap φ (𝟙 K₂) F (.up ℤ)) :=
  mappingCone.lift _ (p₁ φ K₂ F) (p₂ φ K₂ F) (by
    ext n _ rfl p q hpq
    dsimp at hpq
    have h₁ : (ComplexShape.up ℤ).Rel q (q + 1) := rfl
    have h₂ : (ComplexShape.up ℤ).Rel p (p + 1) := rfl
    simp [mapBifunctor.d_eq, ι_p₁₀_v_assoc _ _ _ p q n _ _ rfl _ rfl,
      mapBifunctor.d₁_eq (mappingCone φ) K₂ F (.up ℤ) h₂ q (n + 1) (by dsimp; omega),
      mapBifunctor.d₂_eq (mappingCone φ) K₂ F (.up ℤ) p h₁ (n + 1) (by dsimp; omega),
      mapBifunctor.d₁_eq L₁ K₂ F (.up ℤ) h₂ q (n + 1) (by dsimp; omega),
      mapBifunctor.d₂_eq L₁ K₂ F (.up ℤ) p h₁ (n + 1) (by dsimp; omega),
      ← Functor.map_comp, ← Functor.map_comp_assoc,
      ← NatTrans.comp_app_assoc, ← NatTrans.comp_app, d_snd_v])

end mapBifunctorMappingCone₁Iso

variable [HasMapBifunctor (mappingCone φ) K₂ F (ComplexShape.up ℤ)]
  [HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
  [HasMapBifunctor L₁ K₂ F (ComplexShape.up ℤ)]
  [HasHomotopyCofiber (mapBifunctorMap φ (𝟙 K₂) F (.up ℤ))]

/-open mapBifunctorMappingCone₁Iso in
noncomputable def mapBifunctorMappingCone₁Iso :
    mapBifunctor (mappingCone φ) K₂ F (.up ℤ) ≅
      mappingCone (mapBifunctorMap φ (𝟙 K₂) F (.up ℤ)) where
  hom := hom φ K₂ F
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry-/

end CochainComplex
