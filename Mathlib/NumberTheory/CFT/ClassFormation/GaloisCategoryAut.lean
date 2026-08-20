/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.NumberTheory.CFT.ClassFormation.GrothendieckTopology
public import Mathlib.NumberTheory.CFT.ClassFormation.GaloisCover

/-!
# Morphisms between automorphisms in Galois categories

-/

-- to be moved to `CategoryTheory/Galois`

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- If `f ≫ g = fg`, this is the morphism between the group of automorphisms
of `Over.mk f` to the group of automorphism of `Over.mk fg`. -/
@[implicit_reducible]
def Aut.overMap {Z Y X : C} (f : Z ⟶ Y) (g : Y ⟶ X) (fg : Z ⟶ X)
    (fac : f ≫ g = fg := by cat_disch) :
    Aut (Over.mk f) →* Aut (Over.mk fg) where
  toFun σ := Over.isoMk ((Over.forget ..).mapIso σ)
    (by simp [← fac, Functor.mapIso, dsimp% σ.hom.w_assoc])
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
lemma Aut.overMap_hom_left {Z Y X : C} (f : Z ⟶ Y) (g : Y ⟶ X) (fg : Z ⟶ X)
    (fac : f ≫ g = fg := by cat_disch) (γ : Aut (Over.mk f)) :
    (Aut.overMap f g fg fac γ).hom.left = γ.hom.left := rfl

lemma Aut.injective_overMap {Z Y X : C} (f : Z ⟶ Y) (g : Y ⟶ X) (fg : Z ⟶ X)
    (fac : f ≫ g = fg := by cat_disch) :
    Function.Injective (overMap f g fg fac) := by
  intro σ₁ σ₂ hσ
  ext
  exact (Over.forget X).congr_map (congr_arg Iso.hom hσ)

noncomputable def Aut.overMapEquiv
    {Z Y X : C} (f : Z ⟶ Y) (g : Y ⟶ X) (fg : Z ⟶ X)
    (fac : f ≫ g = fg := by cat_disch) :
    Aut (Over.mk f) ≃* (Aut.overMap f g fg).range :=
  MulEquiv.ofBijective (overMap f g fg).rangeRestrict ⟨by
    simpa only [MonoidHom.rangeRestrict_injective_iff] using
      Aut.injective_overMap f g fg, MonoidHom.rangeRestrict_surjective _⟩

open PreGaloisCategory

namespace GaloisCategory

variable [GaloisCategory C]

section

variable {Y' Y X : C}
  [PreGaloisCategory.IsConnected X] (f : Y' ⟶ Y) (g : Y ⟶ X) (fg : Y' ⟶ X)
  [IsGaloisCover fg] [IsGaloisCover g]

/-- If `f ≫ g = fg` where both `fg` and `g` are Galois covers, this is
the canonical morphism `Aut (Over.mk fg) →* Aut (Over.mk g)`. -/
noncomputable def autMapOfIsGaloisCover (h : f ≫ g = fg := by cat_disch) :
    Aut (Over.mk fg) →* Aut (Over.mk g) :=
  autMapHom (Over.homMk f)

lemma autMapOfIsGaloisCover_surjective (h : f ≫ g = fg := by cat_disch) :
    Function.Surjective (autMapOfIsGaloisCover f g fg) :=
  autMap_surjective_of_isGalois _

@[reassoc (attr := simp)]
lemma comp_autMapOfIsGaloisCover_hom_left
    (γ : Aut (Over.mk fg)) (h : f ≫ g = fg := by cat_disch) :
    f ≫ ((autMapOfIsGaloisCover f g fg h) γ).hom.left =
      γ.hom.left ≫ f :=
  (Over.forget _).congr_map
    (comp_autMap (Over.homMk f : Over.mk fg ⟶ Over.mk g) γ)

lemma autMapOfIsGaloisCover_eq
    (γ : Aut (Over.mk fg)) (φ : Aut (Over.mk g)) (h : f ≫ g = fg := by cat_disch)
    (hφ : f ≫ φ.hom.left = γ.hom.left ≫ f := by cat_disch) :
    (autMapOfIsGaloisCover f g fg) γ = φ :=
  autMap_unique _ _ _ (by cat_disch)

@[reassoc (attr := simp)]
lemma comp_autMapOfIsGaloisCover_inv_left
    (γ : Aut (Over.mk fg)) (h : f ≫ g = fg := by cat_disch) :
    f ≫ ((autMapOfIsGaloisCover f g fg h) γ).inv.left =
      γ.inv.left ≫ f := by
  simpa using! comp_autMapOfIsGaloisCover_hom_left f g fg γ⁻¹

@[simp]
lemma autMapOfIsGaloisCover_overMap
    (γ : Aut (Over.mk f)) (h : f ≫ g = fg := by cat_disch) :
    (autMapOfIsGaloisCover f g fg h) ((Aut.overMap f g fg h) γ) = 1 :=
  autMapOfIsGaloisCover_eq _ _ _ _ _ (h := h) (hφ := by
    simp [Aut.one_def, dsimp% γ.hom.w])

@[simps]
def kerAutMapOfIsGaloisCoverMulEquiv (h : f ≫ g = fg := by cat_disch) :
    (autMapOfIsGaloisCover f g fg h).ker ≃* Aut (Over.mk f) where
  toFun σ := Over.isoMk ((Over.forget _).mapIso σ.val) (by
    obtain ⟨σ, hσ⟩ := σ
    have := hσ
    simp only [MonoidHom.mem_ker] at hσ
    simpa [hσ, Aut.one_def] using! (comp_autMapOfIsGaloisCover_hom_left f g fg σ).symm)
  invFun σ := ⟨(Aut.overMap f g fg) σ, by simp⟩
  map_mul' := by aesop

lemma autMapOfIsGaloisCover_eq_one_iff (σ : Aut (Over.mk fg))
    (h : f ≫ g = fg := by cat_disch) :
    autMapOfIsGaloisCover f g fg h σ = 1 ↔ σ.hom.left ≫ f = f := by
  refine ⟨fun hσ ↦ ?_, fun hσ ↦ autMapOfIsGaloisCover_eq f g fg _ _ h ?_⟩
  · simpa [hσ, Aut.one_def] using (comp_autMapOfIsGaloisCover_hom_left f g fg σ).symm
  · simpa [Aut.one_def] using hσ.symm

lemma autMapOfIsGaloisCover_eq_one_iff' (σ : Aut (Over.mk fg))
    (h : f ≫ g = fg := by cat_disch) :
    autMapOfIsGaloisCover f g fg h σ = 1 ↔ σ.inv.left ≫ f = f := by
  rw [autMapOfIsGaloisCover_eq_one_iff f g fg]
  refine ⟨fun hσ ↦ ?_, fun hσ ↦ ?_⟩
  · nth_rw 1 [← hσ]
    simp [← Over.comp_left_assoc, σ.inv_hom_id]
  · nth_rw 1 [← hσ]
    simp [← Over.comp_left_assoc, σ.hom_inv_id]

noncomputable def autQuotientMulEquiv (h : f ≫ g = fg := by cat_disch) :
    Aut (Over.mk fg) ⧸ (autMapOfIsGaloisCover f g fg h).ker ≃* Aut (Over.mk g) :=
  MulEquiv.ofBijective (QuotientGroup.lift _ (autMapOfIsGaloisCover f g fg h) (by simp)) (by
    refine ⟨?_, fun σ ↦ ?_⟩
    · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro σ hσ
      induction σ using QuotientGroup.induction_on with | _ σ
      simpa using hσ
    · obtain ⟨σ', rfl⟩ := (autMapOfIsGaloisCover_surjective f g fg) σ
      exact ⟨σ', by simp⟩)

@[simp]
lemma autQuotientMulEquiv_mk (σ : Aut (Over.mk fg)) (h : f ≫ g = fg := by cat_disch) :
  (autQuotientMulEquiv f g fg) σ = (autMapOfIsGaloisCover f g fg) σ := rfl

end

end GaloisCategory

end CategoryTheory
