/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Nick Ward
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# Horns as colimits

In this file, we express horns as colimits:
* horns in `Δ[2]` are pushouts of two copies of `Δ[1]`.

-/

@[expose] public section

universe u

namespace SSet

open CategoryTheory Simplicial Opposite

namespace horn₂₀

lemma sq : Subcomplex.BicartSq.{u} (stdSimplex.face {0}) (stdSimplex.face {0, 1})
    (stdSimplex.face {0, 2}) Λ[2, 0] where
  sup_eq := by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · exact face_le_horn (2 : Fin 3) 0 (by simp)
      · exact face_le_horn (1 : Fin 3) 0 (by simp)
    · rw [horn_eq_iSup, iSup_le_iff]
      rintro i
      fin_cases i
      · exact le_sup_right
      · exact le_sup_left
  inf_eq := by simp [stdSimplex.face_inter_face]

/-- The inclusion `Δ[1] ⟶ Λ[2, 0]` which avoids `2`. -/
abbrev ι₀₁ : Δ[1] ⟶ Λ[2, 0] := horn.ι.{u} 0 2 (by simp)

/-- The inclusion `Δ[1] ⟶ Λ[2, 0]` which avoids `1`. -/
abbrev ι₀₂ : Δ[1] ⟶ Λ[2, 0] := horn.ι.{u} 0 1 (by simp)

lemma isPushout :
    IsPushout (stdSimplex.{u}.δ (1 : Fin 2))
      (stdSimplex.{u}.δ (1 : Fin 2)) ι₀₁ ι₀₂ := by
  fapply sq.{u}.isPushout.of_iso' (stdSimplex.faceSingletonIso _)
    (stdSimplex.facePairIso _ _ (by simp)) (stdSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals decide

end horn₂₀

namespace horn₂₁

lemma sq : Subcomplex.BicartSq.{u} (stdSimplex.face {1}) (stdSimplex.face {0, 1})
    (stdSimplex.face {1, 2}) Λ[2, 1] where
  sup_eq := by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · exact face_le_horn (2 : Fin 3) 1 (by simp)
      · exact face_le_horn (0 : Fin 3) 1 (by simp)
    · rw [horn_eq_iSup, iSup_le_iff]
      rintro i
      fin_cases i
      · exact le_sup_right
      · exact le_sup_left
  inf_eq := by simp [stdSimplex.face_inter_face]

/-- The inclusion `Δ[1] ⟶ Λ[2, 1]` which avoids `2`. -/
abbrev ι₀₁ : Δ[1] ⟶ Λ[2, 1] := horn.ι.{u} 1 2 (by simp)

/-- The inclusion `Δ[1] ⟶ Λ[2, 1]` which avoids `0`. -/
abbrev ι₁₂ : Δ[1] ⟶ Λ[2, 1] := horn.ι.{u} 1 0 (by simp)

lemma isPushout :
    IsPushout (stdSimplex.{u}.δ (0 : Fin 2))
      (stdSimplex.{u}.δ (1 : Fin 2)) ι₀₁ ι₁₂ := by
  apply sq.{u}.isPushout.of_iso' (stdSimplex.faceSingletonIso _ )
    (stdSimplex.facePairIso _ _ (by simp)) (stdSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals decide

end horn₂₁

namespace horn₂₂

lemma sq : Subcomplex.BicartSq.{u} (stdSimplex.face {2}) (stdSimplex.face {0, 2})
    (stdSimplex.face {1, 2}) Λ[2, 2] where
  sup_eq := by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · exact face_le_horn (1 : Fin 3) 2 (by simp)
      · exact face_le_horn (0 : Fin 3) 2 (by simp)
    · rw [horn_eq_iSup, iSup_le_iff]
      rintro i
      fin_cases i
      · exact le_sup_right
      · exact le_sup_left
  inf_eq := by simp [stdSimplex.face_inter_face]

/-- The inclusion `Δ[1] ⟶ Λ[2, 2]` which avoids `1`. -/
abbrev ι₀₂ : Δ[1] ⟶ Λ[2, 2] := horn.ι.{u} 2 1 (by simp)

/-- The inclusion `Δ[1] ⟶ Λ[2, 2]` which avoids `0`. -/
abbrev ι₁₂ : Δ[1] ⟶ Λ[2, 2] := horn.ι.{u} 2 0 (by simp)

lemma isPushout :
    IsPushout (stdSimplex.{u}.δ (0 : Fin 2))
      (stdSimplex.{u}.δ (0 : Fin 2)) ι₀₂ ι₁₂ := by
  fapply sq.{u}.isPushout.of_iso' (stdSimplex.faceSingletonIso _ )
    (stdSimplex.facePairIso _ _ (by simp)) (stdSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals decide

end horn₂₂

end SSet
