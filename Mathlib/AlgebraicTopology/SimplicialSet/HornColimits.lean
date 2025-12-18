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
* horns in `Δ[2]` are pushouts of two copies of `Δ[1]`;
* horns in `Δ[n]` are multicoequalizers of copies of the standard
simplex of dimension `n-1` (a dedicated API is provided for inner
horns in `Δ[3]`).

-/

@[expose] public section

universe u

namespace SSet

open CategoryTheory Simplicial Opposite Limits

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
  apply sq.{u}.isPushout.of_iso' (stdSimplex.faceSingletonIso _)
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
  fapply sq.{u}.isPushout.of_iso' (stdSimplex.faceSingletonIso _)
    (stdSimplex.facePairIso _ _ (by simp)) (stdSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals decide

end horn₂₂

namespace horn

variable {n : ℕ} (i : Fin (n + 1))

/-- The multicoequalizer diagram which expresses `Λ[n, i]` as a gluing
of all `1`-codimensional faces of the standard simplex but one
along suitable `2`-codimensional faces. -/
lemma multicoequalizerDiagram :
    Subcomplex.MulticoequalizerDiagram Λ[n, i]
      (ι := ({i}ᶜ : Set (Fin (n + 1)))) (fun j ↦ stdSimplex.face {j.1}ᶜ)
      (fun j k ↦ stdSimplex.face {j.1, k.1}ᶜ) where
  iSup_eq := by rw [horn_eq_iSup]
  eq_inf j k := by
    rw [stdSimplex.face_inter_face]
    congr
    aesop

/-- The horn is a multicoequalizer of all `1`-codimensional faces of the
standard simplex but one along suitable `2`-codimensional faces. -/
noncomputable def isColimit :
    IsColimit ((multicoequalizerDiagram i).multicofork.toLinearOrder.map
      Subcomplex.toSSetFunctor) :=
  (multicoequalizerDiagram i).isColimit'

end horn

namespace horn₃₁

/-- The inclusion `Δ[2] ⟶ Λ[3, 1]` which avoids `0`. -/
abbrev ι₀ : Δ[2] ⟶ Λ[3, 1] := horn.ι.{u} 1 0 (by simp)

/-- The inclusion `Δ[2] ⟶ Λ[3, 1]` which avoids `2`. -/
abbrev ι₂ : Δ[2] ⟶ Λ[3, 1] := horn.ι.{u} 1 2 (by simp)

/-- The inclusion `Δ[2] ⟶ Λ[3, 1]` which avoids `3`. -/
abbrev ι₃ : Δ[2] ⟶ Λ[3, 1] := horn.ι.{u} 1 3 (by simp)

variable {X : SSet.{u}} (f₀ f₂ f₃ : Δ[2] ⟶ X)
  (h₁₂ : stdSimplex.δ 2 ≫ f₀ = stdSimplex.δ 0 ≫ f₃)
  (h₁₃ : stdSimplex.δ 1 ≫ f₀ = stdSimplex.δ 0 ≫ f₂)
  (h₂₃ : stdSimplex.δ 2 ≫ f₂ = stdSimplex.δ 2 ≫ f₃)

/-- Auxiliary definition for `desc`. -/
@[simps! pt]
def desc.multicofork :
    Multicofork ((horn.multicoequalizerDiagram (1 : Fin 4)).multispanIndex.toLinearOrder.map
      Subcomplex.toSSetFunctor) :=
  Multicofork.ofπ _ X (fun ⟨(i : Fin 4), hi⟩ ↦ match i with
    | 0 => (stdSimplex.faceSingletonComplIso 0).inv ≫ f₀
    | 1 => False.elim (by simp at hi)
    | 2 => (stdSimplex.faceSingletonComplIso 2).inv ≫ f₂
    | 3 => (stdSimplex.faceSingletonComplIso 3).inv ≫ f₃) (fun x ↦ by
      dsimp at x ⊢
      fin_cases x
      · simp only [← cancel_epi (stdSimplex.facePairIso.{u} (n := 3) 1 3 (by simp)).hom,
          ← Category.assoc]
        convert h₁₃ <;> decide
      · dsimp
        simp only [← cancel_epi (stdSimplex.facePairIso.{u} (n := 3) 1 2 (by simp)).hom,
          ← Category.assoc]
        convert h₁₂ <;> decide
      · dsimp
        simp only [← cancel_epi (stdSimplex.facePairIso.{u} (n := 3) 0 1 (by simp)).hom,
          ← Category.assoc]
        convert h₂₃ <;> decide)

@[simp, reassoc]
lemma desc.multicofork_π_zero :
  (desc.multicofork f₀ f₂ f₃ h₁₂ h₁₃ h₂₃).π ⟨0, by simp⟩ =
    (stdSimplex.faceSingletonComplIso 0).inv ≫ f₀ := rfl

@[simp, reassoc]
lemma desc.multicofork_π_two :
  (desc.multicofork f₀ f₂ f₃ h₁₂ h₁₃ h₂₃).π ⟨2, by simp⟩ =
    (stdSimplex.faceSingletonComplIso 2).inv ≫ f₂ := rfl

@[simp, reassoc]
lemma desc.multicofork_π_three :
  (desc.multicofork f₀ f₂ f₃ h₁₂ h₁₃ h₂₃).π ⟨3, by simp⟩ =
    (stdSimplex.faceSingletonComplIso 3).inv ≫ f₃ := rfl

/-- The morphism `Λ[3, 1] ⟶ X` which is obtained by gluing three
morphisms `Δ[2] ⟶ X`. -/
noncomputable def desc : (Λ[3, 1] : SSet) ⟶ X :=
  (horn.isColimit (n := 3) 1).desc (desc.multicofork f₀ f₂ f₃ h₁₂ h₁₃ h₂₃)

@[reassoc (attr := simp)]
lemma ι₀_desc : ι₀ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₀ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 0).inv, ← Category.assoc,
    horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 1).fac _ (.right ⟨0, by simp⟩)

@[reassoc (attr := simp)]
lemma ι₂_desc : ι₂ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₂ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 2).inv, ← Category.assoc,
    horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 1).fac _ (.right ⟨2, by simp⟩)

@[reassoc (attr := simp)]
lemma ι₃_desc : ι₃ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₃ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 3).inv, ← Category.assoc,
    horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 1).fac _ (.right ⟨3, by simp⟩)

include h₁₂ h₁₃ h₂₃ in
lemma exists_desc : ∃ (φ : (Λ[3, 1] : SSet) ⟶ X),
    ι₀ ≫ φ = f₀ ∧ ι₂ ≫ φ = f₂ ∧ ι₃ ≫ φ = f₃ :=
  ⟨desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃, by simp⟩

end horn₃₁

namespace horn₃₂

/-- The inclusion `Δ[2] ⟶ Λ[3, 2]` which avoids `0`. -/
abbrev ι₀ : Δ[2] ⟶ Λ[3, 2] := horn.ι.{u} 2 0 (by simp)

/-- The inclusion `Δ[2] ⟶ Λ[3, 2]` which avoids `1`. -/
abbrev ι₁ : Δ[2] ⟶ Λ[3, 2] := horn.ι.{u} 2 1 (by simp)

/-- The inclusion `Δ[2] ⟶ Λ[3, 2]` which avoids `3`. -/
abbrev ι₃ : Δ[2] ⟶ Λ[3, 2] := horn.ι.{u} 2 3 (by simp)

variable {X : SSet.{u}} (f₀ f₁ f₃ : Δ[2] ⟶ X)
  (h₀₂ : stdSimplex.δ 2 ≫ f₁ = stdSimplex.δ 1 ≫ f₃)
  (h₁₂ : stdSimplex.δ 2 ≫ f₀ = stdSimplex.δ 0 ≫ f₃)
  (h₂₃ : stdSimplex.δ 0 ≫ f₀ = stdSimplex.δ 0 ≫ f₁)

/-- Auxiliary definition for `desc`. -/
@[simps! pt]
def desc.multicofork :
    Multicofork ((horn.multicoequalizerDiagram (2 : Fin 4)).multispanIndex.toLinearOrder.map
      Subcomplex.toSSetFunctor) :=
  Multicofork.ofπ _ X (fun ⟨(i : Fin 4), hi⟩ ↦ match i with
    | 0 => (stdSimplex.faceSingletonComplIso 0).inv ≫ f₀
    | 1 => (stdSimplex.faceSingletonComplIso 1).inv ≫ f₁
    | 2 => False.elim (by simp at hi)
    | 3 => (stdSimplex.faceSingletonComplIso 3).inv ≫ f₃) (fun x ↦ by
      dsimp at x ⊢
      fin_cases x
      · dsimp
        simp only [← cancel_epi (stdSimplex.facePairIso.{u} (n := 3) 2 3 (by simp)).hom,
          ← Category.assoc]
        convert h₂₃ <;> decide
      · dsimp
        simp only [← cancel_epi (stdSimplex.facePairIso.{u} (n := 3) 1 2 (by simp)).hom,
          ← Category.assoc]
        convert h₁₂ <;> decide
      · dsimp
        simp only [← cancel_epi (stdSimplex.facePairIso.{u} (n := 3) 0 2 (by simp)).hom,
          ← Category.assoc]
        convert h₀₂ <;> decide)

@[simp, reassoc]
lemma desc.multicofork_π_zero :
  (desc.multicofork f₀ f₁ f₃ h₀₂ h₁₂ h₂₃).π ⟨0, by simp⟩ =
    (stdSimplex.faceSingletonComplIso 0).inv ≫ f₀ := rfl

@[simp, reassoc]
lemma desc.multicofork_π_one :
  (desc.multicofork f₀ f₁ f₃ h₀₂ h₁₂ h₂₃).π ⟨1, by simp⟩ =
    (stdSimplex.faceSingletonComplIso 1).inv ≫ f₁ := rfl

@[simp, reassoc]
lemma desc.multicofork_π_three :
  (desc.multicofork f₀ f₁ f₃ h₀₂ h₁₂ h₂₃).π ⟨3, by simp⟩ =
    (stdSimplex.faceSingletonComplIso 3).inv ≫ f₃ := rfl

/-- The morphism `Λ[3, 2] ⟶ X` which is obtained by gluing three
morphisms `Δ[2] ⟶ X`. -/
noncomputable def desc : (Λ[3, 2] : SSet) ⟶ X :=
  (horn.isColimit (n := 3) 2).desc (desc.multicofork f₀ f₁ f₃ h₀₂ h₁₂ h₂₃)

@[reassoc (attr := simp)]
lemma ι₀_desc : ι₀ ≫ desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ = f₀ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 0).inv, ← Category.assoc,
    horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 2).fac _ (.right ⟨0, by simp⟩)

@[reassoc (attr := simp)]
lemma ι₁_desc : ι₁ ≫ desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ = f₁ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 1).inv, ← Category.assoc,
    horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 2).fac _ (.right ⟨1, by simp⟩)

@[reassoc (attr := simp)]
lemma ι₃_desc : ι₃ ≫ desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ = f₃ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 3).inv, ← Category.assoc,
    horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 2).fac _ (.right ⟨3, by simp⟩)

include h₀₂ h₁₂ h₂₃ in
lemma exists_desc : ∃ (φ : (Λ[3, 2] : SSet) ⟶ X),
    ι₀ ≫ φ = f₀ ∧ ι₁ ≫ φ = f₁ ∧ ι₃ ≫ φ = f₃ :=
  ⟨desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃, by simp⟩

end horn₃₂

end SSet
