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

namespace SSet

open CategoryTheory Simplicial Opposite Limits

universe u

namespace horn₂₀

lemma sq : Subcomplex.BicartSq (stdSimplex.face {0}) (stdSimplex.face {0, 1})
    (stdSimplex.face {0, 2}) (horn 2 0) where
  max_eq := by
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
  min_eq := by simp [stdSimplex.face_inter_face]

/-- The inclusion `Δ[1] ⟶ horn 2 0` which avoids `2`. -/
abbrev ι₀₁ : Δ[1] ⟶ horn.{u} 2 0 := horn.ι 0 2 (by simp)

/-- The inclusion `Δ[1] ⟶ horn 2 0` which avoids `1`. -/
abbrev ι₀₂ : Δ[1] ⟶ horn.{u} 2 0 := horn.ι 0 1 (by simp)

lemma isPushout :
    IsPushout (stdSimplex.{u}.δ (1 : Fin 2))
      (stdSimplex.{u}.δ (1 : Fin 2)) ι₀₁ ι₀₂ := by
  fapply sq.{u}.isPushout.of_iso' (stdSimplex.faceSingletonIso _)
    (stdSimplex.facePairIso _ _ (by simp)) (stdSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals decide

end horn₂₀

namespace horn₂₁

lemma sq : Subcomplex.BicartSq (stdSimplex.face {1}) (stdSimplex.face {0, 1})
    (stdSimplex.face {1, 2}) (horn 2 1) where
  max_eq := by
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
  min_eq := by simp [stdSimplex.face_inter_face]

/-- The inclusion `Δ[1] ⟶ horn 2 1` which avoids `2`. -/
abbrev ι₀₁ : Δ[1] ⟶ horn.{u} 2 1 := horn.ι 1 2 (by simp)

/-- The inclusion `Δ[1] ⟶ horn 2 1` which avoids `0`. -/
abbrev ι₁₂ : Δ[1] ⟶ horn.{u} 2 1 := horn.ι 1 0 (by simp)

lemma isPushout :
    IsPushout (stdSimplex.{u}.δ (0 : Fin 2))
      (stdSimplex.{u}.δ (1 : Fin 2)) ι₀₁ ι₁₂ := by
  apply sq.{u}.isPushout.of_iso' (stdSimplex.faceSingletonIso _ )
    (stdSimplex.facePairIso _ _ (by simp)) (stdSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals decide

end horn₂₁

namespace horn₂₂

lemma sq : Subcomplex.BicartSq (stdSimplex.face {2}) (stdSimplex.face {0, 2})
    (stdSimplex.face {1, 2}) (horn 2 2) where
  max_eq := by
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
  min_eq := by simp [stdSimplex.face_inter_face]

/-- The inclusion `Δ[1] ⟶ horn 2 2` which avoids `1`. -/
abbrev ι₀₂ : Δ[1] ⟶ horn.{u} 2 2 := horn.ι 2 1 (by simp)

/-- The inclusion `Δ[1] ⟶ horn 2 2` which avoids `0`. -/
abbrev ι₁₂ : Δ[1] ⟶ horn.{u} 2 2 := horn.ι 2 0 (by simp)

lemma isPushout :
    IsPushout (stdSimplex.{u}.δ (0 : Fin 2))
      (stdSimplex.{u}.δ (0 : Fin 2)) ι₀₂ ι₁₂ := by
  fapply sq.{u}.isPushout.of_iso' (stdSimplex.faceSingletonIso _ )
    (stdSimplex.facePairIso _ _ (by simp)) (stdSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals decide

end horn₂₂


namespace horn

section

variable {n : ℕ} (i : Fin (n + 1))

/-- The multicoequalizer diagram which expresses a `horn n i` as a gluing
of all `1`-codimensional faces of the standard simplex but one
along suitable `2`-codimensional faces. -/
lemma multicoequalizerDiagram :
  Subcomplex.MulticoequalizerDiagram (horn n i)
    (ι := ({i}ᶜ : Set (Fin (n +1)))) (fun j ↦ stdSimplex.face {j.1}ᶜ)
    (fun j k ↦ stdSimplex.face {j.1, k.1}ᶜ) where
  iSup_eq := by rw [horn_eq_iSup]
  min_eq j k := by
    rw [stdSimplex.face_inter_face]
    congr
    aesop

/-- The horn is a multicoequalizer of all `1`-codimensional faces of the
standard simplex but one along suitable `2`-codimensional faces. -/
noncomputable def isColimit :
    IsColimit ((multicoequalizerDiagram i).multicofork.toLinearOrder.map
      Subcomplex.toSSetFunctor) :=
  (multicoequalizerDiagram i).isColimit'

lemma exists_desc' {X : SSet.{u}}
    (f : ∀ (j : ({i}ᶜ : Set _)), (stdSimplex.face {j.1}ᶜ : SSet) ⟶ X)
    (hf : ∀ (j k : ({i}ᶜ : Set _)) (_ : j.1 < k.1),
      Subcomplex.homOfLE (show stdSimplex.face {j.1, k.1}ᶜ ≤ _ by
        simp [stdSimplex.face_le_face_iff]) ≫ f j =
      Subcomplex.homOfLE (show stdSimplex.face {j.1, k.1}ᶜ ≤ _ by
        simp [stdSimplex.face_le_face_iff]) ≫ f k) :
    ∃ (φ : (Λ[n, i] : SSet) ⟶ X),
      ∀ j, faceι i j.1 (by simpa only [Finset.mem_compl, Finset.mem_singleton] using j.2) ≫
        φ = f j :=
  ⟨(isColimit i).desc (Multicofork.ofπ _ _ f (fun s ↦ hf _ _ s.2)),
    fun j ↦ (isColimit i).fac _ (.right j)⟩

end

open stdSimplex in
lemma exists_desc {n : ℕ} {i : Fin (n + 3)} {X : SSet.{u}}
    (f : ({i}ᶜ : Set _) → ((Δ[n + 1] : SSet) ⟶ X))
    (hf : ∀ (j k : ({i}ᶜ : Set _)) (hjk : j.1 < k.1),
      stdSimplex.δ (k.1.pred (Fin.ne_zero_of_lt hjk)) ≫ f j =
        stdSimplex.δ (j.1.castPred (Fin.ne_last_of_lt hjk)) ≫ f k) :
    ∃ (φ : (Λ[n + 2, i] : SSet) ⟶ X), ∀ j, ι i j.1 j.2 ≫ φ = f j := by
  obtain ⟨φ, hφ⟩ := exists_desc' (i := i)
    (f := fun j ↦
      (faceSingletonComplIso j.1).inv ≫ f j) (fun j k hjk ↦ by
        dsimp
        sorry
        --rw [homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_δ_pred_assoc _ _ hjk,
        --  homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_δ_castPred_assoc _ _ hjk,
        --  hf _ _ hjk]
        )
  exact ⟨φ, fun j ↦ by
    rw [← cancel_epi (faceSingletonComplIso j.1).inv, ← hφ,
      faceSingletonComplIso_inv_ι_assoc]⟩

lemma hom_ext' {n : ℕ} {i : Fin (n + 2)} {X : SSet.{u}} {f g : (Λ[n + 1, i] : SSet) ⟶ X}
    (h : ∀ (j : Fin (n + 2)) (hij : j ≠ i), horn.ι i j hij ≫ f = horn.ι i j hij ≫ g) :
    f = g := by
  sorry
  /-
  apply Multicofork.IsColimit.hom_ext
    (Subcomplex.multicoforkIsColimit (multicoequalizerDiagram i))
  intro ⟨j, hj⟩
  dsimp [CompleteLattice.MulticoequalizerDiagram.multicofork, Multicofork.ofπ,
    Multicofork.map, Multicofork.π]
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso j).hom]
  exact h _ hj-/

end horn

namespace horn₃₁

/-- The inclusion `Δ[2] ⟶ horn 3 1` which avoids `0`. -/
abbrev ι₀ : Δ[2] ⟶ horn.{u} 3 1 := horn.ι 1 0 (by simp)

/-- The inclusion `Δ[2] ⟶ horn 3 1` which avoids `2`. -/
abbrev ι₂ : Δ[2] ⟶ horn.{u} 3 1 := horn.ι 1 2 (by simp)

/-- The inclusion `Δ[2] ⟶ horn 3 1` which avoids `3`. -/
abbrev ι₃ : Δ[2] ⟶ horn.{u} 3 1 := horn.ι 1 3 (by simp)

variable {X : SSet.{u}} (f₀ f₂ f₃ : Δ[2] ⟶ X)
  (h₁₂ : stdSimplex.δ 2 ≫ f₀ = stdSimplex.δ 0 ≫ f₃)
  (h₁₃ : stdSimplex.δ 1 ≫ f₀ = stdSimplex.δ 0 ≫ f₂)
  (h₂₃ : stdSimplex.δ 2 ≫ f₂ = stdSimplex.δ 2 ≫ f₃)

/-- Auxiliary definition for `desc`. -/
@[simps!]
def desc.multicofork :
    Multicofork ((horn.multicoequalizerDiagram (1 : Fin 4)).multispanIndex.toLinearOrder.map
      Subcomplex.toSSetFunctor) :=
  Multicofork.ofπ _ X (fun ⟨(i : Fin 4), hi⟩ ↦ match i with
    | 0 => (stdSimplex.faceSingletonComplIso 0).inv ≫ f₀
    | 1 => by simp at hi
    | 2 => (stdSimplex.faceSingletonComplIso 2).inv ≫ f₂
    | 3 => (stdSimplex.faceSingletonComplIso 3).inv ≫ f₃) (by
      dsimp
      intro x
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

/-- The morphism `horn 3 1 ⟶ X` which is obtained by gluing three
morphisms `Δ[2] ⟶ X`. -/
noncomputable def desc : (horn 3 1 : SSet) ⟶ X :=
  (horn.isColimit (n := 3) 1).desc (desc.multicofork f₀ f₂ f₃ h₁₂ h₁₃ h₂₃)

@[reassoc (attr := simp)]
lemma ι₀_desc : ι₀ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₀ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso 0).inv, ← Category.assoc,
    horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 1).fac _ (.right ⟨0, by simp⟩)

@[reassoc (attr := simp)]
lemma ι₂_desc : ι₂ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₂ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso 2).inv, ← Category.assoc,
    horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 1).fac _ (.right ⟨2, by simp⟩)

@[reassoc (attr := simp)]
lemma ι₃_desc : ι₃ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₃ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso 3).inv, ← Category.assoc,
    horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 1).fac _ (.right ⟨3, by simp⟩)

include h₁₂ h₁₃ h₂₃ in
lemma exists_desc : ∃ (φ : (horn 3 1 : SSet) ⟶ X),
    ι₀ ≫ φ = f₀ ∧ ι₂ ≫ φ = f₂ ∧ ι₃ ≫ φ = f₃ :=
  ⟨desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃, by simp⟩

end horn₃₁

namespace horn₃₂

/-- The inclusion `Δ[2] ⟶ horn 3 2` which avoids `0`. -/
abbrev ι₀ : Δ[2] ⟶ horn.{u} 3 2 := horn.ι 2 0 (by simp)

/-- The inclusion `Δ[2] ⟶ horn 3 2` which avoids `1`. -/
abbrev ι₁ : Δ[2] ⟶ horn.{u} 3 2 := horn.ι 2 1 (by simp)

/-- The inclusion `Δ[2] ⟶ horn 3 2` which avoids `3`. -/
abbrev ι₃ : Δ[2] ⟶ horn.{u} 3 2 := horn.ι 2 3 (by simp)

variable {X : SSet.{u}} (f₀ f₁ f₃ : Δ[2] ⟶ X)
  (h₀₂ : stdSimplex.δ 2 ≫ f₁ = stdSimplex.δ 1 ≫ f₃)
  (h₁₂ : stdSimplex.δ 2 ≫ f₀ = stdSimplex.δ 0 ≫ f₃)
  (h₂₃ : stdSimplex.δ 0 ≫ f₀ = stdSimplex.δ 0 ≫ f₁)

/-- Auxiliary definition for `desc`. -/
@[simps!]
def desc.multicofork :
    Multicofork ((horn.multicoequalizerDiagram (2 : Fin 4)).multispanIndex.toLinearOrder.map
      Subcomplex.toSSetFunctor) :=
  Multicofork.ofπ _ X (fun ⟨(i : Fin 4), hi⟩ ↦ match i with
    | 0 => (stdSimplex.faceSingletonComplIso 0).inv ≫ f₀
    | 1 => (stdSimplex.faceSingletonComplIso 1).inv ≫ f₁
    | 2 => by simp at hi
    | 3 => (stdSimplex.faceSingletonComplIso 3).inv ≫ f₃) (by
      dsimp
      intro x
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

/-- The morphism `horn 3 2 ⟶ X` which is obtained by gluing three
morphisms `Δ[2] ⟶ X`. -/
noncomputable def desc : (horn 3 2 : SSet) ⟶ X :=
  (horn.isColimit (n := 3) 2).desc (desc.multicofork f₀ f₁ f₃ h₀₂ h₁₂ h₂₃)

@[reassoc (attr := simp)]
lemma ι₀_desc : ι₀ ≫ desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ = f₀ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso 0).inv, ← Category.assoc,
    horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 2).fac _ (.right ⟨0, by simp⟩)

@[reassoc (attr := simp)]
lemma ι₁_desc : ι₁ ≫ desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ = f₁ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso 1).inv, ← Category.assoc,
    horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 2).fac _ (.right ⟨1, by simp⟩)

@[reassoc (attr := simp)]
lemma ι₃_desc : ι₃ ≫ desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ = f₃ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso 3).inv, ← Category.assoc,
    horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 2).fac _ (.right ⟨3, by simp⟩)

include h₀₂ h₁₂ h₂₃ in
lemma exists_desc : ∃ (φ : (horn 3 2 : SSet) ⟶ X),
    ι₀ ≫ φ = f₀ ∧ ι₁ ≫ φ = f₁ ∧ ι₃ ≫ φ = f₃ :=
  ⟨desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃, by simp⟩

end horn₃₂

end SSet
