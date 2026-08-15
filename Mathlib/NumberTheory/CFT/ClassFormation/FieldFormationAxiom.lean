/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.NumberTheory.CFT.ClassFormation.Basic
public import Mathlib.GroupTheory.PGroup

/-!
# THe field formation axiom

-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [GaloisCategory C]

open PreGaloisCategory GaloisCategory

namespace Formation

variable (Φ : Formation C)

lemma isZero_H_of_degMap_eq_one
    {Y X : C} [PreGaloisCategory.IsConnected Y] [PreGaloisCategory.IsConnected X]
    (f : Y ⟶ X) [IsGaloisCover f] (n : ℕ) [NeZero n]
    (hf : degMap f = 1) :
    IsZero (Φ.H f n) := sorry


lemma exists_fac_of_degMap_eq_pow {Y X : C} [PreGaloisCategory.IsConnected Y]
    [PreGaloisCategory.IsConnected X] (f : Y ⟶ X)
    [IsGaloisCover f] {p d : ℕ} [Fact p.Prime]
    (hf : degMap f = p ^ d) (hd : 2 ≤ d) :
    ∃ (d₁ d₂ : ℕ) (hd₁ : 0 ≠ d₁) (hd₂ : 0 ≠ d₂) (hd : d₁ + d₂ = d)
      (Z : C) (a : Y ⟶ Z) (b : Z ⟶ X) (_ : PreGaloisCategory.IsConnected Z),
        a ≫ b = f ∧ IsGaloisCover a ∧ IsGaloisCover b ∧ degMap a = p ^ d₁ ∧
          degMap b = p ^ d₂ := sorry

section

variable {Z Y X : C}
  (f : Z ⟶ Y) (g : Y ⟶ X) (fg : Z ⟶ X)
  [PreGaloisCategory.IsConnected Z] [PreGaloisCategory.IsConnected Y]
  [PreGaloisCategory.IsConnected X]
  [IsGaloisCover f] [IsGaloisCover g] [IsGaloisCover fg]

/-- The short complex consisting of the inflation and the restriction,
in nonzero degree. -/
noncomputable abbrev shortComplexHOfComp
    (n : ℕ) [NeZero n] (hfg : f ≫ g = fg := by cat_disch) :
    ShortComplex Ab.{v} :=
  ShortComplex.mk (Φ.inflation f g fg n) (Φ.restriction f g fg n) sorry

lemma shortComplexHOfComp_one_exact (hfg : f ≫ g = fg := by cat_disch) :
    (Φ.shortComplexHOfComp f g fg 1).Exact := sorry

lemma isZero_H_one_comp (hf : IsZero (Φ.H f 1)) (hg : IsZero (Φ.H g 1))
    (hfg : f ≫ g = fg := by cat_disch) :
    IsZero (Φ.H fg 1) :=
  (Φ.shortComplexHOfComp_one_exact f g fg).isZero_X₂ (hg.eq_of_src ..) (hf.eq_of_tgt ..)

end

/-- The cohomology in degree `1` of a formation vanishes for Galois covers
of degree the power of a prime `p` when it vanishes for cyclic covers of degree `p`. -/
lemma isZero_H_of_isPGroup {Y X : C}
    [PreGaloisCategory.IsConnected Y] [PreGaloisCategory.IsConnected X]
    (f : Y ⟶ X) [IsGaloisCover f] {p : ℕ} [Fact p.Prime]
    (hf : IsPGroup p (Aut (Over.mk f)))
    (h : ∀ ⦃Y' X' : C⦄ (g : Y' ⟶ X') (a : Y ⟶ Y') (b : X' ⟶ X)
      [PreGaloisCategory.IsConnected Y']
      [PreGaloisCategory.IsConnected X'] [IsGaloisCover g],
        a ≫ g ≫ b = f → degMap g = p → IsZero (Φ.H g 1)) :
    IsZero (Φ.H f 1) := by
  rw [IsPGroup.iff_card, natCard_aut_overMk] at hf
  obtain ⟨n, hn'⟩ := hf
  induction n using Nat.strong_induction_on generalizing Y X with | _ n hn
  obtain _ | _ | n := n
  · exact Φ.isZero_H_of_degMap_eq_one f 1 (by simpa using hn')
  · exact h f (𝟙 Y) (𝟙 X) (by simp) (by simpa using hn')
  · obtain ⟨d₁, d₂, _, _, _, Z, a, b, _, fac, _, _, hd₁, hd₂⟩ :=
      exists_fac_of_degMap_eq_pow f hn' (by simp)
    refine Φ.isZero_H_one_comp a b f ?_ ?_ fac
    · exact hn _ (by lia) a (fun _ _  f' a' b' _ _ _ fac' hf' ↦
        h f' a' (b' ≫ b) (by rw [reassoc_of% fac', fac]) hf') hd₁
    · exact hn _ (by lia) b (fun _ _ f' a' b' _ _ _ fac' hf' ↦
        h f' (a ≫ a') b' (by rw [Category.assoc, fac', fac]) hf') hd₂

lemma isZero_H_of_isZero_H_of_isCyclic {Y X : C}
    [PreGaloisCategory.IsConnected Y] [PreGaloisCategory.IsConnected X]
    (f : Y ⟶ X) [IsGaloisCover f]
    (h : ∀ ⦃Y' X' : C⦄ (g : Y' ⟶ X') (a : Y ⟶ Y') (b : X' ⟶ X)
      [PreGaloisCategory.IsConnected Y']
      [PreGaloisCategory.IsConnected X'] [IsGaloisCover g],
        a ≫ g ≫ b = f → Nat.Prime (degMap g) → IsZero (Φ.H g 1)) :
    IsZero (Φ.H f 1) := by
  sorry

end Formation

/-- Constructor for field formations, assuming that the cohomology vanishes
in degree `1` for cyclic covers of prime degree. -/
abbrev FieldFormation.mk' (Φ : Formation C)
    (h : ∀ ⦃Y X : C⦄ [PreGaloisCategory.IsConnected Y] [PreGaloisCategory.IsConnected X]
      (f : Y ⟶ X) [IsGaloisCover f], Nat.Prime (degMap f) → IsZero (Φ.H f 1)) :
    FieldFormation C where
  toFormation := Φ
  isZero_H_one f _ _ _ :=
    Φ.isZero_H_of_isZero_H_of_isCyclic f (fun _ _ g _ _ _ _ _ _ hg ↦ h g hg)

end CategoryTheory
