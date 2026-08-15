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

lemma isZero_H_of_subsingleton
    {Y X : C} [PreGaloisCategory.IsConnected Y] [PreGaloisCategory.IsConnected X]
    (f : Y ⟶ X) [IsGaloisCover f] (n : ℕ) [NeZero n]
    (hf : Subsingleton (Aut (Over.mk f)) := by infer_instance) :
    IsZero (Φ.H f n) := sorry

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

/-- The cohomology of a formation in degree `1` vanishes. -/
lemma isZero_H_of_isPGroup {Y X : C}
    [PreGaloisCategory.IsConnected Y] [PreGaloisCategory.IsConnected X]
    (f : Y ⟶ X) [IsGaloisCover f] {p : ℕ} [Fact p.Prime]
    (hf : IsPGroup p (Aut (Over.mk f)))
    (h : ∀ ⦃Y' X' : C⦄ (g : Y' ⟶ X') (a : Y ⟶ Y') (b : X' ⟶ X)
      [PreGaloisCategory.IsConnected Y']
      [PreGaloisCategory.IsConnected X'] [IsGaloisCover g] [IsCyclic (Aut (Over.mk f))],
        a ≫ g ≫ b = f → Nat.card (Aut (Over.mk f)) = p → IsZero (Φ.H g 1)) :
    IsZero (Φ.H f 1) := by
  rw [IsPGroup.iff_card] at hf
  obtain ⟨n, hn⟩ := hf
  induction n using Nat.strong_induction_on generalizing Y X with | _ n hn
  obtain _ | _ | n := n
  · refine Φ.isZero_H_of_subsingleton _ _ ?_
    simp only [pow_zero] at hn
    rw [← Finite.card_le_one_iff_subsingleton]
    lia
  · simp only [zero_add, pow_one] at hn
    have : IsCyclic (Aut (Over.mk f)) := isCyclic_of_prime_card hn
    exact h f (𝟙 Y) (𝟙 X) (by simp) hn
  · sorry

lemma isZero_H_of_isZero_H_of_isCyclic {Y X : C}
    [PreGaloisCategory.IsConnected Y] [PreGaloisCategory.IsConnected X]
    (f : Y ⟶ X) [IsGaloisCover f]
    (h : ∀ ⦃Y' X' : C⦄ (g : Y' ⟶ X') (a : Y ⟶ Y') (b : X' ⟶ X)
      [PreGaloisCategory.IsConnected Y']
      [PreGaloisCategory.IsConnected X'] [IsGaloisCover g] [IsCyclic (Aut (Over.mk g))],
        a ≫ g ≫ b = f → Nat.Prime (Nat.card (Aut (Over.mk g))) → IsZero (Φ.H g 1)) :
    IsZero (Φ.H f 1) := by
  sorry

end Formation

/-- Constructor for field formations, assuming that the cohomology vanishes
in degree `1` for cyclic covers of prime degree. -/
abbrev FieldFormation.mk' (Φ : Formation C)
    (h : ∀ ⦃Y X : C⦄ [PreGaloisCategory.IsConnected Y] [PreGaloisCategory.IsConnected X]
      (f : Y ⟶ X) [IsGaloisCover f] [IsCyclic (Aut (Over.mk f))],
        Nat.Prime (Nat.card (Aut (Over.mk f))) → IsZero (Φ.H f 1)) :
    FieldFormation C where
  toFormation := Φ
  isZero_H_one f _ _ _ :=
    Φ.isZero_H_of_isZero_H_of_isCyclic f (fun _ _ g _ _ _ _ _ _ _ hg ↦ h g hg)

end CategoryTheory
